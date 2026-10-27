# Fast replacement for grid13's edge_feasible: same LP, but (1) accept immediately if some cell corner
# satisfies all constraints, (2) otherwise call HiGHS's C API (Highs_lpCall) directly on plain arrays.
using HiGHS, LinearAlgebra
const HIGHS_INFEASIBLE = 8     # kHighsModelStatusInfeasible
# one persistent single-threaded HiGHS instance per Julia thread
const HIGHS_POOL = Dict{Int,Ptr{Cvoid}}()
const HIGHS_POOL_LOCK = ReentrantLock()
function highs_instance_unlocked()
    begin
        get!(HIGHS_POOL, 0) do
            h = HiGHS.Highs_create()
            HiGHS.Highs_setBoolOptionValue(h, "output_flag", false)
            h
        end
    end
end
rowfun(M, f) = ntuple(i -> sum(f[r] * M[r, i] for r in 1:5), 5)
# certified bounds on the game value v = max_μ min_r (Pμ)_r = min_y max_j (yᵀP)_j by multiplicative weights:
# returns :feasible (a μ with min_r (Pμ)_r ≥ 0), :infeasible (a y with max_j (yᵀP)_j < -tol), or :unknown
function mw_decide(P::Matrix{Float64}, tol; iters=300)
    m, n = size(P); sc = maximum(abs, P); sc == 0 && return :feasible
    η = sqrt(8 * log(max(m, 2)) / iters) / sc
    w = ones(m); μsum = zeros(n); ysum = zeros(m); y = zeros(m); Pμ = zeros(m); yP = zeros(n)
    for it in 1:iters
        y .= w ./ sum(w)
        @inbounds for jj in 1:n; acc = 0.0; for r in 1:m; acc += P[r, jj] * y[r]; end; yP[jj] = acc; end   # best response to y
        j = argmax(yP); yP[j] < -tol && return :infeasible     # y certifies: every column < -tol
        μsum[j] += 1; ysum .+= y
        @views w .*= exp.(-η .* P[:, j]); w ./= maximum(w)
        if it % 20 == 0
            @inbounds for r in 1:m; acc = 0.0; for jj in 1:n; acc += P[r, jj] * μsum[jj]; end; Pμ[r] = acc; end
            minimum(Pμ) >= 0 && return :feasible
            @inbounds for jj in 1:n; acc = 0.0; for r in 1:m; acc += P[r, jj] * ysum[r]; end; yP[jj] = acc / it; end
            maximum(yP) < -tol && return :infeasible
        end
    end
    :unknown
end
function lp_feasible(P::Matrix{Float64})        # exists μ ≥ 0, Σμ = 1, P μ ≥ 0 ?  (up to a small margin)
    m, n = size(P)
    for j in 1:n; all(P[r, j] >= 0 for r in 1:m) && return true; end
    tol = 1e-7 * maximum(abs, P)
    d = mw_decide(P, tol)
    d === :feasible && return true
    d === :infeasible && return false
    v, y = game_value(P)
    if !isnan(v)
        v >= -tol && return true
        # claimed infeasible: verify the Farkas certificate ŷ (ŷ ≥ 0, Σŷ = 1, max_j ŷᵀP_j < -tol) directly
        sy = sum(y)
        if sy > 0 && all(>=(0), y)
            ok = true
            @inbounds for jj in 1:n
                acc = 0.0; for r in 1:m; acc += y[r] * P[r, jj]; end
                acc / sy < -tol || (ok = false; break)
            end
            ok && return false
        end
    end
    # simplex inconclusive: exact-enough fallback (serialized HiGHS)
    # max ε  s.t.  Σμ = 1,  P μ - ε ≥ 0,  μ ≥ 0,  ε free   (always feasible; feasible iff ε* ≥ 0)
    nc = n + 1; nrow = m + 1
    a_start = Int32[(j - 1) * nrow for j in 1:nc]
    a_index = Int32[i for j in 1:nc for i in 0:m]
    a_value = Float64[j <= n ? (i == 0 ? 1.0 : P[i, j]) : (i == 0 ? 0.0 : -1.0) for j in 1:nc for i in 0:m]
    cost = zeros(nc); cost[end] = 1.0
    cl = zeros(nc); cl[end] = -Inf; cu = fill(Inf, nc)
    rl = [1.0; zeros(m)]; ru = [1.0; fill(Inf, m)]
    colv = zeros(nc); cold = zeros(nc); rowv = zeros(nrow); rowd = zeros(nrow)
    cb = zeros(Int32, nc); rb = zeros(Int32, nrow); ms = Ref{Int32}(0)
    lock(HIGHS_POOL_LOCK) do      # HiGHS instances are not safe to run concurrently (segfaults)
        h = highs_instance_unlocked()
        HiGHS.Highs_clearModel(h)
        HiGHS.Highs_passLp(h, nc, nrow, nc * nrow, 1, -1, 0.0, cost, cl, cu, rl, ru, a_start, a_index, a_value)
        HiGHS.Highs_run(h)
        ms[] = HiGHS.Highs_getModelStatus(h)
        ms[] == 7 && HiGHS.Highs_getSolution(h, colv, cold, rowv, rowd)
    end
    ms[] == 7 || return true                      # not solved to optimality: be conservative
    colv[end] >= -1e-7 * maximum(abs, P)          # infeasible only with a clear negative margin
end
# target-cell constraints on the successor z' = M z, as functionals of z: the target box plus (strip cells)
# the outer/inner strip cuts of the target polygon (true successors of far states lie on the strip).
# branch conditions as typed rows (c·z ≥ 0), avoiding type-unstable Tuple(::Vector) in hot loops
const BCOND = [NTuple{5,Float64}[need > 0 ? ntuple(i -> Float64(c[i]), 5) : ntuple(i -> -Float64(c[i]), 5) for (c, need) in br[3]] for br in BRANCHES]
const TCUT = Dict{NTuple{8,Float64},Vector{NTuple{3,Float64}}}()
const TCLOCK = ReentrantLock()
const TCUTS_ON = Ref(get(ENV, "TCUTS", "1") == "1")
function tcuts(t::Box)       # rows (n1, n2, h): n1 a + n2 b ≤ h
    key = (t.lo..., t.hi...)
    v = lock(TCLOCK) do; get(TCUT, key, nothing); end
    v === nothing || return v
    alo, ahi, blo, bhi = t.lo[3], t.hi[3], t.lo[4], t.hi[4]
    c1 = (alo + ahi)/2; c2 = (blo + bhi)/2
    g1 = -8c1 - 4c2 + 4; g2 = -4c1 - 8c2 + 4; hc = heronab(c1, c2)
    out = [(-g1, -g2, -(g1*c1 + g2*c2) + hc + 1e-12)]
    if isstrip(t)
        Bq(x, y) = 4*(x-c1)^2 + 4*(x-c1)*(y-c2) + 4*(y-c2)^2
        Bmax = maximum(Bq(p...) for p in ((alo,blo),(ahi,blo),(ahi,bhi),(alo,bhi)))
        push!(out, (g1, g2, g1*c1 + g2*c2 + striptau(t) - hc + Bmax + 1e-12))
    end
    lock(TCLOCK) do; TCUT[key] = out; end
    out
end
function tgtG(T1, L1, V1, D2, A1, B1, t::Box)
    G = NTuple{5,Float64}[L1 .- t.lo[1] .* T1, t.hi[1] .* T1 .- L1, D2 .- t.lo[2] .* V1, t.hi[2] .* V1 .- D2,
         A1 .- t.lo[3] .* L1, t.hi[3] .* L1 .- A1, B1 .- t.lo[4] .* L1, t.hi[4] .* L1 .- B1]
    TCUTS_ON[] && for (n1, n2, h) in tcuts(t); push!(G, h .* L1 .- n1 .* A1 .- n2 .* B1); end
    G
end
function edge_feasible_fast(b::Box, t::Box)
    poly = abpoly(b); isempty(poly) && return false
    C = corners(b, poly)
    for (k, br) in enumerate(BRANCHES)
        ok = true
        for (c, need) in br[3]
            st = sgn(c, C); if st != 0 && st != need; ok = false; break; end
        end
        ok || continue
        br[1] == :Rx && b.hi[1] < 0.2 && continue
        br[1] in (:O, :I) && b.hi[1] <= 0.5 && continue
        M = BMATS[k]
        T1 = rowfun(M, (1,1,1,1,1)); L1 = rowfun(M, (0,0,1,1,1)); V1 = rowfun(M, (1,1,0,0,0))
        D2 = rowfun(M, (1,0,0,0,0)); A1 = rowfun(M, (0,0,1,0,0)); B1 = rowfun(M, (0,0,0,1,0))
        G = NTuple{5,Float64}[]
        append!(G, BCOND[k])
        append!(G, tgtG(T1, L1, V1, D2, A1, B1, t))
        P = [sum(G[r][i] * C[j][i] for i in 1:5) for r in 1:length(G), j in 1:length(C)]
        lp_feasible(P) && return true
    end
    false
end

# per-source-box preparation, reused across many targets
struct EdgePrep
    C::Vector{NTuple{5,Float64}}
    br::Vector{Tuple{Matrix{Float64},NTuple{6,NTuple{5,Float64}}}}   # (condition rows at corners, (T1,L1,V1,D2,A1,B1))
end
function edge_prep(b::Box)
    poly = abpoly(b); isempty(poly) && return EdgePrep(NTuple{5,Float64}[], [])
    C = corners(b, poly); out = Tuple{Matrix{Float64},NTuple{6,NTuple{5,Float64}}}[]
    for (k, br) in enumerate(BRANCHES)
        ok = true
        for (c, need) in br[3]; st = sgn(c, C); if st != 0 && st != need; ok = false; break; end; end
        ok || continue
        br[1] == :Rx && b.hi[1] < 0.2 && continue
        br[1] in (:O, :I) && b.hi[1] <= 0.5 && continue
        M = BMATS[k]
        F = (rowfun(M, (1,1,1,1,1)), rowfun(M, (0,0,1,1,1)), rowfun(M, (1,1,0,0,0)),
             rowfun(M, (1,0,0,0,0)), rowfun(M, (0,0,1,0,0)), rowfun(M, (0,0,0,1,0)))
        Gc = BCOND[k]
        Pc = [sum(Gc[r][i] * C[j][i] for i in 1:5) for r in 1:length(Gc), j in 1:length(C)]
        push!(out, (Pc, F))
    end
    EdgePrep(C, out)
end
function edge_feasible_prep(ep::EdgePrep, t::Box)
    isempty(ep.C) && return false
    C = ep.C; nc = length(C)
    for (Pc, (T1, L1, V1, D2, A1, B1)) in ep.br
        G = tgtG(T1, L1, V1, D2, A1, B1, t)
        Pt = [sum(G[r][i] * C[j][i] for i in 1:5) for r in 1:length(G), j in 1:nc]
        lp_feasible(vcat(Pc, Pt)) && return true
    end
    false
end

# Game value v = max_μ min_r (Pμ)_r by a dense tableau simplex (pure Julia, thread-safe).
# Shift P' = P + c > 0; then max 1ᵀy s.t. P'ᵀ y ≤ 1, y ≥ 0 has optimum 1/(v + c) and slack basis start.
function game_value(P::Matrix{Float64}; maxit=2000)
    m, n = size(P)
    c = 1.0 - minimum(P)                 # all entries of P' ≥ 1
    nv = m + n                           # variables: y (m), slacks (n)
    T = zeros(n + 1, nv + 1)             # rows 1..n constraints, row n+1 objective; last column rhs
    @inbounds for j in 1:n
        for r in 1:m; T[j, r] = P[r, j] + c; end
        T[j, m + j] = 1.0; T[j, end] = 1.0
    end
    @inbounds for r in 1:m; T[n + 1, r] = -1.0; end
    basis = collect(m + 1:m + n)
    tol = 1e-12
    for it in 1:maxit
        # entering: Dantzig, switching to Bland after many iterations
        e = 0; best = -tol
        @inbounds for k in 1:nv
            rc = T[n + 1, k]
            if it < 500 ? rc < best : rc < -tol
                e = k; best = rc; it >= 500 && break
            end
        end
        if e == 0                                         # optimal: value and row weights
            y = zeros(m)
            @inbounds for j in 1:n; basis[j] <= m && (y[basis[j]] = T[j, end]); end
            return 1.0 / T[n + 1, end] - c, y
        end
        # leaving: min ratio (Bland tie-break by basis index)
        l = 0; br = Inf
        @inbounds for j in 1:n
            a = T[j, e]
            if a > tol
                ratio = T[j, end] / a
                if ratio < br - 1e-15 || (abs(ratio - br) <= 1e-15 && l != 0 && basis[j] < basis[l]); br = ratio; l = j; end
            end
        end
        l == 0 && return NaN, Float64[]                     # unbounded (cannot happen: P' > 0)
        pv = T[l, e]
        @inbounds for k in 1:nv + 1; T[l, k] /= pv; end
        @inbounds for j in 1:n + 1
            j == l && continue
            f = T[j, e]; f == 0 && continue
            for k in 1:nv + 1; T[j, k] -= f * T[l, k]; end
        end
        basis[l] = e
    end
    NaN, Float64[]                                          # iteration limit
end
