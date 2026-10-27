# Recovery trees with GENERIC neutral-word runs in the exact form checked by Lean (RecCert3).
# Pattern P (length PL) with α_P = 1 and M_P = I + N, N acting on Δ only and depending on D only (N² = 0).
# A run node is the child of branch P[1] at a node with state z.  The maximal run follows P for q ≥ 0 full periods
# and then deviates at phase r: with u = z + q N z, the exit state is Pre_r(u), r ∈ 1..PL (r = PL: deviation at phase 0
# of the next period, then u is the state before the last full period).  Bound: F(u) ≥ 0 for a functional F that is
# a Δ coordinate or a condition row of branch P[1] (it holds at u since phase 0 was followed there); ℓ = −F∘N > 0.
# With (a, b) = Δ-part of F, hN = −b N₂ + a N₃ and κ = hN/ℓ: u = z + (−ρ(a,b) + τ(−b,a))/W, W = a² + b², ρ = qℓ ∈ [0, F(z)],
# τ = κρ.  Per κ-piece u ∈ conv of three linear images E_e z / S (finite pieces: via F; lower: via Δ₃(u) ≥ 0, needs
# a > 0; upper: via Δ₂(u) ≥ 0, needs b > 0).  Parts are tripled: columns hcat(E₀Z, E₁Z, E₂Z), old rows summed.
include("rtree2_core.jl")
using LinearAlgebra
const ID5F = Matrix{Float64}(I, 5, 5)
const KQ5 = [(-1000, 1), (-30, 1), (-10, 1), (-5, 1), (-3, 1), (-2, 1), (-3, 2), (-6, 5), (-1, 1), (-4, 5), (-1, 2), (-1, 4),
            (0, 1), (1, 4), (1, 2), (4, 5), (1, 1), (6, 5), (3, 2), (2, 1), (3, 1), (5, 1), (10, 1), (30, 1), (1000, 1)]
struct GWord; P::Vector{Int}; N::Matrix{Float64}; end
wmat(P) = foldl((A, k) -> BMATS[k] * A, P; init = ID5F)
function gword_table(maxL = 6)
    T = Dict{Vector{Int},GWord}()
    for L in 1:maxL, wt in Iterators.product(fill(1:9, L)...)
        w = collect(wt)
        prod(BALPHA[k] for k in w) == 1 || continue
        M = wmat(w)
        for p in (1, 2, 3, 6)
            N = M^p - ID5F
            iszero(N) && break
            if iszero(N^2) && iszero(N[3:5, :]) && iszero(N[:, 1:2])
                T[w] = GWord(repeat(w, p), N); break
            end
        end
    end
    T
end
const GTAB = gword_table()
const NPER = Ref(2)
# exact cycle words: α = 1 and M_P = I (followed forever ⇒ periodic orbit, impossible since λ → 0)
function cword_table(maxL = 6)
    T = Dict{Vector{Int},Vector{Int}}()
    for L in 1:maxL, wt in Iterators.product(fill(1:9, L)...)
        w = collect(wt)
        prod(BALPHA[k] for k in w) == 1 || continue
        M = wmat(w)
        for p in (1, 2, 3, 4, 6)
            if iszero(round.(M^p - ID5F, digits = 12)); T[w] = repeat(w, p); break; end
        end
    end
    T
end
const CTAB = cword_table()
# dynamic patterns: tails of the path repeating with a period 7 ≤ L ≤ DYNL (classified once, cached)
const DYNL = Ref(40); const DYNC = Dict{Vector{Int},Any}(); const DYNLK = ReentrantLock()
function classify_word(w::Vector{Int})
    v = lock(DYNLK) do; get(DYNC, w, missing); end
    v === missing || return v
    res = nothing
    if prod(BALPHA[k] for k in w) == 1
        M = wmat(w)
        for p in (1, 2, 3, 4, 6)
            N = M^p - ID5F
            if maximum(abs, N) < 1e-9; res = (:cyc, repeat(w, p)); break; end
            if maximum(abs, N^2) < 1e-9 * max(1.0, maximum(abs, N)^2) && maximum(abs, N[3:5, :]) < 1e-9 && maximum(abs, N[:, 1:2]) < 1e-9
                res = (:gen, GWord(repeat(w, p), round.(N; digits = 12))); break
            end
        end
    end
    lock(DYNLK) do; DYNC[w] = res; end
    res
end
function detect_dyn(path::Vector{Int}, kind::Symbol)
    for L in 7:DYNL[]
        length(path) >= 2L || break
        all(j -> path[end-2L+j] == path[end-L+j], 1:L) || continue
        w = path[end-L+1:end]
        any(d -> L % d == 0 && all(j -> w[j] == w[(j - 1) % d + 1], 1:L), 1:L-1) && continue   # power of a shorter word
        c = classify_word(w)
        c !== nothing && c[1] == kind && return c[2]
    end
    nothing
end
function detect_cword(path::Vector{Int})
    for L in 1:6
        length(path) >= L || continue
        w = path[end-L+1:end]
        haskey(CTAB, w) || continue
        P = CTAB[w]; PL = length(P)
        length(path) >= PL || continue
        all(j -> path[end-PL+j] == w[(j - 1) % L + 1], 1:PL) && return P
    end
    detect_dyn(path, :cyc)
end
# exits of a cycle run (child of branch P[1] at nd): Pre_r(z), r = 1..PL, excluded branch P[r % PL + 1]
function cyc_run(nd::Node, P::Vector{Int})
    PL = length(P); out = Tuple{Node,Int}[]
    R1 = vcat(nd.R, permutedims(reduce(hcat, condrows(P[1], nd.Z))))
    Zt = nd.Z; prow = Vector{Float64}[]
    for r in 1:PL
        append!(prow, condrows(P[r], Zt)); Zt = BMATS[P[r]] * Zt
        rows = vcat(prow, [rowof(unitrow(q), Zt) for q in 1:5])
        Rn = vcat(R1, permutedims(reduce(hcat, rows)))
        lp_feasible(Rn) || continue
        αr = prod(BALPHA[P[t]] for t in 1:r)
        push!(out, (Node(Zt, Rn, nd.l0, nd.t0, nd.α * αr), P[r % PL + 1]))
    end
    out
end
# the pattern whose last two periods end the path (next letter = P[1])
function detect_gword(path::Vector{Int})
    for L in 1:6
        length(path) >= L || continue
        w = path[end-L+1:end]
        haskey(GTAB, w) || continue
        gw = GTAB[w]; PL = length(gw.P)
        np = get(task_local_storage(), :nper, NPER[]) * PL
        length(path) >= np || continue
        all(j -> path[end-np+j] == w[(j - 1) % L + 1], 1:np) && return gw
    end
    detect_dyn(path, :gen)
end
condrows(k, Z) = [rowof(g, Z) for g in BCOND[k]]
unitrow(q) = ntuple(k -> k == q ? 1.0 : 0.0, 5)
# vertex maps (float, already divided by the scale) of piece i ∈ 0..25 for bound F with Δ-part (a, b)
function piecemaps5(i, F, a, b)
    W = a^2 + b^2
    rank1(S, v, G) = (E = S .* ID5F; E[1, :] .+= v[1] .* collect(G); E[2, :] .+= v[2] .* collect(G); E ./ S)
    if 1 <= i <= 24
        p1, q1 = KQ5[i]; p2, q2 = KQ5[i+1]; S = q1 * q2 * W
        return [ID5F, rank1(S, (q2 * (-q1 * a - p1 * b), q2 * (-q1 * b + p1 * a)), F),
                rank1(S, (q1 * (-q2 * a - p2 * b), q1 * (-q2 * b + p2 * a)), F)]
    elseif i == 0
        p, q = KQ5[1]; D = q * b - a * p; S = a * D
        return [ID5F, rank1(S, (D * b, -D * a), unitrow(2)), rank1(S, (a * (-q * a - p * b), a * (-q * b + p * a)), unitrow(2))]
    else
        p, q = KQ5[25]; D = a * q + b * p; S = b * D
        return [ID5F, rank1(S, (-D * b, D * a), unitrow(1)), rank1(S, (b * (-q * a - p * b), b * (-q * b + p * a)), unitrow(1))]
    end
end
function piecerows5(i, ellc, hNc)
    rows = Vector{Float64}[]
    i >= 1 && (push!(rows, KQ5[i][2] .* hNc .- KQ5[i][1] .* ellc))          # κ ≥ κ_{i-1} (1-based KQ5[i])
    i <= 24 && (push!(rows, KQ5[i+1][1] .* ellc .- KQ5[i+1][2] .* hNc))     # κ ≤ κ_i
    rows
end
# Candidate bounds at node nd (rows already include the conditions of branch P[1] at z).  Returns the exits
# [(node, excluded branch)] or nothing if no candidate works.
function gen_run(nd::Node, gw::GWord)
    P = gw.P; PL = length(P); N = gw.N
    R1 = vcat(nd.R, permutedims(reduce(hcat, condrows(P[1], nd.Z))))
    cands = vcat([unitrow(1), unitrow(2), (1.0, 1.0, 0.0, 0.0, 0.0)], BCOND[P[1]])
    for F in cands
        Fv = collect(F); a, b = Fv[1], Fv[2]
        (a == 0 && b == 0) && continue
        ell = -(N' * Fv)                                  # ℓ(z) = −F(Nz)
        hN = -b .* N[1, :] .+ a .* N[2, :]
        ellc = rowof(Tuple(ell), nd.Z); hNc = rowof(Tuple(hN), nd.Z)
        auto = all(ell[3:5] .>= 0) && sum(ell[3:5]) > 0
        auto || !lp_feasible(vcat(R1, -ellc')) || continue  # ℓ > 0 on the node
        out = Tuple{Node,Int}[]; ok = true
        for i in 0:25
            Rp = vcat(R1, permutedims(reduce(hcat, piecerows5(i, ellc, hNc))))
            lp_feasible(Rp) || continue
            if (i == 0 && !(a > 0 && KQ5[1][2] * b - a * KQ5[1][1] > 0)) || (i == 25 && !(b > 0 && a * KQ5[25][2] + b * KQ5[25][1] > 0))
                ok = false; break                          # unbounded piece that is not refuted
            end
            Es = piecemaps5(i, Fv, a, b)
            Zu = hcat((E * nd.Z for E in Es)...)
            Rb = hcat(Rp, Rp, Rp)
            urows = [rowof(unitrow(q), Zu) for q in 1:5]
            Zt = Zu; prow = Vector{Float64}[]
            for r in 1:PL
                append!(prow, condrows(P[r], Zt)); Zt = BMATS[P[r]] * Zt
                rows = vcat(urows, prow, [rowof(unitrow(q), Zt) for q in 1:5])
                Rn = vcat(Rb, permutedims(reduce(hcat, rows)))
                lp_feasible(Rn) || continue
                αr = prod(BALPHA[P[t]] for t in 1:r)
                push!(out, (Node(Zt, Rn, vcat(nd.l0, nd.l0, nd.l0), vcat(nd.t0, nd.t0, nd.t0), nd.α * αr), P[r % PL + 1]))
            end
        end
        ok && return out
    end
    nothing
end
# leaf test S ≥ 0 as a decision: no point of the node polytope has num ≥ thr·den, thr = α^(GAM/0.7)
function Sok(nd::Node)
    T = rowof((1,1,1,1,1), nd.Z); L = rowof((0,0,1,1,1), nd.Z)
    thr = nd.α^(GAM / 0.7)
    side = nd.t0 .- 5 .* nd.l0
    parts = Tuple{Matrix{Float64},Vector{Float64}}[]
    if minimum(side) >= 0; push!(parts, (nd.R, nd.t0))
    elseif maximum(side) <= 0; push!(parts, (nd.R, 5 .* nd.l0))
    else
        Pa = vcat(nd.R, side'); lp_feasible(Pa) && push!(parts, (Pa, nd.t0))
        Pb = vcat(nd.R, (-side)'); lp_feasible(Pb) && push!(parts, (Pb, 5 .* nd.l0))
    end
    ok = true
    for (Pp, den) in parts, num in (T, 5 .* L)
        lp_feasible(vcat(Pp, (num .- thr .* den)')) && (ok = false; break)
    end
    ok && return true
    # exactly neutral leaves (S = 0 on part of the polytope): one denominator for the whole node, tolerance ε
    for den in (5 .* nd.l0, nd.t0)
        good = true
        for num in (T, 5 .* L)
            row = num .- thr .* den
            maximum(row .- 1e-12 .* (abs.(num) .+ abs.(den))) <= 0 && continue     # every generator satisfies it
            lp_feasible(vcat(nd.R, (row .- 1e-6 .* (abs.(num) .+ abs.(den)))')) && (good = false; break)
        end
        good && return true
    end
    false
end
# a step that also records the nonnegativity of the new state (Lean: RC3.subu)
stepU(nd::Node, kb) = (ch = step(nd, kb); Node(ch.Z, vcat(ch.R, permutedims(reduce(hcat, [rowof(unitrow(q), ch.Z) for q in 1:5]))), ch.l0, ch.t0, ch.α))
const USEU = Ref(true)
# supporting cut of the physical cone {Q(D) ≥ 0}: p on its boundary near the node's shape, row pᵀJ·D ≥ 0
const USECUT = Ref(false)
function conecut(Z)
    m = vec(sum(Z, dims = 2)) ./ size(Z, 2)
    d = max.(m[3:5], 0.0); sum(d) > 0 || return nothing
    r = sqrt.(d ./ sum(d)); i = argmax(r); r[i] = sum(r) - r[i]          # largest root = sum of the others
    p = r .^ 2
    row = (0.0, 0.0, -p[1] + p[2] + p[3], p[1] - p[2] + p[3], p[1] + p[2] - p[3])
    rowof(row, Z)
end
function stepX(nd::Node, kb)
    ch = USEU[] ? stepU(nd, kb) : step(nd, kb)
    USECUT[] || return ch
    c = conecut(ch.Z); c === nothing && return ch
    Node(ch.Z, vcat(ch.R, c'), ch.l0, ch.t0, ch.α)
end
const RUNMAX5 = Ref(3); const TRACE = Ref(false); const FAILPATH = Ref(String[]); const FAILNODE = Ref{Any}(nothing); const TLIM5 = Ref(120.0)
function tree5(b::Box)
    t0 = time()
    C = corners(b, abpoly(b)); isempty(C) && return (:empty, 0, 0)
    Z0 = reduce(hcat, [collect(c) for c in C])
    root = Node(Z0, zeros(0, size(Z0, 2)), rowof((0,0,1,1,1), Z0), rowof((1,1,1,1,1), Z0), 1.0)
    nleaf = 0; maxk = 0; fail = Ref{Symbol}(:ok)
    function rec(nd::Node, k, raw, path, excl, runs, lab = String[])
        fail[] == :ok || return
        if raw > 0 && Sok(nd); nleaf += 1; maxk = max(maxk, k); return; end
        k >= KMAX2[] && (fail[] = :depth; FAILPATH[] = lab; FAILNODE[] = nd; return)
        raw >= get(task_local_storage(), :rawmax, RAWMAX2[]) && (fail[] = :raw; FAILPATH[] = lab; return)
        time() - t0 > TLIM5[] && (fail[] = :time; FAILPATH[] = lab; return)
        gw = runs < get(task_local_storage(), :runmax, RUNMAX5[]) ? detect_gword(path) : nothing
        exits = (gw === nothing || gw.P[1] == excl) ? nothing : gen_run(nd, gw)
        if exits === nothing && runs < get(task_local_storage(), :runmax, RUNMAX5[])
            cp = detect_cword(path)
            if cp !== nothing && cp[1] != excl
                gw = GWord(cp, zeros(5, 5)); exits = cyc_run(nd, cp)
            end
        end
        for kb in 1:9
            kb == excl && continue
            if exits !== nothing && kb == gw.P[1]
                for (ex, exb) in exits, kc in 1:9
                    kc == exb && continue
                    ch = stepX(ex, kc); lp_feasible(ch.R) || continue
                    rec(ch, k + 1, raw + 1, [kc], 0, runs + 1, TRACE[] ? vcat(lab, "[" * join(gw.P) * "]", string(kc)) : lab)
                    nleaf > MAXLEAF2[] && (fail[] = :size; return)
                end
                continue
            end
            ch = stepX(nd, kb); lp_feasible(ch.R) || continue
            rec(ch, k + (kb == 2 ? 0 : 1), raw + 1, vcat(path, kb), 0, runs, TRACE[] ? vcat(lab, string(kb)) : lab)
            nleaf > MAXLEAF2[] && (fail[] = :size; return)
        end
    end
    rec(root, 0, 0, Int[], 0, 0)
    (fail[], nleaf, maxk)
end
