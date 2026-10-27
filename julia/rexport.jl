# rexport.jl — exact recovery-tree certificates for the Lean checker NMR.chkRT (Scratch/RecCert.lean).
# For a cell (IBox on the grid G = 4096) we rebuild its recovery tree in exact integer arithmetic:
#   W   : five integer functionals of z0 tracking the current state (16^j-scaled), W0 = identity;
#   rows: integer functionals of z0 that are ≥ 0 on the path (branch conjuncts composed through W);
#   inf : branch k impossible — sparse y ≥ 0 with  −Σ y_i rows_i > 0  on the cell (chk strict);
#   leaf: (den, rn, rd, y1, p1, y2, p2) with  rn·den − rd·T_k − Σ y1·rows ≥ 0  and  rn·den − rd·5λ_k − Σ y2·rows ≥ 0
#         on the cell (chk), and 2^(8 nC) rn^7 ≤ 2^(8 nE) (rd 16^j)^7.
# Multipliers come from float LPs over the cell's corners and are verified exactly (BigInt mirror of fcheck).
ENV["TAU"] = get(ENV, "TAU", "9.5367431640625e-7")
include("cells.jl")
include("grid13.jl")      # Box, abpoly, corners (float), BRANCHES
include("fastlp.jl")      # lp_feasible, game_value
using Printf
const BI = BigInt
const G = 4096

# ---- exact cell constraints (mirror of Lean `con`, τ = 2^-20) and fcheck ----
struct IBox; s0::Int; s1::Int; p0::Int; p1::Int; a0::Int; a1::Int; b0::Int; b1::Int; end
isstripI(b::IBox) = b.s0 >= 8
tierDenI(b::IBox) = b.s0 >= 512 ? 1048576 : b.s0 >= 64 ? 8192 : 128
function conI(b::IBox, k::Int)
    X = BI(b.a0 + b.a1); Y = BI(b.b0 + b.b1)
    g1 = 8G - 8X - 4Y; g2 = 8G - 4X - 8Y
    H = 8G*X + 8G*Y - (4X*X + 4X*Y + 4Y*Y + 4BI(G)*G)
    gc = g1*X + g2*Y
    WA = BI(b.a1 - b.a0); WB = BI(b.b1 - b.b0)
    k == 0 && return (BI(-G), BI(0), BI(-b.a0))
    k == 1 && return (BI(G), BI(0), BI(b.a1))
    k == 2 && return (BI(0), BI(-G), BI(-b.b0))
    k == 3 && return (BI(0), BI(G), BI(b.b1))
    k == 4 && return (BI(1), BI(1), BI(1))
    k == 5 && return (-2G*g1, -2G*g2, -gc + H)
    k == 6 && return isstripI(b) ? (2G*g1, 2G*g2, gc - H + (BI(G)*G ÷ tierDenI(b) * 4 + 4*(WA*WA + WA*WB + WB*WB))) : (BI(0), BI(0), BI(0))
    (BI(0), BI(0), BI(0))
end
const NCON = 7
function fcheckI(S0, S1, P0, P1, ci, cj, c, strict)
    L0 = c[1]*P0 + c[2]*(G - P0); L1 = c[1]*P1 + c[2]*(G - P1); Lm = min(L0, L1)
    d1 = c[3] - c[5]; d2 = c[4] - c[5]
    det = ci[1]*cj[2] - ci[2]*cj[1]
    Yi = -(d1*cj[2]) + d2*cj[1]; Yj = -(d2*ci[1]) + d1*ci[2]
    if !(det > 0); det = -det; Yi = -Yi; Yj = -Yj; end
    mD = det*c[5] - (Yi*ci[3] + Yj*cj[3])
    E0 = (G - S0)*Lm*det + (S0*G)*mD
    E1 = (G - S1)*Lm*det + (S1*G)*mD
    det > 0 && Yi >= 0 && Yj >= 0 && (strict ? (E0 > 0 && E1 > 0) : (E0 >= 0 && E1 >= 0))
end
chkI(b::IBox, cons, pr, c, strict) = fcheckI(b.s0, b.s1, b.p0, b.p1, cons[pr ÷ 8 + 1], cons[pr % 8 + 1], c, strict)
function cellpolyI(b::IBox, cons)
    R = Rational{BI}
    P = [(R(b.a0, G), R(b.b0, G)), (R(b.a1, G), R(b.b0, G)), (R(b.a1, G), R(b.b1, G)), (R(b.a0, G), R(b.b1, G))]
    lab = [2, 1, 3, 0]
    for k in 4:6
        n1, n2, h = cons[k+1]
        (n1 == 0 && n2 == 0) && continue
        m = length(P); m == 0 && break
        NP = eltype(P)[]; NL = Int[]
        for i in 1:m
            p = P[i]; q = P[mod1(i+1, m)]
            fp = n1*p[1] + n2*p[2] - h; fq = n1*q[1] + n2*q[2] - h
            fp <= 0 && (push!(NP, p); push!(NL, lab[i]))
            if (fp < 0 && fq > 0) || (fp > 0 && fq < 0)
                t = fp / (fp - fq); push!(NP, (p[1] + t*(q[1]-p[1]), p[2] + t*(q[2]-p[2]))); push!(NL, fp < 0 ? k : lab[i])
            end
        end
        P = NP; lab = NL
    end
    P, lab
end
function find_pairI(b, cons, P, lab, c, strict)
    m = length(P)
    if m > 0
        vals = [(c[3] - c[5])*p[1] + (c[4] - c[5])*p[2] for p in P]
        i = argmin(vals); pr = 8lab[mod1(i-1, m)] + lab[i]
        chkI(b, cons, pr, c, strict) && return pr
    end
    for i in 0:NCON-1, j in 0:NCON-1
        i == j && continue
        chkI(b, cons, 8i + j, c, strict) && return 8i + j
    end
    nothing
end

# ---- exact branch data ----
const MI = [BI.(round.(Int, 16 .* M)) for M in BMATS]                 # 16·brM_k (integer)
const CONDS = [[(BI.(round.(Int, 16 .* c)), need > 0) for (c, need) in br[3]] for br in BRANCHES]   # = Lean brConds
comb5(c, W) = sum(c[r] .* W[r] for r in 1:5)                            # functional c of the tracked state
stepW(k, W) = [comb5(MI[k][r, :], W) for r in 1:5]
const W0 = [BI.([i == j ? 1 : 0 for j in 1:5]) for i in 1:5]
brRows(k, W) = [need ? comb5(c, W) : -comb5(c, W) for (c, need) in CONDS[k]]
const TTv = BI[1, 1, 1, 1, 1]; const L5v = BI[0, 0, 5, 5, 5]
eUp(k) = k == 1 ? 1 : 0; eDn(k) = k >= 4 ? 1 : 0

# ---- float LPs over the cell corners ----
# corners of the cell in z-space (projective): s ∈ {s0,s1}, ψ ∈ {p0,p1}, (a,b) polygon vertices
function cornersI(P, b::IBox)
    C = Vector{Float64}[]
    for (a, bb) in P, (s, ψ) in ((b.s0, b.p0), (b.s1, b.p0), (b.s0, b.p1), (b.s1, b.p1))
        sf = s / G; ψf = ψ / G; af = Float64(a); bf = Float64(bb)
        push!(C, [(1-sf)*ψf, (1-sf)*(1-ψf), sf*af, sf*bf, sf*(1-af-bf)])
    end
    C
end
fvals(row, C) = [Float64(sum(Float64(row[i]) * c[i] for i in 1:5)) for c in C]
# overflow-safe values: the row scaled by 2^-E (E chosen so that the integer entries fit a Float64 comfortably)
bexp(x) = x == 0 ? 0 : ndigits(abs(BigInt(x)), base = 2)
rowexp(rows...) = max(0, maximum(r -> maximum(bexp, r), rows) - 900)
fvalsS(row, C, E) = E == 0 ? fvals(row, C) : [Float64(sum(BigFloat(row[i]) * c[i] for i in 1:5) / BigFloat(2)^E) for c in C]
normrow(v) = (m = maximum(abs, v); m > 0 ? v ./ m : v)

# sparse integer Farkas multipliers: rationalize y_i/scale_i, common denominator
function intmults(y, scales; tol = 1e-9)
    idx = [i for i in eachindex(y) if y[i] > tol * maximum(y)]
    isempty(idx) && return Tuple{Int,BI}[]
    rs = [rationalize(BI, y[i] / scales[i]; tol = 1e-12 * y[i] / scales[i]) for i in idx]
    D = lcm([denominator(r) for r in rs])
    [(i - 1, numerator(r) * (D ÷ denominator(r))) for (i, r) in zip(idx, rs)]       # 0-based row indices
end
farkasI(rows, ys) = isempty(ys) ? zeros(BI, 5) : sum(BI(y) .* rows[i+1] for (i, y) in ys)

using JuMP, HiGHS
function lpmodel()
    m = Model(HiGHS.Optimizer); set_silent(m); m
end
# infeasibility: y ≥ 0, Σ y = 1, minimize t with Σ y_i row_i(c_j) ≤ t at all corners; certificate if t < 0
function inf_cert(b, cons, P, lab, C, rows)
    isempty(rows) && return nothing
    V = [fvals(r, C) for r in rows]; sc = [max(maximum(abs, v), 1e-300) for v in V]
    m = lpmodel(); n = length(rows)
    @variable(m, y[1:n] >= 0); @variable(m, t)
    @constraint(m, sum(y) == 1)
    for j in eachindex(C); @constraint(m, sum(y[i] * V[i][j] / sc[i] for i in 1:n) <= t); end
    @objective(m, Min, t); optimize!(m)
    termination_status(m) == MOI.OPTIMAL || return nothing
    objective_value(m) < -1e-10 || return nothing
    yv = value.(y)
    for tol in (1e-9, 1e-7, 1e-5, 1e-3)
        ys = intmults(yv, sc; tol = tol)
        isempty(ys) && continue
        F = -farkasI(rows, ys)
        pr = find_pairI(b, cons, P, lab, F, true)
        pr !== nothing && return (ys, pr)
    end
    nothing
end
# leaf part: minimize r with r·den − num − Σ y_i row_i ≥ 0 at all corners; exact (rn, rd, ys, pr) with
# rn·den − rd·num − Σ ys·rows ≥ 0 on the cell (chk non-strict)
function leaf_part(b, cons, P, lab, C, rows, num, den)
    dv = fvals(den, C); nv = fvals(num, C)
    minimum(dv) > 0 || return nothing
    V = [fvals(r, C) for r in rows]; sc = [max(maximum(abs, v), 1e-300) for v in V]
    nsc = max(maximum(abs, nv), 1e-300); dsc = max(maximum(abs, dv), 1e-300)
    m = lpmodel(); n = length(rows)
    @variable(m, r >= 0); @variable(m, y[1:n] >= 0)
    for j in eachindex(C)
        @constraint(m, r * dv[j] / dsc - nv[j] / nsc - (n == 0 ? 0.0 : sum(y[i] * V[i][j] / sc[i] for i in 1:n)) >= 0)
    end
    @objective(m, Min, r); optimize!(m)
    termination_status(m) == MOI.OPTIMAL || return nothing
    rv = value(r) * nsc / dsc                   # in true units: num ≤ rv·den on the polytope
    yv = n == 0 ? Float64[] : value.(y)          # in units of num: Σ y_i row_i/sc_i scaled by nsc
    for marg in (1e-9, 1e-7, 1e-5, 1e-3)
        rq = rationalize(BI, rv * (1 + marg); tol = rv * marg / 10)
        rn = numerator(rq); rd = denominator(rq)
        # ys: rd · (nsc · y_i / sc_i), rounded down (multipliers may be decreased: only weakens the bound side)
        ys = Tuple{Int,Rational{BI}}[]
        for i in 1:n
            yv[i] > 1e-12 || continue
            q = rationalize(BI, rd * nsc * yv[i] / sc[i] * (1 - marg); tol = max(1e-30, rd * nsc * yv[i] / sc[i] * marg / 10))
            q > 0 || continue
            push!(ys, (i - 1, q))
        end
        # common denominator for ys and the (rn, rd) part
        D = isempty(ys) ? BI(1) : lcm([denominator(q) for (_, q) in ys])
        ysI = [(i, numerator(q) * (D ÷ denominator(q))) for (i, q) in ys]
        F = BI(rn) * D .* den .- BI(rd) * D .* num .- farkasI(rows, ysI)
        pr = find_pairI(b, cons, P, lab, F, false)
        pr !== nothing && return (rn * D, rd * D, ysI, pr)
    end
    nothing
end

# ---- exact recovery tree of one cell ----
# node tree as nested tuples: (:leaf, den::Bool, rn, rd, y1, p1, y2, p2) | (:node, [child for k=1..9]),
# child = (:inf, ys, pr) | (:sub, subtree)
function rtree_exact(b::IBox; KMAX = 40, RAWMAX = 150)
    cons = [conI(b, k) for k in 0:NCON-1]
    P, lab = cellpolyI(b, cons); isempty(P) && return :empty
    C = cornersI(P, b)
    function leafcert(W, rows, j, nE, nC)
        j >= 1 || return nothing
        Tk = comb5(TTv, W); Lk = comb5(L5v, W)
        best = nothing
        for den in (true, false)
            dvec = den ? TTv : L5v
            a = leaf_part(b, cons, P, lab, C, rows, Tk, dvec); a === nothing && continue
            c = leaf_part(b, cons, P, lab, C, rows, Lk, dvec); c === nothing && continue
            # common r: use the larger rn/rd, rescale the other certificate
            (rn1, rd1, y1, p1) = a; (rn2, rd2, y2, p2) = c
            if rn1 * rd2 >= rn2 * rd1
                rn, rd = rn1, rd1
                # second inequality with r = rn/rd ≥ rn2/rd2 still holds after scaling by rd/rd2·(rn/rd vs rn2/rd2)
                y2s = [(i, y * rd1) for (i, y) in y2]; mult = rd2
                F2 = BI(rn1) * rd2 .* dvec .- BI(rd1) * rd2 .* Lk .- farkasI(rows, y2s)
                pr2 = find_pairI(b, cons, P, lab, F2, false); pr2 === nothing && continue
                rnF, rdF = rn1 * rd2, rd1 * rd2
                y1F = [(i, y * rd2) for (i, y) in y1]
                F1 = BI(rnF) .* dvec .- BI(rdF) .* Tk .- farkasI(rows, y1F)
                pr1 = find_pairI(b, cons, P, lab, F1, false); pr1 === nothing && continue
                cand = (den, rnF, rdF, y1F, pr1, y2s, pr2)
            else
                y1s = [(i, y * rd2) for (i, y) in y1]
                F1 = BI(rn2) * rd1 .* dvec .- BI(rd2) * rd1 .* Tk .- farkasI(rows, y1s)
                pr1 = find_pairI(b, cons, P, lab, F1, false); pr1 === nothing && continue
                rnF, rdF = rn2 * rd1, rd2 * rd1
                y2F = [(i, y * rd1) for (i, y) in y2]
                F2 = BI(rnF) .* dvec .- BI(rdF) .* Lk .- farkasI(rows, y2F)
                pr2 = find_pairI(b, cons, P, lab, F2, false); pr2 === nothing && continue
                cand = (den, rnF, rdF, y1s, pr1, y2F, pr2)
            end
            (_, rnF, rdF) = cand
            # exponent check 2^(8 nC) rn^7 ≤ 2^(8 nE) (rd 16^j)^7
            BI(2)^(8nC) * BI(rnF)^7 <= BI(2)^(8nE) * (BI(rdF) * BI(16)^j)^7 || continue
            best = cand; break
        end
        best === nothing ? nothing : (:leaf, best...)
    end
    fail = Ref{Symbol}(:ok)
    function rec(W, rows, j, nE, nC, k_nonrx, raw)
        lc = leafcert(W, rows, j, nE, nC)
        lc !== nothing && return lc
        (k_nonrx >= KMAX || raw >= RAWMAX) && (fail[] = :depth; return nothing)
        ch = Any[]
        for k in 1:9
            rows2 = vcat(rows, brRows(k, W))
            ic = inf_cert(b, cons, P, lab, C, rows2)
            if ic !== nothing
                push!(ch, (:inf, ic...))
            else
                sub = rec(stepW(k, W), rows2, j + 1, nE + eUp(k), nC + eDn(k), k_nonrx + (k == 2 ? 0 : 1), raw + 1)
                sub === nothing && return nothing
                push!(ch, (:sub, sub))
            end
        end
        (:node, ch)
    end
    t = rec(W0, Vector{BI}[], 0, 0, 0, 0, 0)
    t === nothing ? fail[] : t
end

# ---- BigInt mirror of the Lean checker (chkRT) ----
function chkRT_mirror(b::IBox, t, W, rows, j, nE, nC)
    cons = [conI(b, k) for k in 0:NCON-1]
    if t[1] == :leaf
        (_, den, rn, rd, y1, p1, y2, p2) = t
        dvec = den ? TTv : L5v
        j >= 1 && rd >= 1 || return false
        F1 = BI(rn) .* dvec .- BI(rd) .* comb5(TTv, W) .- farkasI(rows, y1)
        F2 = BI(rn) .* dvec .- BI(rd) .* comb5(L5v, W) .- farkasI(rows, y2)
        chkI(b, cons, p1, F1, false) && chkI(b, cons, p2, F2, false) &&
            BI(2)^(8nC) * BI(rn)^7 <= BI(2)^(8nE) * (BI(rd) * BI(16)^j)^7
    else
        for k in 1:9
            c = t[2][k]; rows2 = vcat(rows, brRows(k, W))
            if c[1] == :inf
                chkI(b, cons, c[3], -farkasI(rows2, c[2]), true) || return false
            else
                chkRT_mirror(b, c[2], stepW(k, W), rows2, j + 1, nE + eUp(k), nC + eDn(k)) || return false
            end
        end
        true
    end
end
treesize(t) = t[1] == :leaf ? (1, 0) : (s = (0, 1); for c in t[2]; c[1] == :sub && (s = s .+ treesize(c[2])); end; s)

# ---- Lean emission ----
leanZ(x) = x >= 0 ? string(x) : error("negative")
leanys(ys) = "[" * join(["(" * string(i) * ", " * string(y) * ")" for (i, y) in ys], ", ") * "]"
function leanRT(io, t)
    if t[1] == :leaf
        (_, den, rn, rd, y1, p1, y2, p2) = t
        print(io, "(RT.leaf ", den ? "true" : "false", " ", rn, " ", rd, " ", leanys(y1), " ", p1, " ", leanys(y2), " ", p2, ")")
    else
        print(io, "(RT.node")
        for c in t[2]
            if c[1] == :inf; print(io, " (RC.inf ", leanys(c[2]), " ", c[3], ")")
            else; print(io, " (RC.sub "); leanRT(io, c[2]); print(io, ")"); end
        end
        print(io, ")")
    end
end
leanBox(b::IBox) = "(⟨$(b.s0), $(b.s1), $(b.p0), $(b.p1), $(b.a0), $(b.a1), $(b.b0), $(b.b1)⟩ : Box)"
