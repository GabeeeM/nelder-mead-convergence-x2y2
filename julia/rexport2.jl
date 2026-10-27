# rexport2.jl — exact recovery-tree certificates with symbolic Rx runs (multi-part tracking), mirroring the
# Lean checker NMR2 (lean/RecCert2.lean).  State after the path = Σ_p c_p · (W_p z0)/σ with c_p ≥ 0, Σ c_p = 1 (parts W_p);
# rows are per-part functionals r_p with Σ_p c_p r_p(z0) ≥ 0; every certificate (shared multipliers y) is checked
# part by part with chk on the cell.  A run node (branch 2) replaces "Rx forever-then-exit" by, for each κ-piece and
# parity, the exit state  w = Σ λ_i E_i(z_j)  (even) or M_Rx(...) (odd), E_0 = id and E_1, E_2 the piece's vertex maps.
include("rexport.jl")

const DIAG = Dict{Symbol,Int}()
diag!(s) = (DIAG[s] = get(DIAG, s, 0) + 1)
const KQ = [(-1000, 1), (-30, 1), (-10, 1), (-5, 1), (-3, 1), (-2, 1), (-3, 2), (-6, 5), (-1, 1), (-4, 5), (-1, 2),
            (-1, 4), (0, 1), (1, 4), (1, 2), (4, 5), (1, 1), (6, 5), (3, 2), (2, 1), (3, 1), (5, 1), (10, 1), (30, 1), (1000, 1)]
const M2I = BI.(round.(Int, BMATS[2]))                 # Rx matrix (integer)
const M2INV = BI.(round.(Int, inv(BMATS[2])))
@assert M2I * M2INV == BI.([i == j ? 1 : 0 for i in 1:5, j in 1:5])

# vertex maps of piece i (0 … length(KQ)): three integer 5×5 matrices with a common positive scale S
function piecemaps(i)
    Id = BI.([r == c ? 1 : 0 for r in 1:5, c in 1:5])
    n = length(KQ)
    if 1 <= i < n                      # finite piece [κ_i, κ_{i+1}] (1-based thresholds KQ[i], KQ[i+1])
        (p1, q1) = KQ[i]; (p2, q2) = KQ[i+1]; L = q1 * q2; S = 2L      # (Lean uses the product, not the lcm)
        E = Matrix{BI}[]
        push!(E, S .* Id)
        for (p, q) in ((p1, q1), (p2, q2))
            # S z + L (Δ2+Δ3) (κ−1, −κ−1, 0,0,0),  L(κ − 1) = (L/q)(p − q)
            M = S .* Id; f = L ÷ q
            M[1, 1] += f * (p - q); M[1, 2] += f * (p - q)
            M[2, 1] += f * (-p - q); M[2, 2] += f * (-p - q)
            push!(E, M)
        end
        return E, BI(S)
    elseif i == n                      # upper infinite piece κ ≥ κ_L = p/q:  z + Δ3/(q+p)(p−q, −p−q),  z + Δ3 (1, −1)
        (p, q) = KQ[n]; S = q + p
        M1 = S .* Id; M1[1, 2] += p - q; M1[2, 2] += -p - q
        M2 = S .* Id; M2[1, 2] += S; M2[2, 2] -= S
        return [S .* Id, M1, M2], BI(S)
    else                               # i == 0: lower infinite piece κ ≤ κ_F = p/q:  z + Δ2/(q−p)(p−q, −p−q),  z + Δ2 (−1, 1)
        (p, q) = KQ[1]; S = q - p
        M1 = S .* Id; M1[1, 1] += p - q; M1[2, 1] += -p - q
        M2 = S .* Id; M2[1, 1] -= S; M2[2, 1] += S
        return [S .* Id, M1, M2], BI(S)
    end
end
# κ-piece rows for the run start (functionals of the state): κ ≥ κ_i  and  κ ≤ κ_{i+1}
function piecerows(i)
    n = length(KQ); out = Vector{BI}[]
    if i >= 1; (p, q) = KQ[i]; push!(out, BI[0, 0, -q, -p, q]); end          # q(D23 − D12) − p D13 ≥ 0
    if i < n; (p, q) = KQ[i+1]; push!(out, BI[0, 0, q, p, -q]); end          # p D13 − q(D23 − D12) ≥ 0
    out
end
applymat(E, W) = [comb5(E[r, :], W) for r in 1:5]

# ---- LPs with parts ----
pvals(rows, p, C) = [fvals(r[p], C) for r in rows]
function inf_cert2(b, cons, P, lab, C, rows, np)
    isempty(rows) && return nothing
    Er = [rowexp(r...) for r in rows]
    V = [[fvalsS(r[p], C, Er[i]) for p in 1:np] for (i, r) in enumerate(rows)]
    sc = [max(maximum(maximum(abs, v) for v in Vr), 1e-300) for Vr in V]
    m = lpmodel(); n = length(rows)
    @variable(m, y[1:n] >= 0); @variable(m, t)
    @constraint(m, sum(y) == 1)
    for p in 1:np, j in eachindex(C); @constraint(m, sum(y[i] * V[i][p][j] / sc[i] for i in 1:n) <= t); end
    @objective(m, Min, t); optimize!(m)
    termination_status(m) == MOI.OPTIMAL || return nothing
    objective_value(m) < -1e-10 || return nothing
    yv = value.(y)
    for tol in (0.0, 1e-9, 1e-6)
        yq = [(i - 1, Rational{BI}(yv[i] / sc[i]) / BI(2)^Er[i]) for i in eachindex(yv) if yv[i] > tol * maximum(yv)]
        isempty(yq) && continue
        D = lcm([denominator(q) for (_, q) in yq])
        ys = [(i, numerator(q) * (D ÷ denominator(q))) for (i, q) in yq]
        prs = Int[]
        for p in 1:np
            F = -farkasI([r[p] for r in rows], ys)
            pr = find_pairI(b, cons, P, lab, F, true); pr === nothing && break
            push!(prs, pr)
        end
        length(prs) == np && return (ys, prs)
    end
    diag!(:inf_exact_fail)
    nothing
end
# smallest r with r·den − num_p − Σ y row_p ≥ 0 at all corners for all parts; exact (rn, rd, ys, prs)
function leaf_part2(b, cons, P, lab, C, rows, nums, den, np)
    Ed = rowexp(den); dv = fvalsS(den, C, Ed); minimum(dv) > 0 || return nothing
    En = rowexp(nums...); NV = [fvalsS(nums[p], C, En) for p in 1:np]
    Er = [rowexp(r...) for r in rows]
    V = [[fvalsS(r[p], C, Er[i]) for p in 1:np] for (i, r) in enumerate(rows)]
    sc = [max(maximum(maximum(abs, v) for v in Vr), 1e-300) for Vr in V]
    nsc = max(maximum(maximum(abs, v) for v in NV), 1e-300); dsc = max(maximum(abs, dv), 1e-300)
    m = lpmodel(); n = length(rows)
    @variable(m, r >= 0); @variable(m, y[1:n] >= 0)
    for p in 1:np, j in eachindex(C)
        @constraint(m, r * dv[j] / dsc - NV[p][j] / nsc - (n == 0 ? 0.0 : sum(y[i] * V[i][p][j] / sc[i] for i in 1:n)) >= 0)
    end
    @objective(m, Min, r); optimize!(m)
    termination_status(m) == MOI.OPTIMAL || return nothing
    rvq = Rational{BI}(value(r) * nsc / dsc) * BI(2)^max(En - Ed, 0) / BI(2)^max(Ed - En, 0); yv = n == 0 ? Float64[] : value.(y)
    # multipliers kept exact (binary rationals of the float LP solution); the whole safety margin goes on r
    yq = [(i - 1, Rational{BI}(nsc * yv[i] / sc[i]) * BI(2)^max(En - Er[i], 0) / BI(2)^max(Er[i] - En, 0)) for i in 1:n if yv[i] > 0]
    for marg in (1e-9, 1e-7, 1e-5, 1e-3, 1e-2)
        rq = rvq * Rational{BI}(1 + marg) + Rational{BI}(1, BI(2)^200)
        D = lcm(vcat([denominator(q) for (_, q) in yq], [denominator(rq)]))
        rn = numerator(rq) * (D ÷ denominator(rq)); rd = D
        ysI = [(i, numerator(q) * (D ÷ denominator(q))) for (i, q) in yq]
        prs = Int[]
        for p in 1:np
            F = BI(rn) .* den .- BI(rd) .* nums[p] .- farkasI([r[p] for r in rows], ysI)
            pr = find_pairI(b, cons, P, lab, F, false); pr === nothing && break
            push!(prs, pr)
        end
        length(prs) == np && return (rn, rd, ysI, prs)
    end
    diag!(:leaf_exact_fail)
    nothing
end


# leaf part with a FIXED exact ratio rn/rd: try y = 0 first, else LP maximizing the slack t of
# rn·den − rd·num_p − Σ y·row_p ≥ t at the corners; y kept exact (binary rationals); verified per part
function leaf_fixed2(b, cons, P, lab, C, rows, nums, den, np, rn, rd)
    function verify(ysI)
        prs = Int[]
        for p in 1:np
            F = BI(rn) .* den .- BI(rd) .* nums[p] .- farkasI([r[p] for r in rows], ysI)
            pr = find_pairI(b, cons, P, lab, F, false); pr === nothing && return nothing
            push!(prs, pr)
        end
        prs
    end
    prs = verify(Tuple{Int,BI}[]); prs !== nothing && return (Tuple{Int,BI}[], prs)
    isempty(rows) && return nothing
    Er = [rowexp(r...) for r in rows]
    V = [[fvalsS(r[p], C, Er[i]) for p in 1:np] for (i, r) in enumerate(rows)]
    sc = [max(maximum(maximum(abs, v) for v in Vr), 1e-300) for Vr in V]
    Gr = [BI(rn) .* den .- BI(rd) .* nums[p] for p in 1:np]; Eg = rowexp(Gr...)
    G0 = [fvalsS(Gr[p], C, Eg) for p in 1:np]
    gs = max(maximum(maximum(abs, g) for g in G0), 1e-300)
    m = lpmodel(); n = length(rows)
    @variable(m, y[1:n] >= 0); @variable(m, t <= 1)
    for p in 1:np, j in eachindex(C)
        @constraint(m, G0[p][j] / gs - sum(y[i] * V[i][p][j] / sc[i] for i in 1:n) >= t)
    end
    @objective(m, Max, t); optimize!(m)
    termination_status(m) == MOI.OPTIMAL || return nothing
    value(t) >= -1e-12 || return nothing
    yq = [(i - 1, Rational{BI}(gs * value(y[i]) / sc[i]) * BI(2)^max(Eg - Er[i], 0) / BI(2)^max(Er[i] - Eg, 0)) for i in 1:n if value(y[i]) > 0]
    D = isempty(yq) ? BI(1) : lcm([denominator(q) for (_, q) in yq])
    ysI = [(i, numerator(q) * (D ÷ denominator(q))) for (i, q) in yq]
    # scale (rn, rd) by D as well: F·D = (rn D) den − (rd D) num − Σ ysI row
    prs = Int[]
    for p in 1:np
        F = BI(rn) * D .* den .- BI(rd) * D .* nums[p] .- farkasI([r[p] for r in rows], ysI)
        pr = find_pairI(b, cons, P, lab, F, false); pr === nothing && return nothing
        push!(prs, pr)
    end
    (ysI, prs, D)
end

# ---- exact recovery tree with runs ----
# tree: (:leaf, den, rn, rd, y1, prs1, y2, prs2) | (:node, children[1..9]);
# child: (:inf, ys, prs) | (:sub, tree) | (:skip) (branch 2 right after a run) |
#        (:run, [(piece, parity) => (:inf, ys, prs) | (:sub, tree)])  (branch 2, symbolic run)
function rtree_exact2(b::IBox; KMAX = 40, RAWMAX = 150, RUNK = 30)
    cons = [conI(b, k) for k in 0:NCON-1]
    P, lab = cellpolyI(b, cons); isempty(P) && return :empty
    C = cornersI(P, b)
    function leafcert(parts, rows, σ, moved, nE, nC)
        moved || return nothing
        np = length(parts)
        Tk = [comb5(TTv, W) for W in parts]; Lk = [comb5(L5v, W) for W in parts]
        # exactly neutral recovery (S = 0): r = σ exactly, possible when nE ≥ nC
        if nE >= nC
            for den in (false, true)
                dvec = den ? TTv : L5v
                a = leaf_fixed2(b, cons, P, lab, C, rows, Tk, dvec, np, σ, BI(1)); a === nothing && continue
                c = leaf_fixed2(b, cons, P, lab, C, rows, Lk, dvec, np, σ, BI(1)); c === nothing && continue
                Da = length(a) == 3 ? a[3] : BI(1); Dc = length(c) == 3 ? c[3] : BI(1)
                D = Da * Dc
                y1F = [(i, y * Dc) for (i, y) in a[1]]; y2F = [(i, y * Da) for (i, y) in c[1]]
                rnF = σ * D; rdF = D
                prs1 = Int[]; prs2 = Int[]
                for p in 1:np
                    F1 = BI(rnF) .* dvec .- BI(rdF) .* Tk[p] .- farkasI([r[p] for r in rows], y1F)
                    F2 = BI(rnF) .* dvec .- BI(rdF) .* Lk[p] .- farkasI([r[p] for r in rows], y2F)
                    q1 = find_pairI(b, cons, P, lab, F1, false); q2 = find_pairI(b, cons, P, lab, F2, false)
                    (q1 === nothing || q2 === nothing) && break
                    push!(prs1, q1); push!(prs2, q2)
                end
                length(prs1) == np || continue
                BI(2)^(8nC) * BI(rnF)^7 <= BI(2)^(8nE) * (BI(rdF) * σ)^7 || continue
                return (:leaf, den, rnF, rdF, y1F, prs1, y2F, prs2)
            end
        end
        for den in (true, false)
            dvec = den ? TTv : L5v
            a = leaf_part2(b, cons, P, lab, C, rows, Tk, dvec, np); a === nothing && continue
            c = leaf_part2(b, cons, P, lab, C, rows, Lk, dvec, np); c === nothing && continue
            (rn1, rd1, y1, _) = a; (rn2, rd2, y2, _) = c
            # common r = max: rescale both to the common denominator rd1·rd2
            rnF = max(rn1 * rd2, rn2 * rd1); rdF = rd1 * rd2
            y1F = [(i, y * rd2) for (i, y) in y1]; y2F = [(i, y * rd1) for (i, y) in y2]
            prs1 = Int[]; prs2 = Int[]
            for p in 1:np
                F1 = BI(rnF) .* dvec .- BI(rdF) .* Tk[p] .- farkasI([r[p] for r in rows], y1F)
                F2 = BI(rnF) .* dvec .- BI(rdF) .* Lk[p] .- farkasI([r[p] for r in rows], y2F)
                q1 = find_pairI(b, cons, P, lab, F1, false); q2 = find_pairI(b, cons, P, lab, F2, false)
                (q1 === nothing || q2 === nothing) && break
                push!(prs1, q1); push!(prs2, q2)
            end
            length(prs1) == np || (diag!(:leaf_common_fail); continue)
            BI(2)^(8nC) * BI(rnF)^7 <= BI(2)^(8nE) * (BI(rdF) * σ)^7 || (diag!(den ? :exp_fail_T : :exp_fail_L); continue)
            return (:leaf, den, rnF, rdF, y1F, prs1, y2F, prs2)
        end
        nothing
    end
    fail = Ref{Symbol}(:ok)
    function rec(parts, rows, σ, moved, nE, nC, knr, raw, consec, post)
        lc = leafcert(parts, rows, σ, moved, nE, nC)
        lc !== nothing && return lc
        (knr >= KMAX || raw >= RAWMAX) && (fail[] = :depth; diag!(raw >= RAWMAX ? :raw_limit : :knr_limit); return nothing)
        np = length(parts); ch = Any[]
        for k in 1:9
            if k == 2 && post; push!(ch, (:skip,)); continue; end
            rows2 = vcat(rows, [[need ? comb5(c, W) : -comb5(c, W) for W in parts] for (c, need) in CONDS[k]])
            ic = inf_cert2(b, cons, P, lab, C, rows2, np)
            if ic !== nothing; push!(ch, (:inf, ic...)); continue; end
            if k == 2 && consec >= RUNK
                pcs = Any[]
                for i in 0:length(KQ), odd in (false, true)
                    E, S = piecemaps(i)
                    np3 = 3np
                    uparts = [applymat(E[e], W) for e in 1:3 for W in parts]          # part index (e, p)
                    wparts = odd ? [stepW(2, U) for U in uparts] : uparts
                    prevparts = odd ? uparts : [applymat(M2INV, U) for U in uparts]
                    rep(r) = [r[(q - 1) % np + 1] for q in 1:np3]                     # replicate an old row
                    rws = [rep(r) for r in rows2]                                     # incl. the Rx conjuncts at z_j
                    for f in piecerows(i); push!(rws, rep([comb5(f, W) for W in parts])); end
                    for (c, need) in CONDS[2]; push!(rws, [need ? comb5(c, U) : -comb5(c, U) for U in prevparts]); end
                    for r in 1:5; e = BI.([q == r ? 1 : 0 for q in 1:5]); push!(rws, [comb5(e, U) for U in wparts]); end
                    σ2 = σ * S * (odd ? 16 : 1)
                    ic2 = inf_cert2(b, cons, P, lab, C, rws, np3)
                    if ic2 !== nothing; push!(pcs, (:inf, ic2...)); continue; end
                    sub = rec(wparts, rws, σ2, true, nE, nC, knr + 1, raw + 1, 0, true)
                    sub === nothing && return nothing
                    push!(pcs, (:sub, sub))
                end
                push!(ch, (:run, pcs))
                continue
            end
            sub = rec([stepW(k, W) for W in parts], rows2, σ * 16, true, nE + eUp(k), nC + eDn(k),
                      knr + (k == 2 ? 0 : 1), raw + 1, k == 2 ? consec + 1 : 0, false)
            sub === nothing && return nothing
            push!(ch, (:sub, sub))
        end
        (:node, ch)
    end
    t = rec([W0], Vector{Vector{BI}}[], BI(1), false, 0, 0, 0, 0, 0, false)
    t === nothing ? fail[] : t
end
treesize2(t) = t[1] == :leaf ? (1, 0, 0) : begin
    s = (0, 1, 0)
    for c in t[2]
        if c[1] == :sub; s = s .+ treesize2(c[2])
        elseif c[1] == :run; s = s .+ (0, 0, 1); for pc in c[2]; pc[1] == :sub && (s = s .+ treesize2(pc[2])); end
        end
    end
    s
end
