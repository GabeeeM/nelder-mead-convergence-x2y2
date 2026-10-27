# rexport3.jl — exact recovery-tree certificates for the Lean checker NMR3.chkRT3 (lean/RecCert5.lean): explicit steps,
# generic neutral-word runs (grun) and exact cycle runs (gcyc), searched like rtree5_core.jl (tree5) but with
# exact integer data and exact certificates.  Tree format:
#   (:leaf, den, rn, rd, y1, p1, y2, p2) | (:node, [child × 9])
#   child = (:inf, ys, prs) | (:sub, tree) | (:skip,) | (:grun, P, fs, ld, ly, lp, [piece-child × 26PL]) | (:gcyc, P, [piece-child × PL])
#   piece-child = (:inf, ys, prs) | (:sub, tree)
include("rexport2.jl")
include("rtree5_core.jl")
const DIAGL = ReentrantLock()
diag!(s) = lock(DIAGL) do; DIAG[s] = get(DIAG, s, 0) + 1; end   # thread-safe

const KQI = [(BI(p), BI(q)) for (p, q) in KQ]
unitv(r) = BI.([q == r ? 1 : 0 for q in 1:5])
applyM(E, W) = [comb5(E[r], W) for r in 1:5]                 # E: 5 rows (F5)
brRowsP(k, ps) = [[need ? comb5(c, W) : -comb5(c, W) for W in ps] for (c, need) in CONDS[k]]
walkParts(ks, qs) = foldl((q, k) -> [stepW(k, W) for W in q], ks; init = qs)
function walkRows(ks, qs)
    out = Vector{Vector{BI}}[]
    for k in ks; append!(out, brRowsP(k, qs)); qs = [stepW(k, W) for W in qs]; end
    out
end
unitRows(qs) = [[W[r] for W in qs] for r in 1:5]
repRow(np, row) = [row[q % np + 1] for q in 0:3np-1]
onParts(fs, ps) = [[comb5(f, W) for W in ps] for f in fs]
upC(ks) = sum(eUp(k) for k in ks; init = 0); dnC(ks) = sum(eDn(k) for k in ks; init = 0)

# ---- run data (mirror of RunGen/RunExit/RecCert5) ----
wFull(P) = walkParts(P, [W0])[1]
function nilOK(W, s)
    W[1][1] == s && W[1][2] == 0 && W[2][1] == 0 && W[2][2] == s &&
        all(r -> all(c -> W[r][c] == (r == c ? s : 0), 1:5), 3:5)
end
idOK(W, s) = nilOK(W, s) && all(W[1][3:5] .== 0) && all(W[2][3:5] .== 0)
nrow(W, r) = BI[0, 0, W[r][3], W[r][4], W[r][5]]
function fSel(k, fs)
    fs == 0 && return unitv(1); fs == 1 && return unitv(2); fs == 2 && return BI[1, 1, 0, 0, 0]
    j = fs - 3; j < length(CONDS[k]) || return zeros(BI, 5)
    (c, need) = CONDS[k][j+1]; need ? c : -c
end
kqI(i) = KQI[i+1]                                        # 0-based like Lean kq
gA(a, b, p, q) = (-q * a - p * b, -q * b + p * a)
function gS(a, b, i)
    i == 0 && return a * (kqI(0)[2] * b - a * kqI(0)[1])
    i < 25 && return kqI(i - 1)[2] * kqI(i)[2] * (a * a + b * b)
    b * (a * kqI(24)[2] + b * kqI(24)[1])
end
function gV(a, b, i, e)
    e == 0 && return (BI(0), BI(0))
    if i == 0
        D = kqI(0)[2] * b - a * kqI(0)[1]
        e == 1 && return (D * b, -D * a)
        g = gA(a, b, kqI(0)...); return (a * g[1], a * g[2])
    elseif i < 25
        if e == 1; g = gA(a, b, kqI(i - 1)...); return (kqI(i)[2] * g[1], kqI(i)[2] * g[2]); end
        g = gA(a, b, kqI(i)...); return (kqI(i - 1)[2] * g[1], kqI(i - 1)[2] * g[2])
    else
        D = a * kqI(24)[2] + b * kqI(24)[1]
        e == 1 && return (-D * b, D * a)
        g = gA(a, b, kqI(24)...); return (b * g[1], b * g[2])
    end
end
gG(F, i) = i == 0 ? unitv(2) : i < 25 ? F : unitv(1)
function gE(a, b, F, i, e)
    S = gS(a, b, i); (x, y) = gV(a, b, i, e); G_ = gG(F, i)
    [S .* unitv(1) .+ x .* G_, S .* unitv(2) .+ y .* G_, S .* unitv(3), S .* unitv(4), S .* unitv(5)]
end
gBnd(a, b, i) = i == 0 ? (a > 0 && kqI(0)[2] * b - a * kqI(0)[1] > 0) :
                i < 25 ? true : (b > 0 && a * kqI(24)[2] + b * kqI(24)[1] > 0)
function pieceRowsG(i, l, h)
    out = Vector{BI}[]
    i >= 1 && push!(out, kqI(i - 1)[2] .* h .- kqI(i - 1)[1] .* l)
    i <= 24 && push!(out, kqI(i)[1] .* l .- kqI(i)[2] .* h)
    out
end
autoPos(l) = l[1] == 0 && l[2] == 0 && all(l[3:5] .>= 0) && sum(l[3:5]) > 0

# strict positivity of ℓ on all parts: y ≥ 0 with ℓ_p − Σ y row_p > 0 on the cell
function pos_cert(b, cons, P, lab, C, rows, lps, np)
    m = lpmodel(); n = length(rows)
    Er = [rowexp(r...) for r in rows]
    V = [[fvalsS(r[p], C, Er[i]) for p in 1:np] for (i, r) in enumerate(rows)]
    sc = [max(maximum(maximum(abs, v) for v in Vr), 1e-300) for Vr in V]
    El = rowexp(lps...); LV = [fvalsS(lps[p], C, El) for p in 1:np]; lsc = max(maximum(maximum(abs, v) for v in LV), 1e-300)
    @variable(m, y[1:n] >= 0); @variable(m, t <= 1)
    for p in 1:np, j in eachindex(C)
        @constraint(m, LV[p][j] / lsc - (n == 0 ? 0.0 : sum(y[i] * V[i][p][j] / sc[i] for i in 1:n)) >= t)
    end
    @objective(m, Max, t); optimize!(m)
    termination_status(m) == MOI.OPTIMAL || return nothing
    value(t) > 1e-10 || return nothing
    yq = [(i - 1, Rational{BI}(lsc * value(y[i]) / sc[i]) * BI(2)^max(El - Er[i], 0) / BI(2)^max(Er[i] - El, 0)) for i in 1:n if value(y[i]) > 0]
    D = isempty(yq) ? BI(1) : lcm([denominator(q) for (_, q) in yq])
    ys = [(i, numerator(q) * (D ÷ denominator(q))) for (i, q) in yq]
    prs = Int[]
    for p in 1:np
        F = D .* lps[p] .- farkasI([r[p] for r in rows], ys)
        pr = find_pairI(b, cons, P, lab, F, true); pr === nothing && return nothing
        push!(prs, pr)
    end
    (ys, prs, D)
end

function rtree_exact3(b::IBox; KMAX = 60, RAWMAX = 200, RUNMAX = 3, TLIM = 600.0)
    cons = [conI(b, k) for k in 0:NCON-1]
    P_, lab = cellpolyI(b, cons); isempty(P_) && return :empty
    C = cornersI(P_, b)
    t0 = time()
    inf(rows, np) = inf_cert2(b, cons, P_, lab, C, rows, np)
    function leafcert(parts, rows, σ, moved, nE, nC)
        moved || return nothing
        np = length(parts)
        Tk = [comb5(TTv, W) for W in parts]; Lk = [comb5(L5v, W) for W in parts]
        verify(rn, rd, y1, y2, dvec) = begin
            prs1 = Int[]; prs2 = Int[]
            for p in 1:np
                F1 = BI(rn) .* dvec .- BI(rd) .* Tk[p] .- farkasI([r[p] for r in rows], y1)
                F2 = BI(rn) .* dvec .- BI(rd) .* Lk[p] .- farkasI([r[p] for r in rows], y2)
                q1 = find_pairI(b, cons, P_, lab, F1, false); q2 = find_pairI(b, cons, P_, lab, F2, false)
                (q1 === nothing || q2 === nothing) && return nothing
                push!(prs1, q1); push!(prs2, q2)
            end
            (prs1, prs2)
        end
        if nE >= nC
            for den in (false, true)
                dvec = den ? TTv : L5v
                a = leaf_fixed2(b, cons, P_, lab, C, rows, Tk, dvec, np, σ, BI(1)); a === nothing && continue
                c = leaf_fixed2(b, cons, P_, lab, C, rows, Lk, dvec, np, σ, BI(1)); c === nothing && continue
                Da = length(a) == 3 ? a[3] : BI(1); Dc = length(c) == 3 ? c[3] : BI(1); D = Da * Dc
                y1 = [(i, y * Dc) for (i, y) in a[1]]; y2 = [(i, y * Da) for (i, y) in c[1]]
                v = verify(σ * D, D, y1, y2, dvec); v === nothing && continue
                BI(2)^(8nC) * BI(σ * D)^7 <= BI(2)^(8nE) * (BI(D) * σ)^7 || continue
                return (:leaf, den, σ * D, D, y1, v[1], y2, v[2])
            end
        end
        for den in (true, false)
            dvec = den ? TTv : L5v
            a = leaf_part2(b, cons, P_, lab, C, rows, Tk, dvec, np); a === nothing && continue
            c = leaf_part2(b, cons, P_, lab, C, rows, Lk, dvec, np); c === nothing && continue
            (rn1, rd1, y1, _) = a; (rn2, rd2, y2, _) = c
            rn = max(rn1 * rd2, rn2 * rd1); rd = rd1 * rd2
            y1 = [(i, y * rd2) for (i, y) in y1]; y2 = [(i, y * rd1) for (i, y) in y2]
            v = verify(rn, rd, y1, y2, dvec); v === nothing && continue
            BI(2)^(8nC) * BI(rn)^7 <= BI(2)^(8nE) * (BI(rd) * σ)^7 || continue
            return (:leaf, den, rn, rd, y1, v[1], y2, v[2])
        end
        nothing
    end
    fail = Ref{Symbol}(:ok)
    # piece child at an exit: infeasible or subtree with excluded branch `post`
    function exitchild(parts, rows, σ, nE, nC, post, k, raw, runs)
        ic = inf(rows, length(parts)); ic !== nothing && return (:inf, ic...)
        sub = rec(parts, rows, σ, true, post, nE, nC, k + 1, raw + 1, Int[], runs + 1)
        sub === nothing ? nothing : (:sub, sub)
    end
    function grun(P, parts, rows2, σ, nE, nC, k, raw, runs)
        PL = length(P); np = length(parts); Wf = wFull(P); s = BI(16)^PL
        (nilOK(Wf, s) && upC(P) == dnC(P)) || return nothing
        n0 = nrow(Wf, 1); n1 = nrow(Wf, 2)
        for fs in 0:2 + length(CONDS[P[1]])
            F = fSel(P[1], fs); a = F[1]; bq = F[2]
            a * a + bq * bq > 0 || continue
            l = -(a .* n0 .+ bq .* n1); h = -bq .* n0 .+ a .* n1
            ly = Tuple{Int,BI}[]; lp = Int[]; ld = BI(1)
            if !autoPos(l)
                pc = pos_cert(b, cons, P_, lab, C, rows2, [comb5(l, W) for W in parts], np)
                pc === nothing && continue
                ly, lp, ld = pc
            end
            pcs = Any[]; ok = true
            for idx in 0:26PL-1
                i = idx ÷ PL; r = idx % PL + 1
                prows = pieceRowsG(i, l, h)
                if !gBnd(a, bq, i)
                    ic = inf(vcat(rows2, onParts(prows, parts)), np)
                    ic === nothing && (ok = false; break)
                    push!(pcs, (:inf, ic...)); continue
                end
                Es = [gE(a, bq, F, i, e) for e in 0:2]
                up = vcat([[applyM(Es[e], W) for W in parts] for e in 1:3]...)
                ex = walkParts(P[1:r], up)
                rws = vcat([repRow(np, rr) for rr in rows2], [repRow(np, rr) for rr in onParts(prows, parts)],
                           unitRows(up), walkRows(P[1:r], up), unitRows(ex))
                σ2 = σ * gS(a, bq, i) * BI(16)^r
                c = exitchild(ex, rws, σ2, nE + upC(P[1:r]), nC + dnC(P[1:r]), P[r % PL + 1], k, raw, runs)
                c === nothing && (ok = false; break)
                push!(pcs, c)
            end
            ok && return (:grun, P, fs, ld, ly, lp, pcs)
            fail[] = :ok                       # retry with the next bound functional
        end
        nothing
    end
    function gcyc(P, parts, rows2, σ, nE, nC, k, raw, runs)
        PL = length(P); s = BI(16)^PL
        (idOK(wFull(P), s) && upC(P) == dnC(P)) || return nothing
        pcs = Any[]
        for r in 1:PL
            ex = walkParts(P[1:r], parts)
            rws = vcat(rows2, walkRows(P[1:r], parts), unitRows(ex))
            c = exitchild(ex, rws, σ * BI(16)^r, nE + upC(P[1:r]), nC + dnC(P[1:r]), P[r % PL + 1], k, raw, runs)
            c === nothing && return nothing
            push!(pcs, c)
        end
        (:gcyc, P, pcs)
    end
    function rec(parts, rows, σ, moved, post, nE, nC, k, raw, path, runs)
        lc = leafcert(parts, rows, σ, moved, nE, nC)
        lc !== nothing && return lc
        (k >= KMAX || raw >= RAWMAX) && (fail[] = :depth; return nothing)
        time() - t0 > TLIM && (fail[] = :time; return nothing)
        np = length(parts)
        gw = runs < RUNMAX ? detect_gword(path) : nothing
        cp = runs < RUNMAX ? detect_cword(path) : nothing
        ch = Any[]
        for kb in 1:9
            if kb == post; push!(ch, (:skip,)); continue; end
            rows2 = vcat(rows, brRowsP(kb, parts))
            ic = inf(rows2, np)
            if ic !== nothing; push!(ch, (:inf, ic...)); continue; end
            c = nothing
            gw !== nothing && gw.P[1] == kb && (c = grun(gw.P, parts, rows2, σ, nE, nC, k, raw, runs))
            c === nothing && cp !== nothing && cp[1] == kb && (c = gcyc(cp, parts, rows2, σ, nE, nC, k, raw, runs))
            if c === nothing
                fail[] = :ok
                sub = rec([stepW(kb, W) for W in parts], rows2, σ * 16, true, 0, nE + eUp(kb), nC + eDn(kb),
                          k + (kb == 2 ? 0 : 1), raw + 1, vcat(path, kb), runs)
                sub === nothing && return nothing
                c = (:sub, sub)
            end
            push!(ch, c)
        end
        (:node, ch)
    end
    t = rec([W0], Vector{Vector{BI}}[], BI(1), false, 0, 0, 0, 0, 0, Int[], 0)
    t === nothing ? fail[] : t
end
treesize3(t) = t[1] == :leaf ? 1 : sum((c[1] == :sub ? treesize3(c[2]) : c[1] in (:grun, :gcyc) ?
    sum((pc[1] == :sub ? treesize3(pc[2]) : 0) for pc in c[end]; init = 0) : 0) for c in t[2]; init = 0)
