# Recovery trees with weight representation and symbolic Rx-run nodes.
# A node: weights μ ≥ 0 (Σ μ = 1) over columns; current state z = Z μ (5×n); constraint rows R μ ≥ 0;
# base quantities λ0 = l0·μ, T0 = t0·μ (of the start state); accumulated area factor α; counters.
# S = log P(z) − log P(z0) = 0.8 log α − 0.7 log( max(T, 5λ) / max(T0, 5λ0) )   (P = A^0.8 / max(T,5λ)^0.7).
const MRX = BMATS[2]
const NRX = MRX * MRX - [i == j ? 1.0 : 0.0 for i in 1:5, j in 1:5]
const KMAX2 = Ref(24); const RAWMAX2 = Ref(80); const RUNK = Ref(3); const MAXLEAF2 = Ref(3000)
struct Node
    Z::Matrix{Float64}
    R::Matrix{Float64}
    l0::Vector{Float64}
    t0::Vector{Float64}
    α::Float64
end
rowof(g, Z) = [g[1]*Z[1,j] + g[2]*Z[2,j] + g[3]*Z[3,j] + g[4]*Z[4,j] + g[5]*Z[5,j] for j in 1:size(Z, 2)]
# certified upper bound of num/den over {μ ≥ 0, Σμ = 1, P μ ≥ 0} (den may vanish on some columns but must be
# positive on the polytope): doubling to an infeasible bracket, then bisection
function ratio_max(P, num, den; steps = 12)
    feas(r) = lp_feasible(vcat(P, (num .- r .* den)'))       # exists point with num ≥ r den
    pos = [j for j in eachindex(den) if den[j] > 0]
    hi = isempty(pos) ? 1.0 : max(maximum(num[j] / den[j] for j in pos), 1e-12)
    k = 0
    while feas(hi); hi *= 2; k += 1; k > 60 && return Inf; end
    lo = 0.0
    for _ in 1:steps; m = (lo + hi) / 2; feas(m) ? (lo = m) : (hi = m); end
    hi
end
function Slow2(nd::Node)
    T = rowof((1,1,1,1,1), nd.Z); L = rowof((0,0,1,1,1), nd.Z)
    side = nd.t0 .- 5 .* nd.l0                       # ≥ 0 ⇔ s_0 ≤ 1/5
    parts = Tuple{Matrix{Float64},Vector{Float64}}[]
    if minimum(side) >= 0; push!(parts, (nd.R, nd.t0))
    elseif maximum(side) <= 0; push!(parts, (nd.R, 5 .* nd.l0))
    else
        Pa = vcat(nd.R, side'); lp_feasible(Pa) && push!(parts, (Pa, nd.t0))
        Pb = vcat(nd.R, (-side)'); lp_feasible(Pb) && push!(parts, (Pb, 5 .* nd.l0))
    end
    r = 0.0
    for (Pp, den) in parts
        # columns with den = 0 (relaxed run directions) are allowed only if the numerator vanishes there too
        r = max(r, ratio_max(Pp, T, den), ratio_max(Pp, 5 .* L, den))
        isfinite(r) || return -Inf
    end
    GAM * log(nd.α) - 0.7 * log(r)
end
step(nd::Node, kb) = Node(BMATS[kb] * nd.Z, vcat(nd.R, permutedims(reduce(hcat, [rowof(g, nd.Z) for g in BCOND[kb]]))), nd.l0, nd.t0, nd.α * BALPHA[kb])
# exit states of an Rx run continuing from nd (any number m ≥ 0 of further Rx pairs), for both parities
const KAPPAS = Ref([-1e3, -30.0, -10.0, -5.0, -3.0, -2.0, -1.5, -1.2, -1.0, -0.8, -0.5, -0.25, 0.0, 0.25, 0.5, 0.8, 1.0, 1.2, 1.5, 2.0, 3.0, 5.0, 10.0, 30.0, 1e3])
# split a node into κ-pieces, κ = (D23 − D12)/D13 of the CURRENT state (rows on the weights)
function kappa_pieces(nd::Node)
    D12 = rowof((0,0,1,0,0), nd.Z); D13 = rowof((0,0,0,1,0), nd.Z); D23 = rowof((0,0,0,0,1), nd.Z)
    ks = KAPPAS[]; out = Node[]
    for i in 0:length(ks)
        rows = Vector{Float64}[]
        i >= 1 && push!(rows, D23 .- D12 .- ks[i] .* D13)              # κ ≥ κ_i
        i < length(ks) && push!(rows, ks[i+1] .* D13 .- D23 .+ D12)     # κ ≤ κ_{i+1}
        R = isempty(rows) ? nd.R : vcat(nd.R, permutedims(reduce(hcat, rows)))
        lp_feasible(R) && push!(out, Node(nd.Z, R, nd.l0, nd.t0, nd.α))
    end
    out
end
const AV = (-1.0, -1.0, 0.0, 0.0, 0.0); const BV = (1.0, -1.0, 0.0, 0.0, 0.0)
# exit states of an Rx run from nd: w = z + ρ1 A + ρ2 B (even number of further Rx steps) or M_Rx(...) (odd)
function runexits(nd::Node)
    out = Node[]
    n = size(nd.Z, 2)
    Dsum = rowof((1,1,0,0,0), nd.Z)                     # Δ2 + Δ3 of the run start, per column
    ks = KAPPAS[]
    for i in 0:length(ks), odd in (false, true)
        # ρ2 = κ_base ρ1 ± σ, σ ≥ 0: columns A + κ_base B (weight ρ1) and ±B (weight σ); no cancelling pairs
        κb = i >= 1 ? ks[i] : ks[1]; sg = i >= 1 ? 1.0 : -1.0
        Zr = hcat(nd.Z, collect(AV) .+ κb .* collect(BV), sg .* collect(BV))
        Z = odd ? MRX * Zr : Zr
        R = hcat(nd.R, zeros(size(nd.R, 1), 2))
        rows = Vector{Float64}[]
        push!(rows, vcat(Dsum, -2.0, 0.0))                                       # 2 ρ1 ≤ Δsum(z)
        1 <= i < length(ks) && push!(rows, vcat(zeros(n), ks[i+1] - ks[i], -1.0)) # σ ≤ (κ_{i+1} − κ_i) ρ1
        D12 = rowof((0,0,1,0,0), nd.Z); D13 = rowof((0,0,0,1,0), nd.Z); D23 = rowof((0,0,0,0,1), nd.Z)
        i >= 1 && push!(rows, vcat(D23 .- D12 .- ks[i] .* D13, 0.0, 0.0))
        i < length(ks) && push!(rows, vcat(ks[i+1] .* D13 .- D23 .+ D12, 0.0, 0.0))
        for q in 1:5; push!(rows, rowof(ntuple(k -> k == q ? 1.0 : 0.0, 5), Z)); end          # exit state ≥ 0
        prev = inv(MRX) * Z
        for g in BCOND[2]; push!(rows, rowof(g, prev)); end                                   # previous step was Rx
        Rn = vcat(R, permutedims(reduce(hcat, rows)))
        lp_feasible(Rn) || continue
        push!(out, Node(Z, Rn, vcat(nd.l0, zeros(2)), vcat(nd.t0, zeros(2)), nd.α))
    end
    out
end
function tree2(b::Box)
    C = corners(b, abpoly(b)); isempty(C) && return (:empty, 0, 0)
    Z0 = reduce(hcat, [collect(c) for c in C])
    root = Node(Z0, zeros(0, size(Z0, 2)), rowof((0,0,1,1,1), Z0), rowof((1,1,1,1,1), Z0), 1.0)
    nleaf = 0; maxk = 0; fail = Ref{Symbol}(:ok)
    function rec(nd::Node, k, raw, consec, inrun)
        fail[] == :ok || return
        if raw > 0 && Slow2(nd) >= 0
            nleaf += 1; maxk = max(maxk, k); return
        end
        k >= KMAX2[] && (fail[] = :depth; return)
        raw >= RAWMAX2[] && (fail[] = :raw; return)
        if consec >= RUNK[] && !inrun
            for ex in runexits(nd)                        # symbolic run: continue from the exit states
                lp_feasible(ex.R) || continue
                for kb in 1:9
                    kb == 2 && continue
                    ch = step(ex, kb); lp_feasible(ch.R) || continue
                    rec(ch, k + 1, raw + 1, 0, false)
                    nleaf > MAXLEAF2[] && (fail[] = :size; return)
                end
            end
            return
        end
        for kb in 1:9
            ch = step(nd, kb); lp_feasible(ch.R) || continue
            rec(ch, k + (kb == 2 ? 0 : 1), raw + 1, kb == 2 ? consec + 1 : 0, false)
            nleaf > MAXLEAF2[] && (fail[] = :size; return)
        end
    end
    rec(root, 0, 0, 0, false)
    (fail[], nleaf, maxk)
end
