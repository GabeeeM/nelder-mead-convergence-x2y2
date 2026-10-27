# Cell certificate search on the far region U = {tall: s < S0} ∪ {strip: s ≥ S0, heron(D/λ) ≤ TAU}.
# Potential P = A · T^(-κ) · q(cell),  T = (f3-f1) + ΣD.  Per-step log-change of A·T^-κ is
#   log α - κ log(T'/T)  (exact), so q only has to absorb losses.
# Coordinates u = (s, ψ, a, b): z = ((1-s)ψ, (1-s)(1-ψ), s a, s b, s(1-a-b)).
include("cells.jl")
using JuMP, HiGHS
include("polys.jl")
using Printf, LinearAlgebra

const GAM = parse(Float64, get(ENV, "GAM", "0.8"))
const DEL = (3GAM - 1)/2
const S1 = parse(Float64, get(ENV, "S1", "0.2"))
const S0 = parse(Float64, get(ENV, "S0", "0.125"))
const TAU = parse(Float64, get(ENV, "TAU", "0.005"))
const NG = parse(Int, get(ENV, "NG", "16"))

struct Box; lo::NTuple{4,Float64}; hi::NTuple{4,Float64}; end
heronab(a, b) = (c = 1 - a - b; 2*(a*b + a*c + b*c) - a^2 - b^2 - c^2)

# valid D-shape region inside the box, as a convex polygon in (a,b):
#   tall boxes: box ∩ disk ;  strip boxes: convex hull of sampled points of box ∩ {0 ≤ heron ≤ TAU}
# (exploration version; the rigorous version will use certified polygons)
function sample_region(b::Box, strip::Bool; n=24)
    pts = NTuple{2,Float64}[]
    for i in 0:n, j in 0:n
        a = b.lo[3] + i/n*(b.hi[3]-b.lo[3]); bb = b.lo[4] + j/n*(b.hi[4]-b.lo[4])
        h = heronab(a, bb)
        (h >= 0 && (!strip || h <= TAU)) && push!(pts, (a, bb))
    end
    # add boundary crossings along grid lines (heron = 0 and heron = TAU) by bisection
    for lev in (strip ? (0.0, TAU) : (0.0,))
        for i in 0:n
            a = b.lo[3] + i/n*(b.hi[3]-b.lo[3])
            for j in 0:n-1
                b1 = b.lo[4] + j/n*(b.hi[4]-b.lo[4]); b2 = b.lo[4] + (j+1)/n*(b.hi[4]-b.lo[4])
                h1 = heronab(a, b1) - lev; h2 = heronab(a, b2) - lev
                if h1*h2 < 0
                    lo, hi = b1, b2
                    for _ in 1:40; m = (lo+hi)/2; (heronab(a, m) - lev)*h1 > 0 ? (lo = m) : (hi = m); end
                    push!(pts, (a, (lo+hi)/2))
                end
            end
        end
        for j in 0:n
            bb = b.lo[4] + j/n*(b.hi[4]-b.lo[4])
            for i in 0:n-1
                a1 = b.lo[3] + i/n*(b.hi[3]-b.lo[3]); a2 = b.lo[3] + (i+1)/n*(b.hi[3]-b.lo[3])
                h1 = heronab(a1, bb) - lev; h2 = heronab(a2, bb) - lev
                if h1*h2 < 0
                    lo, hi = a1, a2
                    for _ in 1:40; m = (lo+hi)/2; (heronab(m, bb) - lev)*h1 > 0 ? (lo = m) : (hi = m); end
                    push!(pts, ((lo+hi)/2, bb))
                end
            end
        end
    end
    pts
end
function hull(pts)
    P = unique(pts); length(P) <= 2 && return P
    sort!(P)
    cross(o, a, b) = (a[1]-o[1])*(b[2]-o[2]) - (a[2]-o[2])*(b[1]-o[1])
    lower = NTuple{2,Float64}[]
    for p in P
        while length(lower) >= 2 && cross(lower[end-1], lower[end], p) <= 0; pop!(lower); end
        push!(lower, p)
    end
    upper = NTuple{2,Float64}[]
    for p in reverse(P)
        while length(upper) >= 2 && cross(upper[end-1], upper[end], p) <= 0; pop!(upper); end
        push!(upper, p)
    end
    vcat(lower[1:end-1], upper[1:end-1])
end
# strip tiers (Lean `tierDen`): heron ≤ τ λ² for s ≥ 1/8 (τ = 2^-20), s ≥ 1/64 (2^-13), s ≥ 1/512 (2^-7)
const TIERS = get(ENV, "TIERS", "1") == "1"
tauof(s0) = s0 >= 0.125 - 1e-12 ? 2.0^-20 : s0 >= 1/64 - 1e-12 ? 2.0^-13 : 2.0^-7
tauqof(s0) = Rational{BigInt}(1, s0 >= 0.125 - 1e-12 ? BigInt(2)^20 : s0 >= 1/64 - 1e-12 ? BigInt(2)^13 : BigInt(2)^7)
isstrip(b::Box) = b.lo[1] >= (TIERS ? 1/512 : S0) - 1e-12
striptau(b::Box) = TIERS ? tauof(b.lo[1]) : TAU
const POLYCACHE = Dict{NTuple{8,Float64},Vector{NTuple{2,Float64}}}()
const PCLOCK = ReentrantLock()
function abpoly(b::Box)
    key = (b.lo..., b.hi...)
    v = lock(PCLOCK) do; get(POLYCACHE, key, nothing); end
    v === nothing || return v
    poly = simple_poly(b.lo[3], b.hi[3], b.lo[4], b.hi[4], isstrip(b), TIERS ? tauqof(b.lo[1]) : TAUQ)
    P = [(Float64(p[1]), Float64(p[2])) for p in poly]
    lock(PCLOCK) do; POLYCACHE[key] = P; end
    P
end
const TAUQ = rationalize(BigInt, TAU)
function clip(poly, n1, n2, h)
    out = NTuple{2,Float64}[]
    m = length(poly); m == 0 && return out
    for i in 1:m
        P = poly[i]; Q = poly[mod1(i+1, m)]
        fP = n1*P[1] + n2*P[2] - h; fQ = n1*Q[1] + n2*Q[2] - h
        fP <= 0 && push!(out, P)
        if (fP < 0 && fQ > 0) || (fP > 0 && fQ < 0)
            t = fP / (fP - fQ); push!(out, (P[1] + t*(Q[1]-P[1]), P[2] + t*(Q[2]-P[2])))
        end
    end
    out
end

lin(c, z) = c[1]*z[1] + c[2]*z[2] + c[3]*z[3] + c[4]*z[4] + c[5]*z[5]
function sgn(c, Z)
    mn = Inf; mx = -Inf
    for z in Z; v = lin(c, z); mn = min(mn, v); mx = max(mx, v); end
    mn >= 0 ? 1 : mx < 0 ? -1 : 0
end
function corners(b::Box, poly)
    C = NTuple{5,Float64}[]
    for (a, bb) in poly, k in 0:3
        s = (k & 1 == 1) ? b.hi[1] : b.lo[1]; ψ = (k & 2 == 2) ? b.hi[2] : b.lo[2]
        push!(C, ((1-s)*ψ, (1-s)*(1-ψ), s*a, s*bb, s*(1-a-bb)))
    end
    C
end
struct Edge; lo::NTuple{4,Float64}; hi::NTuple{4,Float64}; Δ::Float64; end
function edges(b::Box)
    poly = abpoly(b)
    out = Edge[]
    length(poly) == 0 && return (out, true)
    C = corners(b, poly)
    for (k, br) in enumerate(BRANCHES)
        ok = true
        for (c, need) in br[3]
            st = sgn(c, C); if st != 0 && st != need; ok = false; break; end
        end
        ok || continue
        br[1] == :Rx && b.hi[1] < 0.2 && continue          # Rx needs s ≥ 1/5
        br[1] in (:O, :I) && b.hi[1] <= 0.5 && continue    # contraction needs s > 1/2
        M = BMATS[k]
        imgs = [M * collect(z) for z in C]
        T0 = [sum(z) for z in C]; T1 = [sum(v) for v in imgs]
        d12 = [v[1] + v[2] for v in imgs]
        rr = Float64[]; sa = Float64[]; sb = Float64[]; λ1s = Float64[]
        for (a, bb) in poly
            v = M * [0.0, 0.0, a, bb, 1 - a - bb]; l1 = v[3] + v[4] + v[5]
            push!(rr, 1 / l1); push!(sa, v[3]/l1); push!(sb, v[4]/l1)
        end
        λ1 = [v[3]+v[4]+v[5] for v in imgs]
        (minimum(T1) > 0 && minimum(rr) > 0) || return (out, true)
        rT = maximum(T1 ./ T0)
        rng(f) = (v = [f(i) for i in eachindex(imgs)]; (max(0.0, minimum(v)), min(1.0, maximum(v))))
        s2 = rng(i -> λ1[i] / T1[i]); ψ2 = minimum(d12) > 0 ? rng(i -> imgs[i][1] / d12[i]) : (0.0, 1.0)
        a2 = (max(0.0, minimum(sa)), min(1.0, maximum(sa))); b2 = (max(0.0, minimum(sb)), min(1.0, maximum(sb)))
        # potential  A^γ λ^((1-3γ)/2) min(s,S1)^δ
        lrmax = maximum(1 ./ rr)                     # max λ'/λ
        smin = b.lo[1]; smax = b.hi[1]
        Δ = GAM*log(BALPHA[k]) + (1 - 3GAM)/2*log(lrmax) + DEL*(log(min(max(s2[1], 1e-300), S1)) - log(min(smax, S1)))
        if br[1] in (:R, :Rx)
            # λ' = λ, α = 1 exactly: Δ = δ (log min(s',S1) - log min(s,S1))
            if smin >= S1 && s2[1] >= S1
                Δ = 0.0
            else
                Δ = DEL*(log(min(max(s2[1], 1e-300), S1)) - log(min(smax, S1)))
                br[1] == :R && (Δ = max(Δ, 0.0))     # R: s' ≥ s exactly
            end
        elseif br[1] == :E && smax < S1 && s2[2] < S1
            Δ = max(Δ, 0.0)                          # tall E: exact lemma
        end
        push!(out, Edge((s2[1], ψ2[1], a2[1], b2[1]), (s2[2], ψ2[2], a2[2], b2[2]), Δ))
    end
    (out, false)
end
# ---- kd-tree over leaf boxes ----
mutable struct Node; box::Box; kids::Union{Nothing,Tuple{Int,Int}}; leaf::Int; end
function maketree(boxes)
    nodes = Node[]
    function rec(ids)
        if length(ids) == 1; push!(nodes, Node(boxes[ids[1]], nothing, ids[1])); return length(nodes); end
        lo = ntuple(d -> minimum(boxes[i].lo[d] for i in ids), 4); hi = ntuple(d -> maximum(boxes[i].hi[d] for i in ids), 4)
        d = argmax([hi[k] - lo[k] for k in 1:4])
        srt = sort(ids, by = i -> boxes[i].lo[d] + boxes[i].hi[d]); m = length(srt) ÷ 2
        l = rec(srt[1:m]); r = rec(srt[m+1:end])
        push!(nodes, Node(Box(lo, hi), (l, r), 0)); return length(nodes)
    end
    root = rec(collect(1:length(boxes)))
    nodes, root
end
function query!(out, nodes, k, lo, hi)
    nd = nodes[k]
    all(i -> nd.box.lo[i] <= hi[i] && lo[i] <= nd.box.hi[i], 1:4) || return
    if nd.kids === nothing; push!(out, nd.leaf); else; query!(out, nodes, nd.kids[1], lo, hi); query!(out, nodes, nd.kids[2], lo, hi); end
end
const PRUNED = Set{Tuple{NTuple{8,Float64},NTuple{8,Float64}}}()
bkey(b::Box) = (b.lo..., b.hi...)
# LP test: can some state of box b, following some feasible branch, land in box t?
function edge_feasible(b::Box, t::Box)
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
        m = Model(HiGHS.Optimizer); set_silent(m)
        nc = length(C)
        @variable(m, μ[1:nc] >= 0)
        @constraint(m, sum(μ) == 1)
        z = [sum(μ[j]*C[j][i] for j in 1:nc) for i in 1:5]
        for (c, need) in br[3]
            if need > 0; @constraint(m, sum(c[i]*z[i] for i in 1:5) >= 0)
            else @constraint(m, sum(c[i]*z[i] for i in 1:5) <= 0) end
        end
        zp = [sum(M[r, i]*z[i] for i in 1:5) for r in 1:5]
        λp = zp[3] + zp[4] + zp[5]; Tp = sum(zp); dp = zp[1] + zp[2]
        @constraint(m, λp - t.lo[1]*Tp >= 0); @constraint(m, t.hi[1]*Tp - λp >= 0)
        @constraint(m, zp[1] - t.lo[2]*dp >= 0); @constraint(m, t.hi[2]*dp - zp[1] >= 0)
        @constraint(m, zp[3] - t.lo[3]*λp >= 0); @constraint(m, t.hi[3]*λp - zp[3] >= 0)
        @constraint(m, zp[4] - t.lo[4]*λp >= 0); @constraint(m, t.hi[4]*λp - zp[4] >= 0)
        optimize!(m)
        termination_status(m) == MOI.INFEASIBLE || return true
    end
    false
end
function graph(boxes)
    n = length(boxes); nodes, root = maketree(boxes)
    succ = [Tuple{Int,Float64}[] for _ in 1:n]; bad = falses(n)
    Threads.@threads for i in 1:n
        E, isbad = edges(boxes[i])
        if isbad; bad[i] = true; continue; end
        kb = bkey(boxes[i])
        for e in E
            out = Int[]; query!(out, nodes, root, e.lo, e.hi)
            for t in out
                (kb, bkey(boxes[t])) in PRUNED && continue
                push!(succ[i], (t, e.Δ))
            end
        end
    end
    succ, bad
end
function bellman(succ, bad; iters=300)
    n = length(succ); lq = [bad[i] ? -1e3 : 0.0 for i in 1:n]; pred = zeros(Int, n)
    for it in 1:iters
        ch = Threads.Atomic{Int}(0)
        Threads.@threads for i in 1:n
            bad[i] && continue
            v = 0.0; pj = 0
            for (j, Δ) in succ[i]; w = lq[j] + Δ; if w < v; v = w; pj = j; end; end
            if v < lq[i] - 1e-9; lq[i] = max(v, -1e3); pred[i] = pj; Threads.atomic_add!(ch, 1); end
        end
        ch[] == 0 && return lq, true, pred
        # early exit as soon as the predecessor graph contains a negative cycle
        (it % 10 == 0 && !isempty(negcycles(succ, pred))) && return lq, false, pred
    end
    lq, false, pred
end
function negcycles(succ, pred)
    n = length(succ); cycles = Vector{Vector{Int}}()
    w(i, j) = minimum(Δ for (k, Δ) in succ[i] if k == j)
    seen = falses(n)
    for i0 in 1:n
        (pred[i0] == 0 || seen[i0]) && continue
        path = Int[]; pos = Dict{Int,Int}(); i = i0
        while i != 0 && !haskey(pos, i) && !seen[i]
            pos[i] = length(path) + 1; push!(path, i); i = pred[i]
        end
        if i != 0 && haskey(pos, i)
            c = path[pos[i]:end]
            sum(w(c[t], c[mod1(t+1, length(c))]) for t in 1:length(c)) < -1e-9 && push!(cycles, c)
        end
        seen[path] .= true
    end
    cycles
end
inU(b::Box) = length(abpoly(b)) >= 1
# does some sampled true state of cell b map (by the exact NM step) into box t?
# b-values with heronab(a, b) = h (both branches), restricted to [lo, hi] and a + b ≤ 1
function strip_bs(a, h, lo, hi)
    B = 4 - 4a; C = -4a^2 + 4a - 1 - h; d = B^2 + 16C
    d < 0 && return Float64[]
    r = sqrt(d)
    [x for x in ((B - r) / 8, (B + r) / 8) if lo <= x <= hi && a + x <= 1]
end
# a random valid state (s, ψ, a, b) of the cell of box b, or nothing; strip cells are sampled on the thin strip
function sample_cell(b::Box)
    s_ = b.lo[1] + rand()*(b.hi[1]-b.lo[1]); ψ = b.lo[2] + rand()*(b.hi[2]-b.lo[2])
    a = b.lo[3] + rand()*(b.hi[3]-b.lo[3])
    if isstrip(b)
        bs = strip_bs(a, rand() * striptau(b), b.lo[4], b.hi[4]); isempty(bs) && return nothing
        bb = rand(bs)
    else
        bb = b.lo[4] + rand()*(b.hi[4]-b.lo[4])
        (a + bb <= 1 && heronab(a, bb) >= 0) || return nothing
    end
    (s_, ψ, a, bb)
end
function edge_realized(b::Box, t::Box; N=parse(Int, get(ENV, "NSAMP", "4000")))
    got = 0; tries = 0
    while got < N && tries < 50N
        tries += 1
        smp = sample_cell(b); smp === nothing && continue
        (s_, ψ, a, bb) = smp
        got += 1
        z = ((1-s_)*ψ, (1-s_)*(1-ψ), s_*a, s_*bb, s_*(1-a-bb))
        z2, _, _ = nmstep(z)
        λ = z2[3]+z2[4]+z2[5]; T = sum(z2); V = z2[1]+z2[2]
        u = (λ/T, V > 0 ? z2[1]/V : 0.0, z2[3]/λ, z2[4]/λ)
        all(i -> t.lo[i] <= u[i] <= t.hi[i], 1:4) && return true
    end
    false
end
function splitbox(b::Box)
    w = [b.hi[i] - b.lo[i] for i in 1:4]; d = argmax(w); m = (b.lo[d] + b.hi[d]) / 2
    (Box(b.lo, ntuple(i -> i == d ? m : b.hi[i], 4)), Box(ntuple(i -> i == d ? m : b.lo[i], 4), b.hi))
end
function initboxes(N)
    B = Box[]
    for i in 0:N-1, j in 0:N-1, k in 0:N-1, l in 0:N-1
        b = Box((i/N, j/N, k/N, l/N), ((i+1)/N, (j+1)/N, (k+1)/N, (l+1)/N))
        b.lo[3] + b.lo[4] <= 1 && inU(b) && push!(B, b)
    end
    B
end
function prerefine(boxes; tmax=parse(Int, get(ENV, "TMAX", "150")), minw=parse(Float64, get(ENV, "MINW", "0.0078")), passes=parse(Int, get(ENV, "PASSES", "4")))
    for pass in 1:passes
        nodes, root = maketree(boxes)
        cnt = zeros(Int, length(boxes))
        Threads.@threads for i in 1:length(boxes)
            E, isbad = edges(boxes[i])
            if isbad; cnt[i] = typemax(Int); continue; end
            c = 0
            for e in E; out = Int[]; query!(out, nodes, root, e.lo, e.hi); c = max(c, length(out)); end
            cnt[i] = c
        end
        nb = Box[]; nsplit = 0
        for (i, b) in enumerate(boxes)
            w = maximum(b.hi[d] - b.lo[d] for d in 1:4)
            if cnt[i] > tmax && w > minw
                nsplit += 1
                for c in splitbox(b); c.lo[3] + c.lo[4] <= 1 && inU(c) && push!(nb, c); end
            else
                push!(nb, b)
            end
        end
        @printf("prerefine pass %d: split %d -> boxes %d\n", pass, nsplit, length(nb)); flush(stdout)
        boxes = nb
        nsplit == 0 && break
    end
    boxes
end
function loadboxes(f)
    B = Box[]
    for line in eachline(f)
        v = parse.(Float64, split(line))
        push!(B, Box(Tuple(v[1:4]), Tuple(v[5:8])))
    end
    B
end
function saveboxes(f, B)
    open(f * ".tmp", "w") do io
        for b in B; println(io, join(vcat(collect(b.lo), collect(b.hi)), " ")); end
    end
    mv(f * ".tmp", f; force=true)
end
if abspath(PROGRAM_FILE) == @__FILE__
    BOXFILE = get(ENV, "BOXFILE", "tmp/grid13_boxes.txt")
    boxes = isfile(BOXFILE) && get(ENV, "RESUME", "0") == "1" ? loadboxes(BOXFILE) : prerefine(initboxes(NG))
    # optional: split given boxes (e.g. cells on negative cycles of the exact integer graph) before starting
    SPLITFILE = get(ENV, "SPLITFILE", "")
    if SPLITFILE != "" && isfile(SPLITFILE)
        tosplit = Set(Tuple(parse.(Float64, split(l))) for l in eachline(SPLITFILE))
        nb = Box[]
        for b in boxes
            if (b.lo..., b.hi...) in tosplit
                cs = [b]
                for d in 1:4
                    ns = Box[]
                    for c in cs
                        m = (c.lo[d] + c.hi[d])/2
                        push!(ns, Box(c.lo, ntuple(k -> k == d ? m : c.hi[k], 4)))
                        push!(ns, Box(ntuple(k -> k == d ? m : c.lo[k], 4), c.hi))
                    end
                    cs = ns
                end
                for c in cs; c.lo[3] + c.lo[4] <= 1 && inU(c) && push!(nb, c); end
            else push!(nb, b) end
        end
        println("split from SPLITFILE: ", length(boxes), " -> ", length(nb))
        global boxes = nb
    end
    # optional anisotropic pre-split near X*: widths in s and a down to 1/ANIS_S, 1/ANIS_A
    if get(ENV, "ANISO", "0") == "1"
        ws = 1 / parse(Int, get(ENV, "ANIS_S", "512")); wa = 1 / parse(Int, get(ENV, "ANIS_A", "256"))
        inr(b) = b.hi[1] > 0.84 && b.lo[1] < 0.94 && b.hi[2] > 0.25 && b.lo[2] < 0.55 && b.hi[3] > 0.36 && b.lo[3] < 0.45 && b.lo[4] < 0.04
        todo = copy(boxes); nb = Box[]
        while !isempty(todo)
            b = pop!(todo)
            d = !inr(b) ? 0 : (b.hi[1] - b.lo[1] > ws + 1e-15 ? 1 : (b.hi[3] - b.lo[3] > wa + 1e-15 ? 3 : 0))
            if d == 0; push!(nb, b); continue; end
            m = (b.lo[d] + b.hi[d]) / 2
            for c in (Box(b.lo, ntuple(k -> k == d ? m : b.hi[k], 4)), Box(ntuple(k -> k == d ? m : b.lo[k], 4), b.hi))
                c.lo[3] + c.lo[4] <= 1 && inU(c) && push!(todo, c)
            end
        end
        println("aniso split: ", length(boxes), " -> ", length(nb)); flush(stdout)
        global boxes = nb
    end
    PRFILE = get(ENV, "PRFILE", "tmp/grid13_pruned_state.txt")
    if isfile(PRFILE) && get(ENV, "RESUME", "0") == "1"
        for line in eachline(PRFILE)
            v = parse.(Float64, split(line)); push!(PRUNED, (Tuple(v[1:8]), Tuple(v[9:16])))
        end
        println("loaded pruned edges: ", length(PRUNED))
    end
    for rnd in 1:parse(Int, get(ENV, "ROUNDS", "40"))
        t_graph = @elapsed begin; succ, bad = graph(boxes); end
        tb = 0.0; tp = 0.0; nbell = 0
        mark = falses(length(boxes)); conv = false; lq = Float64[]; totpr = 0; ncyc = 0
        FULLDONE = Set{Int}()
        ncut = 0; MAXCUT = parse(Int, get(ENV, "MAXCUT", "1"))
        for inner in 1:parse(Int, get(ENV, "INNER", "25"))
            tb += @elapsed ((lq, conv, pred) = bellman(succ, bad)); nbell += 1
            conv && break
            cyc = negcycles(succ, pred); ncyc = length(cyc)
            isempty(cyc) && break
            open("tmp/g13cyc_last.txt", "w") do io
                for c in cyc
                    println(io, "cycle ", length(c))
                    for k in 1:length(c)
                        i = c[k]; j = c[mod1(k+1, length(c))]
                        w = minimum(Δ for (t, Δ) in succ[i] if t == j)
                        println(io, "  ", boxes[i].lo, " ", boxes[i].hi, "  Δ->next ", w)
                    end
                end
            end
            np = 0
            for c in cyc
                anyp = false
                for k in 1:length(c)
                    i = c[k]; j = c[mod1(k+1, length(c))]
                    key = (bkey(boxes[i]), bkey(boxes[j]))
                    key in PRUNED && continue
                    if !edge_feasible(boxes[i], boxes[j])
                        push!(PRUNED, key); np += 1; anyp = true
                        filter!(e -> e[1] != j, succ[i])
                        if !(i in FULLDONE)
                            tg = unique([e[1] for e in succ[i]])
                            infe = falses(length(tg))
                            Threads.@threads for q in 1:length(tg)
                                infe[q] = !edge_feasible(boxes[i], boxes[tg[q]])
                            end
                            bad_t = Set(tg[infe])
                            for t in bad_t; push!(PRUNED, (bkey(boxes[i]), bkey(boxes[t]))); end
                            filter!(e -> !(e[1] in bad_t), succ[i]); np += length(bad_t)
                            push!(FULLDONE, i)
                        end
                    end
                end
                if !anyp
                    # refine only the sources of edges that sampling cannot realize (likely spurious);
                    # if every edge is realized, refine the whole cycle
                    unreal = [i for (q, i) in enumerate(c) if !edge_realized(boxes[i], boxes[c[mod1(q+1, length(c))]])]
                    for i in (isempty(unreal) ? c : unreal); mark[i] = true; end
                end
            end
            totpr += np
            if np == 0
                # cut the unprunable cycles out and look for further, disjoint ones
                for c in cyc, i in c; mark[i] && empty!(succ[i]); end
                ncut += 1
                ncut >= MAXCUT && break
            end
        end
        @printf("round %d: boxes %d edges %d | conv %s  pruned %d  marked %d  last #cycles %d | graph %.0fs bellman %.0fs (%d) \n", rnd, length(boxes), sum(length, succ), conv, totpr, count(mark), ncyc, t_graph, tb, nbell)
        flush(stdout)
        if conv
            println("lq distribution: ", [count(x -> x < t, lq) for t in (-0.1, -0.5, -1, -2, -3, -5)])
            open("tmp/grid13_cert_boxes.txt", "w") do io
                for (b, l) in zip(boxes, lq); println(io, join(vcat(collect(b.lo), collect(b.hi)), " "), " ", l); end
            end
            open("tmp/grid13_pruned.txt", "w") do io
                for (k1, k2) in PRUNED; println(io, join(k1, " "), " ", join(k2, " ")); end
            end
            break
        end
        nb = Box[]
        for (i, b) in enumerate(boxes)
            if mark[i]
                # split in all four dimensions
                cs = [b]
                for d in 1:4
                    ns = Box[]
                    for c in cs
                        m = (c.lo[d] + c.hi[d])/2
                        push!(ns, Box(c.lo, ntuple(k -> k == d ? m : c.hi[k], 4)))
                        push!(ns, Box(ntuple(k -> k == d ? m : c.lo[k], 4), c.hi))
                    end
                    cs = ns
                end
                for c in cs; c.lo[3] + c.lo[4] <= 1 && inU(c) && push!(nb, c); end
            else push!(nb, b) end
        end
        global boxes = nb
        saveboxes(BOXFILE, boxes)
        open(PRFILE * ".tmp", "w") do io
            for (k1, k2) in PRUNED; println(io, join(k1, " "), " ", join(k2, " ")); end
        end
        mv(PRFILE * ".tmp", PRFILE; force=true)
    end
end
