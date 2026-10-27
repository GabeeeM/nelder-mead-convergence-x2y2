# final_build9.jl — as final_build5 (split9 emission). Assemble the Lean data for NMR3.nm_converges_of_reccert3 from the exact certificate streams
# (old rexport2 trees and rexport3 trees share the RT3 token format): k-d tree over rootBox with hole leaves,
# chunks of ≤ CH leaves checked by `decide +kernel`, composed with walkR3_node.
# usage: julia final_build9.jl OUT.lean stream1.jls stream2.jls ...   (normally called via reproduce.jl)
include("rexport3.jl"); include("remit5.jl"); include("split9.jl")
using Serialization, Printf, Mmap
loadtree(r) = (open(r[1]) do io; seek(io, r[2] - 1); deserialize(IOBuffer(read(io, r[3] - r[2] + 1)))[2]; end)
function hole_certI(b::IBox)
    cons = [conI(b, k) for k in 0:NCON-1]
    for i in 0:NCON-1, j in i+1:NCON-1, k in j+1:NCON-1
        ci, cj, ck = cons[i+1], cons[j+1], cons[k+1]
        yi = cj[1]*ck[2] - cj[2]*ck[1]; yj = ck[1]*ci[2] - ck[2]*ci[1]; yk = ci[1]*cj[2] - ci[2]*cj[1]
        S = yi*ci[3] + yj*cj[3] + yk*ck[3]
        if (yi >= 0 && yj >= 0 && yk >= 0 && S < 0) || (yi <= 0 && yj <= 0 && yk <= 0 && S > 0)
            return i + 8j + 64k
        end
    end
    nothing
end
loI(b::IBox, d) = (b.s0, b.p0, b.a0, b.b0)[d+1]
hiI(b::IBox, d) = (b.s1, b.p1, b.a1, b.b1)[d+1]
function sethiI(b::IBox, d, v); f = [b.s0, b.s1, b.p0, b.p1, b.a0, b.a1, b.b0, b.b1]; f[2d+2] = v; IBox(f...); end
function setloI(b::IBox, d, v); f = [b.s0, b.s1, b.p0, b.p1, b.a0, b.a1, b.b0, b.b1]; f[2d+1] = v; IBox(f...); end
const MISSING = Any[]
mutable struct KNode
    leaf::Bool; box::IBox; cert::Any; d::Int; v::Int; l::Union{KNode,Nothing}; r::Union{KNode,Nothing}; nleaf::Int
end
function buildK(cells::Vector{IBox}, ids::Vector{Int}, region::IBox, certs, edepth = 0)
    if length(ids) == 1 && cells[ids[1]] == region
        c = certs[ids[1]]
        return KNode(true, region, c isa Tuple && c[1] == :hole ? c : (:tree, c), 0, 0, nothing, nothing, 1)
    end
    if isempty(ids)
        hc = hole_certI(region)
        hc !== nothing && return KNode(true, region, (:hole, hc), 0, 0, nothing, nothing, 1)
        if edepth >= 8
            push!(MISSING, (region, 0)); return KNode(true, region, (:hole, 0), 0, 0, nothing, nothing, 1)
        end
    end
    ws = [hiI(region, d) - loI(region, d) for d in 0:3]
    for d in sortperm(ws, rev = true, alg = MergeSort) .- 1
        w = ws[d+1]; w <= 1 && continue
        v = loI(region, d) + w ÷ 2
        any(i -> loI(cells[i], d) < v < hiI(cells[i], d), ids) && continue
        L = filter(i -> hiI(cells[i], d) <= v, ids); R = filter(i -> loI(cells[i], d) >= v, ids)
        ed = isempty(ids) ? edepth + 1 : 0
        l = buildK(cells, L, sethiI(region, d, v), certs, ed); r = buildK(cells, R, setloI(region, d, v), certs, ed)
        return KNode(false, region, nothing, d, v, l, r, l.nleaf + r.nleaf)
    end
    push!(MISSING, (region, length(ids)))                   # reported; the build is invalid if any
    KNode(true, region, (:hole, 0), 0, 0, nothing, nothing, 1)
end
ktok(io, nd::KNode) = nd.leaf ? print(io, " L 0 ", nd.cert[1] == :hole ? "1" : "0") :
    (print(io, " N ", nd.d, " ", nd.v, " 0"); ktok(io, nd.l); ktok(io, nd.r))
function lctok(io, nd::KNode)
    if nd.leaf
        nd.cert[1] == :hole ? print(io, " H ", hx(nd.cert[2])) : tokLC(io, loadtree(nd.cert[2]))
    else; lctok(io, nd.l); lctok(io, nd.r); end
end
const NTREE = IdDict{KNode,Int}()
LIMS[] = parse(Int, get(ENV, "LIM", "300000"))
ntree(nd::KNode) = get!(NTREE, nd) do
    nd.leaf ? (nd.cert[1] == :hole ? 0 : 1) : ntree(nd.l) + ntree(nd.r)
end
isbig(nd::KNode) = nd.leaf && nd.cert[1] == :tree && (s = IOBuffer(); tokRT(s, loadtree(nd.cert[2])); position(s) > LIMS[])
const BIGC = IdDict{KNode,Bool}()
hasbig(nd::KNode) = get!(BIGC, nd) do; nd.leaf ? isbig(nd) : (hasbig(nd.l) || hasbig(nd.r)); end
function emit_all(root::KNode, path; CH = 64, TCH = parse(Int, get(ENV, "TCH", "1")))
    nch = Ref(0)
    open(path, "w") do io
        println(io, "open NMC NMR NMR2 NMR3")
        function go(nd::KNode)
            if nd.leaf && hasbig(nd)
                nch[] += 1; c = nch[]; B = leanBoxI(nd.box)
                tn, th = build_root(io, B, loadtree(nd.cert[2]))
                empty!(SZ)
                println(io, "noncomputable def NMLoadR3.kt$c : KT := KT.leaf 0 false")
                println(io, "noncomputable def NMLoadR3.cs$c : List LC3 := [LC3.tree $tn]")
                println(io, "theorem NMLoadR3.ch$c : walkR3 NMLoadR3.kt$c $B NMLoadR3.cs$c = some [] :=")
                println(io, "  NMR3.walk_one $B 0 $tn (by decide) $th")
                return ("NMLoadR3.kt$c", "NMLoadR3.cs$c", "NMLoadR3.ch$c")
            end
            if nd.nleaf <= CH && ntree(nd) <= TCH && !hasbig(nd)
                nch[] += 1; c = nch[]
                kt = IOBuffer(); ktok(kt, nd); cs = IOBuffer(); lctok(cs, nd)
                println(io, "ktr_def NMLoadR3.kt$c \"", String(take!(kt)), "\"")
                println(io, "lc3s_def NMLoadR3.cs$c \"", String(take!(cs)), "\"")
                println(io, "theorem NMLoadR3.ch$c : walkR3 NMLoadR3.kt$c $(leanBoxI(nd.box)) NMLoadR3.cs$c = some [] :=")
                println(io, "  walkOK_eq _ _ _ (by decide +kernel)")
                return ("NMLoadR3.kt$c", "NMLoadR3.cs$c", "NMLoadR3.ch$c")
            end
            (kl, cl, pl) = go(nd.l); (kr, cr, pr) = go(nd.r)
            ("(KT.node $(nd.d) $(nd.v) 0 $kl $kr)", "($cl ++ $cr)",
             "(walkR3_node $(nd.d) $(nd.v) 0 _ _ $(leanBoxI(nd.box)) _ _ $pl $pr)")
        end
        (k, c, p) = go(root)
        println(io, "\nnoncomputable def NMLoadR3.rootKT : KT := $k")
        println(io, "noncomputable def NMLoadR3.rootCerts : List LC3 := $c")
        println(io, "theorem NMLoadR3.rootOK : walkR3 NMLoadR3.rootKT rootBox NMLoadR3.rootCerts = some [] := $p")
    end
    nch[]
end
ovl(x::IBox, y::IBox) = x.s0 < y.s1 && y.s0 < x.s1 && x.p0 < y.p1 && y.p0 < x.p1 && x.a0 < y.a1 && y.a0 < x.a1 && x.b0 < y.b1 && y.b0 < x.b1
function main()
    out = ARGS[1]; ents = Any[]
    hdr = UInt8[0x37, 0x4a, 0x4c, 0x1e, 0x04, 0x00, 0x00, 0x00]
    for f in ARGS[2:end]
        data = Mmap.mmap(f); n = length(data)
        pos = [i for i in 1:n-7 if data[i] == 0x37 && data[i+1] == 0x4a && view(data, i:i+7) == hdr]
        push!(pos, n + 1); nbad = 0; nok = 0
        for k in 1:length(pos)-1
            seg = view(data, pos[k]:pos[k+1]-1)
            item = try deserialize(IOBuffer(Vector{UInt8}(seg))) catch; nothing end
            if item isa Tuple && length(item) == 2 && item[1] isa IBox && (item[2] === :empty || item[2] isa Tuple)
                push!(ents, (item[1], item[2] === :empty ? :empty : (f, pos[k], pos[k+1] - 1))); nok += 1
            else
                nbad += 1
            end
        end
        println(f, ": ", nok, " items, ", nbad, " unreadable segments"); flush(stdout)
    end
    # later entries win: a restarted cell's complete subdivision replaces partial earlier pieces
    acc = Any[]; ndrop = 0
    for (b, tr) in reverse(ents)
        any(e -> ovl(e[1], b), acc) ? (ndrop += 1) : push!(acc, (b, tr))
    end
    cells = IBox[]; certs = Any[]; nbadhole = 0
    for (b, tr) in acc
        if tr === :empty
            hc = hole_certI(b)
            hc === nothing && (nbadhole += 1; continue)          # left to the region recursion
            push!(cells, b); push!(certs, (:hole, hc))
        else
            push!(cells, b); push!(certs, tr)
        end
    end
    println("empty cells without a 3-constraint certificate: ", nbadhole)
    println("entries ", length(ents), ", dropped (overlap) ", ndrop, ", leaves ", length(cells)); flush(stdout)
    root = buildK(cells, collect(eachindex(cells)), IBox(0, G, 0, G, 0, G, 0, G), certs)
    if !isempty(MISSING)
        println("MISSING regions: ", length(MISSING)); for m in MISSING[1:min(end, 30)]; println("  ", m); end
        open(get(ENV, "MISSF", "tmp/missing.txt"), "w") do f; for m in MISSING; println(f, m[1]); end; end
        get(ENV, "DRY", "0") == "1" || get(ENV, "SKIPMISS", "0") == "1" || error("uncovered regions")
    end
    println("k-d tree leaves ", root.nleaf); flush(stdout)
    get(ENV, "DRY", "0") == "1" && return
    nch = emit_all(root, out)
    println("leaves ", root.nleaf, ", chunks ", nch)
end
main()
