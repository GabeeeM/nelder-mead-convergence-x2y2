# remit5.jl — emit exact trees as LoaderR5 token streams (pair codes packed base 64, multiplier lists packed)
packc(ns) = sum(BigInt(x) * BigInt(64)^(p - 1) for (p, x) in enumerate(ns); init = BigInt(0))
tokC(io, ns) = print(io, " ", hx(packc(ns)))
function tokPY(io, ys)
    es = BigInt[]
    for (i, y) in ys
        0 <= i < 2^20 || error("row index too large for packing: $i")
        push!(es, BigInt(i) + BigInt(2)^20 * BigInt(y))
    end
    K = isempty(es) ? 1 : maximum(ndigits(e, base = 2) for e in es) + 1
    B = BigInt(2)^K
    c = sum(e * B^(t - 1) for (t, e) in enumerate(es); init = BigInt(0))
    print(io, " ", hx(length(es)), " ", hx(B), " ", hx(c))
end
hx(x) = string(BigInt(x), base = 16)
tokYS(io, ys) = (print(io, " ", hx(length(ys))); for (i, y) in ys; print(io, " ", hx(i), " ", hx(y)); end)
tokNS(io, ns) = (print(io, " ", hx(length(ns))); for x in ns; print(io, " ", hx(x)); end)
function tokRT(io, t)
    if t[1] == :leaf
        (_, den, rn, rd, y1, p1, y2, p2) = t
        print(io, " L ", den ? "1" : "0", " ", hx(rn), " ", hx(rd)); tokPY(io, y1); tokC(io, p1); tokPY(io, y2); tokC(io, p2)
    else
        print(io, " N"); for c in t[2]; tokRC(io, c); end
    end
end
tokRL(io, pcs) = (print(io, " ", hx(length(pcs))); for c in pcs; tokRC(io, c); end)
function tokRC(io, c)
    if c[1] == :inf; print(io, " I"); tokPY(io, c[2]); tokC(io, c[3])
    elseif c[1] == :sub; print(io, " S"); tokRT(io, c[2])
    elseif c[1] == :subu; print(io, " V"); tokRT(io, c[2])
    elseif c[1] == :skip; print(io, " K")
    elseif c[1] == :run; print(io, " U"); tokRL(io, c[2])
    elseif c[1] == :grun; print(io, " G"); tokNS(io, c[2]); print(io, " ", hx(c[3]), " ", hx(c[4])); tokPY(io, c[5]); tokC(io, c[6]); tokRL(io, c[7])
    elseif c[1] == :gcyc; print(io, " C"); tokNS(io, c[2]); tokRL(io, c[3])
    else error("bad child $(c[1])") end
end
tokLC(io, tr) = tr === :empty ? error("empty cell needs a hole certificate") : (print(io, " T"); tokRT(io, tr))
leanBoxI(b) = "(⟨$(b.s0), $(b.s1), $(b.p0), $(b.p1), $(b.a0), $(b.a1), $(b.b0), $(b.b1)⟩ : Box)"
