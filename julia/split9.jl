# split9.jl (from split8: scale/count states s, e, c are literals too (`sdefN`); node proofs use NMR3.node_get with
# children `RT3.child t k`; transport by NMR3.rt_congr5) — keeps theorem statements short
# split8.jl (from split7: run pieces are again separate theorems, so that Lean checks them in parallel)
# split7.jl (from split6: states P/R are literal definitions `sdefP`/`sdefR` (LoaderR6) with kernel-checked
# equations `.eq`; a split node's proof is transported back to the expression states by NMR3.rt_congr)
# split6.jl (from split5: small children / run pieces inlined, proofs by decide inside the parent theorem; big sub
# children inlined as "S XT t" with an inline NMR3.sub_of proof; only P and R states named)
# split5.jl — emit the kernel check of a large recovery tree as many small theorems (LoaderR5 / RecCert5).
# Subtrees larger than LIMS are cut: the node (or run piece list) gets named child definitions (rt3_def / rc3_def with
# XT/XC references), each child its own theorem (decide +kernel, or recursively composed), and the parent is closed by
# the assembly lemmas NMR3.node_of / sub_of / subu_of / grun_of / gl_cons_of / gp_sub_of / gcyc_of / cl_cons_of /
# cp_sub_of / run_of / rl_cons_of / rp_sub_of.  States are named definitions (P: parts, R: rows, s: scale, e/c: counts).
const LIMS = Ref(300_000)
const NCNT = Ref(0)
newname(p) = (NCNT[] += 1; "NMS.$(p)$(NCNT[])")
const SZ = IdDict{Any,Int}()
rtsize(t) = get!(SZ, t) do; s = IOBuffer(); tokRT(s, t); position(s); end
rcsize(c) = get!(SZ, c) do; s = IOBuffer(); tokRC(s, c); position(s); end
plist(P) = "[" * join(string.(P), ", ") * "]"
struct St; P::String; R::String; s::String; mv::String; post::String; e::String; c::String; end
function name_state(io, st::St)
    p = newname("P"); r = newname("R"); s = newname("s"); e = newname("e"); c = newname("c")
    println(io, "sdefP $p := $(st.P)"); println(io, "sdefR $r := $(st.R)")
    println(io, "sdefN $s := $(st.s)"); println(io, "sdefN $e := $(st.e)"); println(io, "sdefN $c := $(st.c)")
    St(p, r, s, st.mv, st.post, e, c)
end
rtstmt(B, tn, st) = "chkRT3 $B $tn $(st.P) $(st.R) $(st.s) $(st.mv) $(st.post) $(st.e) $(st.c) = true"
# define a tree and prove its check; returns (tree name, theorem name)
function build_rt(io, B, t, st::St)
    tn = newname("t"); th = newname("L")
    if t[1] == :leaf || rtsize(t) <= LIMS[]
        s = IOBuffer(); tokRT(s, t); println(io, "rt3_def $tn \"", String(take!(s)), "\"")
        println(io, "theorem $th : $(rtstmt(B, tn, st)) := by decide +kernel")
        return tn, th
    end
    st0 = st
    st = name_state(io, st)
    cs = [child_tp(io, B, t[2][k], k, st) for k in 1:9]
    println(io, "rt3_def $tn \"N", join([" " * c[1] for c in cs]), "\"")
    println(io, "theorem $th : $(rtstmt(B, tn, st)) :=\n  NMR3.node_get $B $tn",
            " $(st.P) $(st.R) $(st.s) $(st.mv) $(st.post) $(st.e) $(st.c) ", join([c[2] for c in cs], " "), " rfl")
    tn, "(NMR3.rt_congr5 $(st.P).eq $(st.R).eq $(st.s).eq $(st.e).eq $(st.c).eq $th)"
end
# child k of a big node: (token string, proof term)
function child_tp(io, B, c, k, st::St)
    if rcsize(c) <= LIMS[] || c[1] in (:inf, :skip)
        s = IOBuffer(); tokRC(s, c); return String(take!(s)), "(by decide +kernel)"
    end
    if c[1] in (:sub, :subu)
        R1 = c[1] == :sub ? "(rsPush $(st.R) (brRowsP $k $(st.P)))" :
             "(rsPush (rsPush $(st.R) (brRowsP $k $(st.P))) (unitRows (List.map (stepW $k) $(st.P))))"
        stc = St("(List.map (stepW $k) $(st.P))", R1, "(16 * $(st.s))", "true", "0", "($(st.e) + eUp $k)", "($(st.c) + eDn $k)")
        tn, tth = build_rt(io, B, c[2], stc)
        lem = c[1] == :sub ? "sub_of" : "subu_of"
        return (c[1] == :sub ? "S" : "V") * " XT $tn", "(NMR3.$lem $B $k $(st.post) $tn $(st.P) $(st.R) $(st.s) $(st.e) $(st.c) $tth)"
    end
    cn, th = build_rc(io, B, c, k, st)
    "XC $cn", th
end
function build_rc(io, B, c, k, st::St)
    cn = newname("x"); th = newname("L")
    stmt = "chkRC3 $B $k $(st.post) $cn $(st.P) $(st.R) $(st.s) $(st.e) $(st.c) = true"
    big = rcsize(c) > LIMS[]
    if !big || c[1] in (:inf, :skip)
        s = IOBuffer(); tokRC(s, c); println(io, "rc3_def $cn \"", String(take!(s)), "\"")
        println(io, "theorem $th : $stmt := by decide +kernel")
        return cn, th
    end
    if c[1] in (:sub, :subu)
        R1 = c[1] == :sub ? "(rsPush $(st.R) (brRowsP $k $(st.P)))" :
             "(rsPush (rsPush $(st.R) (brRowsP $k $(st.P))) (unitRows (List.map (stepW $k) $(st.P))))"
        stc = St("(List.map (stepW $k) $(st.P))", R1, "(16 * $(st.s))", "true", "0", "($(st.e) + eUp $k)", "($(st.c) + eDn $k)")
        tn, tth = build_rt(io, B, c[2], stc)
        println(io, "rc3_def $cn \"", c[1] == :sub ? "S" : "V", " XT $tn\"")
        lem = c[1] == :sub ? "sub_of" : "subu_of"
        println(io, "theorem $th : $stmt :=\n  NMR3.$lem $B $k $(st.post) $tn $(st.P) $(st.R) $(st.s) $(st.e) $(st.c) $tth")
        return cn, th
    end
    R2 = newname("R"); println(io, "noncomputable def $R2 : RS := rsPush $(st.R) (brRowsP $k $(st.P))")
    if c[1] == :grun
        (_, P, fs, ld, ly, lp, pcs) = c; PL = length(P); Pl = plist(P)
        ps = Any[]
        for (j, pc) in enumerate(pcs)
            idx = j - 1; i = idx ÷ PL; r = idx % PL + 1
            push!(ps, build_piece(io, B, :g, (Pl, fs, i, r, PL), pc, St(st.P, R2, st.s, "", "", st.e, st.c)))
        end
        s = IOBuffer(); print(s, "G"); tokNS(s, P); print(s, " ", hx(fs), " ", hx(ld)); tokPY(s, ly); tokC(s, lp)
        print(s, " ", hx(length(pcs))); for p in ps; print(s, " ", p[1]); end
        println(io, "rc3_def $cn \"", String(take!(s)), "\"")
        chain = "(by decide +kernel)"
        for p in reverse(ps); chain = "(NMR3.gl_cons_of _ _ _ _ _ _ _ _ _ _ _ $(p[2]) $chain)"; end
        println(io, "theorem $th : $stmt :=\n  NMR3.grun_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) $chain")
    elseif c[1] == :gcyc
        (_, P, pcs) = c; PL = length(P); Pl = plist(P)
        ps = [build_piece(io, B, :c, (Pl, 0, 0, j, PL), pc, St(st.P, R2, st.s, "", "", st.e, st.c)) for (j, pc) in enumerate(pcs)]
        s = IOBuffer(); print(s, "C"); tokNS(s, P); print(s, " ", hx(length(pcs))); for p in ps; print(s, " ", p[1]); end
        println(io, "rc3_def $cn \"", String(take!(s)), "\"")
        chain = "(by decide +kernel)"
        for p in reverse(ps); chain = "(NMR3.cl_cons_of _ _ _ _ _ _ _ _ _ _ $(p[2]) $chain)"; end
        println(io, "theorem $th : $stmt :=\n  NMR3.gcyc_of _ _ _ _ _ _ _ _ _ _ (by decide +kernel) $chain")
    elseif c[1] == :run
        pcs = c[2]
        ps = [build_piece(io, B, :r, (j - 1,), pc, St(st.P, R2, st.s, "", "", st.e, st.c)) for (j, pc) in enumerate(pcs)]
        s = IOBuffer(); print(s, "U ", hx(length(pcs))); for p in ps; print(s, " ", p[1]); end
        println(io, "rc3_def $cn \"", String(take!(s)), "\"")
        chain = "(by decide +kernel)"
        for p in reverse(ps); chain = "(NMR3.rl_cons_of _ _ _ _ _ _ _ _ _ $(p[2]) $chain)"; end
        println(io, "theorem $th : $stmt :=\n  NMR3.run_of _ _ _ _ _ _ _ _ $chain")
    else
        error("unexpected child $(c[1])")
    end
    cn, th
end
# a run piece (exit child); returns (piece name, theorem name)
function build_piece(io, B, kind, a, pc, st::St)
    pn = newname("x"); th = newname("L")
    if kind == :g
        (Pl, fs, i, r, PL) = a
        stmt = "gPieceOK $B $Pl $fs $i $r $pn $(st.P) $(st.R) $(st.s) $(st.e) $(st.c) = true"
        stc = () -> St("(gExParts $Pl $fs $i $r $(st.P))", "(rsEx $Pl $fs $i $r $(st.P) $(st.R))", "(gSig $Pl $fs $i $r $(st.s))",
                   "true", "(letter $Pl ($r % $PL))", "($(st.e) + upC (List.take $r $Pl))", "($(st.c) + dnC (List.take $r $Pl))")
        lem = (tn, tth) -> "NMR3.gp_sub_of $B $Pl $fs $i $r $tn $(st.P) $(st.R) $(st.s) $(st.e) $(st.c) (by decide +kernel) $tth"
    elseif kind == :c
        (Pl, _, _, r, PL) = a
        stmt = "cPieceOK $B $Pl $r $pn $(st.P) $(st.R) $(st.s) $(st.e) $(st.c) = true"
        stc = () -> St("(cExParts $Pl $r $(st.P))", "(rsC $Pl $r $(st.P) $(st.R))", "($(st.s) * 16 ^ $r)", "true",
                   "(letter $Pl ($r % $PL))", "($(st.e) + upC (List.take $r $Pl))", "($(st.c) + dnC (List.take $r $Pl))")
        lem = (tn, tth) -> "NMR3.cp_sub_of $B $Pl $r $tn $(st.P) $(st.R) $(st.s) $(st.e) $(st.c) $tth"
    else
        (idx,) = a
        wp = "(wpartsOf ($idx / 2) (oddOf $idx) $(st.P))"; wr = "(rsRun ($idx / 2) (oddOf $idx) $(st.P) $(st.R))"
        ws = "(runSig ($idx / 2) (oddOf $idx) $(st.s))"
        stmt = "pieceOK3 $B $pn $wp $wr $ws $(st.e) $(st.c) = true"
        stc = () -> St(wp, wr, ws, "true", "2", st.e, st.c)
        lem = (tn, tth) -> "NMR3.rp_sub_of $B $tn $wp $wr $ws $(st.e) $(st.c) $tth"
    end
    if pc[1] == :sub && rcsize(pc) > LIMS[]
        tn, tth = build_rt(io, B, pc[2], stc())
        println(io, "rc3_def $pn \"S XT $tn\"")
        println(io, "theorem $th : $stmt :=\n  ", lem(tn, tth))
    else
        s = IOBuffer(); tokRC(s, pc); println(io, "rc3_def $pn \"", String(take!(s)), "\"")
        println(io, "theorem $th : $stmt := by decide +kernel")
    end
    "XC $pn", th
end
# a whole big tree of a k-d leaf: returns the root theorem name and the tree name
function build_root(io, B, tr)
    st = St("[W5.id]", "⟨[], 0⟩", "1", "false", "0", "0", "0")
    build_rt(io, B, tr, st)
end
