# reproduce.jl — reproduces every number reported in PROOF.md from the exact certificate streams, and rebuilds
# the Lean certificate data that Proof.lean checks.
#
#   julia --project=julia julia/reproduce.jl   # run from the repo root: stream statistics + k-d coverage + Lean data (tmp/data_final9.lean)
#   then: ./assemble.sh tmp/data_final9.lean Proof.lean   and compile Proof.lean (see README.md)
#
# Certificate streams (Julia serialization, (IBox, tree) or (IBox, :empty) records), shipped in certificates.tar.zst
# (release v1.0). They were produced by these search drivers, which are not included in this repository
# (see NOTES.md for the order and the input cell lists):
#   tmp/rex_certs.jls   rexport_run.jl  (old run trees, rexport2 format)
#   tmp/rc5_certs.jls   rcert5.jl       tmp/rc6_certs.jls  rcert6.jl      tmp/rc8_certs.jls  rcert8.jl
#   tmp/rc7, rc9 … rc15 tmp/rcert9.jl … tmp/rcert15.jl (re-certification of the remaining cells)
# Every number below is printed by this script:
#   records per stream, unreadable segments, entries, overlap drops, certified leaves, k-d tree leaves,
#   uncovered regions (must be 0), number of Lean chunks; and the declaration counts of the Lean data.
const STREAMS = ["tmp/rex_certs.jls"; ["tmp/rc$(i)_certs.jls" for i in 5:15]]
const OUTF = get(ENV, "OUT", "tmp/data_final9.lean")
empty!(ARGS); push!(ARGS, OUTF); append!(ARGS, STREAMS)
include("final_build9.jl")          # runs main(): prints the coverage statistics and writes OUTF
let c = Dict{String,Int}(); nh = 0; nt = 0
    for l in eachline(OUTF)
        isempty(l) || l[1] == ' ' || (k = split(l)[1]; c[k] = get(c, k, 0) + 1)
        if startswith(l, "lc3s_def")                  # tokens H (empty cell) / T (recovery tree) occur only at top level
            for t in split(split(l, '"')[2]); t == "H" && (nh += 1); t == "T" && (nt += 1); end
        elseif occursin("NMR3.walk_one", l)
            nt += 1                                    # a big tree split into many theorems
        end
    end
    println("k-d leaves: ", nh, " certified empty, ", nt, " with a recovery tree")
    println("Lean data: ", filesize(OUTF), " bytes; commands by kind: ", sort(collect(c), by = x -> -x[2]))
end
