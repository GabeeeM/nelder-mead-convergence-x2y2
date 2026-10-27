# batchify.py IN OUT [N] [mode] — group the commands of an emitted data file into `batch_begin ... batch_end`
# commands of ≤ N commands each (the Lean frontend keeps per-command snapshots, which costs memory per top-level
# command).  mode "all": every command batched, in order.  mode "defs": only non-theorem commands batched, theorems
# stay top-level (Lean then elaborates/kernel-checks them asynchronously, in parallel).  mode "hoist": as "defs", but
# all definitions are emitted first (definitions never refer to theorems, and the relative order of the definitions
# and of the theorems is kept, so every reference still points backwards), then all theorems.
import sys
inp, out = sys.argv[1], sys.argv[2]
N = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
mode = sys.argv[4] if len(sys.argv) > 4 else 'all'
def cmds(f):
    cur = None
    for line in f:
        if not line.strip(): continue
        if line[0] in ' \t': cur += line; continue
        if cur is not None: yield cur
        cur = line
    if cur is not None: yield cur
def emit(g, seq):
    n = 0; opened = False
    for c in seq:
        top = c.startswith('open ') or (mode != 'all' and c.startswith('theorem '))
        if top or n == N:
            if opened: g.write('batch_end\n'); opened = False
            n = 0
        if top: g.write(c); continue
        if not opened: g.write('batch_begin\n'); opened = True
        g.write(c); n += 1
    if opened: g.write('batch_end\n')
with open(out, 'w') as g:
    if mode == 'hoist':
        with open(inp) as f: emit(g, (c for c in cmds(f) if not c.startswith('theorem ')))
        with open(inp) as f: emit(g, (c for c in cmds(f) if c.startswith('theorem ')))
    else:
        with open(inp) as f: emit(g, cmds(f))
