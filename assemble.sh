#!/bin/bash
# Assemble Proof.lean: Lean sources + batched certificate data + main theorem, in one file.
# usage: ./assemble.sh tmp/data_final9.lean Proof.lean   (data file written by julia/reproduce.jl)
set -e
L=$(dirname "$0")/lean
DATA=$1; OUT=$2
{
  echo "import Mathlib"
  echo
  grep -v "^import " $L/NM.lean
  grep -v "^import " $L/Check.lean
  grep -v "^import " $L/Cert.lean
  for f in Sound RecCert RecCert2 RunGen RunExit RecCert5 LoaderR5 LoaderR6; do grep -v "^import \|^#print" $L/$f.lean; done
  echo
  cat <<'EOT'
/-! ## Certificate data
`batch_begin … batch_end` only groups commands into one top-level command (each is elaborated exactly as if it
stood alone; this saves the frontend's per-command memory) and prints a progress line to stderr. -/
open Lean Elab Command in
elab "batch_begin" cs:command* "batch_end" : command => do
  for c in cs do
    withEnableInfoTree false (elabCommand c)
  IO.eprintln s!"batch done at {(← IO.monoMsNow) / 1000} s"

set_option linter.all false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
EOT
  python3 $L/batchify.py $DATA "$OUT.batched.tmp" 500 all; cat "$OUT.batched.tmp"; rm -f "$OUT.batched.tmp"
  cat $L/MainR3.lean
} > $OUT
