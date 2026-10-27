# Nelder–Mead converges on x² + y² (McKinnon's question)

A Lean 4 / Mathlib proof that **the original Nelder–Mead method, including expansion steps, converges to the
minimizer of f(x, y) = x² + y² from every nondegenerate starting triangle**. This answers the first part of the
question left open in

> J. C. Lagarias, B. Poonen, M. H. Wright,
> *Convergence of the restricted Nelder–Mead algorithm in two dimensions*,
> SIAM J. Optim. 22 (2012), arXiv:1104.0350, §4:
>
> "Consequently, McKinnon's question remains open: does the original Nelder–Mead algorithm, including
> expansion steps, always converge for the function x² + y², or more generally for a class of functions like
> those treated in Theorem 3.17?"

## The result

`NM.mckinnon_x2y2` (in `lean/MainR3.lean`): for Algorithm NM of Lagarias–Reeds–Wright–Wright (SIAM J. Optim.
9 (1998); coefficients ρ = 1, χ = 2, γ = σ = ½, with their tie-breaking rules), started from any sorted
nondegenerate triangle, all three vertices tend to (0, 0). `NM.mckinnon_x2y2'` states the same for any
nondegenerate triangle, sorted first. The algorithm (`step`, `traj`) is defined at the top of `lean/NM.lean`.

Because Nelder–Mead is affine invariant, the same then holds for every positive-definite quadratic on ℝ²
(this remark is not part of the Lean statement). Earlier results: convergence in 1D and shrinking simplices in
2D (Lagarias–Reeds–Wright–Wright 1998), and convergence of the *restricted* method without expansion steps
(Lagarias–Poonen–Wright 2012).

## The idea

1. For x² + y², one Nelder–Mead step is a linear map on a 5-number description of the triangle (value gaps and
   squared side lengths), chosen from 9 cases by linear inequalities. Shrink steps never happen.
2. If the vertices did not converge to the minimizer, the triangles would eventually be tiny compared with their
   distance from it ("far" states).
3. A shape score P tends to 0, yet from every far state it returns to at least its current value after finitely
   many steps. These are incompatible, so the method converges.
4. Step 3 is checked by computer: the far states are split into 179,095 regions; 158,483 are shown empty, and for
   the other 20,612 an exact tree of all possible step sequences shows the score recovers. Every inequality comes
   with an exact Farkas certificate.

The checker is a Lean function whose soundness is proved in Lean; the Lean kernel runs it on the certificate.
Details: [`PROOF.md`](PROOF.md). The research log is [`NOTES.md`](NOTES.md).

## Checking

The verified file `Proof.lean` (1.58 GB: Lean sources + certificate data) is too large for git. It is attached
to the [v1.0 release](https://github.com/GabeeeM/nelder-mead-convergence-x2y2/releases/tag/v1.0) as `Proof.lean.zst`.

```sh
lake exe cache get
zstd -d --long=27 Proof.lean.zst            # or rebuild it, see below
systemd-run --user --scope -p MemoryMax=40G lake env lean Proof.lean
```

The check is single-threaded and took 25.6 hours with a peak of about 35 GB RAM. The output ends with

```
'NM.mckinnon_x2y2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NM.mckinnon_x2y2'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorry`, `native_decide` or custom axiom. The certificate is checked with `decide +kernel`.
Meta-level loader code (`lean/LoaderR5.lean`, `lean/LoaderR6.lean`) only builds terms: every value it
computes is stored as a literal whose defining equation the kernel checks by `Eq.refl`.

### Rebuilding Proof.lean from the certificates

`certificates.tar.zst` (same release) holds the certificate streams found by the Julia search.

```sh
tar --zstd -xf certificates.tar.zst          # -> tmp/*_certs.jls
julia --project=julia -e 'using Pkg; Pkg.instantiate()'
julia --project=julia julia/reproduce.jl     # prints all counts, writes tmp/data_final9.lean
./assemble.sh tmp/data_final9.lean Proof.lean
```

This rebuilds `Proof.lean` byte-for-byte (`sha256sum -c Proof.lean.sha256`).

## How it was found

The problem, the proof strategy, the Julia search and the Lean proof were all produced by an autonomous
Claude (Opus 5.5) research loop running in Claude Code. The operator did not suggest the problem or the proof. The result was checked by
an independent Claude session (statement fidelity against LRWW 1998, axioms, no `sorry`). No human
mathematician has reviewed it yet; comments are welcome via issues.

## Licence

Apache-2.0 (see `LICENSE`).
