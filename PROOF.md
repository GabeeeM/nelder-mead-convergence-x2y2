# Nelder–Mead converges on f(x, y) = x² + y² (McKinnon's question)

**Status: PROVED and verified in Lean** (`Proof.lean` compiles with the prescribed command, no `sorry`;
`#print axioms NM.mckinnon_x2y2` → `[propext, Classical.choice, Quot.sound]`; 2026-10-27).

## The question

Lagarias, Poonen, Wright, *Convergence of the restricted Nelder–Mead algorithm in two dimensions*,
arXiv:1104.0350 (SIAM J. Optim. 22 (2012)), §4:

> "Consequently, McKinnon's question remains open: does the original Nelder–Mead algorithm, including
> expansion steps, always converge for the function x² + y², or more generally for a class of functions like
> those treated in Theorem 3.17?"

We answer the first part: **yes**. Algorithm NM of Lagarias–Reeds–Wright–Wright (standard coefficients
ρ = 1, χ = 2, γ = ½, σ = ½, with their tie-breaking rules), started from any nondegenerate triangle, produces
triangles whose three vertices all converge to the minimizer (0, 0). NM is affine invariant, so the same
holds for every positive-definite quadratic on ℝ².

## Lean statement

`NM.mckinnon_x2y2 (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :`
`Tendsto (fun k => (traj t0 k).p1) atTop (𝓝 0) ∧ … p2 … ∧ … p3 …`

where `traj t0 k = step^[k] t0` and `step` is one NM iteration exactly as in LRWW (reflection; expansion
accepted iff f(e) < f(r); outside contraction accepted iff f(oc) ≤ f(r); inside contraction accepted iff
f(ic) < f(p3); shrink otherwise; a new vertex is inserted after vertices with equal value).
`NM.mckinnon_x2y2'` gives the same for any nondegenerate triangle (x, y, z), ordered with `sort3`.

## Proof outline

1. **Linear structure.** For f = |x|², f(Σλᵢpᵢ) = Σλᵢfᵢ − Σ_{i<k}λᵢλₖ|pᵢ − pₖ|² (Σλᵢ = 1). In the
   coordinates z = (f₂−f₁, f₃−f₂, D₁₂, D₁₃, D₂₃) (Dᵢₖ = squared side lengths) one NM step is a linear map
   chosen among 9 branches by linear inequalities, and the area changes by exactly α ∈ {2, 1, ½}
   (`step_branch`). Shrinks never occur.
2. **No stalling (Lemma B).** The sorted values decrease to limits a₁ ≤ a₂ ≤ a₃; a₂ = a₃, a₁ = a₂ and
   λ = D₁₂+D₁₃+D₂₃ → 0 (`B1`, `B2`, `lam_to_zero`). If the limit value f* were positive, the triangle would
   eventually be tiny compared with its distance from the minimizer: f₁ ≥ K·λ ("far region"),
   K = 169 869 312.
3. **Potential and recovery.** P = A^{4/5} / max(T, 5λ)^{7/10} (A = twice the area, T = (f₃ − f₁) + λ); equivalently
   P = A^{4/5} λ^{−7/10} min(λ/T, 1/5)^{7/10}. Since A ≤ λ, P ≤ (λ/5⁷)^{1/10} → 0. The key property is
   **recovery**: from every far state, the potential returns to at least its current value after finitely many
   steps (it may first dip — e.g. along chains of outside contractions — but always recovers). Then along
   the times n₀ < n₁ < … with n_{i+1} = n_i + (recovery time of the state at n_i) the potential never
   decreases, contradicting P → 0 (`converge_of_recovery`, `nm_converges_of_recovery`).
4. **Far region geometry.** By the Cayley–Menger identity −CM₅ = 2f₁·heron, a far state with T ≤ (m+1)λ
   satisfies heron·K ≤ (3m²+2m+1)λ² (`far_strip_m`). Used in three tiers: s = λ/T ≥ 1/8 ⇒ 2²⁰·heron ≤ λ²,
   s ≥ 1/64 ⇒ 2¹³·heron ≤ λ², s ≥ 1/512 ⇒ 2⁷·heron ≤ λ² (`StripZ`, `strip_of_far`, `tierDen`). Without the
   lower tiers, cells just below s = 1/8 contain non-collinear (hence non-far) states whose orbits genuinely
   never recover (they converge nearby, P → 0); with them most such cells are empty.
5. **Recovery trees.** Far states are described by u = (s, ψ, a, b) = (λ/T, Δ₂/(Δ₂+Δ₃), D₁₂/λ, D₁₃/λ).
   A k-d tree partitions [0,1]⁴ (grid 4096) into 179 095 cells: 158 483 certified empty (a Farkas
   combination of three cell constraints), 20 612 carrying a recovery tree. For each nonempty cell a *recovery
   tree* follows the possible branch sequences exactly (compositions of the linear branch maps): at each node,
   each of the 9 branches is either impossible in the cell (Farkas certificate) or leads to a subtree; at a
   leaf a Farkas certificate shows rd·σ·max(T_k, 5λ_k) ≤ rn·max(T₀, 5λ₀) on the whole node polytope and
   2^{8n_C} rn⁷ ≤ 2^{8n_E} (rd σ)⁷, which is exactly P(z_k) ≥ P(z₀). Long runs of accepted reflections
   (two coincident-looking vertices "rolling") are handled symbolically: with M the Rx matrix, M² = I + N,
   so 2m Rx steps give z + m·Nz; a maximal run is finite (D₁₃ > 0), and its exit state is a convex
   combination of three linear images of the run start, per κ-piece (κ = (D₂₃ − D₁₂)/D₁₃, 26 pieces) and
   parity — tracked as several "parts" with shared Farkas multipliers (`run_exit`, `piece_tri`).
   **Generic neutral-word runs** (`RC3.grun`, `grun_exit`): a pattern P of branches with area factor 1 whose
   16-scaled composed matrix is checked to be 16^|P|·(I + N), N mapping D into Δ (so N² = 0 and q periods give
   z + qNz). A bound functional F (a Δ coordinate or a signed condition row of the first branch, valid at every
   period start) decreases by ℓ = −F∘N > 0 per period (ℓ > 0 read off the coefficients or by a strict Farkas
   certificate), so the maximal run is finite (`run_finite_gen`). With (a,b) the Δ-part of F and
   κ = (−bN₂ + aN₃)/ℓ in 26 pieces, the state at the last period start lies in a triangle with three
   integer vertex maps (finite pieces via F ≥ 0, infinite pieces via Δ₃ ≥ 0 resp. Δ₂ ≥ 0, else refuted)
   (`piece_triG`); exits at every phase r of the period, with the deviating branch excluded.
   **Exact cycles** (`RC3.gcyc`, `cyc_exit`): if the composed matrix is exactly 16^|P|·I, following P
   forever would make the orbit periodic with constant λ > 0, contradicting λ → 0 (`lam_to_zero`), so the
   run is finite and its exits are the states after each phase.
6. **Verification.** The checker (`chkRT3`, `walkR3`) is a Lean function on natural numbers (signed values as
   Nat pairs); its soundness is proved in Lean (`fcheck_sound`, `chk_sound`, `rec3_sound`, `run_exit`,
   `grun_exit`, `cyc_exit`, `recovery_of_cert3`, `nm_converges_of_reccert3`). The certificate data (1.58 GB of
   text) is turned into terms by meta-level commands (`rc3_def`, `rt3_def`, `lc3s_def`, `ktr_def`; `LoaderR5`) and
   checked by the kernel with `decide +kernel`: 29 955 chunks of the k-d tree (28 664 small chunks checked whole,
   1 291 chunks holding one large recovery tree, which is cut into pieces), 81 996 theorems in total,
   assembled by proved composition lemmas (`node_get`, `sub_of`, `grun_of`, `gl_cons_of`, …, `rt_congr5`,
   `walk_one`, `walkR3_node`). The tracked state at each cut point (parts, row store, scale, step counts) is a
   literal (`sdefP`/`sdefR`/`sdefN`, `LoaderR6`): meta code evaluates it, and the kernel checks the equation
   `n = e` with its defining expression by `Eq.refl` — nothing computed by meta code is trusted (the
   `unsafe`/`implemented_by` helpers in `LoaderR6` only run during elaboration to produce these literals).
   Row stores share the previous store as a tail, with a flat checkpoint every 16 links, so row lookups stay
   cheap in recovery trees up to 1 252 levels deep. `batch_begin … batch_end` only groups commands (500 per
   group) to save frontend memory; each command inside is elaborated exactly as on its own.
## How the certificate was found (not needed for the proof)

Graph-based Lyapunov certificates (cells × Q-bins with a Bellman potential) failed: the abstraction's
transitions compose slivers that no true orbit follows. The recovery-tree certificate avoids the graph
entirely — each cell's tree is exact, and only the leaf inequality is checked. See NOTES.md.

## Reproduce

See the README. In short: `julia --project=julia julia/reproduce.jl` reads the certificate streams
`tmp/*_certs.jls`, prints every number above and writes `tmp/data_final9.lean` (a fresh run regenerated it
byte-identically, 2026-10-27); `./assemble.sh tmp/data_final9.lean Proof.lean` builds the single Lean file;
`lake env lean Proof.lean` checks it. Verification run (2026-10-25 to 2026-10-27, Berlin time): single-threaded, 25.6 h wall time,
peak RSS ≈ 35.7 GB (33.2 GiB), 673 batches, no errors; output ends with
`'NM.mckinnon_x2y2' depends on axioms: [propext, Classical.choice, Quot.sound]` (same for `mckinnon_x2y2'`).
