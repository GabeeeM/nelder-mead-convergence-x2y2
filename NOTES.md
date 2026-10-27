> Research log of the session that found the proof, kept as written. It refers to many intermediate
> scripts and files that are not part of this repository; only the final pipeline is included.

# McKinnon's question: does the original Nelder–Mead algorithm converge on f(x,y) = x² + y² ?

## Candidate ranking (by how many people benefit, how directly)

1. **McKinnon's question (Nelder–Mead on x²+y²).** NM is the *default* method of R's `optim`, it is
   MATLAB's `fminsearch`, `scipy.optimize.minimize(method="Nelder-Mead")`, and it ships in NAG, IMSL, Scilab,
   GSL, Numerical Recipes (`amoeba`). Nelder & Mead (1965) has tens of thousands of citations; the method is used
   daily in model fitting across science and engineering. The question is about the actual algorithm those
   libraries run (with expansion steps), on the simplest strictly convex function. By affine invariance of NM,
   x²+y² stands for *every* positive-definite quadratic in 2D. Either answer is directly about the tool people use.
2. **Gauss–Kronrod existence/positivity for Gegenbauer weights.** QUADPACK (scipy `quad`, R `integrate`) only
   needs the Legendre case, which is settled; other weights are niche.
3. **Growth factor of Gaussian elimination with complete/rook pivoting (Edelman–Urschel conjectures).** LAPACK
   users are many, but GEPP (partial pivoting) is what they run and its worst case is known; complete pivoting is rare.
4. **Graillat–Lefèvre–Muller: x^n by repeated multiplication has relative error < (n−1)u.** Proven for all
   practical n (n ≲ 2^{p/2}); open only for n ~ 10^8 in binary64, so direct impact is negligible.
5. **Fair-division existence questions (EFX, EF1+EQ1).** Users are fair-division platforms (Spliddit etc.); small,
   and other sessions already work on them.

Pick: **1**.

## Published statement

J. C. Lagarias, B. Poonen, M. H. Wright, *Convergence of the restricted Nelder–Mead algorithm in two
dimensions*, arXiv:1104.0350 (v1, 3 Apr 2011, the only version; SIAM J. Optim. 22 (2012) 501–532), §4:

> "Consequently, McKinnon's question remains open: does the original Nelder–Mead algorithm, including
> expansion steps, always converge for the function x² + y², or more generally for a class of functions like
> those treated in Theorem 3.17?"

and §1: "As noted by McKinnon [18, page 148], it is not even known whether the NM algorithm converges for the
prototypically nice function f(x, y) = x² + y²."

Status checks (2026-10-12):
- Semantic Scholar citations of arXiv:1104.0350 (60 papers): none resolves it. Galántai, *Convergence of the
  NM method for convex functions* (Acta Polytech. Hung. 21(10), 2024) proves accumulation simplices are collapsed
  points and says the limit need not be the minimizer (McKinnon); nothing on x²+y². Galántai, *The NM simplex
  algorithm is sixty years old: new convergence results and open questions* (Algorithms 17 (2024) 523).
- Newest papers of Lagarias and Poonen on arXiv: unrelated.
- Palomar registry (rev 242): "Nelder-Mead", "Nelder Mead", "McKinnon", "simplex method convergence": nothing.

## Which outcome is more useful

A **proof** (NM always converges on every 2D positive-definite quadratic) is a guarantee users can rely on, and
would be the first convergence theorem for the real NM algorithm in 2D. Work that side first. A counterexample
(a starting triangle from which NM converges to a non-minimizer of x²+y²) would be a strong warning; switch to it
only if evidence points there.

## Algorithm (LRWW 1998 / LPW §2 with expansion, standard coefficients ρ=1, χ=2, γ=1/2, σ=1/2)
Order f1 ≤ f2 ≤ f3; c = (p1+p2)/2; r = 2c − p3.
- f1 ≤ fr < f2: accept r.  fr < f1: e = 3c − 2p3; accept e if fe < fr else r.
- f2 ≤ fr < f3: oc = (c+r)/2, accept if f(oc) ≤ fr else shrink.
- fr ≥ f3: ic = (c+p3)/2, accept if f(ic) < f3 else shrink. (No shrinks for strictly convex f.)

## Log
- Blow-up model: near a non-minimizing limit point p (|p| = R), in coordinates X = x/ε, Y = 2R y/ε² the
  function is (up to constants) X² + Y + κY², κ = ε²/4R² → 0. Limit model g = X² + Y has symmetries
  X-shift+shear, Y-shift, (sX, s²Y): shape space 3-D. (explore_g.jl)
- Random g-orbits: shrink only while the triangle is flat (normalized area Ŝ small), then switch to an
  expanding regime (mostly E) or neutral pure-reflection rolling. Max future shrink C(s) ≈ 0.73·log(1/Ŝ)+O(1).
- No exactly self-similar shrinking word containing E up to length 7 (needs eigenvalues {1, μ, μ²}).
- KEY: for f = |x|², f(Σλᵢpᵢ) = Σλᵢfᵢ − ½Σᵢₖλᵢλₖ Dᵢₖ (Dᵢₖ = |pᵢ−pₖ|², Σλ = 1); new squared side lengths are also
  linear in (f, D). So NM on |x|² is a piecewise-LINEAR map on z = (f₁,f₂,f₃,D₁₂,D₁₃,D₂₃) with LINEAR decisions.
  The g-model is the same PL map on the boundary where D is collinear (A_D = 0).
  Conserved: with w = z − f*(1,1,1,0,0,0), f* = N(w)/(c·A_D(w)²) (planar Cayley–Menger), N cubic.
  On the boundary, normalized g-area² Ŝ² ∝ N/λ³.
- Collinear sub-world (Ŝ = 0, 1-D NM on a parabola): chaotic, shrink 0.418/step, area factor e^{-0.538}/step,
  Ŝ grows like e^{1.71·shrink} (average) → transversally repelling.
- POTENTIAL (2026-10-12): P = A / T^κ · q(shape), A = area, T = (f3−f1) + (D12+D13+D23), κ ∈ (0.81,1) (κ=7/8 ⇔ γ=0.8).
  Per step: Δlog(A/T^κ) = log α − κ log(T'/T), α ∈ {1,2,½}. Exact facts (linear algebra):
  R (accepted, f1≤fr<f2): T' ≤ T.  E: T' ≤ 2T < 2^{1/κ}T.  Rx (fr<f1≤..., fe≥fr): T' = T − K, K = D13+D23−D12;
  Rx needs s := λ/T ≥ 1/5;  contraction needs s > 1/2.  So only Rx/O/I in s ≥ 1/5 can lose; q fixes these.
  Contradiction: if P nondecreasing and q ≤ 1: A/T^κ ≥ c, A ≤ T/(4√3) ⇒ T^{1−κ} ≥ c' ⇒ T bounded below,
  contradicting T → 0 (values converge to f*, diam → 0).
- Lemma B for |x|² (no compactness): values ↓ a1≤a2≤a3; a2=a3 (else only position-3 contractions, p3→c, f(c)<a2);
  a1=a2 (else p1 fixed, I impossible, pure-R has period 6, each O lowers λ by ≥ ¾(a2−a1));
  with values in [f*,f*+ε]: E/O/I give λ_after ≤ 40ε, R/Rx keep λ, pure R/Rx forever impossible (K must be 0 at worst
  vertex, then the right angle sits at the new non-worst vertex) ⇒ λ→0, F=f1/λ→∞, T→0.
- Certificate search (grid3.jl): cells = box in (s,ψ,a,b) × bin of F=f1/λ; F' ∈ [F(1−2/√F−3/F)λ/λ', Fλ/λ'].
- Lean (Scratch/nelder_mead_x2y2/NM.lean): definitions, step cases, area factor, sortedness, Lemma B1, B2,
  λ→0 (lam_to_zero) all verified (no sorry).
- Certificate search: cells (s,ψ,a,b)-box × F-bin with validity-aware polygon bounds still cycles in the
  "O-chain" region (b≈0, a≈0.4, s≈0.85): near-fixed point of projective O-map, Ŝ² = N/λ³ drifts ×0.70/step.
  Plan: add Ŝ-bins (exact update Ŝ²' = α²(λ/λ')³(f1'/f1)Ŝ²) as a clock.
- 2026-10-12 later: rolling (pure R/Rx) cycles are EXACTLY neutral for A/T^κ ⇒ interval over-approximation
  creates unremovable negative cycles. New potential P = A^γ λ^{(1-3γ)/2} min(s,1/5)^δ q (γ=4/5, δ=7/10):
  R/Rx exactly neutral for s,s' ≥ 1/5; equals (A/T^κ)^γ for s < 1/5 (tall lemmas kept). Debt ≤ 2.2 (BigFloat sims).
  Lean: GoodPotential/converge_of_potential rewritten for P^10 = A^8 q^10 min(λ/T,1/5)^7/λ^7 ≤ λ/5^7 (compiles).
- Domain: far states are tall (s<1/8, any shape) or in the thin strip η=heron/λ² ≤ τ (η ≤ c/F when s ≥ 1/8).
- Clock: Q = N/λ³ = 8 f1 A²/λ³ (N = −CM5 = 2 f1·heron, heron = 4 area2², checked symbolically);
  Q' = α²(λ/λ')³(f1'/f1) Q, f1'/f1 ∈ [1−2/√K−3/K, 1].  grid7.jl = (box, Q-bin) cells.
- Certificate search status: grid10/grid11 (no Q-bins; potential with exact-neutral reflections; prerefine by target
  count; cycle refinement; LP pruning of infeasible cycle edges via convex hull of corner images + branch constraints).
- Planned Lean checker: kd-tree leaves (s,ψ,a,b) with kind tall/strip, H-polygon (global tangent cuts + inner cut),
  q ∈ (0,1]; every bound is c·z ≥ 0 checked as (1−s)L(ψ)+sΛ(D̂) with a Farkas certificate for Λ over the polygon;
  pruned edges carry Farkas certificates; arithmetic in Nat (kernel ~1e5 ops/s).
- Kernel speed: Nat ~1e5 ops/s, Int ~2e4, Rat ~3e3 ⇒ checker in Nat (signed functionals as pos/neg parts).
- Checker design: membership = linear inequalities in z (no division); each bound c·z ≥ 0 via
  c1Δ2+c2Δ3 ≥ Lmin(Δ2+Δ3) (ψ-interval), Λ ≥ mλ (Farkas from the 2 active polygon constraints at the min vertex),
  then endpoint check in s. Enclosures/U recomputed as corner extremes then verified. Pruned edges: Farkas w.
- Rigorous polygons (polys.jl): rect ∩ global tangent cuts (exact rational validity check) ∩ inner cut for strip
  (Handelman degree-2 certificate heron − τ ≥ ε on rect∩{n0·x ≤ c0}).
- 2026-10-12 evening: data-free cell polygons (tangent plane at box centre = outer cut; Hessian-bound inner cut for
  strip) — Lean lemmas heron_expand/outer_cut/Bq_le_corners/inner_cut proved (Check.lean). grid13.jl search with
  these polygons + LP pruning + 16-way splitting of stuck cycles. The O-chain region (a≈0.41,b≈0.014,s≈0.88)
  converges to a point X* on the collinear surface lying on the O/I decision boundary; chains are ≤ 8 steps
  (local search cannot lengthen them; they end at Q ≥ 3e-4), so debt is bounded there.
- exact_check.jl: exact rational re-verification mirroring the planned Lean checker; q = 2^(-n/320),
  per (leaf,branch) w = floor(log2(F10^32)), integer Bellman n_L ≥ n_t − w.

## 2026-10-12 (later): reflective Lean checker + full soundness proof
- Kernel speed: `decide +kernel` runs theorems serially (no -j speedup). Int ops ~1.6e4/s, Nat ops ~2e5/s
  → signed numbers as Nat pairs (`NMC.Z`), all data dyadic/integer (G = 4096 box grid, E = 2^24 enclosure grid,
  τ = 1/256 strip width, K = 41472 = 162·256).
- Lean files (Scratch/nelder_mead_x2y2): NM.lean (dynamics, Lemma B, potential ⇒ convergence), Check.lean (tangent cuts),
  Cert.lean (computational checker + `fcheck_sound`), Sound.lean (soundness: tree lookup/walk/query, enclosures,
  prune and hole certificates, w-factor, `step_ineq`, `goodPotential_of_cert`, `nm_converges_of_cert`).
  `#print axioms NMS.nm_converges_of_cert` = [propext, Classical.choice, Quot.sound].
- Remaining hypotheses of nm_converges_of_cert: `mxOK tree = true` and `AllOK tree tree rootBox`, to be discharged by
  `decide +kernel` on the exported data (chunked into subtrees, composed with `allOK_node`).
- export.jl mirrors the Lean checker in BigInt; Farkas pairs from the polygon's active constraints (fallback search);
  holes (empty dyadic boxes) certified by 3-constraint Farkas.
- grid13: still 1 negative cycle per round (long cycles through near-collinear O/R chains, sums slightly < 0);
  added MAXCUT (cut a found cycle out of the graph, look for more in the same round).

## 2026-10-13 early: certificate search stalls; diagnosis
- grid13 (box refinement, pruning, targeted splits, aniso split near X*): >150k boxes, still 1 negative cycle/round,
  cycle sums not shrinking (−1.6 … −6.9).
- True dynamics near X* ≈ (s,ψ,a,b) = (0.885,0.40,0.41,0.01): O-run length k needs Q = N/λ³ ≳ 2.6e-4·(1/0.7)^k
  (run 1: Q ≥ 2.7e-4, run 7: Q ≥ 5.9e-3), Q shrinks ×0.7 per O step; worst true cumulative drop −2.53 (bounded).
  Also correlated with the linear margin fr3/λ. Debt ≈ log Q: cells must resolve Q ~ 1e-4 near the collinear surface.
- Q-targeted box refinement explodes (>30M boxes). Any A^γ λ^β potential (γ+β>0) loses on O steps near X*, so debt
  is intrinsic.
- Q-bin prototype (qgraph.jl, 60 log bins, exact Q' = α²(λ/λ')³(f1'/f1)Q): diverges. Cycle: coarse a≈0 cells give
  huge Q' ranges (artifact), and Δ=0 rolling steps lower Q legitimately (f1 decreases, λ fixed) — Q-bins must be
  combined with refinement; Lean would additionally need certified lower bounds of the cubic Q per cell.
- grid14 (Q-bins, bulk LP pruning): ~1.9M→0.2M prunes/round then plateau ~200–370k/round, cycles stay at cap.
  Cycle diagnosis (tmp/cyc14.jl): most transitions unrealized by sampled true states; several (box,bin) states on
  cycles are EMPTY (sampled Q-range padding ×0.8/×1.25 too loose) → tightened to m=8 sampling, ×0.97/×1.03.
- Structural remark: q·P with q = (Q_lo/clamp(Q,Q_lo,Q_hi))^κ equals min/max combinations of P1 = A^0.8 λ^-0.7 m^0.7
  and P2 = P1·Q^-κ ∝ A^{0.8-2κ} λ^{3κ-0.7} f1^{-κ} m^0.7 (f1^{-κ} nondecreasing, bounded under the contradiction
  hypothesis). κ ≥ 0.9 makes O steps near X* neutral for P2. Any route needs certified per-cell bounds on the
  cubic Q (O chains end because O requires Q ≳ 2.6e-4 near X*).

## 2026-10-14 evening: step back
- Exact rewrite: P = A^0.8 λ^-0.7 m^0.7 q = C f1^-0.4 · Q^0.4 · λ^0.5 · m^0.7 · q (Q = N/λ³ = 8 f1 A²/λ³).
  So the certificate ⇔ a shape function W bounded above with log λ + W nondecreasing in the far region
  (max future shrink of λ controlled by flatness). No direct proof of these rates is known to me.
- ROOT CAUSE of the X* plateau: strip cells allow heron/λ² ∈ [0, τ]; at fixed (s,ψ,a), Q ≈ Q0 + 0.15·heron/λ²,
  i.e. a smear of ~7.5e-4 for τ = 0.005 — the size of the O-chain thresholds 2.6e-4·1.43^k. Unresolvable by boxes.
  Fix: τ = 2^-20 (K = 162·2^20; K is free since f1/λ → ∞). Prunes/tightenings stay valid (thinner set).
  Samplers rewritten to sample on the strip (heron = 0 and heron = τ curves). Test round: states 1.37M → 1.0M,
  Bellman pass 1.0 s → 0.22 s. Lean impact: one constant (con 6 uses 4G²τ = 64) and K.
- grid15: box-level edges with bin shift (no per-bin replication): memory 40+ GB → 15 GB.
- Lean status vs Q-bin search: per-box Q ranges are sampled (need certified cubic bounds), Q-bin semantics,
  monotone-q, tightened transitions (Farkas certificates) and hashed caches are NOT yet covered by the Lean checker.
- Lean constants switched to τ = 2^-20 (con 6: 4G²τ = 64; strip condition 1048576·heron ≤ λ²; K = 169869312);
  Sound.lean recompiles (backups *_tau256.lean.bak).
- Lean-side cost warning for the Q-bin route: the search has ~55M cached edge tightenings (of ~80M box edges).
  Verifying each in the kernel is infeasible. Plan once converged: with final n, keep the cheap untightened
  per-(leaf,branch) λ'/λ bound and supply tightening certificates (Farkas-type, like prune certificates) only for
  edges that VIOLATE n_t ≤ n_L + w under the untightened bin; also need certified per-cell Q bounds (or all bins
  with monotone n) — measure both counts at convergence before committing to the Lean design.
- Thin-strip run (grid15, τ = 2^-20): ~8 min/round, still ~480 cycles/round (cap). Diagnostic tmp/cyc15.jl (samples
  on the thin strip): only 8/32 cycle transitions realized; some (box,bin) states empty. Remaining leak: box→box LP
  pruning ignores the Q bin (a transition (i,j)→(t,jt) survives if ANY state of box i reaches box t); Q enters only
  via λ'/λ tightening. Candidate fix: bin-aware pruning with a linearized constraint N(z) − Q_lo λ³ ≥ −R over the cell
  (affine in z, hence linear in corner weights), R a remainder bound (rigorous R needed for Lean).
- Bin-aware pruning (2026-10-15): per-edge source-bin ranges; on-demand version plateaued (~5k edges/round).
  Sample of 300 boxes: a BULK pass shrinks 95% of edge ranges, empties 72% of edges, keeps 21% of (edge,bin)
  transitions — most bin-level transitions were spurious. Optimized bin_range (full-range test first, per-box
  linearization with remainders R_N, R_L): agrees with per-bin version on 63664/63788 edges (124 looser, 0 tighter),
  1.8× faster; full pass ≈ 1 h on 7 threads, done once in build (cached in BRG, persisted tmp/g14_br_h.bin).
- Bulk bin pass done (34M ranges, 53 min once threads balanced with :greedy / strided static); Bellman 0.08 s/pass,
  rounds 4–10 min. Remaining cycles (~450–510/round) now broken mostly by SPLITTING (670–955 boxes/round, 16-way →
  +6–9k boxes/round, 420k→493k in 10 rounds). Switched to TARGETED splits: per refuting edge i→t choose a dimension
  whose midpoint split makes i→t box-infeasible for one half (else widest), split only along chosen dimensions.
- Progress metric (cold Bellman, 300 sweeps): ~1.36M of 1.38M states < −20, min ≈ −140 → graph pervasively
  negative; ~500 cycles/round fixes cannot converge at this rate. Worst cycle (tmp/worstcyc.log): O4 chain near X*
  descending 10 bins (−0.31…−0.32 each, ≈ −3.2), credit regained by I5/I7 steps out of coarse a≈0 cells jumping +7
  bins (Q' overestimated from wide λ'/λ), connected by free monotonicity edges and Δ=0 Rx rolling.
- Candidate reformulation (no bins): W(Q) = min(0.8 log Q, 0.8 log Qc − β log(Q/Qc)) (concave in log Q, bounded
  above), i.e. P = q(cell)·min(P1, c·P2) with P2 = P1·(Qc/Q)^{(β+0.8)/2} ∝ A^{0.8−(β+0.8)} λ^{...} f1^{...}.
  Within a regime the per-step change is exact from λ'/λ (no quantization). Step condition per edge:
  q'P1' ≥ q·min(P1,cP2) via Δ1 or (cross) via Q ≥ 1.44 Qc for O steps (β≈0.95) — with Qc ≈ 1.8e-4 this is exactly
  the O-threshold 2.6e-4. Needs certified Q bounds ONLY where cross terms are used (near X*), not 60 bins everywhere.

## 2026-10-15: true-orbit debt, worst-cycle realizability, bin rounding
- True far orbits (tmp/drawdown.jl, tmp/recov.jl; exact z-dynamics from strip starts, ε = 1e-6, 2000–6000 orbits):
  worst drawdown of cumulative ΔlogP −2.57; recovery time (first k with S_k ≥ S_0): 90% k=1, 99% ≤ 5, 99.9% ≤ 7,
  max 443 (one orbit). Long recoveries all follow the pattern "O O (O) I I O I, Rx-rolling (neutral), R Rx I E E";
  Q after "I I O I" ≈ 0.1. So the potential is sound on true orbits; the search graph's negativity is abstraction leakage.
- Worst cycle of the current graph (tmp/worstcyc.log, 57 states, −2.68): O4 chain near X* (bins 30→20, realized),
  then I5, I5, O6, I7 back up 15 bins (realized only by tiny slivers: 5/20000, 2/10000 samples), Rx-rolling with free
  monotone bin drops, and I5 I5 O6 I7 into X* at bin 30 — those three edges have 0 hits on the thin strip.
  Off-strip (convex-hull) sampling: hits exist, mostly with heron/λ² < 0 (impossible states, −1e-5…−2e-4) but some on
  the strip. Splitting the source 16× in (a,b) never kills any of these edges (≥ 1 piece stays feasible), so they are
  boundary contacts, not polygon fatness.
- Added target strip cuts (outer/inner cut of the target polygon) to every edge LP (fastlp.tgtG; sound: successors of
  far states are far, hence satisfy the cuts — Lean prune certificates must then be allowed to use them). No effect on
  the worst-cycle edges.
- Q-bin rounding: target bin = bin of binhi(j)·e^{l1}, i.e. up to one bin (×1.4, 0.336 in log Q) pessimism per step.
  Where q depends on Q (X*: ~0.31 per bin) this costs up to ~0.3 per I-step, the size of the true I-step gain
  (+0.3…+0.4) that repays the O-chain debt. ⇒ restart with RB = 1.1 (≤ 0.09 per step), fresh bin ranges
  (tmp/g14_br_h_rb11.bin); bin_range now by binary search (2 log2(#bins) LPs instead of a linear scan).
- Structure (for a possible redesign): the far limit is NM on h(u,v) = u + v² (affine image of |x|² near a far point,
  scaled (u,v) → (c²u, cv)); its symmetry group (u-shift, v-translation with shear, scaling) leaves a 3-d shape space.
  On the strip, Q is a function of the leading-order z. A periodic orbit of the limit with Q ≠ 0 would need
  |ℓ2| = ℓ1² for the position map of the branch word (non-generic), so limit periodic orbits sit in Q = 0
  (h-collinear), where the O-chain fixed point X* lies on the O/I switching boundary.
- Per-target tightening of Δ (max λ'/λ over cell∩branch∩target) on the worst-cycle edges: gains ≤ 0.014 per edge — not worth it.
- Lean TODO (if target cuts are used in final prunes): pruneOK must accept extra Farkas weights on the target polygon rows (con tb 4..6 applied to A1, B1, L1); sound by far_strip + outer_cut/inner_cut on the successor.
- RB = 1.1 (209 bins, 3.88M states) round 1: cold-Bellman min −144.8, 3.74M states < −20 — no improvement over RB = 1.4.
  Bin rounding is NOT the main leak. (Bin pass made 3.2× faster: type-unstable Tuple(::Vector) of branch conditions
  replaced by typed BCOND; base LP rows built once per edge; binary search.)
- KEY FINDING (tmp/macro_test.jl): every 2-step window of the worst cycle is infeasible under exact composition
  (LP on the composed conditions; confirmed by sampling 300k true strip states per window: 0 follow both steps), incl.
  the O-chain pairs. The negative cycles are chains of individually realizable steps that never compose.
- grid16 = grid15 + DEEPENING (deep.jl): a cell of depth L uses edges = LP-feasible words of L branch steps (exact
  composed map, conditions of all steps as functionals of z_0), word-level enclosure (bisection LPs), Δ_w from the
  composed λ_L/λ_0 and s_L, Q shift l1 = log(α_w²/min(λ_L/λ_0)³), per-target LP prune and bin range. Refinement order
  per cycle: bin shrink, Q-tightening, box-pair prune, then DEEPEN the source of an infeasible 2-word window (depth+1,
  max 4), else split. Monotone: old constraints imply the new ones. Soundness: potential checked at macro-step ends
  (stopping times), P(x_{n_k}) nondecreasing still gives the contradiction. Lean: per deep cell a word tree with Farkas
  certificates for infeasible prefixes — cost grows only with the number of deep cells.
- grid16 first 6 rounds: ~3.3–4.4k deepenings/round, cycles/round 494–792 (not yet decreasing), 13.4k deep cells,
  54–119 degenerate words → those cells stay at depth 1 (fallback added: a word with λ'/T'/λ ≤ 0 at a corner has no
  enclosure; dropping it silently would delete real transitions). Cold-Bellman metric magnitude is not comparable
  any more (word edges carry multi-step Δ). Boxes with some negative single-step branch: 181,942 of 529,388
  (O4 112k, I5 67k, O6 12k, E1 11k, I7 8k, O8 2k, I9 1k) — upper bound on where deepening can be needed.
- Lean cost warning for the final certificate: kernel ~2e5 Nat ops/s; certifying every one of ~34M box edges with
  a Farkas check is ~2 days. Plan: check q(i,j) ≤ Δ + q(t,·) first with cheap enclosure bounds and supply prune /
  tightening / bin-range certificates only for violating edges; Q upper bound per cell by interval evaluation of
  Q = N(rψ, r(1−ψ), a, b, 1−a−b), r = (1−s)/s (only the upper end b1 matters with q clamped outside [b0,b1]).

## 2026-10-15 afternoon: self-similar collapse impossible for short words; deepening status
- Self-similar collapse criterion. In the far limit NM on |x|² is NM on h(u,v) = u + v² (affine invariance). An affine
  g with h∘g = κh + const has linear part [[E², B], [0, E]] (κ = E²). So an orbit that is periodic up to h-symmetries
  (exact self-similar collapse at a non-minimizer, Q ≠ 0) needs a branch word w whose edge map A_w (2×2, on
  (v2−v1, v3−v1)) has eigenvalues (x, x²), 0 < |x| < 1. det A_w = ±2^k, so x = ±2^(k/3) with 3 | k, and
  trace = x + x² (exact dyadic arithmetic). In z-terms: such a word plus strict branch conditions at the eigenvector z*
  of M_w (eigenvalue x²) with N(z*) > 0 would give an explicit counterexample (z0 = z* + ε·e_{x⁴}, all z with heron > 0
  are realizable; f1 = N/(2 heron) → const > 0). Exhaustive search over ALL 9^n words, n ≤ 10 (tmp/periodic3.jl,
  3.9e9 words): NO word satisfies the eigenvalue condition. (Consistency of the per-branch edge maps with the BMATS
  D-blocks checked.) Evidence for convergence; does not exclude aperiodic collapse.
- grid16 after 10+ rounds: cycles/round flat (~600), 23k deep cells; depth histogram {2: 15k, 3: 5k, 4 (cap): 5k};
  one depth-4 cell has 162k word edges (4-step images spread widely — chaotic expansion). Deepening is not converging
  either: cycles route through the deep cells' macro-step boundaries.
- DECISIVE: graph of SAMPLED TRUE transitions on the current 529k cells × Q-bins (tmp/sampgraph.jl, 40 strip
  samples/box, 16.7M samples, 7.8M edges, exact Δ and exact target bins): NO negative cycle, Bellman converges in 26
  sweeps, min lq −3.26 (true worst debt ≈ 2.6). So piecewise-constant q on these cells is adequate; the search graph's
  negativity comes entirely from over-approximated edges (LP-feasible transitions realized only on slivers / not at all).
- MONOTONICITY IS A LEAK: adding the certificate's "q nonincreasing in Q" edges (box, j) → (box, j−1) to the sampled
  true-transition graph (40/box) creates negative cycles (−2.58 over 185 steps; drift to −40). Without them the same
  graph is acyclic. Low Q is not uniformly better (near-collinear states shrink). Monotonicity was only needed because
  edges used an upper bound on Q'; but f1'/f1 ≥ 1 − 2/√K − 3/K (≈ 1 − 1.5e-4 for K = 1.7e8) gives a lower bound too:
  Q' ∈ [(1−ε) α² (λ/λ')³_min Q, α² (λ/λ')³_max Q]. ⇒ edges map a source bin to a target-bin RANGE,
  q(i,j) ≤ Δ + min over the range; no monotonicity. (Also: with 200 samples/box and no monotonicity a mild negative
  cycle (−0.19, length 43) appears — modest refinement will still be needed.)
- LP-edge violations w.r.t. the sampled true-transition q (40/box, no monotonicity, converged, min −3.26):
  monotone semantics 38M of 139M state-edges (372k boxes, max 38.6 — q distorted by the mono leak);
  RANGE semantics 19.2M (128.7k boxes, max 2.9). ⇒ grid17 (range semantics, EPSF = 2e-4, no monotonicity edges).
- grid17 (range semantics, no deepening) rounds 1–2: min lq −106, 465–471 cycles/round: range semantics alone does not
  fix the LP graph.
- Within-cell spread of the sampled value v(x) = min(0, Δ(x) + q0(target)) over 1.41M states: median 0, 90% 0.32,
  99% 1.79, 99.9% 2.85; spread > 0.3 in 161k states, > 1.0 in 36k. Piecewise-constant q needs much finer cells where
  V jumps (V = drawdown function, discontinuous where the future branch pattern changes).
- Large-spread cells (> 0.3): 95.5k boxes = 2.85% of the (s,ψ,a,b) volume, concentrated at s > 0.75, a ∈ [0.375,0.625]
  (X* zone a≈0.41 b≈0.01, rolling zone a≈0.5 b≈0) — next to degenerate boundaries (b → 0: two vertices merge).
- Explicit factor e^{g(Q)}, g = −κ log(1+Q/Qc): best worst drawdown −1.78 (κ 0.1, Qc 1e-3) vs −1.90 base: no help.
- grid17 stopped after 2 rounds. Next: sampling-based refinement by spread (tmp/sref.jl) to measure the partition size
  at which piecewise-constant q fits the true transitions.
- Spread-driven refinement (tmp/sref.jl, θ = 0.1): boxes 530k → 564k → 624k, boxes with spread > 0.1 rise
  116k → 143k → 161k, 99% spread flat at 2.24. Not converging: V (drawdown) depends on the next ~10–20 steps of a chaotic
  map, so its discontinuities are dense. Spread is the wrong target: validity only needs the edge constraints, and
  the sampled graph on the ORIGINAL cells already has a valid piecewise-constant q. The LP graph fails because of its
  extra edges (transitions realized on tiny sets or not at all).
- Realizability of LP edges violating the sampled q0 (tmp/edgecheck.jl, 2000 random violating state-edges, 200k strip
  samples per source box, ~4.9k in the source bin): 789 realized (thin slivers, measure ~1e-4..1e-3), 1211 never hit.
  Both kinds matter; the realized-edge (closure) graph itself is not acyclic at this resolution (cf. 200/box: −0.19).
- Sampled-graph CEGAR (tmp/sref.jl MODE=cegar, 200 samples/box): 1–2 negative cycles per iteration, magnitudes
  −0.24, −0.17, −0.21, −0.03, −0.04; after 5 iterations 530.0k boxes (+212). The TRUE transition relation at this
  density needs only light refinement. Next: 1000/box. Plan (grid18): truth-anchored refinement — CEGAR on sampled
  graph → q0; LP edges violating q0 ranked by violation; exact pruning/tightening, else split the source; final
  certificate = converged Bellman on the LP graph.
- Sampled CEGAR at 1000/box (deduped CSR + parallel Bellman: 13 min/iteration instead of 53): cycles per iteration
  7, 8, 9, 7, 11, 11, 8 (means −0.18…−0.43), ~1000 splits/iteration, boxes 531k → 537k. Not yet decreasing.
- grid18.jl: truth-anchored refinement of the LP graph (sampled q0 + violating LP edges → exact prune / tighten,
  else split the source towards the target; LP-graph Bellman every CHECK rounds).
- grid18 rounds 1–2: LP violations 7.00M → 7.14M box edges while boxes 537k → 697k (334k more splits queued):
  refinement does not reduce LP violations. Stopped.
- NEW DIRECTION (local certificate, no graph): potential factor e^{W} with W depending only on rolling invariants:
  log Q (R/Rx: Q' = Q·f1'/f1, the drift is cancelled by a free factor f1^{-κ}, κ ≥ |∂W/∂log Q|, bounded since
  f1 ≥ f* > 0) and the side-length shape symmetrized over vertex relabelings (R/Rx permute the D's). Then R/Rx are
  exactly neutral and the certificate is a per-cell, per-branch inequality Δ + W(x') − W(x) ≥ 0 — no target leakage.
  Test: LP fit of piecewise-linear W(log Q, σ1, σ2) on sampled true transitions (tmp/wfit.jl).
- Local-W test (tmp/wfit.jl, 100k sampled true transitions, W piecewise multilinear on a 24×12×12 grid in
  (log Q, σ1, σ2)): best minimum slack over non-rolling steps t = −0.303 (LP optimal). A worst slack of one O-step
  means true transition chains return to the same (log Q, shape) features with negative sum, so no W(log Q, shape)
  can make every step nonnegative. Finer-grid / value-feature variants were too slow in HiGHS IPM (> 2 h); stopped.
- Finite-lookahead potential W_L(x) = min(0, min_{j≤L} S_j(x)) (P e^{W_L} nondecreasing at x iff S_{L+1} ≥
  min(0, min_{j≤L} S_j)): violating fraction of strip states (tmp/lookahead.jl, 192k states): L=3 12%, 5 4.1%,
  8 0.22%, 10 0.041%, 12 0.041%, 15 0.085%, 20 0.32%, 30 1.4%, 40 2.8% — minimum at L ≈ 10–12, then late new debts
  after neutral stretches dominate. No single L works.
- LP-feasible words per cell are FEW (tmp/wordcount.jl, 11 random cells): depth 2/4/6/8 → 1–2 / 1–4 / 1–5 / 1–7 words.
  The dynamics restricted to a cell is nearly deterministic over many steps.
- BOUNDED-RECOVERY CERTIFICATE idea: if every far state x has k ≤ R with S_k(x) ≥ 0 (log P back to its start value),
  then along any far orbit n_{i+1} = n_i + r(x_{n_i}) gives P(x_{n_i}) ≥ P(x_0) > 0, contradicting P ≤ Cλ^{0.1} → 0.
  Certificate = per cell an exact word tree, every leaf with certified S_k ≥ 0 at its end (rolling: S = 0 exactly).
  No graph, no q, no Q bins, no target leakage. Needs the recovery-time tail to be bounded on the far region.
- Recovery-time tail on 128k uniform strip states (tmp/rectail.jl, horizon 2000): r ≤ 1 59%, ≤ 5 77.6%,
  ≤ 10 91.0%, ≤ 20 99.50%; > 25: 193, > 50: 56, > 100: 23, max 1721. Long recoveries = a debt (I, or O I I O I)
  followed by a long run of Rx steps (exactly neutral), so the debt persists. Rx runs must be handled as a unit.
- Long Rx runs (tmp/rxrun.jl): all at a = 0.5, b ≈ 0 (b < 5e-6): vertices 1 and 3 nearly coincide (merged-vertex
  regime). Each Rx moves the doubled vertex to the other end; ψ drifts linearly (∝ √b per step), s, a, b, Q
  ~constant; run length ~1/√b → unbounded as b → 0. Same configurations as the Rx2 rolling segments of the worst graph
  cycles. ⇒ Plan: two-level bounded-recovery certificate: generic cells recover within a word tree (no targets, no
  leakage) or enter the merged-vertex region with certified bounded debt; the run region is analyzed in blown-up
  coordinates (√b), runs are near-translations in ψ with Δ = 0, exits explicit, recovery from exits covers the debt.
- Recovery counted in NON-Rx steps (tmp/rectail2.jl, 128k strip states): max 24 (≤ 20: 99.96%, ≤ 30: 100%). Debt
  carried into Rx runs: worst −1.96. ⇒ Bounded-recovery certificate works if Rx runs are handled as a unit.
- Rx algebra: M_Rx² = I + N, N² = 0 (N z has zero D-part: λ fixed, Δ's drift linearly). So Rx^{2m} = I + mN; run
  conditions are affine in m (endpoints suffice); the exit set of a run from a cell polytope P lies in the polyhedral
  cone cone(P ∪ NP) ∩ {exit conditions}; Δ = 0 along the run while s ≥ 1/5 (s monotone along the run).
- PLAN (recovery-tree certificate): per cell a tree of exact branch words (LP-feasible children only), Rx runs as
  symbolic nodes, leaf = certified S ≥ 0 on its polytope, depth ≤ ~24 non-Rx steps; contradiction lemma: bounded
  recovery ⇒ P(x_{n_i}) ≥ P(x_0) > 0 along a subsequence, but P ≤ Cλ^{0.1} → 0. No graph, no q, no Q bins.
- RECOVERY TREES WORK (tmp/rtree.jl, 300 random current cells, no run nodes, depth ≤ 24 non-Rx, raw ≤ 60):
  251 of 256 nonempty cells certified, leaves median 1, max 17, non-Rx depth max 23; 5 failed at the depth limit.
  20 s for 300 cells. Since there is no leakage, the partition can be rebuilt adaptively from coarse cells.
- Potential identity: P = A^0.8 λ^-0.7 min(λ/T,1/5)^0.7 = A^0.8 / max(T, 5λ)^0.7, so S = log P(x_k) − log P(x_0) =
  0.8 log α − 0.7 log( max(T_k,5λ_k) / max(T_0,5λ_0) ): one ratio, denominator linear on each side of s_0 = 1/5.
  The first recovery-tree runs failed on all cells containing the s = 0 face only because of a λ_0 > 0 gate (true
  recovery there is 1 step). With the single-ratio bound and no gate: 58 of 60 previously failing cells certify;
  2 hit the raw-step limit (Rx runs).
- Adaptive recovery-tree certification, fixed bound (tmp/rcert.jl → tmp/rcert2.log): level 1 (8^4 grid, 1416 cells):
  1294 certified, 49 depth, 73 raw; level 2: 72/244. Symbolic run nodes (tmp/rtree2_core.jl, weight representation,
  exit cone {Z, NZ} / {MZ, MNZ} ∩ positivity ∩ Rx-before-exit): remove raw failures but are looser; use only for runs
  > 30 steps (on 200 hard cells: 190 ok vs 191 for explicit stepping, which leaves 8 raw).
- Lean plan for the recovery-tree certificate:
  (1) NM.lean: converge_of_recovery — if every far sorted nondeg t has 1 ≤ k ≤ R with
      A(t)^8 · max(T,5λ)(step^k t)^7 ≤ A(step^k t)^8 · max(T,5λ)(t)^7, then f(p3) → 0 (subsequence n_{i+1} = n_i + k;
      P^10 = A^8/max(T,5λ)^7 is nondecreasing along it, positive, and ≤ (λ/5^7)^… → 0).
  (2) Cert/Sound: far t ⇒ zc t in a leaf cell (existing walk/fcheck/far_strip); along the tree path
      zc(step^j t) = M_w(zc t) by step_branch; absent branches: Farkas infeasibility (fcheck on Σ y_i rows, strict
      flags as in pruneOK); leaves: T_k ≤ r·den, 5λ_k ≤ r·den (den = T_0 or 5λ_0, side row s_0 ≶ 1/5) by fcheck,
      and α_w^8 ≥ r^7 in exact rationals. Composed rows = integer-scaled F5 (×16 per step; signs preserved).
  (3) Symbolic Rx runs only if some cells cannot be certified without them (needs M² = I + N and a lemma that an
      infinite Rx run is impossible).
- LEAN: Scratch/nelder_mead_x2y2/Rec.lean — `Mx t = max (T t) (5 lam t)`, `Recovery K R` (every far sorted nondeg t
  has 1 ≤ k ≤ R with A t^8 · Mx(step^[k] t)^7 ≤ A(step^[k] t)^8 · Mx t^7), `converge_of_recovery`,
  `nm_converges_of_recovery` — compile; axioms = [propext, Classical.choice, Quot.sound].
- Adaptive certification levels 3–5: ok 36/344, 251/570, 159/412; depth failures 141 → 114 → 47 (resolved by
  splitting), raw failures ~205 flat. Raw failures = I-step creating a near-merged pair, then a long Rx run (up to
  > 3000 steps), then "R Rx I E E" recovery. converge_of_recovery does not need the bound R (only k ≥ 1), so runs of
  unbounded length are fine if they terminate (D13 > 0 ⇒ Δ-sum drops by 2·D13 per two Rx steps). The run-exit cone
  relaxation is loose because the drift direction depends on κ = (D23 − D12)/D13 (v1 ∝ (κ−1)D13, v2 ∝ −(κ+1)D13);
  fix: split run nodes into κ-intervals by LINEAR rows D23 − D12 − κ_i D13 ≥ 0.
- Failing-path traces (tmp/rdebug.jl): (1) after a run node S = −Inf: the cone relaxation's direction columns have
  λ = 0 (unphysical points, base denominator 0). Exact fix: N z = (D23−D12)(1,−1,0,0,0) + D13(−1,−1,0,0,0), so the
  exit state is w = z + ρ1 A + ρ2 B with A = (−1,−1,0,0,0), B = (1,−1,0,0,0), ρ1 = t·D13 ≥ 0, ρ2 = t(D23−D12),
  linear constraints 2ρ1 ≤ Δsum(z), κ_i ρ1 ≤ ρ2 ≤ κ_{i+1} ρ1, Δ(w) ≥ 0 (two scalar columns per run, ρ bounded by z).
  (2) other cells: long genuine debt patterns (I/O cycles with Rx), S bounds between −0.2 and −1.9 over 40+ steps.
- LEAN: Scratch/nelder_mead_x2y2/RecCert.lean (imports olean/NMSound = Sound.lean): integer branch rows Mrow
  (= 16·brM, lemma Mrow_ev), state tracking W5/stepW (tracks_step), branch rows brRows, sparse Farkas, recovery-tree
  certificates (mutual RT/RC), checker chkRT/chkRC, soundness rec_sound / goal_of_chk:
  chkRT b T W5.id [] 0 0 0 = true → every sorted nondeg t0 with zc t0 ∈ InCell b has k ≥ 1 with
  A t0^8 Mx(step^[k] t0)^7 ≤ A(step^[k] t0)^8 Mx t0^7. Compiles, axioms [propext, Classical.choice, Quot.sound].
  (Leaves may use den = T0 or 5λ0 freely since Mx ≥ both.) Rx-run nodes not yet in Lean.
- LEAN MILESTONE: RecCert.lean part 4 — LC (hole | tree RT), walkR over the k-d tree, walkR_ok, recovery_of_cert,
  and NMR.nm_converges_of_reccert (kt cs) (hw : walkR kt rootBox cs = some []) : convergence of all three vertices
  to 0 for every sorted nondeg start. Axioms [propext, Classical.choice, Quot.sound]. `Recovery` no longer has a
  bound R (only k ≥ 1). REMAINING: data (k-d tree on grid G = 4096 covering the root box, holes, exact recovery-tree
  certificates for every far cell, no run nodes unless added to Lean) + kernel check by decide.
- rexport.jl: exact recovery-tree exporter (IBox on G = 4096, Lean `con` with τ = 2^-20, BigInt fcheck mirror,
  HiGHS LPs for inf / leaf multipliers, rationalization with margins, chkRT_mirror). Test on 8 certified cells: 7 exact
  certificates verified by the mirror (1–21 leaves), 1 exact failure where the float search had certified → such
  cells get split and retried at export time.
- Lean design for run nodes (if needed): maximal Rx run from z_j (finite: two Rx steps lower Δsum by 2·D13 > 0);
  exit w = z_j + m N z_j (or M_Rx(·)), and with ρ1 = m D13 ≤ Δsum(z_j)/2 and the κ-piece row,
  w ∈ conv{z_j, E1 z_j, E2 z_j}, E_i(z) = z + (Δsum(z)/2)(A + κ_i B) — LINEAR images of z_j. Multi-part tracking:
  state = Σ_p E_p(W u_p) with u_p ∈ cell cone (u_p = λ_p z0); every certificate = one multiplier vector y checked by
  fcheck once per part; nested runs multiply parts by 3. After a maximal run the next branch is not Rx.
- END-TO-END LEAN TEST: RecCert.lean compiled to olean/NMRec; two exported exact certificates (1-leaf and 21-leaf /
  45-node cells) emitted as Lean RT terms; `chkRT box T W5.id [] 0 0 0 = true := by decide +kernel` checks both
  (whole file 8.6 s incl. imports). walkR_append / walkR_node added for chunked composition.
- rcert3 (explicit steps + symbolic runs, KMAX 40, RAWMAX 150, RUNK 30) level 1 on the 801 pending cells: 630 ok,
  170 depth, 1 raw (1540 s); certified total 3228 (72.6k leaves). Run nodes are needed and effective.
- Run nodes in Lean, exact form (u = state after 2m Rx steps, ρ1 = m D13, ρ2 = m(D23 − D12)): finite piece
  [κ_i, κ_{i+1}]: (ρ1, ρ2) ∈ triangle (0,0), (H, κ_i H), (H, κ_{i+1} H), H = Δsum/2; upper piece κ ≥ κ_L:
  (0,0), (Δ3/(1+κ_L), κ_L Δ3/(1+κ_L)), (0, Δ3); lower piece κ ≤ κ_F: (0,0), (Δ2/(1−κ_F), κ_F Δ2/(1−κ_F)), (0, −Δ2).
  Vertices linear in z ⇒ multi-part state with coefficients c_p ≥ 0, Σ c_p = 1; old rows replicate to all parts.
  Caveat: per-part checks with independent u_p are looser than the search's coupled LP — test in the exporter first.
- Core budget: rcert3 runs with -t 8; extra jobs (exporter tests, Lean compiles) wait for its level boundary, after
  which rcert3 is restarted from its per-level saves with -t 7.
- Exact multi-part exporter (rexport2.jl, runs as triangles of vertex maps, independent parts): first 10/30; leaf
  exactness lost by rounding multipliers down — fixed by keeping y exact (binary rationals of the LP solution) and
  putting the whole margin on r. After the fix: 29/30 exact certificates on cells certified with runs (21 use runs).
  ⇒ implement the multi-part Lean checker (RecCert2.lean).
- LEAN MILESTONE 2: Scratch/nelder_mead_x2y2/RecCert2.lean (imports olean/NMRec): multi-part recovery trees with
  symbolic Rx runs — run algebra (nAdd, brM2_twice, brC2_unique, run_even, run_finite), κ-pieces (KQ, pieceE/pieceS,
  piece_cover, tri_fin/tri_up/tri_lo, piece_tri), run exits (upartsOf/wpartsOf/prevpartsOf/runRows/runSig, run_exit),
  checker chkRT2/chkRC2/pieceOK/chkRL2 (mutual RT2/RC2/RL2), soundness rec2_sound, walkR2 (+append/node lemmas),
  recovery_of_cert2, and NMR2.nm_converges_of_reccert2 (kt cs) (hw : walkR2 kt rootBox cs = some []).
  Compiles; axioms [propext, Classical.choice, Quot.sound]. The Julia exporter rexport2.jl mirrors this data format.
  REMAINING: finish search, exact export of all cells (split + retry on exact failure), k-d tree + holes on G = 4096,
  Lean data emission + chunked kernel checks, Proof.lean assembly, PROOF.md / CONJECTURES.md / reproduce script.
- Data path verified end to end: rexport_run.jl (exact certificates, resumable, split-retry) → remit.jl (token
  streams) → LoaderR.lean (`lc2s_def`, `ktr_def`, Bool wrapper `walkOK` + `walkOK_eq`) → `decide +kernel`.
  4 exported cells (incl. a 94-leaf / 222-node tree) check in 34 s total.
- Exporter fix: exactly neutral leaves (S = 0: only R/Rx steps in the strip, λ_k ≡ λ_0, α = 1) need r = σ exactly
  (rn = σ, rd = 1); the 5λ inequality is then an identity (y = 0) and the T inequality has slack. With this the
  slow coarse tall cell (343 s of failing exploration) certifies instantly with a 2-leaf tree.
- rcert3b levels 3–5: ok 316/527, 86/287, 195/402; depth failures plateau at ~200/level (4083 cells certified).
  Pending cells cluster at s ∈ [1/8, 1/4], a ∈ [0, 3/8], b ∈ [1/2, 5/8] (vertices 1, 2 nearly merged) and some at
  s ≈ 0.8–0.94. Traces: genuine long recoveries (E E …, 8-step O-chain to −3.0, recovering to −0.04 at the
  40-step limit); E-chains in the strip lose ≈ 0.42 each (A×2, λ×4: thin triangles get thinner). Pure R has period
  6 (M_R^6 = I) and strictly decreasing worst values, so R runs are ≤ 5 steps. ⇒ raise KMAX to 80, RAWMAX to 300.
- rcert3c (KMAX 80, RAWMAX 300) on the 414 pending cells: 126 ok, 278 depth, 10 raw (48 min). Traces: the tree
  settles into the periodic word E Rx I Rx with S bounds cycling −0.264/−0.069 forever. For w = E Rx I Rx:
  eigenvalues ±1, |det| = 1, M_w² = I + N, N² = 0, rank 2, N z = (−4 D12, 2(D12 − D13 + D23), 0, 0, 0): a neutral
  "generalized rolling run" (α_w = 1, λ preserved, Δ drifts linearly) — same structure as Rx runs.
- Periodic tails of 15 failing paths (KMAX 80): 10 aperiodic, 2 pure E-chains, 3 rolling-type words (R E Rx I,
  Rx I R E, long Rx/R mixes). Generalized runs (words w with M_w^p = I + N, N on Δ only, depending on D only) would
  need the run machinery generalized (bound functional, A/B vectors, κ ratio per word); first see whether more
  refinement levels with KMAX 80 shrink the pending set.
- rcert3c levels 1–3: ok 126/414, 194/518, 121/491; depth failures GROW 278 → 315 → 354 (4524 cells certified).
  True recovery in pending cells (tmp/truerec.jl, 59k samples): max 32 non-Rx steps (99.9% ≤ 20). The trees fail
  because cells touching degenerate faces (a → 0: vertices 1, 2 merged) contain states with arbitrarily long
  neutral E Rx I Rx runs ⇒ symbolic runs needed for more words than Rx.
- Neutral run words (tmp/neutralwords.jl): 680 words of length ≤ 6 (up to rotation) with α_w = 1 and M_w^p = I + N,
  N² = 0, N acting on Δ only and depending on D only (e.g. Rx; Rx R R Rx R R with N(Δ2) = −4 D12; many period-2
  words). ⇒ generic, data-driven run nodes: word w, period p, bound coordinate g ∈ {Δ2, Δ3, Δsum} with
  g(Nz) = −ℓ(z), ℓ ≥ ε λ (finite run), complementary h, κ = h(Nz)/ℓ in pieces (top piece bounded; lower infinite
  piece bounded by h ≥ 0), exits at every phase r via the prefix map applied to the triangle vertices
  z, z + g(z)(−e_g + κ_i e_h), z + g(z)(−e_g + κ_{i+1} e_h). Prototype in the float search first.
- Generic neutral-word runs prototype (tmp/rtree3_core.jl: table of 734 words incl. rotations, detection after two
  super-periods, exits at every phase with the column relaxation): 19/40 pending cells certified (KMAX 60, RAWMAX
  200) where KMAX 80 without word runs failed all. ⇒ rcert4 (adaptive search with tree3).
- rcert4 level 1 (generic word runs, KMAX 60): ok 344/740 (46%), depth 391; certified total 4868.
- Lean: BrUnique.lean — brC_unique (the 9 branch conditions are mutually exclusive for Δ2, Δ3 ≥ 0; 81 cases) and
  step_of_brC; compile OK. Next: RecCert3.lean, generic neutral-word runs (pattern w^p, bound g ∈ {Δ2, Δ3, Δsum},
  N read off the 16-scaled word matrix, triangle lemmas per (g, piece type), exits at every phase).
- Diagnostics of tree3 failures (tmp/diag5.jl): (1) the prototype's run exits dropped the u ≥ 0 rows at phases r > 0,
  so the infinite κ-pieces admitted degenerate states (λ = 0) → S = −Inf chains of E steps; (2) periodic words like
  E R I1 (period 2, N not sign-definite in any Δ coordinate) were missing from the table; (3) long mixed tails.
- NEW RUN DESIGN (exact Lean form, tmp/rtree5_core.jl and Lean RunGen/RunExit/RecCert3): pattern P (word^p, α = 1,
  M_P = I + N, N: D → Δ), placed as the child of branch P[1]; bound functional F = Δ2 | Δ3 | Δsum | a signed condition
  row of P[1] (holds at u because phase 0 of that period was followed); ℓ = −F∘N > 0 (auto from coefficients or a strict
  Farkas certificate); (a, b) = Δ-part of F, hN = −b N₂ + a N₃, κ = hN/ℓ in 26 pieces; u = z + (−ρ(a,b) + τ(−b,a))/W;
  finite pieces via ρ ≤ F(z), lower piece via Δ3(u) ≥ 0 (needs a > 0, qb − ap > 0), upper via Δ2(u) ≥ 0 (needs b > 0,
  aq + bp > 0), otherwise the piece must be refuted. Exit at phase r ∈ 1..PL: Pre_r(u) (r = PL: deviation at phase 0,
  u = state before the last full period), parts tripled, rows: old (replicated), piece rows, u ≥ 0, all phase
  conditions, exit ≥ 0. Table: 3795 words (with rotations), length ≤ 6, p ∈ {1,2,3,6}.
- Leaf test in the search replaced by a decision LP (no bisection): Sok(nd) (profile: Slow2 was ~46% of time).
- LEAN MILESTONE 3: RunGen.lean (walks, period map, finiteness run_finite_gen, fSel_nonneg, piece_coverG, tri2_fin/lo/up,
  piece_triG), RunExit.lean (grun_exit: the exit of a maximal generic run as a multi-part InvP), RecCert3.lean (RT3/RC3
  with .grun, chkRT3, rec3_sound, walkR3, NMR3.nm_converges_of_reccert3). Compiles; axioms [propext, Classical.choice,
  Quot.sound]. Old RC2-style Rx runs kept (RC3.run) so the existing exported certificates remain usable.
- RecCert3 extended: RC3.subu (step + nonnegativity rows of the new state), RC3.gcyc (exact cycle words M_P = I;
  finite by λ → 0 via lam_to_zero, exits Pre_r(z), r = 1..PL; cyc_exit). LoaderR3.lean (tokens V, G, C added).
- ROOT CAUSE of most remaining failures (tmp/diag8.jl): cells just below s = 1/8 (no strip constraint) contain
  non-collinear, NON-far states (heron/λ² ≈ 0.04) whose true orbits never recover (S → −4.5 via inside contractions).
  True far states there are nearly collinear too. FIX: strip tiers from the general Cayley–Menger bound
  (NM.far_strip_m: T ≤ (m+1)λ ⇒ heron·K ≤ (3m²+2m+1)λ²): s ≥ 1/8: τ = 2^-20; s ≥ 1/64: τ = 2^-13; s ≥ 1/512: τ = 2^-7
  (Cert.tierDen, isStrip := s0 ≥ 8, Sound.StripZ / strip_of_s / strip_of_far). Old certificates stay valid (the new
  con 6 is an extra constraint for s0 ∈ [8, 512)). Whole olean chain rebuilt by build_chain.sh (7 min), OK.
  Julia: grid13.jl tauof/tauqof/striptau (TIERS=1 default), fastlp tcuts, rexport conI.
- Exporter rexport3.jl (exact mirror of tree5 with grun/gcyc, RT3 format) + remit3.jl tokens + LoaderR3; first test
  found a mismatch (Lean posOK had no scale for rational multipliers) → RC3.grun got a field `ld` (ld·ℓ − Σy·rows > 0).
  After the fix 5/5 test cells (4 with grun) pass `decide +kernel`; old rexport2 trees (incl. Rx runs) also pass under
  RecCert3 (4/4). Whole assembled source (assemble3.sh, no data) compiles in 6.7 min.
- tree5 needs KMAX 80 (as rcert3c): survey (tmp/survey5.txt, KMAX 80, RAWMAX 300, NPER 8, 120 s) on the 2963
  remaining cells: old (rcert3-certified, not yet exported): 1604 ok, 169 empty, 54 depth/time; new (pending or
  prototype-certified): 323 ok, 343 empty (strip tiers!), 60 depth/time (≈ 410 not surveyed).
- rcert6.jl: exact certification (hint from survey → rtree_exact3 KMAX 80; else tree5 NPER 8/2 → export; split on
  failure, MAXD 5). Streams: tmp/rex_certs.jls (old, 2664 cells), tmp/rc5_certs.jls (rcert5 partial, 205 cells),
  tmp/rc6_certs.jls.
- rcert6c restart: re-queued failures listed in tmp/rc6_fail_run1.txt; entries of rc6_certs.jls before byte offset in tmp/rc6_offset_at_c.txt that lie inside those cells must be dropped at final build (overlaps).
- INCIDENT (Oct 22): SIGTERM did not stop multithreaded Julia jobs; rcert5 (7 thr) and rcert6c ran concurrently with rcert6d (23 threads total) until a peer session flagged it; killed with -9. jobs.sh now uses kill -9. Streams rc5/rc6 may have concurrent appends; final build resolves overlaps (later wins) and checks coverage.
- Hard strip cells (s ≈ 0.16–0.22, a ≈ 0.25, b ≈ 0.65, nearly collinear): diagnosis chain — (i) symbolic runs
  relax badly here (run-free explicit trees with long Rx chains work better); (ii) the decisive issue: the word
  E E R I I is EXACTLY neutral there (α = 1, λ₅ = λ₀, S = 0 for every true state: tmp/diag25.jl), so the leaf must
  be the exact r = 1 leaf with den = 5λ₀ for the whole node; the float leaf test split by sign(T₀ − 5λ₀) and needed
  strict slack. Sok now also tests one denominator per node with a generator check / ε-LP. With it all 64 (a,b)
  sub-cells of a failing cell resolve (10 ok, 54 empty). (The band margin and cone cuts were red herrings.)
- rcert6g: CONFS (nper 8, runmax 6) then run-free explicit (nper 1000, rawmax 3000), strip cells pre-split to
  a/b width 4, MAXD 12, dynamic periodic-pattern detection (tails with period 7..40) in tree5/rexport3.
- FULL COVERAGE (Oct 24): streams rex, rc5–rc15 merged by final_build3.jl (robust stream reader, later entries win on
  overlap, empty cells as explicit hole leaves): 179,095 k-d leaves, 0 missing regions. Last hard unit cells were
  certified directly by the exact exporter (float search's LP tolerance created spurious branches there).
- LEAN SCALABILITY: kernel check cost ≈ 5 s + 0.4 s/KB of tokens per tree, transient memory up to 29 GB for one tree;
  1 GB data → ~4–5 days + OOM. Profiling: nearly all time in evaluating Farkas combinations (row lookups in
  append-built lists; list traversal). RecCert4 (packed pair codes, direct-indexed Farkas) → 2×; RecCert5: rows stored
  newest-first with count (RS; denotation fw = reverse, so the RecCert3 proofs carry over via fw_push/fw_ex/fw_c/fw_run),
  multiplier lists packed into (m, B, c) Nats (PY, decY): heaviest sample tree 132 s / 29 GB → 40 s / 11 GB.
  Data format unchanged on the Julia side except the emitter (remit5.jl). RecCert5 + LoaderR5 compile, axioms clean.
- rcert16 (size-limited re-cert) stopped; replaced by kernel-check splitting (assembly lemmas node_of/sub_of/subu_of/grun_of/gl_cons_of/gp_sub_of/gcyc_of/cl_cons_of/cp_sub_of/run_of/rl_cons_of/rp_sub_of/walk_one in RecCert5). rc16 output unused.
- LEAN FRONTEND MEMORY (Oct 24–25): the Lean frontend keeps ~170 KB per top-level command (≈ 500 KB with -j 1)
  and much more for commands with info trees; with ~850k commands (split5 data) a compile needed > 100 GB.
  Fixes: (1) `batch_begin … batch_end` command elaborating ≤ 500 commands with `withEnableInfoTree false`;
  (2) split6/7/8: small children of a split node are inlined (proof `by decide +kernel` inside the node theorem,
  children given as `_` and unified from the tree constant); only P/R states named; (3) LoaderR6 `sdefP`/`sdefR`:
  states are literals computed by the meta code, with `n.eq : n = e` checked by the kernel (`Eq.refl`) and node
  proofs transported by NMR3.rt_congr — without this every check re-evaluated the whole state chain from the root
  (first big tree 222 s → 64 s); (4) split8: run pieces again separate theorems; (5) `set_option maxHeartbeats 0`
  (many kernel checks inside one theorem share one heartbeat budget).
- Parallel elaboration (theorems top-level, Elab.async) uses ~3 cores but memory grows ~0.6 GB/min (29 GB at 29 % of
  the data); so the final run is sequential (Elab.async false, everything batched): memory flat ≈ 10.5 GB, ~250–350 s
  per batch of 500 commands, 503 batches. Kernel cost ≈ 61 s/MB with compiled imports, ≈ 1.7× in the single-file
  Proof.lean (loader/sdef code interpreted). Data: tmp/data_final8.lean (final_build8.jl), Proof.lean by assemble6.sh.
- Final format (split9 / final_build9 / LoaderR6): s, e, c states also literals (`sdefN`), node proofs by
  NMR3.node_get (children as `RT3.child t k`), transport NMR3.rt_congr5; row stores share the previous store as a
  tail with a flat checkpoint every 16 links (deep trees up to 1252 levels: per-node check 12 s → ≤ 1.5 s).
  Bug found by the shard pre-check: decRS could not read expression-defined row stores (run pieces' R2) — fixed.
- VERIFIED (2026-10-27): Proof.lean (1.58 GB, assemble6.sh from tmp/data_final9.lean) compiled with
  `lake env lean Proof.lean` in 25.6 h single-threaded, peak RSS ≈ 35.7 GB (33.2 GiB; the log reports KiB), 0 errors;
  `#print axioms NM.mckinnon_x2y2` → [propext, Classical.choice, Quot.sound]. CONJECTURES.md entry appended.
