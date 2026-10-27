import NMRec
open NM NMC NMS NMR

/-! Recovery trees with symbolic Rx runs: multi-part tracking.

The state after a path is `z_j` with `σ · z_j = Σ_p c_p · W_p(z0)` for unknown weights `c_p ≥ 0`, `Σ c_p = 1`
(parts `W_p`); a row is a list of functionals (one per part) with `Σ_p c_p · row_p(z0) ≥ 0`.  Certificates use one
multiplier vector and are checked part by part on the cell.  A run node (branch 2) covers a maximal run of Rx steps:
its exit state is a convex combination of three linear images of the run start (per κ-piece and parity). -/

namespace NMR2

def gF (l : List F5) (p : Nat) : F5 := (nth l p).getD F5.zero
def gW (ps : List W5) (p : Nat) : W5 := (nth ps p).getD W5.id

/-- a matrix given by its five row functionals, applied to a tracked state -/
def applyM (E : W5) (W : W5) : W5 :=
  ⟨comb5 E.w0 W, comb5 E.w1 W, comb5 E.w2 W, comb5 E.w3 W, comb5 E.w4 W⟩

def condRow (c : F5 × Bool) (W : W5) : F5 := cond c.2 (comb5 c.1 W) (F5.neg (comb5 c.1 W))
def brRowsP (k : Nat) (ps : List W5) : List (List F5) := (brConds k).map (fun c => ps.map (condRow c))
def farkasP (rows : List (List F5)) (ys : List (Nat × Nat)) (p : Nat) : F5 :=
  farkas (rows.map (fun r => gF r p)) ys
def allP (n : Nat) (f : Nat → Bool) : Bool := (List.range n).all f
def gN (l : List Nat) (p : Nat) : Nat := (nth l p).getD 0

/-! ### run pieces -/

/-- κ thresholds `p/q` in increasing order -/
def KQ : List (Int × Nat) :=
  [(-1000, 1), (-30, 1), (-10, 1), (-5, 1), (-3, 1), (-2, 1), (-3, 2), (-6, 5), (-1, 1), (-4, 5), (-1, 2), (-1, 4),
   (0, 1), (1, 4), (1, 2), (4, 5), (1, 1), (6, 5), (3, 2), (2, 1), (3, 1), (5, 1), (10, 1), (30, 1), (1000, 1)]

def zI (k : Int) : Z := ⟨k.toNat, (-k).toNat⟩
theorem zI_val (k : Int) : (zI k).val = k := by
  simp only [zI, Z.val]
  have h : ((k.toNat : ℤ) - ((-k).toNat : ℤ)) = k := Int.toNat_sub_toNat_neg k
  have h' : (((k.toNat : ℤ) - ((-k).toNat : ℤ) : ℤ) : ℝ) = (k : ℝ) := by rw [h]
  push_cast at h'; exact h'

/-- `S·id` plus `x1, x2` in row 1 (columns Δ2, Δ3) and `y1, y2` in row 2 -/
def mkE (S x1 x2 y1 y2 : Int) : W5 :=
  ⟨⟨zI (S + x1), zI x2, zN 0, zN 0, zN 0⟩, ⟨zI y1, zI (S + y2), zN 0, zN 0, zN 0⟩, ⟨zN 0, zN 0, zI S, zN 0, zN 0⟩,
   ⟨zN 0, zN 0, zN 0, zI S, zN 0⟩, ⟨zN 0, zN 0, zN 0, zN 0, zI S⟩⟩

def kq (i : Nat) : Int × Nat := (nth KQ i).getD (0, 1)

/-- scale and the three vertex maps of piece `i` (`0` = lower infinite, `1 … 24` finite, `25` = upper infinite) -/
def pieceS (i : Nat) : Int :=
  if i = 0 then (kq 0).2 - (kq 0).1
  else if i < 25 then 2 * (kq (i - 1)).2 * (kq i).2
  else (kq 24).2 + (kq 24).1
def pieceE (i e : Nat) : W5 :=
  let S := pieceS i
  if e = 0 then mkE S 0 0 0 0
  else if i = 0 then
    (let p := (kq 0).1; let q := ((kq 0).2 : Int)
     if e = 1 then mkE S (p - q) 0 (-p - q) 0 else mkE S (-S) 0 S 0)
  else if i < 25 then
    (let p1 := (kq (i - 1)).1; let q1 := ((kq (i - 1)).2 : Int); let p2 := (kq i).1; let q2 := ((kq i).2 : Int)
     if e = 1 then mkE S (q2 * (p1 - q1)) (q2 * (p1 - q1)) (q2 * (-p1 - q1)) (q2 * (-p1 - q1))
     else mkE S (q1 * (p2 - q2)) (q1 * (p2 - q2)) (q1 * (-p2 - q2)) (q1 * (-p2 - q2)))
  else
    (let p := (kq 24).1; let q := ((kq 24).2 : Int)
     if e = 1 then mkE S 0 (p - q) 0 (-p - q) else mkE S 0 S 0 (-S))

def loRow (j : Nat) : F5 := ⟨zN 0, zN 0, zI (-((kq j).2 : Int)), zI (-(kq j).1), zI ((kq j).2 : Int)⟩
def hiRow (j : Nat) : F5 := ⟨zN 0, zN 0, zI ((kq j).2 : Int), zI (kq j).1, zI (-((kq j).2 : Int))⟩
/-- κ-piece rows of the run start: `κ ≥ κ_{i-1}` (if `i ≥ 1`) and `κ ≤ κ_i` (if `i ≤ 24`), κ = (D23 − D12)/D13 -/
def pieceRows (i : Nat) : List F5 :=
  (if 1 ≤ i then [loRow (i - 1)] else []) ++ (if i ≤ 24 then [hiRow i] else [])
theorem loRow_mem (i : Nat) (h : 1 ≤ i) : loRow (i - 1) ∈ pieceRows i := by simp [pieceRows, h]
theorem hiRow_mem (i : Nat) (h : i ≤ 24) : hiRow i ∈ pieceRows i := by simp [pieceRows, h]

/-- the inverse of the Rx matrix (integer) as row functionals -/
def M2inv : W5 :=
  ⟨⟨zN 0, zN 1, zN 0, zN 0, zN 0⟩, ⟨zN 1, zN 0, zN 1, zN 1, zM 1⟩, ⟨zN 0, zN 0, zN 0, zN 0, zN 1⟩,
   ⟨zN 0, zN 0, zN 0, zN 1, zN 0⟩, ⟨zN 0, zN 0, zN 1, zN 0, zN 0⟩⟩
def unitF (r : Nat) : F5 :=
  ⟨cond (Nat.beq r 0) (zN 1) (zN 0), cond (Nat.beq r 1) (zN 1) (zN 0), cond (Nat.beq r 2) (zN 1) (zN 0),
   cond (Nat.beq r 3) (zN 1) (zN 0), cond (Nat.beq r 4) (zN 1) (zN 0)⟩

/-! ### semantics -/

theorem evz_comb5 (g : F5) (W : W5) (z : Zc) :
    evz (comb5 g W) z = g.c1.val * evz W.w0 z + g.c2.val * evz W.w1 z + g.c3.val * evz W.w2 z +
      g.c4.val * evz W.w3 z + g.c5.val * evz W.w4 z := by
  unfold comb5; simp only [evz_add, evz_smul]

/-- weighted tracking -/
def TrackP (ps : List W5) (c : Nat → ℝ) (z0 zj : Zc) (σ : ℝ) : Prop :=
  ∀ r, r < 5 → σ * zco zj r = ∑ p ∈ Finset.range ps.length, c p * evz ((gW ps p).get r) z0

def RowsOK (rows : List (List F5)) (c : Nat → ℝ) (n : Nat) (z0 : Zc) : Prop :=
  ∀ row ∈ rows, 0 ≤ ∑ p ∈ Finset.range n, c p * evz (gF row p) z0

theorem comb_trackP (ps : List W5) (c : Nat → ℝ) (z0 zj : Zc) (σ : ℝ) (h : TrackP ps c z0 zj σ) (g : F5) :
    ∑ p ∈ Finset.range ps.length, c p * evz (comb5 g (gW ps p)) z0 = σ * evz g zj := by
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num); have h4 := h 4 (by norm_num)
  simp only [W5.get, zco] at h0 h1 h2 h3 h4
  simp only [evz_comb5, mul_add, Finset.sum_add_distrib]
  have e : ∀ (x : ℝ) (f : Nat → ℝ), ∑ p ∈ Finset.range ps.length, c p * (x * f p) =
      x * ∑ p ∈ Finset.range ps.length, c p * f p := by
    intro x f; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [e, e, e, e, e, ← h0, ← h1, ← h2, ← h3, ← h4]
  simp only [evz, F5.ev]; ring

theorem nth_map {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat), nth (l.map f) i = (nth l i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nth_map f l i

theorem nth_lt {α : Type} : ∀ (l : List α) (i : Nat), i < l.length → ∃ x, nth l i = some x
  | [], _, h => by simp at h
  | a :: _, 0, _ => ⟨a, rfl⟩
  | _ :: l, i + 1, h => nth_lt l i (by simp at h; omega)

theorem gW_map (f : W5 → W5) (ps : List W5) (p : Nat) (hp : p < ps.length) : gW (ps.map f) p = f (gW ps p) := by
  obtain ⟨x, hx⟩ := nth_lt ps p hp
  simp [gW, nth_map, hx]

theorem gF_map (f : W5 → F5) (ps : List W5) (p : Nat) (hp : p < ps.length) : gF (ps.map f) p = f (gW ps p) := by
  obtain ⟨x, hx⟩ := nth_lt ps p hp
  simp [gF, gW, nth_map, hx]

theorem getR_map (rows : List (List F5)) (p i : Nat) :
    getR (rows.map (fun r => gF r p)) i = ((nth rows i).map (fun r => gF r p)).getD F5.zero := by
  simp [getR, nth_map]

/-- the weighted Farkas combination is nonnegative -/
theorem farkasP_nonneg (rows : List (List F5)) (c : Nat → ℝ) (n : Nat) (z0 : Zc) (hc : ∀ p < n, 0 ≤ c p)
    (hr : RowsOK rows c n z0) : ∀ ys, 0 ≤ ∑ p ∈ Finset.range n, c p * evz (farkasP rows ys p) z0
  | [] => by simp [farkasP, farkas]
  | (i, y) :: ys => by
    have ih := farkasP_nonneg rows c n z0 hc hr ys
    have e : ∀ p, evz (farkasP rows ((i, y) :: ys) p) z0 =
        (zN y).val * evz (getR (rows.map (fun r => gF r p)) i) z0 + evz (farkasP rows ys p) z0 := by
      intro p; simp only [farkasP, farkas, evz_add, evz_smul]
    simp only [e, mul_add, Finset.sum_add_distrib]
    have hy : (0 : ℝ) ≤ (zN y).val := by simp [zN, Z.val]
    have hrow : 0 ≤ ∑ p ∈ Finset.range n, c p * ((zN y).val * evz (getR (rows.map (fun r => gF r p)) i) z0) := by
      cases hn : nth rows i with
      | none => simp [getR_map, hn]
      | some row =>
        have := hr row (nth_mem rows i row hn)
        simp only [getR_map, hn, Option.map_some, Option.getD_some]
        have e2 : ∑ p ∈ Finset.range n, c p * ((zN y).val * evz (gF row p) z0) =
            (zN y).val * ∑ p ∈ Finset.range n, c p * evz (gF row p) z0 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
        rw [e2]; exact mul_nonneg hy this
    linarith

theorem trackP_step (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (ps : List W5) (c : Nat → ℝ) (z0 zj : Zc) (σ : ℝ)
    (h : TrackP ps c z0 zj σ) : TrackP (ps.map (stepW k)) c z0 (brM k zj) (16 * σ) := by
  intro r hr
  rw [List.length_map]
  have e : ∀ p ∈ Finset.range ps.length, c p * evz ((gW (ps.map (stepW k)) p).get r) z0 =
      c p * evz (comb5 (Mrow k r) (gW ps p)) z0 := by
    intro p hp
    rw [gW_map _ _ _ (Finset.mem_range.mp hp)]
    have : (stepW k (gW ps p)).get r = comb5 (Mrow k r) (gW ps p) := by interval_cases r <;> rfl
    rw [this]
  rw [Finset.sum_congr rfl e, comb_trackP ps c z0 zj σ h, Mrow_ev k hk1 hk9 r hr]; ring

theorem brRowsP_ok (k : Nat) (ps : List W5) (c : Nat → ℝ) (z0 zj : Zc) (σ : ℝ) (hσ : 0 < σ)
    (h : TrackP ps c z0 zj σ) (hbr : brC k zj) : RowsOK (brRowsP k ps) c ps.length z0 := by
  intro row hrow
  simp only [brRowsP, List.mem_map] at hrow
  obtain ⟨⟨g, need⟩, hmem, rfl⟩ := hrow
  obtain ⟨i, hi⟩ := mem_nth _ _ hmem
  have hb := br_conds k zj hbr i g need hi
  have e : ∀ p ∈ Finset.range ps.length, c p * evz (gF (ps.map (condRow (g, need))) p) z0 =
      c p * evz (condRow (g, need) (gW ps p)) z0 := by
    intro p hp; rw [gF_map _ _ _ (Finset.mem_range.mp hp)]
  rw [Finset.sum_congr rfl e]
  cases need with
  | true =>
    simp only [condRow, cond]; rw [comb_trackP ps c z0 zj σ h]; exact mul_nonneg hσ.le (hb.1 rfl)
  | false =>
    simp only [condRow, cond, evz_neg, mul_neg, Finset.sum_neg_distrib]
    rw [comb_trackP ps c z0 zj σ h]; nlinarith [hb.2 rfl]

/-! ### Rx runs -/

/-- the state after `2m` Rx steps: `z + m·N z` -/
noncomputable def nAdd (z : Zc) (m : ℝ) : Zc :=
  ⟨z.d2 + m * (z.c - z.a - z.b), z.d3 + m * (z.a - z.b - z.c), z.a, z.b, z.c⟩

theorem brM2_twice (z : Zc) (m : ℝ) : brM 2 (brM 2 (nAdd z m)) = nAdd z (m + 1) := by
  simp only [brM, brM2, nAdd, Zc.mk.injEq]; refine ⟨by ring, by ring, by ring, by ring, by ring⟩

theorem nAdd_zero (z : Zc) : nAdd z 0 = z := by simp [nAdd]

/-- if the Rx conditions hold, the step taken is Rx -/
theorem brC2_unique (z : Zc) (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (h2 : brC 2 z) (hk : brC k z)
    (hd2 : 0 ≤ z.d2) (hd3 : 0 ≤ z.d3) : k = 2 := by
  simp only [brC, brC2] at h2
  interval_cases k <;> simp only [brC, brC1, brC3, brC4, brC5, brC6, brC7, brC8, brC9] at hk <;>
    first | rfl | (exfalso; linarith [h2.1, h2.2, hk.1, hk.2]) | (exfalso; linarith [h2.1, h2.2, hk.1])

theorem step_rx (t : Tri) (hs : sorted t) (hn : nondeg t) (h2 : brC 2 (zc t)) :
    zc (step t) = brM 2 (zc t) ∧ A (step t) = A t := by
  obtain ⟨k, hk1, hk9, hbr, hM, hA⟩ := step_branch' t hs hn
  have hz := zc_nonneg t hs
  have := brC2_unique (zc t) k hk1 hk9 h2 hbr hz.1 hz.2.1
  subst this
  exact ⟨hM, by rw [hA]; simp [alpha]⟩

theorem iter_sorted (t : Tri) (hs : sorted t) (hn : nondeg t) (j : Nat) :
    sorted (step^[j] t) ∧ nondeg (step^[j] t) := by
  induction j with
  | zero => exact ⟨hs, hn⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨step_sorted _ ih.1 ih.2, step_nondeg _ ih.1 ih.2⟩

/-- along a run of `2m` Rx steps the state is `nAdd z m` and the area is unchanged -/
theorem run_even (t : Tri) (hs : sorted t) (hn : nondeg t) :
    ∀ m : Nat, (∀ i < 2 * m, brC 2 (zc (step^[i] t))) →
      zc (step^[2 * m] t) = nAdd (zc t) m ∧ A (step^[2 * m] t) = A t := by
  intro m
  induction m with
  | zero => intro _; simp [nAdd_zero]
  | succ m ih =>
    intro hr
    obtain ⟨h1, h2⟩ := ih (fun i hi => hr i (by omega))
    have e1 : step^[2 * (m + 1)] t = step (step (step^[2 * m] t)) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Function.iterate_succ_apply', Function.iterate_succ_apply']
    have s0 := iter_sorted t hs hn (2 * m)
    have r0 := hr (2 * m) (by omega)
    obtain ⟨a1, b1⟩ := step_rx _ s0.1 s0.2 r0
    have s1 := iter_sorted t hs hn (2 * m + 1)
    have r1 := hr (2 * m + 1) (by omega)
    rw [Function.iterate_succ_apply'] at s1 r1
    obtain ⟨a2, b2⟩ := step_rx _ s1.1 s1.2 r1
    refine ⟨?_, ?_⟩
    · rw [e1, a2, a1, h1, brM2_twice]; push_cast; ring_nf
    · rw [e1, b2, b1, h2]

/-- a run is finite: for nondegenerate states there is a first non-Rx index -/
theorem run_finite (t : Tri) (hs : sorted t) (hn : nondeg t) :
    ∃ n, ¬ brC 2 (zc (step^[n] t)) := by
  by_contra hall
  push_neg at hall
  have hb : 0 < (zc t).b := by simp only [zc]; exact D13_pos t hn
  have hz := zc_nonneg t hs
  -- choose m with 2 m b > d2 + d3
  obtain ⟨m, hm⟩ := exists_nat_gt (((zc t).d2 + (zc t).d3) / (2 * (zc t).b))
  have h := run_even t hs hn m (fun i _ => hall i)
  have hv := zc_nonneg _ (iter_sorted t hs hn (2 * m)).1
  rw [h.1] at hv
  simp only [nAdd] at hv
  have : ((zc t).d2 + (zc t).d3) < 2 * (zc t).b * m := by
    rw [div_lt_iff₀ (by positivity)] at hm; linarith
  nlinarith [hv.1, hv.2.1]

/-! ### κ-pieces: the exit state is a convex combination of three vertex states -/

/-- the vertex property: `S · u = Σ λ_e · E_e(z)` coordinatewise -/
def Tri3 (S : ℝ) (u : Zc) (e0 e1 e2 : Zc) : Prop :=
  ∃ l0 l1 l2 : ℝ, 0 ≤ l0 ∧ 0 ≤ l1 ∧ 0 ≤ l2 ∧ l0 + l1 + l2 = 1 ∧
    S * u.d2 = l0 * e0.d2 + l1 * e1.d2 + l2 * e2.d2 ∧ S * u.d3 = l0 * e0.d3 + l1 * e1.d3 + l2 * e2.d3 ∧
    S * u.a = l0 * e0.a + l1 * e1.a + l2 * e2.a ∧ S * u.b = l0 * e0.b + l1 * e1.b + l2 * e2.b ∧
    S * u.c = l0 * e0.c + l1 * e1.c + l2 * e2.c

/-- `S·z` plus `(x1 d2 + x2 d3, y1 d2 + y2 d3)` in the first two coordinates -/
noncomputable def vtx (S x1 x2 y1 y2 : ℝ) (z : Zc) : Zc :=
  ⟨S * z.d2 + x1 * z.d2 + x2 * z.d3, S * z.d3 + y1 * z.d2 + y2 * z.d3, S * z.a, S * z.b, S * z.c⟩

theorem tri_trivial (S : ℝ) (z : Zc) (e1 e2 : Zc) : Tri3 S z (vtx S 0 0 0 0 z) e1 e2 :=
  ⟨1, 0, 0, by norm_num, le_refl _, le_refl _, by norm_num, by simp [vtx], by simp [vtx], by simp [vtx], by simp [vtx], by simp [vtx]⟩

theorem tri_fin (z : Zc) (m : ℝ) (hm : 0 ≤ m) (hb : 0 < z.b) (p1 q1 p2 q2 : ℝ) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hlt : p1 * q2 < p2 * q1) (hlo : 0 ≤ q1 * (z.c - z.a) - p1 * z.b) (hhi : 0 ≤ p2 * z.b - q2 * (z.c - z.a))
    (hu : 0 ≤ (nAdd z m).d2 + (nAdd z m).d3) :
    Tri3 (2 * q1 * q2) (nAdd z m) (vtx (2 * q1 * q2) 0 0 0 0 z)
      (vtx (2 * q1 * q2) (q2 * (p1 - q1)) (q2 * (p1 - q1)) (q2 * (-p1 - q1)) (q2 * (-p1 - q1)) z)
      (vtx (2 * q1 * q2) (q1 * (p2 - q2)) (q1 * (p2 - q2)) (q1 * (-p2 - q2)) (q1 * (-p2 - q2)) z) := by
  set H2 := z.d2 + z.d3
  simp only [nAdd] at hu
  have hu' : 2 * m * z.b ≤ H2 := by simp only [H2]; nlinarith
  rcases eq_or_lt_of_le (le_trans (by positivity : (0 : ℝ) ≤ 2 * m * z.b) hu') with hH | hH
  · -- H2 = 0 forces m = 0
    have : m * z.b = 0 := by nlinarith
    have hm0 : m = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (ne_of_gt hb)
    subst hm0; rw [nAdd_zero]; exact tri_trivial _ _ _ _
  · set Dk := p2 * q1 - p1 * q2
    have hD : 0 < Dk := by simp only [Dk]; linarith
    refine ⟨1 - 2 * m * z.b / H2, 2 * m * q1 * (p2 * z.b - q2 * (z.c - z.a)) / (H2 * Dk),
      2 * m * q2 * (q1 * (z.c - z.a) - p1 * z.b) / (H2 * Dk), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sub_nonneg, div_le_one hH]; exact hu'
    · positivity
    · positivity
    · field_simp; ring
    all_goals simp only [nAdd, vtx]; field_simp; ring

theorem tri_up (z : Zc) (m : ℝ) (hm : 0 ≤ m) (hb : 0 < z.b) (p q : ℝ) (hq : 0 < q) (hp : 0 ≤ p)
    (hlo : 0 ≤ q * (z.c - z.a) - p * z.b) (hu3 : 0 ≤ (nAdd z m).d3) :
    Tri3 (q + p) (nAdd z m) (vtx (q + p) 0 0 0 0 z) (vtx (q + p) 0 (p - q) 0 (-p - q) z)
      (vtx (q + p) 0 (q + p) 0 (-(q + p)) z) := by
  simp only [nAdd] at hu3
  set r1 := m * z.b; set r2 := m * (z.c - z.a)
  have hr1 : 0 ≤ r1 := by positivity
  have hr2 : p * r1 ≤ q * r2 := by simp only [r1, r2]; nlinarith
  have h3 : r1 + r2 ≤ z.d3 := by simp only [r1, r2]; nlinarith
  rcases eq_or_lt_of_le (le_trans (by nlinarith : (0 : ℝ) ≤ r1 + r2) h3) with hd | hd
  · have hr10 : r1 = 0 := by nlinarith
    have hm0 : m = 0 := by
      rcases mul_eq_zero.mp hr10 with h | h
      · exact h
      · exact absurd h (ne_of_gt hb)
    subst hm0; rw [nAdd_zero]; exact tri_trivial _ _ _ _
  · refine ⟨(z.d3 - r1 - r2) / z.d3, r1 * (q + p) / (q * z.d3), (q * r2 - p * r1) / (q * z.d3), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · positivity
    · apply div_nonneg <;> nlinarith
    · field_simp; ring
    all_goals simp only [nAdd, vtx, r1, r2]; field_simp; ring

theorem tri_lo (z : Zc) (m : ℝ) (hm : 0 ≤ m) (hb : 0 < z.b) (p q : ℝ) (hq : 0 < q) (hp : p ≤ 0)
    (hhi : 0 ≤ p * z.b - q * (z.c - z.a)) (hu2 : 0 ≤ (nAdd z m).d2) :
    Tri3 (q - p) (nAdd z m) (vtx (q - p) 0 0 0 0 z) (vtx (q - p) (p - q) 0 (-p - q) 0 z)
      (vtx (q - p) (-(q - p)) 0 (q - p) 0 z) := by
  simp only [nAdd] at hu2
  set r1 := m * z.b; set r2 := m * (z.c - z.a)
  have hr1 : 0 ≤ r1 := by positivity
  have hr2 : q * r2 ≤ p * r1 := by simp only [r1, r2]; nlinarith
  have h2 : r1 - r2 ≤ z.d2 := by simp only [r1, r2]; nlinarith
  have hpos : 0 ≤ r1 - r2 := by nlinarith
  rcases eq_or_lt_of_le (le_trans hpos h2) with hd | hd
  · have hr10 : r1 = 0 := by nlinarith
    have hm0 : m = 0 := by
      rcases mul_eq_zero.mp hr10 with h | h
      · exact h
      · exact absurd h (ne_of_gt hb)
    subst hm0; rw [nAdd_zero]; exact tri_trivial _ _ _ _
  · refine ⟨(z.d2 - r1 + r2) / z.d2, r1 * (q - p) / (q * z.d2), (p * r1 - q * r2) / (q * z.d2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply div_nonneg <;> linarith
    · apply div_nonneg <;> nlinarith
    · apply div_nonneg <;> nlinarith
    · field_simp; ring
    all_goals simp only [nAdd, vtx, r1, r2]; field_simp; ring

/-! ### the computed piece maps -/

noncomputable def evalE (E : W5) (z : Zc) : Zc := ⟨evz E.w0 z, evz E.w1 z, evz E.w2 z, evz E.w3 z, evz E.w4 z⟩

theorem zN_val (k : Nat) : (zN k).val = k := by simp [zN, Z.val]

theorem evalE_mkE (S x1 x2 y1 y2 : Int) (z : Zc) :
    evalE (mkE S x1 x2 y1 y2) z = vtx S x1 x2 y1 y2 z := by
  simp only [evalE, mkE, vtx, evz, F5.ev, zI_val, zN_val, Zc.mk.injEq]; push_cast
  refine ⟨by ring, by ring, by ring, by ring, by ring⟩

theorem KQ_incr : ∀ i, i < 24 → (kq i).1 * ((kq (i + 1)).2 : Int) < (kq (i + 1)).1 * ((kq i).2 : Int) := by
  decide

theorem kq_q_pos : ∀ i, i < 25 → 0 < (kq i).2 := by decide
theorem kq0 : kq 0 = (-1000, 1) := rfl
theorem kq24 : kq 24 = (1000, 1) := rfl

theorem evz_pieceRow_lo (i : Nat) (z : Zc) :
    evz (loRow i) z =
      ((kq i).2 : ℝ) * (z.c - z.a) - ((kq i).1 : ℝ) * z.b := by
  simp only [loRow, hiRow, evz, F5.ev, zI_val, zN_val]; push_cast; ring
theorem evz_pieceRow_hi (i : Nat) (z : Zc) :
    evz (hiRow i) z =
      ((kq i).1 : ℝ) * z.b - ((kq i).2 : ℝ) * (z.c - z.a) := by
  simp only [loRow, hiRow, evz, F5.ev, zI_val, zN_val]; push_cast; ring

/-- every state with `D13 > 0` lies in some κ-piece -/
theorem piece_cover (z : Zc) : ∃ i, i ≤ 25 ∧ ∀ f ∈ pieceRows i, 0 ≤ evz f z := by
  classical
  by_cases hex : ∃ j, j ≤ 24 ∧ 0 ≤ ((kq j).1 : ℝ) * z.b - ((kq j).2 : ℝ) * (z.c - z.a)
  · let i := Nat.find hex
    have hi := Nat.find_spec hex
    have hmin := fun j (hj : j < i) => Nat.find_min hex hj
    refine ⟨i, by omega, ?_⟩
    intro f hf
    simp only [pieceRows, List.mem_append] at hf
    rcases hf with hf | hf
    · split_ifs at hf with h1
      · simp only [List.mem_singleton] at hf; subst hf
        rw [evz_pieceRow_lo]
        have := hmin (i - 1) (by omega)
        push_neg at this
        have := this (by omega)
        linarith
      · simp at hf
    · split_ifs at hf with h2
      · simp only [List.mem_singleton] at hf; subst hf; rw [evz_pieceRow_hi]; exact hi.2
      · simp at hf
  · push_neg at hex
    refine ⟨25, le_refl _, ?_⟩
    intro f hf
    simp only [pieceRows, List.mem_append] at hf
    rcases hf with hf | hf
    · simp only [show (1 : Nat) ≤ 25 from by norm_num, if_true, List.mem_singleton] at hf
      subst hf; rw [evz_pieceRow_lo]; have := hex 24 (le_refl _)
      simp only [show 25 - 1 = 24 from rfl] at *; linarith
    · simp at hf

/-- the exit state of `2m` Rx steps from a state in piece `i` is a convex combination of the piece's vertex states -/
theorem piece_tri (z : Zc) (m : Nat) (hb : 0 < z.b) (i : Nat) (hi : i ≤ 25) (hrows : ∀ f ∈ pieceRows i, 0 ≤ evz f z)
    (hu2 : 0 ≤ (nAdd z m).d2) (hu3 : 0 ≤ (nAdd z m).d3) :
    Tri3 (pieceS i) (nAdd z m) (evalE (pieceE i 0) z) (evalE (pieceE i 1) z) (evalE (pieceE i 2) z) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have hr : 0 ≤ ((kq 0).1 : ℝ) * z.b - ((kq 0).2 : ℝ) * (z.c - z.a) := by
      have := hrows _ (hiRow_mem 0 (by norm_num)); rwa [evz_pieceRow_hi] at this
    rw [kq0] at hr; push_cast at hr
    have e := tri_lo z m hm hb (-1000) 1 (by norm_num) (by norm_num) (by linarith) hu2
    simp only [pieceS, pieceE, kq0, ite_true, show (1 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 0 from by norm_num,
      show (2 : Nat) ≠ 1 from by norm_num, ite_false]
    rw [evalE_mkE, evalE_mkE, evalE_mkE]
    push_cast; norm_num at e ⊢; exact e
  · rcases lt_or_eq_of_le hi with hlt | h25
    · -- finite piece
      have hq1 := kq_q_pos (i - 1) (by omega); have hq2 := kq_q_pos i (by omega)
      have hinc := KQ_incr (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at hinc
      have hlo : 0 ≤ ((kq (i - 1)).2 : ℝ) * (z.c - z.a) - ((kq (i - 1)).1 : ℝ) * z.b := by
        have := hrows _ (loRow_mem i (by omega)); rwa [evz_pieceRow_lo] at this
      have hhi : 0 ≤ ((kq i).1 : ℝ) * z.b - ((kq i).2 : ℝ) * (z.c - z.a) := by
        have := hrows _ (hiRow_mem i (by omega)); rwa [evz_pieceRow_hi] at this
      have hinc' : ((kq (i - 1)).1 : ℝ) * ((kq i).2 : ℝ) < ((kq i).1 : ℝ) * ((kq (i - 1)).2 : ℝ) := by exact_mod_cast hinc
      have hu : 0 ≤ (nAdd z m).d2 + (nAdd z m).d3 := by linarith
      have e := tri_fin z m hm hb _ _ _ _ (by exact_mod_cast hq1) (by exact_mod_cast hq2) hinc' hlo hhi hu
      simp only [pieceS, pieceE, show i ≠ 0 by omega, ite_false, show i < 25 by omega, ite_true,
        show (1 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 1 from by norm_num]
      rw [evalE_mkE, evalE_mkE, evalE_mkE]
      push_cast; exact e
    · subst h25
      have hr : 0 ≤ ((kq 24).2 : ℝ) * (z.c - z.a) - ((kq 24).1 : ℝ) * z.b := by
        have := hrows _ (loRow_mem 25 (by norm_num)); rwa [evz_pieceRow_lo] at this
      rw [kq24] at hr; push_cast at hr
      have e := tri_up z m hm hb 1000 1 (by norm_num) (by norm_num) (by linarith) hu3
      simp only [pieceS, pieceE, kq24, show (25 : Nat) ≠ 0 from by norm_num, ite_false, show ¬ (25 : Nat) < 25 from by norm_num,
        show (1 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 1 from by norm_num,
        ite_true]
      rw [evalE_mkE, evalE_mkE, evalE_mkE]
      push_cast; norm_num at e ⊢; exact e

/-! ### run exits: parts, rows, scale -/

def upartsOf (i : Nat) (ps : List W5) : List W5 :=
  ps.map (applyM (pieceE i 0)) ++ ps.map (applyM (pieceE i 1)) ++ ps.map (applyM (pieceE i 2))
def wpartsOf (i : Nat) (odd : Bool) (ps : List W5) : List W5 := cond odd ((upartsOf i ps).map (stepW 2)) (upartsOf i ps)
def prevpartsOf (i : Nat) (odd : Bool) (ps : List W5) : List W5 :=
  cond odd (upartsOf i ps) ((upartsOf i ps).map (applyM M2inv))
def repRow (np : Nat) (row : List F5) : List F5 := (List.range (3 * np)).map (fun q => gF row (q % np))
def runRows (i : Nat) (odd : Bool) (ps : List W5) (rows : List (List F5)) : List (List F5) :=
  rows.map (repRow ps.length) ++ (pieceRows i).map (fun f => repRow ps.length (ps.map (comb5 f))) ++
    brRowsP 2 (prevpartsOf i odd ps) ++ (List.range 5).map (fun r => (wpartsOf i odd ps).map (comb5 (unitF r)))
def runSig (i : Nat) (odd : Bool) (σ : Nat) : Nat := σ * (pieceS i).toNat * cond odd 16 1

theorem pieceS_pos : ∀ i, i ≤ 25 → 0 < pieceS i := by decide

theorem M2inv_ev (v : Zc) (r : Nat) (hr : r < 5) : evz (M2inv.get r) (brM 2 v) = zco v r := by
  interval_cases r <;> simp [M2inv, W5.get, evz, F5.ev, zN, zM, Z.val, brM, brM2, zco] <;> ring

theorem unitF_ev (r : Nat) (hr : r < 5) (z : Zc) : evz (unitF r) z = zco z r := by
  interval_cases r <;> simp [unitF, evz, F5.ev, zN, Z.val, zco]

theorem length_uparts (i : Nat) (ps : List W5) : (upartsOf i ps).length = 3 * ps.length := by
  simp [upartsOf]; ring

theorem gW_uparts (i : Nat) (ps : List W5) (e p : Nat) (he : e < 3) (hp : p < ps.length) :
    gW (upartsOf i ps) (e * ps.length + p) = applyM (pieceE i e) (gW ps p) := by
  obtain ⟨x, hx⟩ := nth_lt ps p hp
  have hl : ∀ l : List W5, ∀ q, q < l.length → nth l q = l[q]? := by
    intro l; induction l with
    | nil => intro q hq; simp at hq
    | cons a l ih => intro q hq; cases q with
      | zero => rfl
      | succ q => simp only [nth, List.getElem?_cons_succ]; exact ih q (by simp at hq; omega)
  have hlen : e * ps.length + p < (upartsOf i ps).length := by rw [length_uparts]; nlinarith
  simp only [gW, hl _ _ hlen, hl _ _ hp] at hx ⊢
  interval_cases e
  · simp only [upartsOf, zero_mul, zero_add, List.append_assoc]
    rw [List.getElem?_append_left (by simpa using hp)]; simp [hx]
  · simp only [upartsOf, one_mul, List.append_assoc]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp; omega)]; simp [hx]
  · simp only [upartsOf, List.append_assoc]
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.getElem?_map]
    rw [show 2 * ps.length + p - ps.length - ps.length = p by omega]; simp [hx]

/-- sums over the tripled parts -/
theorem sum_three (np : Nat) (g : Nat → ℝ) :
    ∑ q ∈ Finset.range (3 * np), g q = ∑ e ∈ Finset.range 3, ∑ p ∈ Finset.range np, g (e * np + p) := by
  rw [show 3 * np = np + np + np by ring, Finset.sum_range_add, Finset.sum_range_add]
  simp [Finset.sum_range_succ]; ring_nf

/-! ### the invariant and the run-exit step -/

structure InvP (t0 : Tri) (ps : List W5) (rows : List (List F5)) (σ : Nat) (j nE nC : Nat) : Prop where
  srt : sorted (step^[j] t0)
  ndg : nondeg (step^[j] t0)
  wts : ∃ c : Nat → ℝ, (∀ p < ps.length, 0 ≤ c p) ∧ (∑ p ∈ Finset.range ps.length, c p = 1) ∧
    TrackP ps c (zc t0) (zc (step^[j] t0)) σ ∧ RowsOK rows c ps.length (zc t0)
  area : A (step^[j] t0) = (2 : ℝ) ^ nE / 2 ^ nC * A t0
  sig : 1 ≤ σ

/-- tripled weights `c'(e·np + p) = λ_e c_p` -/
noncomputable def triW (np : Nat) (l0 l1 l2 : ℝ) (c : Nat → ℝ) (q : Nat) : ℝ :=
  (if q / np = 0 then l0 else if q / np = 1 then l1 else l2) * c (q % np)

theorem triW_at (np : Nat) (hnp : 0 < np) (l0 l1 l2 : ℝ) (c : Nat → ℝ) (e p : Nat) (he : e < 3) (hp : p < np) :
    triW np l0 l1 l2 c (e * np + p) = (if e = 0 then l0 else if e = 1 then l1 else l2) * c p := by
  have h1 : (e * np + p) / np = e := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnp, Nat.div_eq_of_lt hp, zero_add]
  have h2 : (e * np + p) % np = p := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
  simp only [triW, h1, h2]

theorem sum3_triW (np : Nat) (hnp : 0 < np) (l0 l1 l2 : ℝ) (c : Nat → ℝ) (g : Nat → Nat → ℝ) (G : Nat → ℝ)
    (hG : ∀ e p, e < 3 → p < np → G (e * np + p) = g e p) :
    ∑ q ∈ Finset.range (3 * np), triW np l0 l1 l2 c q * G q =
      l0 * ∑ p ∈ Finset.range np, c p * g 0 p + l1 * ∑ p ∈ Finset.range np, c p * g 1 p +
        l2 * ∑ p ∈ Finset.range np, c p * g 2 p := by
  rw [sum_three]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e : ∀ e, e < 3 → ∑ p ∈ Finset.range np, triW np l0 l1 l2 c (e * np + p) * G (e * np + p) =
      (if e = 0 then l0 else if e = 1 then l1 else l2) * ∑ p ∈ Finset.range np, c p * g e p := by
    intro e he
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp
    rw [triW_at np hnp l0 l1 l2 c e p he (Finset.mem_range.mp hp), hG e p he (Finset.mem_range.mp hp)]; ring
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]; simp

theorem np_pos (ps : List W5) (c : Nat → ℝ) (h : ∑ p ∈ Finset.range ps.length, c p = 1) : 0 < ps.length := by
  rcases Nat.eq_zero_or_pos ps.length with h0 | h0
  · rw [h0] at h; simp at h
  · exact h0

theorem gF_rep (np : Nat) (hnp : 0 < np) (row : List F5) (e p : Nat) (he : e < 3) (hp : p < np) :
    gF (repRow np row) (e * np + p) = gF row p := by
  have hl : e * np + p < 3 * np := by nlinarith
  have hm : (e * np + p) % np = p := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
  unfold repRow gF
  rw [nth_map]
  have : nth (List.range (3 * np)) (e * np + p) = some (e * np + p) := by
    have hl2 : ∀ (k i : Nat), i < k → nth (List.range k) i = some i := by
      intro k i hik
      have : ∀ l : List Nat, ∀ q, q < l.length → nth l q = l[q]? := by
        intro l; induction l with
        | nil => intro q hq; simp at hq
        | cons a l ih => intro q hq; cases q with
          | zero => rfl
          | succ q => simp only [nth, List.getElem?_cons_succ]; exact ih q (by simp at hq; omega)
      rw [this _ _ (by simpa using hik)]; simp [hik]
    exact hl2 _ _ hl
  rw [this]; simp [hm]

theorem zco_evalE (E : W5) (z : Zc) (r : Nat) (hr : r < 5) : zco (evalE E z) r = evz (E.get r) z := by
  interval_cases r <;> rfl
theorem applyM_get (E W : W5) (r : Nat) (hr : r < 5) : (applyM E W).get r = comb5 (E.get r) W := by
  interval_cases r <;> rfl

theorem tri3_coord {S : ℝ} {u e0 e1 e2 : Zc} {l0 l1 l2 : ℝ}
    (h : S * u.d2 = l0 * e0.d2 + l1 * e1.d2 + l2 * e2.d2 ∧ S * u.d3 = l0 * e0.d3 + l1 * e1.d3 + l2 * e2.d3 ∧
      S * u.a = l0 * e0.a + l1 * e1.a + l2 * e2.a ∧ S * u.b = l0 * e0.b + l1 * e1.b + l2 * e2.b ∧
      S * u.c = l0 * e0.c + l1 * e1.c + l2 * e2.c) (r : Nat) (hr : r < 5) :
    S * zco u r = l0 * zco e0 r + l1 * zco e1 r + l2 * zco e2 r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  interval_cases r <;> simp only [zco] <;> assumption

/-- the vertex parts track the run exit `u` with scale `S σ` -/
theorem track_uparts (i : Nat) (ps : List W5) (c : Nat → ℝ) (z0 z u : Zc) (σ S : ℝ) (l0 l1 l2 : ℝ)
    (hnp : 0 < ps.length) (htr : TrackP ps c z0 z σ)
    (htri : S * u.d2 = l0 * (evalE (pieceE i 0) z).d2 + l1 * (evalE (pieceE i 1) z).d2 + l2 * (evalE (pieceE i 2) z).d2 ∧
      S * u.d3 = l0 * (evalE (pieceE i 0) z).d3 + l1 * (evalE (pieceE i 1) z).d3 + l2 * (evalE (pieceE i 2) z).d3 ∧
      S * u.a = l0 * (evalE (pieceE i 0) z).a + l1 * (evalE (pieceE i 1) z).a + l2 * (evalE (pieceE i 2) z).a ∧
      S * u.b = l0 * (evalE (pieceE i 0) z).b + l1 * (evalE (pieceE i 1) z).b + l2 * (evalE (pieceE i 2) z).b ∧
      S * u.c = l0 * (evalE (pieceE i 0) z).c + l1 * (evalE (pieceE i 1) z).c + l2 * (evalE (pieceE i 2) z).c) :
    TrackP (upartsOf i ps) (triW ps.length l0 l1 l2 c) z0 u (S * σ) := by
  intro r hr
  rw [length_uparts]
  rw [sum3_triW ps.length hnp l0 l1 l2 c (fun e p => evz ((applyM (pieceE i e) (gW ps p)).get r) z0)
    (fun q => evz ((gW (upartsOf i ps) q).get r) z0) (fun e p he hp => by simp only [gW_uparts i ps e p he hp])]
  have inner : ∀ e, ∑ p ∈ Finset.range ps.length, c p * evz ((applyM (pieceE i e) (gW ps p)).get r) z0 =
      σ * zco (evalE (pieceE i e) z) r := by
    intro e
    have : ∀ p ∈ Finset.range ps.length, c p * evz ((applyM (pieceE i e) (gW ps p)).get r) z0 =
        c p * evz (comb5 ((pieceE i e).get r) (gW ps p)) z0 := by intro p _; rw [applyM_get _ _ r hr]
    rw [Finset.sum_congr rfl this, comb_trackP ps c z0 z σ htr, zco_evalE _ _ r hr]
  rw [inner 0, inner 1, inner 2]
  have := tri3_coord htri r hr
  linear_combination σ * this

theorem rowsOK_append {r1 r2 : List (List F5)} {c : Nat → ℝ} {n : Nat} {z0 : Zc}
    (h1 : RowsOK r1 c n z0) (h2 : RowsOK r2 c n z0) : RowsOK (r1 ++ r2) c n z0 := by
  intro row hr; rcases List.mem_append.mp hr with h | h
  · exact h1 row h
  · exact h2 row h

theorem iter_add (t : Tri) (j n : Nat) : step^[j + n] t = step^[n] (step^[j] t) := by
  rw [add_comm, Function.iterate_add_apply]

theorem run_exit (t0 : Tri) (ps : List W5) (rows : List (List F5)) (σ j nE nC : Nat)
    (hI : InvP t0 ps rows σ j nE nC) (h2 : brC 2 (zc (step^[j] t0))) :
    ∃ (n i : Nat) (odd : Bool), 1 ≤ n ∧ i ≤ 25 ∧
      InvP t0 (wpartsOf i odd ps) (runRows i odd ps (rows ++ brRowsP 2 ps)) (runSig i odd σ) (j + n) nE nC ∧
      ¬ brC 2 (zc (step^[j + n] t0)) := by
  classical
  obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
  set tj := step^[j] t0 with htj
  set z := zc tj with hz
  have hnp := np_pos ps c hc1
  set np := ps.length with hnpdef
  have hσ : (0 : ℝ) < σ := by have := hI.sig; exact_mod_cast (show 0 < σ by omega)
  have hb : 0 < z.b := by simp only [hz, zc]; exact D13_pos tj hI.ndg
  have hrw' : RowsOK (rows ++ brRowsP 2 ps) c np (zc t0) := rowsOK_append hrw (brRowsP_ok 2 ps c _ _ _ hσ htr h2)
  -- the maximal run
  have hex := run_finite tj hI.srt hI.ndg
  set n := Nat.find hex with hndef
  have hn : ¬ brC 2 (zc (step^[n] tj)) := Nat.find_spec hex
  have hmin : ∀ i < n, brC 2 (zc (step^[i] tj)) := by
    intro i hi; have := Nat.find_min hex hi; push_neg at this; exact this
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso; rw [h0] at hn; exact hn h2
    · exact h0
  set m := n / 2 with hm
  obtain ⟨hu, hAu⟩ := run_even tj hI.srt hI.ndg m (fun i hi => hmin i (by omega))
  have hsu := iter_sorted tj hI.srt hI.ndg (2 * m)
  have hvu := zc_nonneg _ hsu.1
  rw [hu] at hvu
  obtain ⟨i, hi, hrows⟩ := piece_cover z
  obtain ⟨l0, l1, l2, hl0, hl1, hl2, hlsum, htri⟩ := piece_tri z m hb i hi hrows hvu.1 hvu.2.1
  have hS := pieceS_pos i hi
  set S := pieceS i with hSdef
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  set c' := triW np l0 l1 l2 c
  have htrU := track_uparts i ps c (zc t0) z (nAdd z m) σ (S : ℝ) l0 l1 l2 hnp htr htri
  -- weights
  have hc'0 : ∀ q < 3 * np, 0 ≤ c' q := by
    intro q hq
    simp only [c', triW]
    have hc := hc0 (q % np) (Nat.mod_lt _ hnp)
    split_ifs <;> positivity
  have hc'1 : ∑ q ∈ Finset.range (3 * np), c' q = 1 := by
    have := sum3_triW np hnp l0 l1 l2 c (fun _ _ => 1) (fun _ => 1) (fun _ _ _ _ => rfl)
    simp only [mul_one] at this; rw [this, hc1]; linarith
  -- rows of the tripled state (common to both parities, except the previous-step rows)
  have hrep : RowsOK ((rows ++ brRowsP 2 ps).map (repRow np)) c' (3 * np) (zc t0) := by
    intro row hrow
    simp only [List.mem_map] at hrow
    obtain ⟨r0, hr0, rfl⟩ := hrow
    have e := sum3_triW np hnp l0 l1 l2 c (fun _ p => evz (gF r0 p) (zc t0)) (fun q => evz (gF (repRow np r0) q) (zc t0))
      (fun e p he hp => by simp only [gF_rep np hnp r0 e p he hp])
    rw [show ∑ q ∈ Finset.range (3 * np), c' q * evz (gF (repRow np r0) q) (zc t0) =
        ∑ q ∈ Finset.range (3 * np), triW np l0 l1 l2 c q * evz (gF (repRow np r0) q) (zc t0) from rfl, e]
    have := hrw' r0 hr0
    have : (0 : ℝ) ≤ (l0 + l1 + l2) * ∑ p ∈ Finset.range np, c p * evz (gF r0 p) (zc t0) := mul_nonneg (by linarith) this
    linarith
  have hpiece : RowsOK ((pieceRows i).map (fun f => repRow np (ps.map (comb5 f)))) c' (3 * np) (zc t0) := by
    intro row hrow
    simp only [List.mem_map] at hrow
    obtain ⟨g, hg, rfl⟩ := hrow
    have e := sum3_triW np hnp l0 l1 l2 c (fun _ p => evz (gF (ps.map (comb5 g)) p) (zc t0))
      (fun q => evz (gF (repRow np (ps.map (comb5 g))) q) (zc t0))
      (fun e p he hp => by simp only [gF_rep np hnp _ e p he hp])
    rw [show ∑ q ∈ Finset.range (3 * np), c' q * evz (gF (repRow np (ps.map (comb5 g))) q) (zc t0) =
        ∑ q ∈ Finset.range (3 * np), triW np l0 l1 l2 c q * evz (gF (repRow np (ps.map (comb5 g))) q) (zc t0) from rfl, e]
    have hsum : ∑ p ∈ Finset.range np, c p * evz (gF (ps.map (comb5 g)) p) (zc t0) = σ * evz g z := by
      have : ∀ p ∈ Finset.range np, c p * evz (gF (ps.map (comb5 g)) p) (zc t0) = c p * evz (comb5 g (gW ps p)) (zc t0) := by
        intro p hp; rw [gF_map _ _ _ (Finset.mem_range.mp hp)]
      rw [Finset.sum_congr rfl this, comb_trackP ps c _ _ _ htr]
    rw [hsum]
    have := hrows g hg
    have : 0 ≤ (l0 + l1 + l2) * (σ * evz g z) := mul_nonneg (by linarith) (mul_nonneg hσ.le this)
    linarith
  -- parity cases
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- even: the exit is u itself
    have hmk : m = k := by omega
    have hn2 : n = 2 * m := by omega
    have hm1 : 1 ≤ m := by omega
    -- the state one step before the exit
    set v := zc (step^[2 * m - 1] tj)
    have hsv := iter_sorted tj hI.srt hI.ndg (2 * m - 1)
    have hv2 : brC 2 v := hmin _ (by omega)
    have hvu' : brM 2 v = nAdd z m := by
      have := (step_rx _ hsv.1 hsv.2 hv2).1
      rw [← Function.iterate_succ_apply' step (2 * m - 1) tj, show (2 * m - 1).succ = 2 * m by omega, hu] at this
      exact this.symm
    refine ⟨n, i, false, hn1, hi, ⟨?_, ?_, ⟨c', ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [iter_add]; exact (iter_sorted tj hI.srt hI.ndg n).1
    · rw [iter_add]; exact (iter_sorted tj hI.srt hI.ndg n).2
    · simp only [wpartsOf, cond, length_uparts]; exact hc'0
    · simp only [wpartsOf, cond, length_uparts]; exact hc'1
    · simp only [wpartsOf, cond, runSig]
      rw [iter_add, ← htj, hn2, hu]
      have e : ((σ * S.toNat * 1 : Nat) : ℝ) = (S : ℝ) * σ := by
        have hc : ((S.toNat : ℕ) : ℝ) = (S : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hS.le
        push_cast; rw [hc]; ring
      rw [e]; exact htrU
    · simp only [runRows, wpartsOf, prevpartsOf, cond, length_uparts]
      refine rowsOK_append (rowsOK_append (rowsOK_append hrep hpiece) ?_) ?_
      · -- previous step was Rx: parts M2inv ∘ uparts track v with scale Sσ
        have htrV : TrackP ((upartsOf i ps).map (applyM M2inv)) c' (zc t0) v ((S : ℝ) * σ) := by
          intro r hr
          rw [List.length_map, length_uparts]
          have : ∀ q ∈ Finset.range (3 * np), c' q * evz ((gW ((upartsOf i ps).map (applyM M2inv)) q).get r) (zc t0) =
              c' q * evz (comb5 (M2inv.get r) (gW (upartsOf i ps) q)) (zc t0) := by
            intro q hq
            rw [gW_map _ _ _ (by rw [length_uparts]; exact Finset.mem_range.mp hq), applyM_get _ _ r hr]
          rw [Finset.sum_congr rfl this]
          have := comb_trackP (upartsOf i ps) c' (zc t0) (nAdd z m) ((S : ℝ) * σ) htrU (M2inv.get r)
          rw [length_uparts] at this
          rw [this, ← hvu', M2inv_ev v r hr]
        have := brRowsP_ok 2 ((upartsOf i ps).map (applyM M2inv)) c' (zc t0) v ((S : ℝ) * σ) (by positivity) htrV hv2
        simpa [length_uparts] using this
      · -- positivity of the exit state
        intro row hrow
        simp only [List.mem_map, List.mem_range] at hrow
        obtain ⟨r, hr, rfl⟩ := hrow
        have : ∀ q ∈ Finset.range (3 * np), c' q * evz (gF ((upartsOf i ps).map (comb5 (unitF r))) q) (zc t0) =
            c' q * evz (comb5 (unitF r) (gW (upartsOf i ps) q)) (zc t0) := by
          intro q hq; rw [gF_map _ _ _ (by rw [length_uparts]; exact Finset.mem_range.mp hq)]
        rw [Finset.sum_congr rfl this]
        have := comb_trackP (upartsOf i ps) c' (zc t0) (nAdd z m) ((S : ℝ) * σ) htrU (unitF r)
        rw [length_uparts] at this
        rw [this, unitF_ev r hr]
        have hz : 0 ≤ zco (nAdd z m) r := by
          interval_cases r <;> simp only [zco] <;> linarith [hvu.1, hvu.2.1, hvu.2.2.1, hvu.2.2.2.1, hvu.2.2.2.2]
        positivity
    · rw [iter_add, ← htj, hn2, hAu]; exact hI.area
    · simp only [runSig, cond]; have := hI.sig; have : 1 ≤ S.toNat := by omega
      nlinarith
    · rw [iter_add]; exact hn
  · -- odd: one more Rx step after u
    have hn2 : n = 2 * m + 1 := by omega
    have hu2 : brC 2 (nAdd z m) := by have := hmin (2 * m) (by omega); rwa [hu] at this
    have hstep := step_rx _ hsu.1 hsu.2 (by rw [hu]; exact hu2)
    have hw : zc (step^[n] tj) = brM 2 (nAdd z m) := by
      rw [hn2, Function.iterate_succ_apply', hstep.1, hu]
    have htrW : TrackP ((upartsOf i ps).map (stepW 2)) c' (zc t0) (brM 2 (nAdd z m)) (16 * ((S : ℝ) * σ)) :=
      trackP_step 2 (by norm_num) (by norm_num) _ c' _ _ _ htrU
    refine ⟨n, i, true, hn1, hi, ⟨?_, ?_, ⟨c', ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [iter_add]; exact (iter_sorted tj hI.srt hI.ndg n).1
    · rw [iter_add]; exact (iter_sorted tj hI.srt hI.ndg n).2
    · simp only [wpartsOf, cond, List.length_map, length_uparts]; exact hc'0
    · simp only [wpartsOf, cond, List.length_map, length_uparts]; exact hc'1
    · simp only [wpartsOf, cond, runSig]
      rw [iter_add, ← htj, hw]
      have e : ((σ * S.toNat * 16 : Nat) : ℝ) = 16 * ((S : ℝ) * σ) := by
        have hc : ((S.toNat : ℕ) : ℝ) = (S : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hS.le
        push_cast; rw [hc]; ring
      rw [e]; exact htrW
    · simp only [runRows, wpartsOf, prevpartsOf, cond, List.length_map, length_uparts]
      refine rowsOK_append (rowsOK_append (rowsOK_append hrep hpiece) ?_) ?_
      · have := brRowsP_ok 2 (upartsOf i ps) c' (zc t0) (nAdd z m) ((S : ℝ) * σ) (by positivity) htrU hu2
        simpa [length_uparts] using this
      · intro row hrow
        simp only [List.mem_map, List.mem_range] at hrow
        obtain ⟨r, hr, rfl⟩ := hrow
        have : ∀ q ∈ Finset.range (3 * np),
            c' q * evz (gF (((upartsOf i ps).map (stepW 2)).map (comb5 (unitF r))) q) (zc t0) =
            c' q * evz (comb5 (unitF r) (gW ((upartsOf i ps).map (stepW 2)) q)) (zc t0) := by
          intro q hq; rw [gF_map _ _ _ (by rw [List.length_map, length_uparts]; exact Finset.mem_range.mp hq)]
        rw [Finset.sum_congr rfl this]
        have := comb_trackP ((upartsOf i ps).map (stepW 2)) c' (zc t0) _ _ htrW (unitF r)
        rw [List.length_map, length_uparts] at this
        rw [this, unitF_ev r hr]
        have hvw := zc_nonneg _ (iter_sorted tj hI.srt hI.ndg n).1
        rw [hw] at hvw
        have hz : 0 ≤ zco (brM 2 (nAdd z m)) r := by
          interval_cases r <;> simp only [zco] <;> linarith [hvw.1, hvw.2.1, hvw.2.2.1, hvw.2.2.2.1, hvw.2.2.2.2]
        positivity
    · rw [iter_add, ← htj, hn2, Function.iterate_succ_apply', hstep.2, hAu]; exact hI.area
    · simp only [runSig, cond]; have := hI.sig; have : 1 ≤ S.toNat := by omega
      nlinarith
    · rw [iter_add]; exact hn

/-! ### the checker -/

mutual
inductive RT2 where
  | leaf (den : Bool) (rn rd : Nat) (y1 : List (Nat × Nat)) (p1 : List Nat) (y2 : List (Nat × Nat)) (p2 : List Nat)
  | node (c1 c2 c3 c4 c5 c6 c7 c8 c9 : RC2)
inductive RC2 where
  | inf (ys : List (Nat × Nat)) (prs : List Nat)
  | sub (t : RT2)
  | skip
  | run (pcs : RL2)
inductive RL2 where
  | nil
  | cons (c : RC2) (rest : RL2)
end

def leafF (den : Bool) (rn rd : Nat) (fn : F5) (W : W5) (rows : List (List F5)) (ys : List (Nat × Nat)) (p : Nat) : F5 :=
  F5.add (F5.lin (zN rn) (cond den TT L5) (zM rd) (comb5 fn W)) (F5.neg (farkasP rows ys p))

def oddOf (m : Nat) : Bool := Nat.beq (m % 2) 1

mutual
def chkRT2 (b : Box) : RT2 → List W5 → List (List F5) → Nat → Bool → Bool → Nat → Nat → Bool
  | .leaf den rn rd y1 p1 y2 p2, ps, rows, σ, moved, _, nE, nC =>
    moved && Nat.ble 1 rd &&
    allP ps.length (fun p => chk b (gN p1 p) (leafF den rn rd TT (gW ps p) rows y1 p) false) &&
    allP ps.length (fun p => chk b (gN p2 p) (leafF den rn rd L5 (gW ps p) rows y2 p) false) &&
    Nat.ble (2 ^ (8 * nC) * rn ^ 7) (2 ^ (8 * nE) * (rd * σ) ^ 7)
  | .node c1 c2 c3 c4 c5 c6 c7 c8 c9, ps, rows, σ, _, post, nE, nC =>
    chkRC2 b 1 post c1 ps rows σ nE nC && chkRC2 b 2 post c2 ps rows σ nE nC && chkRC2 b 3 post c3 ps rows σ nE nC &&
    chkRC2 b 4 post c4 ps rows σ nE nC && chkRC2 b 5 post c5 ps rows σ nE nC && chkRC2 b 6 post c6 ps rows σ nE nC &&
    chkRC2 b 7 post c7 ps rows σ nE nC && chkRC2 b 8 post c8 ps rows σ nE nC && chkRC2 b 9 post c9 ps rows σ nE nC
def chkRC2 (b : Box) (k : Nat) (post : Bool) : RC2 → List W5 → List (List F5) → Nat → Nat → Nat → Bool
  | .inf ys prs, ps, rows, _, _, _ =>
    allP ps.length (fun p => chk b (gN prs p) (F5.neg (farkasP (rows ++ brRowsP k ps) ys p)) true)
  | .sub t, ps, rows, σ, nE, nC =>
    chkRT2 b t (ps.map (stepW k)) (rows ++ brRowsP k ps) (16 * σ) true false (nE + eUp k) (nC + eDn k)
  | .skip, _, _, _, _, _ => post && Nat.beq k 2
  | .run pcs, ps, rows, σ, nE, nC => Nat.beq k 2 && !post && chkRL2 b pcs 0 ps (rows ++ brRowsP 2 ps) σ nE nC
def pieceOK (b : Box) : RC2 → List W5 → List (List F5) → Nat → Nat → Nat → Bool
  | .inf ys prs, ps, rows, _, _, _ =>
    allP ps.length (fun p => chk b (gN prs p) (F5.neg (farkasP rows ys p)) true)
  | .sub t, ps, rows, σ, nE, nC => chkRT2 b t ps rows σ true true nE nC
  | .skip, _, _, _, _, _ => false
  | .run _, _, _, _, _, _ => false
def chkRL2 (b : Box) : RL2 → Nat → List W5 → List (List F5) → Nat → Nat → Nat → Bool
  | .nil, idx, _, _, _, _, _ => Nat.beq idx 52
  | .cons c rest, idx, ps, rows, σ, nE, nC =>
    pieceOK b c (wpartsOf (idx / 2) (oddOf idx) ps) (runRows (idx / 2) (oddOf idx) ps rows)
      (runSig (idx / 2) (oddOf idx) σ) nE nC && chkRL2 b rest (idx + 1) ps rows σ nE nC
end

/-! ### soundness -/

theorem allP_spec {n : Nat} {f : Nat → Bool} (h : allP n f = true) : ∀ p < n, f p = true := by
  intro p hp; simp only [allP, List.all_eq_true, List.mem_range] at h; exact h p hp

theorem wsum_neg (n : Nat) (c x : Nat → ℝ) (hc : ∀ p < n, 0 ≤ c p) (h1 : ∑ p ∈ Finset.range n, c p = 1)
    (hx : ∀ p < n, x p < 0) : ∑ p ∈ Finset.range n, c p * x p < 0 := by
  have hle : ∀ p ∈ Finset.range n, c p * x p ≤ 0 := fun p hp =>
    mul_nonpos_of_nonneg_of_nonpos (hc p (Finset.mem_range.mp hp)) (hx p (Finset.mem_range.mp hp)).le
  by_contra hcon; push_neg at hcon
  have h0 : ∑ p ∈ Finset.range n, c p * x p = 0 := le_antisymm (Finset.sum_nonpos hle) hcon
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hle).mp h0
  have hc0 : ∀ p ∈ Finset.range n, c p = 0 := by
    intro p hp
    have := hall p hp
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (ne_of_lt (hx p (Finset.mem_range.mp hp)))
  rw [Finset.sum_eq_zero hc0] at h1; norm_num at h1

theorem leaf_goal2 (t0 : Tri) (hn0 : nondeg t0) (j nE nC rn rd σ : Nat) (hj : 1 ≤ j) (hrd : 1 ≤ rd) (hσ : 1 ≤ σ)
    (hT : (rd : ℝ) * σ * Mxz (zc (step^[j] t0)) ≤ rn * Mxz (zc t0))
    (hexp : 2 ^ (8 * nC) * rn ^ 7 ≤ 2 ^ (8 * nE) * (rd * σ) ^ 7)
    (hA : A (step^[j] t0) = (2 : ℝ) ^ nE / 2 ^ nC * A t0)
    (hX : 0 ≤ Mxz (zc (step^[j] t0))) (hY : 0 < Mxz (zc t0)) : Goal t0 := by
  refine ⟨j, hj, ?_⟩
  rw [Mx_eq, Mx_eq, hA]
  set X := Mxz (zc (step^[j] t0)); set Y := Mxz (zc t0)
  set q : ℝ := (rd : ℝ) * σ
  have hq : 0 < q := by have : (1 : ℝ) ≤ rd := by exact_mod_cast hrd
                        have : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
                        positivity
  have hexpR : (2 : ℝ) ^ (8 * nC) * (rn : ℝ) ^ 7 ≤ 2 ^ (8 * nE) * q ^ 7 := by
    have := (Nat.cast_le (α := ℝ)).mpr hexp; push_cast at this; simpa [q] using this
  have h7 : (q * X) ^ 7 ≤ ((rn : ℝ) * Y) ^ 7 := pow_le_pow_left₀ (by positivity) (by simpa [q] using hT) 7
  have hA0 : 0 ≤ A t0 := (A_pos t0 hn0).le
  have key : (2 : ℝ) ^ (8 * nC) * X ^ 7 ≤ 2 ^ (8 * nE) * Y ^ 7 := by
    have e1 : (2 : ℝ) ^ (8 * nC) * q ^ 7 * X ^ 7 ≤ 2 ^ (8 * nC) * (rn : ℝ) ^ 7 * Y ^ 7 := by
      have := mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ 2 ^ (8 * nC))
      calc (2 : ℝ) ^ (8 * nC) * q ^ 7 * X ^ 7 = 2 ^ (8 * nC) * (q * X) ^ 7 := by ring
        _ ≤ 2 ^ (8 * nC) * ((rn : ℝ) * Y) ^ 7 := this
        _ = 2 ^ (8 * nC) * (rn : ℝ) ^ 7 * Y ^ 7 := by ring
    have e2 : (2 : ℝ) ^ (8 * nC) * (rn : ℝ) ^ 7 * Y ^ 7 ≤ 2 ^ (8 * nE) * q ^ 7 * Y ^ 7 :=
      mul_le_mul_of_nonneg_right hexpR (by positivity)
    have e3 := le_trans e1 e2
    have : q ^ 7 * ((2 : ℝ) ^ (8 * nC) * X ^ 7) ≤ q ^ 7 * (2 ^ (8 * nE) * Y ^ 7) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have p8C : (2 : ℝ) ^ (8 * nC) = ((2 : ℝ) ^ nC) ^ 8 := by rw [← pow_mul, mul_comm]
  have p8E : (2 : ℝ) ^ (8 * nE) = ((2 : ℝ) ^ nE) ^ 8 := by rw [← pow_mul, mul_comm]
  rw [p8C, p8E] at key
  rw [show ((2 : ℝ) ^ nE / 2 ^ nC * A t0) ^ 8 * Y ^ 7 = ((2 ^ nE) ^ 8 * A t0 ^ 8 * Y ^ 7) / (2 ^ nC) ^ 8 by
    rw [div_mul_eq_mul_div, div_pow, mul_pow]; ring]
  rw [le_div_iff₀ (by positivity)]
  calc A t0 ^ 8 * X ^ 7 * (2 ^ nC) ^ 8 = A t0 ^ 8 * ((2 ^ nC) ^ 8 * X ^ 7) := by ring
    _ ≤ A t0 ^ 8 * ((2 ^ nE) ^ 8 * Y ^ 7) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = (2 ^ nE) ^ 8 * A t0 ^ 8 * Y ^ 7 := by ring

/-- a certified leaf: `rd σ Mx(z_j) ≤ rn Mx(z0)` from the per-part certificates -/
theorem leaf_bound (b : Box) (t0 : Tri) (hc : InCell b (zc t0)) (ps : List W5) (rows : List (List F5)) (c : Nat → ℝ)
    (z : Zc) (σ : ℝ) (hc0 : ∀ p < ps.length, 0 ≤ c p) (hc1 : ∑ p ∈ Finset.range ps.length, c p = 1)
    (htr : TrackP ps c (zc t0) z σ) (hrw : RowsOK rows c ps.length (zc t0)) (den : Bool) (rn rd : Nat)
    (fn : F5) (y : List (Nat × Nat)) (prs : List Nat)
    (h : allP ps.length (fun p => chk b (gN prs p) (leafF den rn rd fn (gW ps p) rows y p) false) = true) :
    (rd : ℝ) * (σ * evz fn z) ≤ rn * evz (cond den TT L5) (zc t0) := by
  have hp := allP_spec h
  have hpos : ∀ p < ps.length, 0 ≤ evz (leafF den rn rd fn (gW ps p) rows y p) (zc t0) :=
    fun p hpl => (chk_sound b _ _ false (zc t0) hc (hp p hpl)).1
  have hs : 0 ≤ ∑ p ∈ Finset.range ps.length, c p * evz (leafF den rn rd fn (gW ps p) rows y p) (zc t0) :=
    Finset.sum_nonneg (fun p hpm => mul_nonneg (hc0 p (Finset.mem_range.mp hpm)) (hpos p (Finset.mem_range.mp hpm)))
  have hf := farkasP_nonneg rows c ps.length (zc t0) hc0 hrw y
  have e : ∀ p, evz (leafF den rn rd fn (gW ps p) rows y p) (zc t0) =
      (rn : ℝ) * evz (cond den TT L5) (zc t0) - rd * evz (comb5 fn (gW ps p)) (zc t0) - evz (farkasP rows y p) (zc t0) := by
    intro p; simp only [leafF, evz_add, evz_neg, evz_lin, zN_val]; simp [zM, Z.val]; ring
  simp only [e, mul_sub, Finset.sum_sub_distrib] at hs
  have h1 : ∑ p ∈ Finset.range ps.length, c p * ((rn : ℝ) * evz (cond den TT L5) (zc t0)) =
      (rn : ℝ) * evz (cond den TT L5) (zc t0) := by rw [← Finset.sum_mul, hc1, one_mul]
  have h2 : ∑ p ∈ Finset.range ps.length, c p * ((rd : ℝ) * evz (comb5 fn (gW ps p)) (zc t0)) =
      (rd : ℝ) * (σ * evz fn z) := by
    rw [← comb_trackP ps c (zc t0) z σ htr fn, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [h1, h2] at hs; linarith

theorem chkRT2_node (b : Box) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : RC2) (ps : List W5) (rows : List (List F5)) (σ : Nat)
    (moved post : Bool) (nE nC : Nat) (h : chkRT2 b (.node c1 c2 c3 c4 c5 c6 c7 c8 c9) ps rows σ moved post nE nC = true)
    (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) :
    chkRC2 b k post (match k with | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | 5 => c5 | 6 => c6 | 7 => c7 | 8 => c8 | _ => c9)
      ps rows σ nE nC = true := by
  simp only [chkRT2, Bool.and_eq_true] at h
  interval_cases k <;> simp only <;> tauto

theorem inf_false (b : Box) (t0 : Tri) (hc : InCell b (zc t0)) (ps : List W5) (rows : List (List F5)) (c : Nat → ℝ)
    (hc0 : ∀ p < ps.length, 0 ≤ c p) (hc1 : ∑ p ∈ Finset.range ps.length, c p = 1) (hrw : RowsOK rows c ps.length (zc t0))
    (ys : List (Nat × Nat)) (prs : List Nat)
    (h : allP ps.length (fun p => chk b (gN prs p) (F5.neg (farkasP rows ys p)) true) = true) : False := by
  have hp := allP_spec h
  have hneg : ∀ p < ps.length, evz (farkasP rows ys p) (zc t0) < 0 := by
    intro p hpl; have := (chk_sound b _ _ true (zc t0) hc (hp p hpl)).2 rfl; simp only [evz_neg] at this; linarith
  have h1 := wsum_neg ps.length c (fun p => evz (farkasP rows ys p) (zc t0)) hc0 hc1 hneg
  have h2 := farkasP_nonneg rows c ps.length (zc t0) hc0 hrw ys
  linarith

theorem rec2_sound (b : Box) (t0 : Tri) (hs0 : sorted t0) (hn0 : nondeg t0) (hc : InCell b (zc t0)) :
    ∀ (T : RT2) (ps : List W5) (rows : List (List F5)) (σ : Nat) (moved post : Bool) (nE nC j : Nat),
      chkRT2 b T ps rows σ moved post nE nC = true → InvP t0 ps rows σ j nE nC → (moved = true → 1 ≤ j) →
      (post = true → ¬ brC 2 (zc (step^[j] t0))) → Goal t0 := by
  intro T
  induction T using RT2.rec
    (motive_2 := fun C =>
      (∀ (k : Nat) (post : Bool) (ps : List W5) (rows : List (List F5)) (σ nE nC j : Nat), 1 ≤ k → k ≤ 9 →
        chkRC2 b k post C ps rows σ nE nC = true → InvP t0 ps rows σ j nE nC →
        (post = true → ¬ brC 2 (zc (step^[j] t0))) → brC k (zc (step^[j] t0)) →
        zc (step (step^[j] t0)) = brM k (zc (step^[j] t0)) → A (step (step^[j] t0)) = alpha k * A (step^[j] t0) →
        Goal t0) ∧
      (∀ (ps : List W5) (rows : List (List F5)) (σ nE nC j : Nat), pieceOK b C ps rows σ nE nC = true →
        InvP t0 ps rows σ j nE nC → 1 ≤ j → ¬ brC 2 (zc (step^[j] t0)) → Goal t0))
    (motive_3 := fun L =>
      ∀ (idx : Nat) (ps : List W5) (rows : List (List F5)) (σ nE nC j : Nat), chkRL2 b L idx ps rows σ nE nC = true →
        ∀ m, idx ≤ m → m < 52 → ∀ n, 1 ≤ n →
          InvP t0 (wpartsOf (m / 2) (oddOf m) ps) (runRows (m / 2) (oddOf m) ps rows) (runSig (m / 2) (oddOf m) σ)
            (j + n) nE nC → ¬ brC 2 (zc (step^[j + n] t0)) → Goal t0) with
  | leaf den rn rd y1 p1 y2 p2 =>
    intro ps rows σ moved post nE nC j h hI hmv _
    simp only [chkRT2, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨hm, hrd⟩, h1⟩, h2⟩, hexp⟩ := h
    obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
    have b1 := leaf_bound b t0 hc ps rows c _ _ hc0 hc1 htr hrw den rn rd TT y1 p1 h1
    have b2 := leaf_bound b t0 hc ps rows c _ _ hc0 hc1 htr hrw den rn rd L5 y2 p2 h2
    rw [evz_TT] at b1; rw [evz_L5] at b2
    have hv0 := validZ_of t0 hs0 hn0
    have hvj := validZ_of _ hI.srt hI.ndg
    have hden : evz (cond den TT L5) (zc t0) ≤ Mxz (zc t0) := by
      cases den <;> simp only [cond, evz_TT, evz_L5, Mxz] <;> first | exact le_max_left _ _ | exact le_max_right _ _
    have hrn : (0 : ℝ) ≤ rn := Nat.cast_nonneg _
    have hT : (rd : ℝ) * σ * Mxz (zc (step^[j] t0)) ≤ rn * Mxz (zc t0) := by
      have e : (rd : ℝ) * σ * Mxz (zc (step^[j] t0)) =
          max ((rd : ℝ) * (σ * (zc (step^[j] t0)).T)) ((rd : ℝ) * (σ * (5 * (zc (step^[j] t0)).lam))) := by
        simp only [Mxz]
        rw [← mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ rd), ← mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ σ)]
        ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hden hrn
      exact max_le (by linarith) (by linarith)
    exact leaf_goal2 t0 hn0 j nE nC rn rd σ (hmv hm) hrd hI.sig hT hexp hI.area (Mxz_nonneg hvj) (Mxz_pos hv0)
  | node c1 c2 c3 c4 c5 c6 c7 c8 c9 ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9 =>
    intro ps rows σ moved post nE nC j h hI _ hpost
    obtain ⟨k, hk1, hk9, hbr, hM, hA⟩ := step_branch' _ hI.srt hI.ndg
    have hck := chkRT2_node b c1 c2 c3 c4 c5 c6 c7 c8 c9 ps rows σ moved post nE nC h k hk1 hk9
    interval_cases k
    · exact ih1.1 1 post ps rows σ nE nC j (by norm_num) (by norm_num) hck hI hpost hbr hM hA
    · exact ih2.1 2 post ps rows σ nE nC j (by norm_num) (by norm_num) hck hI hpost hbr hM hA
    · exact ih3.1 3 post ps rows σ nE nC j (by norm_num) (by norm_num) hck hI hpost hbr hM hA
    · exact ih4.1 4 post ps rows σ nE nC j (by norm_num) (by norm_num) hck hI hpost hbr hM hA
    · exact ih5.1 5 post ps rows σ nE nC j (by norm_num) (by norm_num) hck hI hpost hbr hM hA
    · exact ih6.1 6 post ps rows σ nE nC j (by norm_num) (by norm_num) hck hI hpost hbr hM hA
    · exact ih7.1 7 post ps rows σ nE nC j (by norm_num) (by norm_num) hck hI hpost hbr hM hA
    · exact ih8.1 8 post ps rows σ nE nC j (by norm_num) (by norm_num) hck hI hpost hbr hM hA
    · exact ih9.1 9 post ps rows σ nE nC j (by norm_num) (by norm_num) hck hI hpost hbr hM hA
  | inf ys prs =>
    refine ⟨?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI _ hbr _ _
      simp only [chkRC2] at h
      obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
      have hσ : (0 : ℝ) < σ := by have := hI.sig; exact_mod_cast (show 0 < σ by omega)
      have hrw' := rowsOK_append hrw (brRowsP_ok k ps c _ _ _ hσ htr hbr)
      exact (inf_false b t0 hc ps _ c hc0 hc1 hrw' ys prs h).elim
    · intro ps rows σ nE nC j h hI _ _
      simp only [pieceOK] at h
      obtain ⟨c, hc0, hc1, _, hrw⟩ := hI.wts
      exact (inf_false b t0 hc ps rows c hc0 hc1 hrw ys prs h).elim
  | sub t ih =>
    refine ⟨?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI _ hbr hM hA
      simp only [chkRC2] at h
      obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
      have hσ : (0 : ℝ) < σ := by have := hI.sig; exact_mod_cast (show 0 < σ by omega)
      have e : step^[j + 1] t0 = step (step^[j] t0) := Function.iterate_succ_apply' step j t0
      apply ih _ _ _ _ _ _ _ (j + 1) h _ (fun _ => by omega) (fun hf => by simp at hf)
      refine ⟨?_, ?_, ⟨c, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [e]; exact step_sorted _ hI.srt hI.ndg
      · rw [e]; exact step_nondeg _ hI.srt hI.ndg
      · rw [List.length_map]; exact hc0
      · rw [List.length_map]; exact hc1
      · rw [e, hM]; push_cast; exact trackP_step k hk1 hk9 ps c _ _ _ htr
      · rw [List.length_map]; exact rowsOK_append hrw (brRowsP_ok k ps c _ _ _ hσ htr hbr)
      · rw [e, hA, hI.area, alpha_e k hk1 hk9, pow_add, pow_add]; ring
      · have := hI.sig; omega
    · intro ps rows σ nE nC j h hI hj hn2
      simp only [pieceOK] at h
      exact ih ps rows σ true true nE nC j h hI (fun _ => hj) (fun _ => hn2)
  | skip =>
    refine ⟨?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI hpost hbr _ _
      simp only [chkRC2, Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨hp, rfl⟩ := h
      exact (hpost hp hbr).elim
    · intro ps rows σ nE nC j h; simp [pieceOK] at h
  | run pcs ih =>
    refine ⟨?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI _ hbr _ _
      simp only [chkRC2, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at h
      obtain ⟨⟨rfl, _⟩, hL⟩ := h
      obtain ⟨n, i, odd, hn1, hi, hI', hn2⟩ := run_exit t0 ps rows σ j nE nC hI hbr
      set m := 2 * i + cond odd 1 0 with hm
      have hmi : m / 2 = i := by cases odd <;> simp [hm, cond] <;> omega
      have hmod : m % 2 = cond odd 1 0 := by cases odd <;> simp only [hm, cond] <;> omega
      have hmo : oddOf m = odd := by simp only [oddOf, hmod]; cases odd <;> rfl
      apply ih 0 ps (rows ++ brRowsP 2 ps) σ nE nC j hL m (Nat.zero_le _) (by cases odd <;> simp [hm, cond] <;> omega) n hn1
      · rw [hmi, hmo]; exact hI'
      · exact hn2
    · intro ps rows σ nE nC j h; simp [pieceOK] at h
  | nil =>
    rename_i idx ps rows σ nE nC j h m hm1 hm2 _ _ _ _
    simp only [chkRL2, Nat.beq_eq] at h; omega
  | cons c rest ihc ihr =>
    rename_i idx ps rows σ nE nC j h m hm1 hm2 n hn1 hI hn2
    simp only [chkRL2, Bool.and_eq_true] at h
    rcases eq_or_lt_of_le hm1 with heq | hlt
    · subst heq
      exact ihc.2 _ _ _ nE nC (j + n) h.1 hI (by omega) hn2
    · exact ihr (idx + 1) ps rows σ nE nC j h.2 m hlt hm2 n hn1 hI hn2

/-! ### cells, walk, main theorem -/

theorem goal_of_chk2 (b : Box) (T : RT2) (h : chkRT2 b T [W5.id] [] 1 false false 0 0 = true) (t0 : Tri)
    (hs0 : sorted t0) (hn0 : nondeg t0) (hc : InCell b (zc t0)) : Goal t0 := by
  apply rec2_sound b t0 hs0 hn0 hc T [W5.id] [] 1 false false 0 0 0 h _ (fun hf => by simp at hf) (fun hf => by simp at hf)
  refine ⟨hs0, hn0, ⟨fun _ => 1, fun _ _ => by norm_num, by simp, ?_, fun row hr => by simp at hr⟩, by simp, le_refl _⟩
  intro r hr
  have := tracks_id (zc t0) r hr
  simp only [List.length_singleton, Finset.sum_range_one, one_mul, Nat.cast_one, Function.iterate_zero, id] at this ⊢
  simpa [gW, nth] using this.symm

inductive LC2 where
  | hole (x : Nat)
  | tree (t : RT2)

def leafOK2 (b : Box) : LC2 → Bool
  | .hole x => chkHole b x
  | .tree t => bdOK b && chkRT2 b t [W5.id] [] 1 false false 0 0

def walkR2 : KT → Box → List LC2 → Option (List LC2)
  | .leaf _ _, b, c :: cs => cond (leafOK2 b c) (some cs) none
  | .leaf _ _, _, [] => none
  | .node d v _ l r, b, cs =>
    match walkR2 l (b.setHi d v) cs with
    | none => none
    | some cs' => walkR2 r (b.setLo d v) cs'

theorem walkR2_ok (z : Zc) : ∀ (t : KT) (b : Box) (cs rest : List LC2), walkR2 t b cs = some rest →
    ∃ c, leafOK2 (look z t b).2.2 c = true := by
  intro t
  induction t with
  | leaf n h =>
    intro b cs rest hw
    rcases cs with _ | ⟨c, cs⟩
    · simp [walkR2] at hw
    · refine ⟨c, ?_⟩
      simp only [walkR2] at hw
      simp only [look]
      cases hc : leafOK2 b c
      · rw [hc] at hw; simp at hw
      · rfl
  | node d v mx l r ihl ihr =>
    intro b cs rest hw
    simp only [walkR2] at hw
    cases hl : walkR2 l (b.setHi d v) cs with
    | none => rw [hl] at hw; simp at hw
    | some cs' =>
      rw [hl] at hw
      simp only [look]
      split_ifs
      · exact ihl _ _ _ hl
      · exact ihr _ _ _ hw

theorem walkR2_append : ∀ (t : KT) (b : Box) (cs rest extra : List LC2), walkR2 t b cs = some rest →
    walkR2 t b (cs ++ extra) = some (rest ++ extra) := by
  intro t
  induction t with
  | leaf n h =>
    intro b cs rest extra hw
    rcases cs with _ | ⟨c, cs⟩
    · simp [walkR2] at hw
    · cases hc : leafOK2 b c
      · simp [walkR2, hc] at hw
      · simp only [walkR2, hc, cond, Option.some.injEq] at hw
        simp only [List.cons_append, walkR2, hc, cond, hw]
  | node d v mx l r ihl ihr =>
    intro b cs rest extra hw
    simp only [walkR2] at hw ⊢
    cases hl : walkR2 l (b.setHi d v) cs with
    | none => rw [hl] at hw; simp at hw
    | some cs' =>
      rw [hl] at hw
      rw [ihl _ _ _ _ hl]
      exact ihr _ _ _ _ hw

theorem walkR2_node (d v mx : Nat) (l r : KT) (b : Box) (cl cr : List LC2)
    (hl : walkR2 l (b.setHi d v) cl = some []) (hr : walkR2 r (b.setLo d v) cr = some []) :
    walkR2 (.node d v mx l r) b (cl ++ cr) = some [] := by
  simp only [walkR2]
  rw [walkR2_append _ _ _ _ _ hl]
  simpa using hr

theorem recovery_of_cert2 (kt : KT) (cs : List LC2) (hw : walkR2 kt rootBox cs = some []) :
    Recovery 169869312 := by
  intro t hs hn hfar
  have hv := validZ_of t hs hn
  have hst := strip_of_far t hs hn hfar
  set z := zc t
  set L := look z kt rootBox with hL
  have hLbox : inBox G L.2.2 z := look_mem z kt rootBox (inBox_root hv)
  obtain ⟨c, hc⟩ := walkR2_ok z kt rootBox cs [] hw
  rw [← hL] at hc
  cases c with
  | hole x =>
    exact (hole_sound _ x hc z hv.lam (cons_of_box hv hLbox (strip_of_s hv hst hLbox))).elim
  | tree T =>
    simp only [leafOK2, bdOK, Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hT⟩ := hc
    have hcell : InCell L.2.2 z := inCell_of hv hLbox (strip_of_s hv hst hLbox)
      ⟨le_trans h1 h2, h2, le_trans h3 h4, h4⟩
    exact goal_of_chk2 L.2.2 T hT t hs hn hcell

/-- the conditional main theorem (recovery trees with symbolic Rx runs) -/
theorem nm_converges_of_reccert2 (kt : KT) (cs : List LC2) (hw : walkR2 kt rootBox cs = some [])
    (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :
    Filter.Tendsto (fun k => (traj t0 k).p1) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p2) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p3) Filter.atTop (nhds 0) :=
  nm_converges_of_recovery 169869312 (recovery_of_cert2 kt cs hw) t0 h0 hn0

end NMR2

#print axioms NMR2.nm_converges_of_reccert2
