import Mathlib

/-!
# Nelder–Mead on f(x,y) = x² + y²

Algorithm NM of Lagarias–Reeds–Wright–Wright (SIAM J. Optim. 9 (1998)), standard coefficients
ρ = 1, χ = 2, γ = 1/2, σ = 1/2, with their tie-breaking rules, in dimension 2.
A state is an ordered triangle (p1, p2, p3) with f p1 ≤ f p2 ≤ f p3.
-/

noncomputable section
namespace NM

abbrev Pt := ℝ × ℝ

/-- the objective -/
def f (p : Pt) : ℝ := p.1 ^ 2 + p.2 ^ 2

@[ext] structure Tri where
  p1 : Pt
  p2 : Pt
  p3 : Pt

/-- affine combination `a•x + b•y + c•z` (coordinates) -/
def comb (a b c : ℝ) (x y z : Pt) : Pt := (a * x.1 + b * y.1 + c * z.1, a * x.2 + b * y.2 + c * z.2)

/-- insert the new vertex `v` next to the kept vertices `p1, p2` (f p1 ≤ f p2), LRWW non-shrink rule:
the new vertex gets the highest index consistent with the ordering. -/
def insert (p1 p2 v : Pt) : Tri :=
  if f v < f p1 then ⟨v, p1, p2⟩ else if f v < f p2 then ⟨p1, v, p2⟩ else ⟨p1, p2, v⟩

/-- stable sort of three points by value (earlier arguments win ties) -/
def sort3 (x y z : Pt) : Tri :=
  if f y < f x then
    (if f z < f y then ⟨z, y, x⟩ else if f z < f x then ⟨y, z, x⟩ else ⟨y, x, z⟩)
  else
    (if f z < f x then ⟨z, x, y⟩ else if f z < f y then ⟨x, z, y⟩ else ⟨x, y, z⟩)

/-- LRWW shrink step: x1 is kept, the others move halfway to x1; reorder (x1 first on ties). -/
def shrinkTri (p1 p2 p3 : Pt) : Tri :=
  sort3 p1 (comb (1/2) (1/2) 0 p1 p2 p3) (comb (1/2) 0 (1/2) p1 p2 p3)

/-- one iteration of Algorithm NM -/
def step (t : Tri) : Tri :=
  let r := comb 1 1 (-1) t.p1 t.p2 t.p3
  if f r < f t.p1 then
    let e := comb (3/2) (3/2) (-2) t.p1 t.p2 t.p3
    if f e < f r then ⟨e, t.p1, t.p2⟩ else ⟨r, t.p1, t.p2⟩
  else if f r < f t.p2 then ⟨t.p1, r, t.p2⟩
  else if f r < f t.p3 then
    let oc := comb (3/4) (3/4) (-1/2) t.p1 t.p2 t.p3
    if f oc ≤ f r then insert t.p1 t.p2 oc else shrinkTri t.p1 t.p2 t.p3
  else
    let ic := comb (1/4) (1/4) (1/2) t.p1 t.p2 t.p3
    if f ic < f t.p3 then insert t.p1 t.p2 ic else shrinkTri t.p1 t.p2 t.p3

def sorted (t : Tri) : Prop := f t.p1 ≤ f t.p2 ∧ f t.p2 ≤ f t.p3

/-- twice the signed area -/
def area2 (t : Tri) : ℝ :=
  (t.p2.1 - t.p1.1) * (t.p3.2 - t.p1.2) - (t.p3.1 - t.p1.1) * (t.p2.2 - t.p1.2)

def nondeg (t : Tri) : Prop := area2 t ≠ 0

def dist2 (p q : Pt) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The key identity: for weights summing to 1,
f(a x + b y + c z) = a f x + b f y + c f z − (ab|x−y|² + ac|x−z|² + bc|y−z|²). -/
theorem f_comb (a b c : ℝ) (h : a + b + c = 1) (x y z : Pt) :
    f (comb a b c x y z) = a * f x + b * f y + c * f z
      - (a * b * dist2 x y + a * c * dist2 x z + b * c * dist2 y z) := by
  have hc : c = 1 - a - b := by linarith
  subst hc
  simp only [f, comb, dist2]
  ring

theorem dist2_comb (a b c : ℝ) (h : a + b + c = 1) (x y z w : Pt) :
    dist2 (comb a b c x y z) w = a * dist2 x w + b * dist2 y w + c * dist2 z w
      - (a * b * dist2 x y + a * c * dist2 x z + b * c * dist2 y z) := by
  have hc : c = 1 - a - b := by linarith
  subst hc
  simp only [comb, dist2]
  ring



/-! ## The linear coordinates of a state -/

def D12 (t : Tri) : ℝ := dist2 t.p1 t.p2
def D13 (t : Tri) : ℝ := dist2 t.p1 t.p3
def D23 (t : Tri) : ℝ := dist2 t.p2 t.p3

theorem dist2_comm (p q : Pt) : dist2 p q = dist2 q p := by simp only [dist2]; ring

theorem dist2_nonneg (p q : Pt) : 0 ≤ dist2 p q := by unfold dist2; positivity

/-- value of the reflection point -/
theorem f_refl (t : Tri) : f (comb 1 1 (-1) t.p1 t.p2 t.p3)
    = f t.p1 + f t.p2 - f t.p3 + (D13 t + D23 t - D12 t) := by
  rw [f_comb 1 1 (-1) (by norm_num)]; simp only [D12, D13, D23]; ring

theorem f_exp (t : Tri) : f (comb (3/2) (3/2) (-2) t.p1 t.p2 t.p3)
    = 3/2 * f t.p1 + 3/2 * f t.p2 - 2 * f t.p3 - (9/4 * D12 t - 3 * D13 t - 3 * D23 t) := by
  rw [f_comb _ _ _ (by norm_num)]; simp only [D12, D13, D23]; ring

theorem f_oc (t : Tri) : f (comb (3/4) (3/4) (-1/2) t.p1 t.p2 t.p3)
    = 3/4 * f t.p1 + 3/4 * f t.p2 - 1/2 * f t.p3 - (9/16 * D12 t - 3/8 * D13 t - 3/8 * D23 t) := by
  rw [f_comb _ _ _ (by norm_num)]; simp only [D12, D13, D23]; ring

theorem f_ic (t : Tri) : f (comb (1/4) (1/4) (1/2) t.p1 t.p2 t.p3)
    = 1/4 * f t.p1 + 1/4 * f t.p2 + 1/2 * f t.p3 - (1/16 * D12 t + 1/8 * D13 t + 1/8 * D23 t) := by
  rw [f_comb _ _ _ (by norm_num)]; simp only [D12, D13, D23]; ring

/-- nondegenerate triangles have positive squared sides -/
theorem D12_pos (t : Tri) (h : nondeg t) : 0 < D12 t := by
  unfold nondeg area2 at h; unfold D12 dist2
  by_contra hc
  have h1 : t.p1.1 - t.p2.1 = 0 := by nlinarith [sq_nonneg (t.p1.1 - t.p2.1), sq_nonneg (t.p1.2 - t.p2.2)]
  have h2 : t.p1.2 - t.p2.2 = 0 := by nlinarith [sq_nonneg (t.p1.1 - t.p2.1), sq_nonneg (t.p1.2 - t.p2.2)]
  apply h; have : t.p2.1 - t.p1.1 = 0 := by linarith
  have : t.p2.2 - t.p1.2 = 0 := by linarith
  simp [*]

/-- outside contraction is always accepted -/
theorem oc_le (t : Tri) (hs : sorted t) (hr : f t.p2 ≤ f (comb 1 1 (-1) t.p1 t.p2 t.p3)) :
    f (comb (3/4) (3/4) (-1/2) t.p1 t.p2 t.p3) ≤ f (comb 1 1 (-1) t.p1 t.p2 t.p3) := by
  rw [f_refl] at hr ⊢; rw [f_oc]
  have := dist2_nonneg t.p1 t.p2
  unfold sorted at hs; simp only [D12] at *
  nlinarith

/-- inside contraction is always accepted -/
theorem ic_lt (t : Tri) (hs : sorted t) (hn : nondeg t) :
    f (comb (1/4) (1/4) (1/2) t.p1 t.p2 t.p3) < f t.p3 := by
  rw [f_ic]
  have h1 := D12_pos t hn
  have := dist2_nonneg t.p1 t.p3; have := dist2_nonneg t.p2 t.p3
  unfold sorted at hs; simp only [D13, D23] at *
  nlinarith



/-! ## Case analysis of one step -/

abbrev rP (t : Tri) : Pt := comb 1 1 (-1) t.p1 t.p2 t.p3
abbrev eP (t : Tri) : Pt := comb (3/2) (3/2) (-2) t.p1 t.p2 t.p3
abbrev ocP (t : Tri) : Pt := comb (3/4) (3/4) (-1/2) t.p1 t.p2 t.p3
abbrev icP (t : Tri) : Pt := comb (1/4) (1/4) (1/2) t.p1 t.p2 t.p3

theorem step_cases (t : Tri) (hs : sorted t) (hn : nondeg t) :
    (f (rP t) < f t.p1 ∧ f (eP t) < f (rP t) ∧ step t = ⟨eP t, t.p1, t.p2⟩) ∨
    (f (rP t) < f t.p1 ∧ f (rP t) ≤ f (eP t) ∧ step t = ⟨rP t, t.p1, t.p2⟩) ∨
    (f t.p1 ≤ f (rP t) ∧ f (rP t) < f t.p2 ∧ step t = ⟨t.p1, rP t, t.p2⟩) ∨
    (f t.p2 ≤ f (rP t) ∧ f (rP t) < f t.p3 ∧ step t = insert t.p1 t.p2 (ocP t)) ∨
    (f t.p3 ≤ f (rP t) ∧ step t = insert t.p1 t.p2 (icP t)) := by
  unfold step
  by_cases h1 : f (rP t) < f t.p1
  · by_cases h2 : f (eP t) < f (rP t)
    · left; exact ⟨h1, h2, by simp [h1, h2]⟩
    · right; left; exact ⟨h1, not_lt.mp h2, by simp [h1, h2]⟩
  · by_cases h3 : f (rP t) < f t.p2
    · right; right; left; exact ⟨not_lt.mp h1, h3, by simp [h1, h3]⟩
    · by_cases h4 : f (rP t) < f t.p3
      · right; right; right; left
        have hoc := oc_le t hs (not_lt.mp h3)
        refine ⟨not_lt.mp h3, h4, ?_⟩
        simp only [h1, h3, h4, ite_false, ite_true]
        exact if_pos hoc
      · right; right; right; right
        have hic := ic_lt t hs hn
        refine ⟨not_lt.mp h4, ?_⟩
        simp only [h1, h3, h4, ite_false]
        exact if_pos hic

theorem insert_sorted (p1 p2 v : Pt) (h : f p1 ≤ f p2) : sorted (insert p1 p2 v) := by
  unfold insert sorted
  split_ifs with h1 h2
  · exact ⟨h1.le, h⟩
  · exact ⟨not_lt.mp h1, h2.le⟩
  · exact ⟨h, not_lt.mp h2⟩


/-! ## Area, sortedness, values -/

def A (t : Tri) : ℝ := |area2 t|

theorem A_insert (p1 p2 v : Pt) : A (insert p1 p2 v) = A ⟨p1, p2, v⟩ := by
  unfold insert A area2
  split_ifs
  · congr 1; ring
  · rw [← abs_neg]; congr 1; ring
  · rfl

theorem A_step (t : Tri) (hs : sorted t) (hn : nondeg t) :
    A (step t) = 2 * A t ∨ A (step t) = A t ∨ A (step t) = 1/2 * A t := by
  rcases step_cases t hs hn with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ <;> rw [h]
  · left; unfold A area2; rw [show (2:ℝ) = |(-2:ℝ)| by norm_num, ← abs_mul]; congr 1; simp only [eP, comb]; ring
  · right; left; unfold A area2; rw [← abs_neg]; congr 1; simp only [rP, comb]; ring
  · right; left; unfold A area2; congr 1; simp only [rP, comb]; ring
  · right; right; rw [A_insert]; unfold A area2
    rw [show (1/2:ℝ) = |(-1/2:ℝ)| by norm_num, ← abs_mul]; congr 1; simp only [ocP, comb]; ring
  · right; right; rw [A_insert]; unfold A area2
    rw [show (1/2:ℝ) = |(1/2:ℝ)| by norm_num, ← abs_mul]; congr 1; simp only [icP, comb]; ring

theorem A_pos (t : Tri) (hn : nondeg t) : 0 < A t := abs_pos.mpr hn

theorem step_nondeg (t : Tri) (hs : sorted t) (hn : nondeg t) : nondeg (step t) := by
  have h := A_pos t hn
  have : 0 < A (step t) := by rcases A_step t hs hn with h' | h' | h' <;> rw [h'] <;> positivity
  exact abs_pos.mp this

theorem step_sorted (t : Tri) (hs : sorted t) (hn : nondeg t) : sorted (step t) := by
  have hs' := hs
  unfold sorted at hs
  rcases step_cases t hs' hn with ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h⟩ <;> rw [h]
  · exact ⟨by simp only []; linarith, hs.1⟩
  · exact ⟨by simp only []; linarith, hs.1⟩
  · exact ⟨h1, h2.le⟩
  · exact insert_sorted _ _ _ hs.1
  · exact insert_sorted _ _ _ hs.1

/-- every value of the new state is at most the corresponding old value, and the
new point has value below the old worst -/
theorem step_vals (t : Tri) (hs : sorted t) (hn : nondeg t) :
    f (step t).p1 ≤ f t.p1 ∧ f (step t).p2 ≤ f t.p2 ∧ f (step t).p3 ≤ f t.p3 := by
  have hs' := hs
  unfold sorted at hs
  have hoc : ∀ v, f v ≤ f t.p3 → f (insert t.p1 t.p2 v).p1 ≤ f t.p1 ∧ f (insert t.p1 t.p2 v).p2 ≤ f t.p2 ∧
      f (insert t.p1 t.p2 v).p3 ≤ f t.p3 := by
    intro v hv; unfold insert; split_ifs with a b
    · exact ⟨a.le, hs.1, hs.2⟩
    · exact ⟨le_rfl, b.le, hs.2⟩
    · exact ⟨le_rfl, le_rfl, hv⟩
  rcases step_cases t hs' hn with ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h⟩ <;> rw [h]
  · exact ⟨by simp only []; linarith, hs.1, hs.2⟩
  · exact ⟨h1.le, hs.1, hs.2⟩
  · exact ⟨le_rfl, h2.le, hs.2⟩
  · exact hoc _ (le_trans (oc_le t hs' h1) h2.le)
  · exact hoc _ (ic_lt t hs' hn).le

/-! ## Sum of squared sides -/

def lam (t : Tri) : ℝ := D12 t + D13 t + D23 t

theorem lam_refl1 (t : Tri) : lam ⟨rP t, t.p1, t.p2⟩ = lam t := by
  simp only [lam, D12, D13, D23, rP, comb, dist2]; ring
theorem lam_refl2 (t : Tri) : lam ⟨t.p1, rP t, t.p2⟩ = lam t := by
  simp only [lam, D12, D13, D23, rP, comb, dist2]; ring
theorem lam_exp (t : Tri) : lam ⟨eP t, t.p1, t.p2⟩ = -1/2 * D12 t + 4 * (D13 t + D23 t) := by
  simp only [lam, D12, D13, D23, eP, comb, dist2]; ring
theorem lam_insert (p1 p2 v : Pt) : lam (insert p1 p2 v) = lam ⟨p1, p2, v⟩ := by
  unfold insert; split_ifs <;> simp only [lam, D12, D13, D23, dist2] <;> ring
theorem lam_oc (t : Tri) : lam ⟨t.p1, t.p2, ocP t⟩ = 11/8 * D12 t + 1/4 * (D13 t + D23 t) := by
  simp only [lam, D12, D13, D23, ocP, comb, dist2]; ring
theorem lam_ic (t : Tri) : lam ⟨t.p1, t.p2, icP t⟩ = 11/8 * D12 t + 1/4 * (D13 t + D23 t) := by
  simp only [lam, D12, D13, D23, icP, comb, dist2]; ring
theorem lam_nonneg (t : Tri) : 0 ≤ lam t := by
  unfold lam D12 D13 D23; have := dist2_nonneg t.p1 t.p2; have := dist2_nonneg t.p1 t.p3
  have := dist2_nonneg t.p2 t.p3; linarith

/-! ## Trajectories and limits -/

def traj (t0 : Tri) (k : ℕ) : Tri := step^[k] t0

theorem traj_succ (t0 : Tri) (k : ℕ) : traj t0 (k+1) = step (traj t0 k) :=
  Function.iterate_succ_apply' step k t0

theorem traj_inv (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) (k : ℕ) :
    sorted (traj t0 k) ∧ nondeg (traj t0 k) := by
  induction k with
  | zero => exact ⟨h0, hn0⟩
  | succ k ih => rw [traj_succ]; exact ⟨step_sorted _ ih.1 ih.2, step_nondeg _ ih.1 ih.2⟩

theorem f_nonneg (p : Pt) : 0 ≤ f p := by unfold f; positivity

section limits
variable (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0)
include h0 hn0

theorem v1_anti : Antitone (fun k => f (traj t0 k).p1) := by
  apply antitone_nat_of_succ_le; intro k; rw [traj_succ]
  have := traj_inv t0 h0 hn0 k; exact (step_vals _ this.1 this.2).1
theorem v2_anti : Antitone (fun k => f (traj t0 k).p2) := by
  apply antitone_nat_of_succ_le; intro k; rw [traj_succ]
  have := traj_inv t0 h0 hn0 k; exact (step_vals _ this.1 this.2).2.1
theorem v3_anti : Antitone (fun k => f (traj t0 k).p3) := by
  apply antitone_nat_of_succ_le; intro k; rw [traj_succ]
  have := traj_inv t0 h0 hn0 k; exact (step_vals _ this.1 this.2).2.2

end limits

theorem tendsto_of_anti {v : ℕ → ℝ} (hv : Antitone v) (hb : ∀ k, 0 ≤ v k) :
    Filter.Tendsto v Filter.atTop (nhds (⨅ k, v k)) :=
  tendsto_atTop_ciInf hv ⟨0, by rintro _ ⟨k, rfl⟩; exact hb k⟩

theorem iInf_le' {v : ℕ → ℝ} (hb : ∀ k, 0 ≤ v k) (k : ℕ) : (⨅ j, v j) ≤ v k :=
  ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact hb j⟩ k

/-! ## Lemma B1: the two worst limits agree -/

/-- if the new worst value is not below the old second value, the step is a contraction
that only moves `p3` -/
theorem step_keep12 (t : Tri) (hs : sorted t) (hn : nondeg t)
    (h : f t.p2 < f (step t).p3) :
    step t = ⟨t.p1, t.p2, ocP t⟩ ∨ step t = ⟨t.p1, t.p2, icP t⟩ := by
  rcases step_cases t hs hn with ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨-, he⟩ <;>
    rw [he] at h ⊢
  · exact absurd h (lt_irrefl _)
  · exact absurd h (lt_irrefl _)
  · exact absurd h (lt_irrefl _)
  · left; unfold insert at h ⊢; split_ifs at h ⊢ <;> first | rfl | exact absurd h (lt_irrefl _)
  · right; unfold insert at h ⊢; split_ifs at h ⊢ <;> first | rfl | exact absurd h (lt_irrefl _)

def mid (p q : Pt) : Pt := ((p.1 + q.1)/2, (p.2 + q.2)/2)

theorem contr_dist (t : Tri) :
    dist2 (ocP t) (mid t.p1 t.p2) = 1/4 * dist2 t.p3 (mid t.p1 t.p2) ∧
    dist2 (icP t) (mid t.p1 t.p2) = 1/4 * dist2 t.p3 (mid t.p1 t.p2) := by
  constructor <;> simp only [ocP, icP, comb, mid, dist2] <;> ring

theorem f_near (p c : Pt) : |f p - f c| ≤ 4 * (|c.1| + |c.2|) * (|p.1 - c.1| + |p.2 - c.2|) + dist2 p c := by
  have e : f p - f c = 2 * (c.1 * (p.1 - c.1) + c.2 * (p.2 - c.2)) + dist2 p c := by
    simp only [f, dist2]; ring
  rw [e]
  have hd := dist2_nonneg p c
  have h1 : |c.1 * (p.1 - c.1)| ≤ (|c.1| + |c.2|) * (|p.1 - c.1| + |p.2 - c.2|) := by
    rw [abs_mul]; apply mul_le_mul <;> first | positivity | linarith [abs_nonneg c.2, abs_nonneg (p.2 - c.2)]
  have h2 : |c.2 * (p.2 - c.2)| ≤ (|c.1| + |c.2|) * (|p.1 - c.1| + |p.2 - c.2|) := by
    rw [abs_mul]; apply mul_le_mul <;> first | positivity | linarith [abs_nonneg c.1, abs_nonneg (p.1 - c.1)]
  have h3 := abs_add_le (c.1 * (p.1 - c.1)) (c.2 * (p.2 - c.2))
  have h4 := abs_add_le (2 * (c.1 * (p.1 - c.1) + c.2 * (p.2 - c.2))) (dist2 p c)
  rw [abs_mul, abs_of_nonneg hd, abs_two] at h4
  linarith

theorem coord_le_dist (p c : Pt) : |p.1 - c.1| + |p.2 - c.2| ≤ 2 * Real.sqrt (dist2 p c) := by
  have h1 : |p.1 - c.1| ≤ Real.sqrt (dist2 p c) := by
    rw [← Real.sqrt_sq_eq_abs]; apply Real.sqrt_le_sqrt; unfold dist2; nlinarith [sq_nonneg (p.2 - c.2)]
  have h2 : |p.2 - c.2| ≤ Real.sqrt (dist2 p c) := by
    rw [← Real.sqrt_sq_eq_abs]; apply Real.sqrt_le_sqrt; unfold dist2; nlinarith [sq_nonneg (p.1 - c.1)]
  linarith

section B1
variable (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0)
include h0 hn0

theorem B1 : (⨅ k, f (traj t0 k).p2) = ⨅ k, f (traj t0 k).p3 := by
  set a2 := ⨅ k, f (traj t0 k).p2
  set a3 := ⨅ k, f (traj t0 k).p3
  have hb2 : ∀ k, 0 ≤ f (traj t0 k).p2 := fun k => f_nonneg _
  have hb3 : ∀ k, 0 ≤ f (traj t0 k).p3 := fun k => f_nonneg _
  have T2 := tendsto_of_anti (v2_anti t0 h0 hn0) hb2
  have T3 := tendsto_of_anti (v3_anti t0 h0 hn0) hb3
  have hle : a2 ≤ a3 := le_of_tendsto_of_tendsto' T2 T3 (fun k => (traj_inv t0 h0 hn0 k).1.2)
  by_contra hne
  have hlt : a2 < a3 := lt_of_le_of_ne hle hne
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp (T2.eventually (Iio_mem_nhds hlt))
  -- from k0 on, only p3 moves
  have key : ∀ k ≥ k0, traj t0 (k+1) = ⟨(traj t0 k).p1, (traj t0 k).p2, ocP (traj t0 k)⟩ ∨
      traj t0 (k+1) = ⟨(traj t0 k).p1, (traj t0 k).p2, icP (traj t0 k)⟩ := by
    intro k hk
    have inv := traj_inv t0 h0 hn0 k
    rw [traj_succ]
    apply step_keep12 _ inv.1 inv.2
    have := iInf_le' hb3 (k+1); rw [traj_succ] at this
    have := hk0 k hk
    linarith
  set P := (traj t0 k0).p1
  set Q := (traj t0 k0).p2
  set c := mid P Q
  have const : ∀ j, (traj t0 (k0+j)).p1 = P ∧ (traj t0 (k0+j)).p2 = Q ∧
      dist2 (traj t0 (k0+j)).p3 c = (1/4)^j * dist2 (traj t0 k0).p3 c := by
    intro j
    induction j with
    | zero => simp [P, Q]
    | succ j ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hk := key (k0 + j) (Nat.le_add_right _ _)
      rw [show k0 + (j+1) = k0 + j + 1 by ring]
      have cd := contr_dist (traj t0 (k0+j))
      rw [h1, h2] at cd
      rcases hk with hk | hk <;> rw [hk] <;> refine ⟨h1, h2, ?_⟩ <;> simp only []
      · rw [cd.1, h3]; ring
      · rw [cd.2, h3]; ring
  -- limits
  have hQ : a2 = f Q := by
    have : Filter.Tendsto (fun k => f (traj t0 k).p2) Filter.atTop (nhds (f Q)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop k0] with k hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [(const j).2.1]
    exact tendsto_nhds_unique T2 this
  have hc : a3 = f c := by
    have : Filter.Tendsto (fun k => f (traj t0 k).p3) Filter.atTop (nhds (f c)) := by
      set e0 := dist2 (traj t0 k0).p3 c
      set M := |c.1| + |c.2|
      have hg : Filter.Tendsto (fun j : ℕ => 4 * M * (2 * Real.sqrt ((1/4:ℝ)^j * e0)) + (1/4:ℝ)^j * e0)
          Filter.atTop (nhds (4 * M * (2 * Real.sqrt (0 * e0)) + 0 * e0)) := by
        have hp : Filter.Tendsto (fun j : ℕ => (1/4:ℝ)^j) Filter.atTop (nhds 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        exact ((hp.mul_const e0).sqrt.const_mul 2 |>.const_mul (4*M)).add (hp.mul_const e0)
      simp only [zero_mul, Real.sqrt_zero, mul_zero, add_zero] at hg
      rw [← Filter.tendsto_add_atTop_iff_nat k0]
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero (fun j => norm_nonneg _) _ hg
      intro j
      rw [Real.norm_eq_abs]
      have hd := (const j).2.2
      calc |f (traj t0 (j + k0)).p3 - f c| ≤ 4 * M * (|(traj t0 (j + k0)).p3.1 - c.1| + |(traj t0 (j + k0)).p3.2 - c.2|)
            + dist2 (traj t0 (j + k0)).p3 c := f_near _ _
        _ ≤ 4 * M * (2 * Real.sqrt ((1/4:ℝ)^j * e0)) + (1/4:ℝ)^j * e0 := by
            rw [add_comm j k0, hd]
            have := coord_le_dist (traj t0 (k0 + j)).p3 c
            rw [hd] at this
            have hM : 0 ≤ M := by positivity
            nlinarith
    exact tendsto_nhds_unique T3 this
  have hfc : f c < f Q := by
    have hD := D12_pos (traj t0 k0) (traj_inv t0 h0 hn0 k0).2
    have hs := (traj_inv t0 h0 hn0 k0).1
    have e : f c = 1/2 * f P + 1/2 * f Q - 1/4 * dist2 P Q := by simp only [c, mid, f, dist2]; ring
    unfold sorted at hs; unfold D12 at hD
    rw [e]; linarith [hs.1]
  linarith

end B1

/-! ## Lemma B2: the best limit agrees too -/

theorem R_period6 (P A B : Pt) :
    let s1 : Tri := ⟨P, A, B⟩
    let s2 : Tri := ⟨s1.p1, rP s1, s1.p2⟩
    let s3 : Tri := ⟨s2.p1, rP s2, s2.p2⟩
    let s4 : Tri := ⟨s3.p1, rP s3, s3.p2⟩
    let s5 : Tri := ⟨s4.p1, rP s4, s4.p2⟩
    let s6 : Tri := ⟨s5.p1, rP s5, s5.p2⟩
    let s7 : Tri := ⟨s6.p1, rP s6, s6.p2⟩
    s7 = s1 := by
  ext <;> simp only [rP, comb] <;> ring

def S (t : Tri) : ℝ := f t.p1 + f t.p2 + f t.p3

section B2
variable (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0)
include h0 hn0

theorem B2 : (⨅ k, f (traj t0 k).p1) = ⨅ k, f (traj t0 k).p2 := by
  set a1 := ⨅ k, f (traj t0 k).p1
  set a2 := ⨅ k, f (traj t0 k).p2
  have hb1 : ∀ k, 0 ≤ f (traj t0 k).p1 := fun k => f_nonneg _
  have hb2 : ∀ k, 0 ≤ f (traj t0 k).p2 := fun k => f_nonneg _
  have hb3 : ∀ k, 0 ≤ f (traj t0 k).p3 := fun k => f_nonneg _
  have T1 := tendsto_of_anti (v1_anti t0 h0 hn0) hb1
  have T2 := tendsto_of_anti (v2_anti t0 h0 hn0) hb2
  have T3 := tendsto_of_anti (v3_anti t0 h0 hn0) hb3
  have h23 := B1 t0 h0 hn0
  have hle : a1 ≤ a2 := le_of_tendsto_of_tendsto' T1 T2 (fun k => (traj_inv t0 h0 hn0 k).1.1)
  by_contra hne
  have hlt : a1 < a2 := lt_of_le_of_ne hle hne
  set g := a2 - a1 with hg
  have hgpos : 0 < g := by linarith
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp
    ((T1.eventually (Iio_mem_nhds (show a1 < a1 + g/6 by linarith))).and (T3.eventually (Iio_mem_nhds (show (⨅ k, f (traj t0 k).p3) < a2 + g/6 by rw [← h23]; linarith))))
  -- values facts
  have v2ge : ∀ k, a2 ≤ f (traj t0 k).p2 := fun k => iInf_le' hb2 k
  have v3ge : ∀ k, a2 ≤ f (traj t0 k).p3 := fun k => by
    show (⨅ k, f (traj t0 k).p2) ≤ _; rw [h23]; exact iInf_le' hb3 k
  have v1ge : ∀ k, a1 ≤ f (traj t0 k).p1 := fun k => iInf_le' hb1 k
  -- one step from k ≥ k0: p1 kept, and either an R step or an O step lowering lam by 3g/4
  have stepk : ∀ k ≥ k0, (traj t0 (k+1)).p1 = (traj t0 k).p1 ∧
      ((traj t0 (k+1) = ⟨(traj t0 k).p1, rP (traj t0 k), (traj t0 k).p2⟩ ∧
         f (rP (traj t0 k)) < f (traj t0 k).p3) ∨
       lam (traj t0 (k+1)) ≤ lam (traj t0 k) - 3/4 * (a2 - f (traj t0 k).p1)) := by
    intro k hk
    obtain ⟨hv1, hv3⟩ := hk0 k hk
    set t := traj t0 k with ht
    have inv := traj_inv t0 h0 hn0 k
    have hs := inv.1; have hn := inv.2
    have e1 := v2ge (k+1); have e2 := v3ge (k+1)
    rw [traj_succ] at e1 e2 ⊢
    rw [← ht] at e1 e2 ⊢
    have hsd := hs; unfold sorted at hsd
    have hfr := f_refl t
    rcases step_cases t hs hn with ⟨-, -, he⟩ | ⟨-, -, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, he⟩ <;>
      rw [he] at e1 e2 ⊢
    · exact absurd e1 (by simp only []; linarith)
    · exact absurd e1 (by simp only []; linarith)
    · exact ⟨rfl, Or.inl ⟨rfl, by rw [← ht] at hsd; linarith [hsd.2]⟩⟩
    · -- outside contraction
      unfold insert at e1 e2 ⊢
      split_ifs at e1 e2 ⊢ with c1 c2
      · exact absurd e1 (by simp only []; linarith)
      · refine ⟨rfl, Or.inr ?_⟩
        have hl : lam (⟨t.p1, ocP t, t.p2⟩ : Tri) = lam ⟨t.p1, t.p2, ocP t⟩ := by
          simp only [lam, D12, D13, D23, dist2]; ring
        rw [hl, lam_oc]; unfold lam
        have h3 := v3ge k; rw [← ht] at h3
        rw [hfr] at h1
        have := dist2_nonneg t.p1 t.p2; unfold D12 at h1 ⊢
        linarith
      · refine ⟨rfl, Or.inr ?_⟩
        rw [lam_oc]; unfold lam
        have h3 := v3ge k; rw [← ht] at h3
        rw [hfr] at h1
        have := dist2_nonneg t.p1 t.p2; unfold D12 at h1 ⊢
        linarith
    · -- inside contraction: impossible
      exfalso
      have hic := f_ic t
      have hD := dist2_nonneg t.p1 t.p2; have hD2 := dist2_nonneg t.p1 t.p3
      have hD3 := dist2_nonneg t.p2 t.p3
      have hp1 : f t.p1 < a1 + g/6 := hv1
      have hs2 := hsd.2; rw [← ht] at hs2
      unfold insert at e1 e2
      split_ifs at e1 e2 with c1 c2
      · simp only [] at e1; linarith
      · simp only [] at e1
        simp only [D12, D13, D23] at hic
        nlinarith
      · simp only [] at e2
        simp only [D12, D13, D23] at hic
        nlinarith
  -- p1 is frozen from k0 on
  set P := (traj t0 k0).p1
  have frozen : ∀ j, (traj t0 (k0 + j)).p1 = P := by
    intro j; induction j with
    | zero => rfl
    | succ j ih => rw [show k0 + (j+1) = k0 + j + 1 by ring, (stepk (k0+j) (by omega)).1, ih]
  have ha1 : a1 = f P := by
    have : Filter.Tendsto (fun k => f (traj t0 k).p1) Filter.atTop (nhds (f P)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop k0] with k hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [frozen j]
    exact tendsto_nhds_unique T1 this
  -- lam is antitone from k0 and drops by 3g/4 at each non-reflection
  set μ := fun j => lam (traj t0 (k0 + j))
  have μstep : ∀ j, μ (j+1) = μ j ∨ μ (j+1) ≤ μ j - 3/4 * g := by
    intro j
    obtain ⟨-, h | h⟩ := stepk (k0 + j) (by omega)
    · left; simp only [μ]; rw [show k0 + (j+1) = k0 + j + 1 by ring, h.1, lam_refl2]
    · right; simp only [μ]; rw [show k0 + (j+1) = k0 + j + 1 by ring]
      rw [frozen j, ← ha1] at h; exact h
  have μanti : Antitone μ := by
    apply antitone_nat_of_succ_le; intro j
    rcases μstep j with h | h <;> linarith
  have μT := tendsto_of_anti μanti (fun j => lam_nonneg _)
  have μdiff : Filter.Tendsto (fun j => μ j - μ (j+1)) Filter.atTop (nhds 0) := by
    have := μT.sub ((Filter.tendsto_add_atTop_iff_nat 1).mpr μT); simpa using this
  obtain ⟨j1, hj1⟩ := Filter.eventually_atTop.mp (μdiff.eventually (Iio_mem_nhds (show (0:ℝ) < 3/4 * g by linarith)))
  set k2 := k0 + j1
  have onlyR : ∀ j, traj t0 (k2 + j + 1) = ⟨(traj t0 (k2+j)).p1, rP (traj t0 (k2+j)), (traj t0 (k2+j)).p2⟩ ∧
      f (rP (traj t0 (k2+j))) < f (traj t0 (k2+j)).p3 := by
    intro j
    obtain ⟨-, h | h⟩ := stepk (k2 + j) (by omega)
    · exact h
    · exfalso
      have hd := hj1 (j1 + j) (by omega)
      simp only [μ] at hd
      rw [show k0 + (j1 + j + 1) = k2 + j + 1 by ring, show k0 + (j1 + j) = k2 + j by ring] at hd
      rw [show k2 + j = k0 + (j1 + j) by ring, frozen, ← ha1] at h
      rw [show k0 + (j1 + j) = k2 + j by ring] at h
      linarith
  -- six reflections return to the same triangle, but S strictly decreases
  have Sdec : ∀ j, S (traj t0 (k2 + j + 1)) < S (traj t0 (k2 + j)) := by
    intro j; rw [(onlyR j).1]; unfold S; simp only []; linarith [(onlyR j).2]
  have back : traj t0 (k2 + 6) = traj t0 k2 := by
    have e : ∀ j, traj t0 (k2 + (j+1)) = ⟨(traj t0 (k2+j)).p1, rP (traj t0 (k2+j)), (traj t0 (k2+j)).p2⟩ :=
      fun j => (onlyR j).1
    have := R_period6 (traj t0 k2).p1 (traj t0 k2).p2 (traj t0 k2).p3
    simp only [] at this
    rw [show k2 + 6 = k2 + (5+1) by rfl, e 5, show k2 + 5 = k2 + (4+1) by rfl, e 4,
      show k2 + 4 = k2 + (3+1) by rfl, e 3, show k2 + 3 = k2 + (2+1) by rfl, e 2,
      show k2 + 2 = k2 + (1+1) by rfl, e 1, show k2 + 1 = k2 + (0+1) by rfl, e 0, Nat.add_zero]
    exact this
  have s0 : S (traj t0 (k2+1)) < S (traj t0 k2) := Sdec 0
  have s1 : S (traj t0 (k2+2)) < S (traj t0 (k2+1)) := Sdec 1
  have s2 : S (traj t0 (k2+3)) < S (traj t0 (k2+2)) := Sdec 2
  have s3 : S (traj t0 (k2+4)) < S (traj t0 (k2+3)) := Sdec 3
  have s4 : S (traj t0 (k2+5)) < S (traj t0 (k2+4)) := Sdec 4
  have s5 : S (traj t0 (k2+6)) < S (traj t0 (k2+5)) := Sdec 5
  rw [back] at s5
  linarith

end B2

/-! ## Lemma B4: if the common limit is positive, the triangle shrinks -/

/-- with all values of `t` and of the new vertex in `[fs, fs+ε]`, a non-reflection step produces
`lam ≤ 40 ε`, and a reflection step keeps `lam` and has `|K| ≤ 2ε` -/
theorem late_step (t : Tri) (hs : sorted t) (hn : nondeg t) (fs ε : ℝ) (hε : 0 ≤ ε)
    (hlo : fs ≤ f t.p1) (hhi : f t.p3 ≤ fs + ε) (hnew : fs ≤ f (step t).p1) :
    (lam (step t) ≤ 40 * ε) ∨
    (lam (step t) = lam t ∧ |D13 t + D23 t - D12 t| ≤ 2 * ε ∧
      (step t = ⟨rP t, t.p1, t.p2⟩ ∨ step t = ⟨t.p1, rP t, t.p2⟩)) := by
  have hsd := hs; unfold sorted at hsd
  have d12 := dist2_nonneg t.p1 t.p2; have d13 := dist2_nonneg t.p1 t.p3
  have d23 := dist2_nonneg t.p2 t.p3
  have hfr : f (rP t) = _ := f_refl t
  have hfe : f (eP t) = _ := f_exp t
  have hfo : f (ocP t) = _ := f_oc t
  have hfi : f (icP t) = _ := f_ic t
  simp only [D12, D13, D23] at hfr hfe hfo hfi ⊢
  rcases step_cases t hs hn with ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, he⟩ <;>
    rw [he] at hnew ⊢
  · left; rw [lam_exp]; simp only [D12, D13, D23]
    simp only [] at hnew; nlinarith
  · right; refine ⟨lam_refl1 t, ?_, Or.inl rfl⟩
    simp only [] at hnew; rw [abs_le]; constructor <;> nlinarith
  · right; refine ⟨lam_refl2 t, ?_, Or.inr rfl⟩
    simp only [] at hnew; rw [abs_le]; constructor <;> nlinarith
  · left; rw [lam_insert, lam_oc]; simp only [D12, D13, D23]
    have hv : fs ≤ f (ocP t) := by
      unfold insert at hnew; split_ifs at hnew <;> simp only [] at hnew <;> linarith
    nlinarith
  · left; rw [lam_insert, lam_ic]; simp only [D12, D13, D23]
    have hv : fs ≤ f (icP t) := by
      unfold insert at hnew; split_ifs at hnew <;> simp only [] at hnew <;> linarith
    nlinarith

/-- the step is a reflection (accepted reflection or rejected expansion) -/
def isRefl (t : Tri) : Prop :=
  (f t.p1 ≤ f (rP t) ∧ f (rP t) < f t.p2) ∨ (f (rP t) < f t.p1 ∧ f (rP t) ≤ f (eP t))

def Kf (t : Tri) : ℝ := D13 t + D23 t - D12 t

theorem refl_form (t : Tri) (h : isRefl t) :
    step t = ⟨rP t, t.p1, t.p2⟩ ∨ step t = ⟨t.p1, rP t, t.p2⟩ := by
  unfold step
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; simp [not_lt.mpr h1, h2]
  · left; simp [h1, not_lt.mpr h2]

theorem late_refl (t : Tri) (hs : sorted t) (hn : nondeg t) (fs ε : ℝ)
    (hlo : fs ≤ f t.p1) (hhi : f t.p3 ≤ fs + ε) (hnew : fs ≤ f (step t).p1) (h : isRefl t) :
    |Kf t| ≤ 2 * ε := by
  have hsd := hs; unfold sorted at hsd
  have hfr : f (rP t) = _ := f_refl t
  have hfe : f (eP t) = _ := f_exp t
  unfold Kf; simp only [D12, D13, D23] at hfr hfe ⊢
  unfold isRefl at h
  rcases step_cases t hs hn with ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, he⟩ <;>
    rw [he] at hnew <;> try simp only [] at hnew
  · exfalso; rcases h with ⟨h3, -⟩ | ⟨-, h3⟩ <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · exfalso; rcases h with ⟨-, h3⟩ | ⟨h3, -⟩ <;> linarith
  · exfalso; rcases h with ⟨-, h3⟩ | ⟨h3, -⟩ <;> linarith [hsd.1, hsd.2]

theorem late_nonrefl (t : Tri) (hs : sorted t) (hn : nondeg t) (fs ε : ℝ)
    (hlo : fs ≤ f t.p1) (hhi : f t.p3 ≤ fs + ε) (hnew : fs ≤ f (step t).p1) (h : ¬ isRefl t) :
    lam (step t) ≤ 40 * ε := by
  have hsd := hs; unfold sorted at hsd
  have d12 := dist2_nonneg t.p1 t.p2; have d13 := dist2_nonneg t.p1 t.p3
  have d23 := dist2_nonneg t.p2 t.p3
  have hfr : f (rP t) = _ := f_refl t
  have hfe : f (eP t) = _ := f_exp t
  have hfo : f (ocP t) = _ := f_oc t
  have hfi : f (icP t) = _ := f_ic t
  simp only [D12, D13, D23] at hfr hfe hfo hfi
  unfold isRefl at h
  rcases step_cases t hs hn with ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, he⟩ <;>
    rw [he] at hnew ⊢
  · rw [lam_exp]; simp only [D12, D13, D23]; simp only [] at hnew; nlinarith
  · exact absurd (Or.inr ⟨h1, h2⟩) h
  · exact absurd (Or.inl ⟨h1, h2⟩) h
  · rw [lam_insert, lam_oc]; simp only [D12, D13, D23]
    have hv : fs ≤ f (ocP t) := by
      unfold insert at hnew; split_ifs at hnew <;> simp only [] at hnew <;> linarith
    nlinarith
  · rw [lam_insert, lam_ic]; simp only [D12, D13, D23]
    have hv : fs ≤ f (icP t) := by
      unfold insert at hnew; split_ifs at hnew <;> simp only [] at hnew <;> linarith
    nlinarith

theorem refl_sides (t : Tri) (h : isRefl t) :
    (D12 (step t) = D23 t ∧ D13 (step t) = D13 t ∧ D23 (step t) = D12 t) ∨
    (D12 (step t) = D23 t ∧ D13 (step t) = D12 t ∧ D23 (step t) = D13 t) := by
  rcases refl_form t h with he | he <;> rw [he]
  · left; refine ⟨?_, ?_, ?_⟩ <;> simp only [D12, D13, D23, rP, comb, dist2] <;> ring
  · right; refine ⟨?_, ?_, ?_⟩ <;> simp only [D12, D13, D23, rP, comb, dist2] <;> ring

theorem refl_K (t : Tri) (h : isRefl t) : Kf (step t) + Kf t = 2 * D13 t := by
  unfold Kf; rcases refl_sides t h with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> rw [a, b, c] <;> ring

theorem D13_pos (t : Tri) (h : nondeg t) : 0 < D13 t := by
  have h' : nondeg ⟨t.p1, t.p3, t.p2⟩ := by
    unfold nondeg area2 at *; intro hc; apply h; linarith
  have := D12_pos _ h'; simpa [D12, D13] using this
theorem D23_pos (t : Tri) (h : nondeg t) : 0 < D23 t := by
  have h' : nondeg ⟨t.p2, t.p3, t.p1⟩ := by
    unfold nondeg area2 at *; intro hc; apply h; linarith
  have := D12_pos _ h'; simpa [D12, D23] using this

section B4
variable (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0)
include h0 hn0

/-- all values eventually lie in `[fs, fs + ε]`, `fs` the common limit -/
theorem late_window (ε : ℝ) (hε : 0 < ε) : ∃ k0, ∀ k ≥ k0,
    (⨅ j, f (traj t0 j).p1) ≤ f (traj t0 k).p1 ∧ f (traj t0 k).p3 ≤ (⨅ j, f (traj t0 j).p1) + ε ∧
    (⨅ j, f (traj t0 j).p1) ≤ f (step (traj t0 k)).p1 := by
  have hb1 : ∀ k, 0 ≤ f (traj t0 k).p1 := fun k => f_nonneg _
  have hb3 : ∀ k, 0 ≤ f (traj t0 k).p3 := fun k => f_nonneg _
  have T3 := tendsto_of_anti (v3_anti t0 h0 hn0) hb3
  have e : (⨅ j, f (traj t0 j).p3) = ⨅ j, f (traj t0 j).p1 := by rw [← B1 t0 h0 hn0, B2 t0 h0 hn0]
  rw [e] at T3
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp (T3.eventually (Iic_mem_nhds (show
    (⨅ j, f (traj t0 j).p1) < (⨅ j, f (traj t0 j).p1) + ε by linarith)))
  refine ⟨k0, fun k hk => ⟨iInf_le' hb1 k, hk0 k hk, ?_⟩⟩
  rw [← traj_succ]; exact iInf_le' hb1 (k+1)

theorem inf_nonrefl : ∀ k1, ∃ k ≥ k1, ¬ isRefl (traj t0 k) := by
  intro k1
  by_contra hcon
  push_neg at hcon
  set t1 := traj t0 k1
  set m := min (D12 t1) (min (D13 t1) (D23 t1))
  have hm : 0 < m := by
    have i1 := traj_inv t0 h0 hn0 k1
    exact lt_min (D12_pos _ i1.2) (lt_min (D13_pos _ i1.2) (D23_pos _ i1.2))
  -- sides stay in the original set
  have sides : ∀ j, m ≤ D12 (traj t0 (k1+j)) ∧ m ≤ D13 (traj t0 (k1+j)) ∧ m ≤ D23 (traj t0 (k1+j)) := by
    intro j; induction j with
    | zero => exact ⟨min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
                     le_trans (min_le_right _ _) (min_le_right _ _)⟩
    | succ j ih =>
      rw [show k1 + (j+1) = k1 + j + 1 by ring, traj_succ]
      rcases refl_sides _ (hcon (k1+j) (by omega)) with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> rw [a, b, c] <;>
        first | exact ⟨ih.2.2, ih.2.1, ih.1⟩ | exact ⟨ih.2.2, ih.1, ih.2.1⟩
  obtain ⟨k0, hk0⟩ := late_window t0 h0 hn0 (m/4) (by linarith)
  set k := max k0 k1
  have i0 := traj_inv t0 h0 hn0 k; have i1 := traj_inv t0 h0 hn0 (k+1)
  obtain ⟨a1, a2, a3⟩ := hk0 k (le_max_left _ _)
  obtain ⟨b1, b2, b3⟩ := hk0 (k+1) (by omega)
  have K0 := late_refl _ i0.1 i0.2 _ _ a1 a2 a3 (hcon k (le_max_right _ _))
  have K1 := late_refl _ i1.1 i1.2 _ _ b1 b2 b3 (hcon (k+1) (by omega))
  have hK := refl_K _ (hcon k (le_max_right _ _))
  rw [← traj_succ] at hK
  have hD := (sides (k - k1)).2.1
  rw [show k1 + (k - k1) = k by omega] at hD
  rw [abs_le] at K0 K1
  linarith [K0.1, K1.1]

theorem lam_to_zero : Filter.Tendsto (fun k => lam (traj t0 k)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨k0, hk0⟩ := late_window t0 h0 hn0 (δ/80) (by positivity)
  obtain ⟨k', hk', hnr⟩ := inf_nonrefl t0 h0 hn0 k0
  refine ⟨k' + 1, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (lam_nonneg _)]
  have claim : ∀ j, lam (traj t0 (k' + 1 + j)) ≤ 40 * (δ/80) := by
    intro j; induction j with
    | zero =>
      have i := traj_inv t0 h0 hn0 k'
      obtain ⟨a1, a2, a3⟩ := hk0 k' hk'
      rw [Nat.add_zero, traj_succ]; exact late_nonrefl _ i.1 i.2 _ _ a1 a2 a3 hnr
    | succ j ih =>
      have i := traj_inv t0 h0 hn0 (k'+1+j)
      obtain ⟨a1, a2, a3⟩ := hk0 (k'+1+j) (by omega)
      rw [show k' + 1 + (j+1) = k' + 1 + j + 1 by ring, traj_succ]
      by_cases hr : isRefl (traj t0 (k'+1+j))
      · rcases refl_form _ hr with he | he <;> rw [he]
        · rw [lam_refl1]; exact ih
        · rw [lam_refl2]; exact ih
      · exact late_nonrefl _ i.1 i.2 _ _ a1 a2 a3 hr
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have := claim j; linarith

end B4

/-! ## From a monotone potential to convergence -/

def T (t : Tri) : ℝ := (f t.p3 - f t.p1) + lam t

theorem A_le_lam (t : Tri) : A t ≤ lam t := by
  unfold A area2 lam D12 D13 D23 dist2
  rw [abs_le]; constructor <;>
    nlinarith [sq_nonneg ((t.p2.1 - t.p1.1) - (t.p3.2 - t.p1.2)), sq_nonneg ((t.p2.1 - t.p1.1) + (t.p3.2 - t.p1.2)),
      sq_nonneg ((t.p3.1 - t.p1.1) - (t.p2.2 - t.p1.2)), sq_nonneg ((t.p3.1 - t.p1.1) + (t.p2.2 - t.p1.2)),
      sq_nonneg (t.p2.1 - t.p3.1), sq_nonneg (t.p2.2 - t.p3.2)]

theorem lam_pos (t : Tri) (hn : nondeg t) : 0 < lam t := by
  have := D12_pos t hn; have := dist2_nonneg t.p1 t.p3; have := dist2_nonneg t.p2 t.p3
  unfold lam D13 D23; linarith

/-- `min(s, 1/5)` with `s = lam / T` -/
def mS (t : Tri) : ℝ := min (lam t / T t) (1/5)

/-- the potential hypothesis: a weight `q ∈ [qmin, 1]` such that
`P = A^(4/5) · lam^(-7/10) · min(s,1/5)^(7/10) · q` never decreases along steps that start and end in
the far region `f p1 ≥ K · lam`; stated for `P^10 = A⁸ q¹⁰ mS⁷ / lam⁷`. -/
def GoodPotential (K : ℝ) (q : Tri → ℝ) : Prop :=
  (∃ qmin > 0, ∀ t, qmin ≤ q t ∧ q t ≤ 1) ∧
  ∀ t, sorted t → nondeg t → K * lam t ≤ f t.p1 → K * lam (step t) ≤ f (step t).p1 →
    A t ^ 8 * q t ^ 10 * mS t ^ 7 * lam (step t) ^ 7 ≤ A (step t) ^ 8 * q (step t) ^ 10 * mS (step t) ^ 7 * lam t ^ 7

theorem converge_of_potential (K : ℝ) (q : Tri → ℝ) (hP : GoodPotential K q)
    (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :
    Filter.Tendsto (fun k => f (traj t0 k).p3) Filter.atTop (nhds 0) := by
  obtain ⟨⟨qmin, hqmin, hq⟩, hmono⟩ := hP
  have hb3 : ∀ k, 0 ≤ f (traj t0 k).p3 := fun k => f_nonneg _
  have hb1 : ∀ k, 0 ≤ f (traj t0 k).p1 := fun k => f_nonneg _
  have T3 := tendsto_of_anti (v3_anti t0 h0 hn0) hb3
  have e31 : (⨅ j, f (traj t0 j).p3) = ⨅ j, f (traj t0 j).p1 := by rw [← B1 t0 h0 hn0, B2 t0 h0 hn0]
  set fs := ⨅ j, f (traj t0 j).p1
  rw [e31] at T3
  by_contra hne
  have hfs0 : fs ≠ 0 := fun h => hne (by rw [h] at T3; exact T3)
  have hfs : 0 < fs := lt_of_le_of_ne (le_ciInf hb1) (Ne.symm hfs0)
  have L := lam_to_zero t0 h0 hn0
  have far : ∀ᶠ k in Filter.atTop, K * lam (traj t0 k) ≤ f (traj t0 k).p1 := by
    have hK : Filter.Tendsto (fun k => K * lam (traj t0 k)) Filter.atTop (nhds 0) := by
      simpa using L.const_mul K
    filter_upwards [hK.eventually (Iio_mem_nhds hfs)] with k hk
    exact le_trans hk.le (iInf_le' hb1 k)
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp far
  have lpos : ∀ k, 0 < lam (traj t0 k) := fun k => lam_pos _ (traj_inv t0 h0 hn0 k).2
  have Tpos : ∀ k, 0 < T (traj t0 k) := by
    intro k; have i := traj_inv t0 h0 hn0 k; unfold T
    have := lpos k; unfold sorted at i; linarith [i.1.1, i.1.2]
  have mpos : ∀ k, 0 < mS (traj t0 k) := fun k => lt_min (div_pos (lpos k) (Tpos k)) (by norm_num)
  set P := fun k => A (traj t0 k) ^ 8 * q (traj t0 k) ^ 10 * mS (traj t0 k) ^ 7 / lam (traj t0 k) ^ 7
  have Pmono : ∀ j, P (k0 + j) ≤ P (k0 + j + 1) := by
    intro j
    have i := traj_inv t0 h0 hn0 (k0+j)
    have h := hmono _ i.1 i.2 (hk0 (k0+j) (by omega)) (by rw [← traj_succ]; exact hk0 (k0+j+1) (by omega))
    rw [← traj_succ] at h
    simp only [P]
    rw [div_le_div_iff₀ (pow_pos (lpos _) 7) (pow_pos (lpos _) 7)]
    linarith
  have Pge : ∀ j, P k0 ≤ P (k0 + j) := by
    intro j; induction j with
    | zero => simp
    | succ j ih => exact le_trans ih (Pmono j)
  have P0pos : 0 < P k0 := by
    have i := traj_inv t0 h0 hn0 k0
    have := A_pos _ i.2; have := (hq (traj t0 k0)).1
    simp only [P]
    exact div_pos (mul_pos (mul_pos (pow_pos (by linarith) 8) (pow_pos (by linarith) 10)) (pow_pos (mpos k0) 7))
      (pow_pos (lpos _) 7)
  have Ple : ∀ k, P k ≤ lam (traj t0 k) := by
    intro k
    have i := traj_inv t0 h0 hn0 k
    have hA := A_le_lam (traj t0 k); have hA0 := A_pos _ i.2
    have hq1 := (hq (traj t0 k)).2; have hq0 := (hq (traj t0 k)).1
    have hm1 : mS (traj t0 k) ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
    have hm0 := (mpos k).le
    have hl := lpos k
    simp only [P]
    rw [div_le_iff₀ (pow_pos hl 7)]
    calc A (traj t0 k) ^ 8 * q (traj t0 k) ^ 10 * mS (traj t0 k) ^ 7
        ≤ lam (traj t0 k) ^ 8 * 1 * 1 := by
          apply mul_le_mul (mul_le_mul (pow_le_pow_left₀ hA0.le hA 8) (pow_le_one₀ (by linarith) hq1)
            (by positivity) (by positivity)) (pow_le_one₀ hm0 hm1) (by positivity) (by positivity)
      _ = lam (traj t0 k) * lam (traj t0 k) ^ 7 := by ring
  obtain ⟨k1, hk1⟩ := Filter.eventually_atTop.mp (L.eventually (Iio_mem_nhds P0pos))
  have := Ple (k0 + k1); have := Pge k1; have := hk1 (k0 + k1) (by omega)
  linarith

theorem norm_le_sqrt_f (p : Pt) : ‖p‖ ≤ Real.sqrt (f p) := by
  rw [Prod.norm_def]
  apply max_le
  · rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]; apply Real.sqrt_le_sqrt; unfold f; nlinarith [sq_nonneg p.2]
  · rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]; apply Real.sqrt_le_sqrt; unfold f; nlinarith [sq_nonneg p.1]

theorem pt_tendsto_zero {x : ℕ → Pt} (h : Filter.Tendsto (fun k => f (x k)) Filter.atTop (nhds 0)) :
    Filter.Tendsto x Filter.atTop (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hs : Filter.Tendsto (fun k => Real.sqrt (f (x k))) Filter.atTop (nhds 0) := by
    simpa using h.sqrt
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => norm_le_sqrt_f _) hs

/-- conditional main theorem: given a good potential, every vertex converges to the minimizer -/
theorem nm_converges_of_potential (K : ℝ) (q : Tri → ℝ) (hP : GoodPotential K q)
    (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :
    Filter.Tendsto (fun k => (traj t0 k).p1) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p2) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p3) Filter.atTop (nhds 0) := by
  have h3 := converge_of_potential K q hP t0 h0 hn0
  have bnd : ∀ k, f (traj t0 k).p1 ≤ f (traj t0 k).p3 ∧ f (traj t0 k).p2 ≤ f (traj t0 k).p3 := by
    intro k; have := (traj_inv t0 h0 hn0 k).1; unfold sorted at this; exact ⟨this.1.trans this.2, this.2⟩
  refine ⟨pt_tendsto_zero ?_, pt_tendsto_zero ?_, pt_tendsto_zero h3⟩
  · exact squeeze_zero (fun k => f_nonneg _) (fun k => (bnd k).1) h3
  · exact squeeze_zero (fun k => f_nonneg _) (fun k => (bnd k).2) h3

/-! ## Cayley–Menger identities and the far region -/

def heron (t : Tri) : ℝ :=
  2 * (D12 t * D13 t + D12 t * D23 t + D13 t * D23 t) - D12 t ^ 2 - D13 t ^ 2 - D23 t ^ 2

/-- `N = -CM5(φ, D)` with `φ = (0, f2 - f1, f3 - f1)` -/
def Ncm (t : Tri) : ℝ :=
  let p2 := f t.p2 - f t.p1
  let p3 := f t.p3 - f t.p1
  let a := D12 t; let b := D13 t; let c := D23 t
  2 * (a^2*p3 + a*b*c - a*b*p2 - a*b*p3 - a*c*p3 - a*p2*p3 + a*p3^2 + b^2*p2 - b*c*p2 + b*p2^2 - b*p2*p3 + c*p2*p3)

theorem heron_eq (t : Tri) : heron t = 4 * area2 t ^ 2 := by
  simp only [heron, area2, D12, D13, D23, dist2]; ring

theorem Ncm_eq (t : Tri) : Ncm t = 2 * f t.p1 * heron t := by
  simp only [Ncm, heron, D12, D13, D23, dist2, f]; ring

theorem N_le_of_spread (p2 p3 a b c L : ℝ) (hp2 : 0 ≤ p2) (h23 : p2 ≤ p3) (hp3 : p3 ≤ 7 * L)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (haL : a ≤ L) (hbL : b ≤ L) (hcL : c ≤ L) :
    2 * (a^2*p3 + a*b*c - a*b*p2 - a*b*p3 - a*c*p3 - a*p2*p3 + a*p3^2 + b^2*p2 - b*c*p2 + b*p2^2
      - b*p2*p3 + c*p2*p3) ≤ 324 * L ^ 3 := by
  have hL : 0 ≤ L := le_trans ha haL
  have hp3' : 0 ≤ p3 := le_trans hp2 h23
  have hp2' : p2 ≤ 7 * L := le_trans h23 hp3
  have t1 : a^2*p3 ≤ L^2 * (7*L) := mul_le_mul (pow_le_pow_left₀ ha haL 2) hp3 hp3' (by positivity)
  have t2 : a*b*c ≤ L*L*L := mul_le_mul (mul_le_mul haL hbL hb hL) hcL hc (by positivity)
  have t3 : a*p3^2 ≤ L*(7*L)^2 := mul_le_mul haL (pow_le_pow_left₀ hp3' hp3 2) (by positivity) hL
  have t4 : b^2*p2 ≤ L^2*(7*L) := mul_le_mul (pow_le_pow_left₀ hb hbL 2) hp2' hp2 (by positivity)
  have t5 : b*p2^2 ≤ L*(7*L)^2 := mul_le_mul hbL (pow_le_pow_left₀ hp2 hp2' 2) (by positivity) hL
  have t6 : c*p2*p3 ≤ L*(7*L)*(7*L) := mul_le_mul (mul_le_mul hcL hp2' hp2 hL) hp3 hp3' (by positivity)
  have n1 : 0 ≤ a*b*p2 := by positivity
  have n2 : 0 ≤ a*b*p3 := by positivity
  have n3 : 0 ≤ a*c*p3 := by positivity
  have n4 : 0 ≤ a*p2*p3 := by positivity
  have n5 : 0 ≤ b*c*p2 := by positivity
  have n6 : 0 ≤ b*p2*p3 := by positivity
  nlinarith

/-- far states with `s ≥ 1/8` lie in the thin strip `heron ≤ 162 lam² / K` -/
theorem far_strip (t : Tri) (hs : sorted t) (K : ℝ) (hK : 0 < K) (hfar : K * lam t ≤ f t.p1)
    (hn : nondeg t) (hS : lam t ≥ (1/8) * T t) : heron t * K ≤ 162 * lam t ^ 2 := by
  have hsd := hs; unfold sorted at hsd
  have hl := lam_pos t hn
  have d12 := dist2_nonneg t.p1 t.p2; have d13 := dist2_nonneg t.p1 t.p3; have d23 := dist2_nonneg t.p2 t.p3
  have hspread : f t.p3 - f t.p1 ≤ 7 * lam t := by unfold T at hS; linarith
  have hN := N_le_of_spread (f t.p2 - f t.p1) (f t.p3 - f t.p1) (D12 t) (D13 t) (D23 t) (lam t)
    (by linarith) (by linarith) hspread d12 d13 d23 (by unfold lam D13 D23; linarith)
    (by unfold lam D12 D23; linarith) (by unfold lam D12 D13; linarith)
  have e := Ncm_eq t
  simp only [Ncm] at e
  rw [e] at hN
  have hf1 : 0 < f t.p1 := lt_of_lt_of_le (mul_pos hK hl) hfar
  have hh : 0 ≤ heron t := by rw [heron_eq]; positivity
  -- 2 f1 heron ≤ 324 lam^3 and K lam ≤ f1
  have : heron t * (K * lam t) ≤ heron t * f t.p1 := mul_le_mul_of_nonneg_left hfar hh
  have h3 : heron t * K * lam t ≤ 162 * lam t ^ 2 * lam t := by nlinarith
  have := (mul_le_mul_iff_of_pos_right hl).mp (by linarith : heron t * K * lam t ≤ 162 * lam t ^ 2 * lam t)
  linarith

theorem N_le_of_spread_m (p2 p3 a b c L m : ℝ) (hm : 0 ≤ m) (hp2 : 0 ≤ p2) (h23 : p2 ≤ p3) (hp3 : p3 ≤ m * L)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (haL : a ≤ L) (hbL : b ≤ L) (hcL : c ≤ L) :
    2 * (a^2*p3 + a*b*c - a*b*p2 - a*b*p3 - a*c*p3 - a*p2*p3 + a*p3^2 + b^2*p2 - b*c*p2 + b*p2^2
      - b*p2*p3 + c*p2*p3) ≤ 2 * (3 * m ^ 2 + 2 * m + 1) * L ^ 3 := by
  have hL : 0 ≤ L := le_trans ha haL
  have hp3' : 0 ≤ p3 := le_trans hp2 h23
  have hp2' : p2 ≤ m * L := le_trans h23 hp3
  have hmL : 0 ≤ m * L := mul_nonneg hm hL
  have t1 : a^2*p3 ≤ L^2 * (m*L) := mul_le_mul (pow_le_pow_left₀ ha haL 2) hp3 hp3' (by positivity)
  have t2 : a*b*c ≤ L*L*L := mul_le_mul (mul_le_mul haL hbL hb hL) hcL hc (by positivity)
  have t3 : a*p3^2 ≤ L*(m*L)^2 := mul_le_mul haL (pow_le_pow_left₀ hp3' hp3 2) (by positivity) hL
  have t4 : b^2*p2 ≤ L^2*(m*L) := mul_le_mul (pow_le_pow_left₀ hb hbL 2) hp2' hp2 (by positivity)
  have t5 : b*p2^2 ≤ L*(m*L)^2 := mul_le_mul hbL (pow_le_pow_left₀ hp2 hp2' 2) (by positivity) hL
  have t6 : c*p2*p3 ≤ L*(m*L)*(m*L) := mul_le_mul (mul_le_mul hcL hp2' hp2 hL) hp3 hp3' (by positivity)
  have n1 : 0 ≤ a*b*p2 := by positivity
  have n2 : 0 ≤ a*b*p3 := by positivity
  have n3 : 0 ≤ a*c*p3 := by positivity
  have n4 : 0 ≤ a*p2*p3 := by positivity
  have n5 : 0 ≤ b*c*p2 := by positivity
  have n6 : 0 ≤ b*p2*p3 := by positivity
  nlinarith

/-- far states with `T ≤ (m+1) λ` satisfy `heron · K ≤ (3m² + 2m + 1) λ²` -/
theorem far_strip_m (t : Tri) (hs : sorted t) (K : ℝ) (hK : 0 < K) (hfar : K * lam t ≤ f t.p1)
    (hn : nondeg t) (m : ℝ) (hm : 0 ≤ m) (hS : (m + 1) * lam t ≥ T t) :
    heron t * K ≤ (3 * m ^ 2 + 2 * m + 1) * lam t ^ 2 := by
  have hsd := hs; unfold sorted at hsd
  have hl := lam_pos t hn
  have d12 := dist2_nonneg t.p1 t.p2; have d13 := dist2_nonneg t.p1 t.p3; have d23 := dist2_nonneg t.p2 t.p3
  have hspread : f t.p3 - f t.p1 ≤ m * lam t := by unfold T at hS; linarith
  have hN := N_le_of_spread_m (f t.p2 - f t.p1) (f t.p3 - f t.p1) (D12 t) (D13 t) (D23 t) (lam t) m hm
    (by linarith) (by linarith) hspread d12 d13 d23 (by unfold lam D13 D23; linarith)
    (by unfold lam D12 D23; linarith) (by unfold lam D12 D13; linarith)
  have e := Ncm_eq t
  simp only [Ncm] at e
  rw [e] at hN
  have hh : 0 ≤ heron t := by rw [heron_eq]; positivity
  have : heron t * (K * lam t) ≤ heron t * f t.p1 := mul_le_mul_of_nonneg_left hfar hh
  have h3 : heron t * K * lam t ≤ (3 * m ^ 2 + 2 * m + 1) * lam t ^ 2 * lam t := by nlinarith
  exact (mul_le_mul_iff_of_pos_right hl).mp h3

/-! ## Linear coordinates of the new triangle -/

/-- value of an affine combination relative to `f p1`, and its squared distances to `p1, p2`,
expressed in the linear coordinates of `t` -/
theorem comb_coords (t : Tri) (a b c : ℝ) (h : a + b + c = 1) :
    f (comb a b c t.p1 t.p2 t.p3) - f t.p1 =
      b * (f t.p2 - f t.p1) + c * (f t.p3 - f t.p1) - (a*b*D12 t + a*c*D13 t + b*c*D23 t) ∧
    dist2 (comb a b c t.p1 t.p2 t.p3) t.p1 = b * D12 t + c * D13 t - (a*b*D12 t + a*c*D13 t + b*c*D23 t) ∧
    dist2 (comb a b c t.p1 t.p2 t.p3) t.p2 = a * D12 t + c * D23 t - (a*b*D12 t + a*c*D13 t + b*c*D23 t) := by
  have hc : c = 1 - a - b := by linarith
  subst hc
  refine ⟨?_, ?_, ?_⟩ <;> simp only [f, comb, D12, D13, D23, dist2] <;> ring

/-! ## The nine branches in linear coordinates -/

/-- linear coordinates `(Δ2, Δ3, D12, D13, D23)` -/
structure Zc where
  d2 : ℝ
  d3 : ℝ
  a : ℝ
  b : ℝ
  c : ℝ

def zc (t : Tri) : Zc := ⟨f t.p2 - f t.p1, f t.p3 - f t.p2, D12 t, D13 t, D23 t⟩

/-- value of a linear functional -/
def ev (w : Fin 5 → ℝ) (z : Zc) : ℝ := w 0 * z.d2 + w 1 * z.d3 + w 2 * z.a + w 3 * z.b + w 4 * z.c

theorem zc_form1 (t : Tri) (v : Pt) : zc ⟨v, t.p1, t.p2⟩ =
    ⟨-(f v - f t.p1), f t.p2 - f t.p1, dist2 v t.p1, dist2 v t.p2, D12 t⟩ := by
  simp only [zc, D12, D13, D23, Zc.mk.injEq]; refine ⟨by ring, trivial, trivial, trivial, trivial⟩
theorem zc_form2 (t : Tri) (v : Pt) : zc ⟨t.p1, v, t.p2⟩ =
    ⟨f v - f t.p1, (f t.p2 - f t.p1) - (f v - f t.p1), dist2 v t.p1, D12 t, dist2 v t.p2⟩ := by
  simp only [zc, D12, D13, D23, Zc.mk.injEq]
  refine ⟨trivial, by ring, dist2_comm _ _, trivial, trivial⟩
theorem zc_form3 (t : Tri) (v : Pt) : zc ⟨t.p1, t.p2, v⟩ =
    ⟨f t.p2 - f t.p1, (f v - f t.p1) - (f t.p2 - f t.p1), D12 t, dist2 v t.p1, dist2 v t.p2⟩ := by
  simp only [zc, D12, D13, D23, Zc.mk.injEq]
  refine ⟨trivial, by ring, trivial, dist2_comm _ _, dist2_comm _ _⟩

def brM1 (z : Zc) : Zc := ⟨(1/2) * z.d2 + 2 * z.d3 + (9/4) * z.a + -3 * z.b + -3 * z.c, 1 * z.d2, (-3/4) * z.a + 1 * z.b + 3 * z.c, (-3/4) * z.a + 3 * z.b + 1 * z.c, 1 * z.a⟩
def brC1 (z : Zc) : Prop := (-1 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) < 0 ∧ ((-1/2) * z.d2 + -1 * z.d3 + (-5/4) * z.a + 2 * z.b + 2 * z.c) < 0
def brM2 (z : Zc) : Zc := ⟨1 * z.d3 + 1 * z.a + -1 * z.b + -1 * z.c, 1 * z.d2, 1 * z.c, 1 * z.b, 1 * z.a⟩
def brC2 (z : Zc) : Prop := (-1 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) < 0 ∧ 0 ≤ ((-1/2) * z.d2 + -1 * z.d3 + (-5/4) * z.a + 2 * z.b + 2 * z.c)
def brM3 (z : Zc) : Zc := ⟨-1 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c, 1 * z.d2 + 1 * z.d3 + 1 * z.a + -1 * z.b + -1 * z.c, 1 * z.c, 1 * z.a, 1 * z.b⟩
def brC3 (z : Zc) : Prop := 0 ≤ (-1 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) ∧ (-1 * z.d2 + -1 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) < 0
def brM4 (z : Zc) : Zc := ⟨(-1/4) * z.d2 + (1/2) * z.d3 + (9/16) * z.a + (-3/8) * z.b + (-3/8) * z.c, 1 * z.d2, (3/16) * z.a + (-1/8) * z.b + (3/8) * z.c, (3/16) * z.a + (3/8) * z.b + (-1/8) * z.c, 1 * z.a⟩
def brC4 (z : Zc) : Prop := 0 ≤ (-1 * z.d2 + -1 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) ∧ (-1 * z.d2 + -2 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) < 0 ∧ ((1/4) * z.d2 + (-1/2) * z.d3 + (-9/16) * z.a + (3/8) * z.b + (3/8) * z.c) < 0
def brM5 (z : Zc) : Zc := ⟨(-3/4) * z.d2 + (-1/2) * z.d3 + (1/16) * z.a + (1/8) * z.b + (1/8) * z.c, 1 * z.d2, (3/16) * z.a + (3/8) * z.b + (-1/8) * z.c, (3/16) * z.a + (-1/8) * z.b + (3/8) * z.c, 1 * z.a⟩
def brC5 (z : Zc) : Prop := 0 ≤ (-1 * z.d2 + -2 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) ∧ ((3/4) * z.d2 + (1/2) * z.d3 + (-1/16) * z.a + (-1/8) * z.b + (-1/8) * z.c) < 0
def brM6 (z : Zc) : Zc := ⟨(1/4) * z.d2 + (-1/2) * z.d3 + (-9/16) * z.a + (3/8) * z.b + (3/8) * z.c, (3/4) * z.d2 + (1/2) * z.d3 + (9/16) * z.a + (-3/8) * z.b + (-3/8) * z.c, (3/16) * z.a + (-1/8) * z.b + (3/8) * z.c, 1 * z.a, (3/16) * z.a + (3/8) * z.b + (-1/8) * z.c⟩
def brC6 (z : Zc) : Prop := 0 ≤ (-1 * z.d2 + -1 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) ∧ (-1 * z.d2 + -2 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) < 0 ∧ 0 ≤ ((1/4) * z.d2 + (-1/2) * z.d3 + (-9/16) * z.a + (3/8) * z.b + (3/8) * z.c) ∧ ((-3/4) * z.d2 + (-1/2) * z.d3 + (-9/16) * z.a + (3/8) * z.b + (3/8) * z.c) < 0
def brM7 (z : Zc) : Zc := ⟨(3/4) * z.d2 + (1/2) * z.d3 + (-1/16) * z.a + (-1/8) * z.b + (-1/8) * z.c, (1/4) * z.d2 + (-1/2) * z.d3 + (1/16) * z.a + (1/8) * z.b + (1/8) * z.c, (3/16) * z.a + (3/8) * z.b + (-1/8) * z.c, 1 * z.a, (3/16) * z.a + (-1/8) * z.b + (3/8) * z.c⟩
def brC7 (z : Zc) : Prop := 0 ≤ (-1 * z.d2 + -2 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) ∧ 0 ≤ ((3/4) * z.d2 + (1/2) * z.d3 + (-1/16) * z.a + (-1/8) * z.b + (-1/8) * z.c) ∧ ((-1/4) * z.d2 + (1/2) * z.d3 + (-1/16) * z.a + (-1/8) * z.b + (-1/8) * z.c) < 0
def brM8 (z : Zc) : Zc := ⟨1 * z.d2, (-3/4) * z.d2 + (-1/2) * z.d3 + (-9/16) * z.a + (3/8) * z.b + (3/8) * z.c, 1 * z.a, (3/16) * z.a + (-1/8) * z.b + (3/8) * z.c, (3/16) * z.a + (3/8) * z.b + (-1/8) * z.c⟩
def brC8 (z : Zc) : Prop := 0 ≤ (-1 * z.d2 + -1 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) ∧ (-1 * z.d2 + -2 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) < 0 ∧ 0 ≤ ((-3/4) * z.d2 + (-1/2) * z.d3 + (-9/16) * z.a + (3/8) * z.b + (3/8) * z.c)
def brM9 (z : Zc) : Zc := ⟨1 * z.d2, (-1/4) * z.d2 + (1/2) * z.d3 + (-1/16) * z.a + (-1/8) * z.b + (-1/8) * z.c, 1 * z.a, (3/16) * z.a + (3/8) * z.b + (-1/8) * z.c, (3/16) * z.a + (-1/8) * z.b + (3/8) * z.c⟩
def brC9 (z : Zc) : Prop := 0 ≤ (-1 * z.d2 + -2 * z.d3 + -1 * z.a + 1 * z.b + 1 * z.c) ∧ 0 ≤ ((-1/4) * z.d2 + (1/2) * z.d3 + (-1/16) * z.a + (-1/8) * z.b + (-1/8) * z.c)

theorem zc_d2_nonneg (t : Tri) (hs : sorted t) : 0 ≤ (zc t).d2 := by
  unfold zc sorted at *; simp only []; linarith [hs.1]

theorem A_perm1 (p1 p2 v : Pt) : A ⟨v, p1, p2⟩ = A ⟨p1, p2, v⟩ := by
  unfold A area2; congr 1; ring
theorem A_perm2 (p1 p2 v : Pt) : A ⟨p1, v, p2⟩ = A ⟨p1, p2, v⟩ := by
  unfold A area2; rw [← abs_neg]; congr 1; ring

set_option maxHeartbeats 1000000 in
/-- every step falls in one of the nine branches -/
theorem step_branch (t : Tri) (hs : sorted t) (hn : nondeg t) :
    (brC1 (zc t) ∧ zc (step t) = brM1 (zc t) ∧ A (step t) = 2 * A t) ∨
    (brC2 (zc t) ∧ zc (step t) = brM2 (zc t) ∧ A (step t) = A t) ∨
    (brC3 (zc t) ∧ zc (step t) = brM3 (zc t) ∧ A (step t) = A t) ∨
    (brC4 (zc t) ∧ zc (step t) = brM4 (zc t) ∧ A (step t) = 1/2 * A t) ∨
    (brC5 (zc t) ∧ zc (step t) = brM5 (zc t) ∧ A (step t) = 1/2 * A t) ∨
    (brC6 (zc t) ∧ zc (step t) = brM6 (zc t) ∧ A (step t) = 1/2 * A t) ∨
    (brC7 (zc t) ∧ zc (step t) = brM7 (zc t) ∧ A (step t) = 1/2 * A t) ∨
    (brC8 (zc t) ∧ zc (step t) = brM8 (zc t) ∧ A (step t) = 1/2 * A t) ∨
    (brC9 (zc t) ∧ zc (step t) = brM9 (zc t) ∧ A (step t) = 1/2 * A t) := by
  have hA := A_step t hs hn
  have cr := comb_coords t 1 1 (-1) (by norm_num)
  have ce := comb_coords t (3/2) (3/2) (-2) (by norm_num)
  have co := comb_coords t (3/4) (3/4) (-1/2) (by norm_num)
  have ci := comb_coords t (1/4) (1/4) (1/2) (by norm_num)
  have fr : f (rP t) - f t.p1 = _ := cr.1
  have rd1 : dist2 (rP t) t.p1 = _ := cr.2.1
  have rd2 : dist2 (rP t) t.p2 = _ := cr.2.2
  have fe : f (eP t) - f t.p1 = _ := ce.1
  have ed1 : dist2 (eP t) t.p1 = _ := ce.2.1
  have ed2 : dist2 (eP t) t.p2 = _ := ce.2.2
  have fo : f (ocP t) - f t.p1 = _ := co.1
  have od1 : dist2 (ocP t) t.p1 = _ := co.2.1
  have od2 : dist2 (ocP t) t.p2 = _ := co.2.2
  have fi : f (icP t) - f t.p1 = _ := ci.1
  have id1 : dist2 (icP t) t.p1 = _ := ci.2.1
  have id2 : dist2 (icP t) t.p2 = _ := ci.2.2
  clear cr ce co ci
  have hAs := A_pos t hn
  rcases step_cases t hs hn with ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, he⟩
  · left
    have hA' : A (step t) = 2 * A t := by
      rw [he]; unfold A area2; rw [show (2:ℝ) = |(-2:ℝ)| by norm_num, ← abs_mul]; congr 1; simp only [eP, comb]; ring
    refine ⟨?_, ?_, hA'⟩
    · simp only [brC1, zc]; constructor <;> linarith
    · rw [he, zc_form1]; simp only [brM1, zc, Zc.mk.injEq]; refine ⟨by linarith, by ring, by linarith, by linarith, by ring⟩
  · right; left
    have hA' : A (step t) = A t := by
      rw [he]; unfold A area2; rw [← abs_neg]; congr 1; simp only [rP, comb]; ring
    refine ⟨?_, ?_, hA'⟩
    · simp only [brC2, zc]; constructor <;> linarith
    · rw [he, zc_form1]; simp only [brM2, zc, Zc.mk.injEq]; refine ⟨by linarith, by ring, by linarith, by linarith, by ring⟩
  · right; right; left
    have hA' : A (step t) = A t := by
      rw [he]; unfold A area2; congr 1; simp only [rP, comb]; ring
    refine ⟨?_, ?_, hA'⟩
    · simp only [brC3, zc]; constructor <;> linarith
    · rw [he, zc_form2]; simp only [brM3, zc, Zc.mk.injEq]; refine ⟨by linarith, by linarith, by linarith, by ring, by linarith⟩
  · -- outside contraction, three insert positions
    have hA0 : A ⟨t.p1, t.p2, ocP t⟩ = 1/2 * A t := by
      unfold A area2
      rw [show (1/2:ℝ) = |(-1/2:ℝ)| by norm_num, ← abs_mul]; congr 1; simp only [ocP, comb]; ring
    rw [he]
    unfold insert
    split_ifs with c1 c2
    · right; right; right; left
      refine ⟨?_, ?_, by rw [A_perm1]; exact hA0⟩
      · simp only [brC4, zc]; refine ⟨by linarith, by linarith, by linarith⟩
      · rw [zc_form1]; simp only [brM4, zc, Zc.mk.injEq]; refine ⟨by linarith, by ring, by linarith, by linarith, by ring⟩
    · right; right; right; right; right; left
      refine ⟨?_, ?_, by rw [A_perm2]; exact hA0⟩
      · simp only [brC6, zc]; refine ⟨by linarith, by linarith, by linarith, by linarith⟩
      · rw [zc_form2]; simp only [brM6, zc, Zc.mk.injEq]; refine ⟨by linarith, by linarith, by linarith, by ring, by linarith⟩
    · right; right; right; right; right; right; right; left
      refine ⟨?_, ?_, hA0⟩
      · simp only [brC8, zc]; refine ⟨by linarith, by linarith, by linarith⟩
      · rw [zc_form3]; simp only [brM8, zc, Zc.mk.injEq]; refine ⟨by ring, by linarith, by ring, by linarith, by linarith⟩
  · -- inside contraction
    have hA0 : A ⟨t.p1, t.p2, icP t⟩ = 1/2 * A t := by
      unfold A area2
      rw [show (1/2:ℝ) = |(1/2:ℝ)| by norm_num, ← abs_mul]; congr 1; simp only [icP, comb]; ring
    rw [he]
    unfold insert
    split_ifs with c1 c2
    · right; right; right; right; left
      refine ⟨?_, ?_, by rw [A_perm1]; exact hA0⟩
      · simp only [brC5, zc]; refine ⟨by linarith, by linarith⟩
      · rw [zc_form1]; simp only [brM5, zc, Zc.mk.injEq]; refine ⟨by linarith, by ring, by linarith, by linarith, by ring⟩
    · right; right; right; right; right; right; left
      refine ⟨?_, ?_, by rw [A_perm2]; exact hA0⟩
      · simp only [brC7, zc]; refine ⟨by linarith, by linarith, by linarith⟩
      · rw [zc_form2]; simp only [brM7, zc, Zc.mk.injEq]; refine ⟨by linarith, by linarith, by linarith, by ring, by linarith⟩
    · right; right; right; right; right; right; right; right
      refine ⟨?_, ?_, hA0⟩
      · simp only [brC9, zc]; refine ⟨by linarith, by linarith⟩
      · rw [zc_form3]; simp only [brM9, zc, Zc.mk.injEq]; refine ⟨by ring, by linarith, by ring, by linarith, by linarith⟩

/-! ## Exact facts for the reflection/expansion branches -/

def Zc.lam (z : Zc) : ℝ := z.a + z.b + z.c
def Zc.T (z : Zc) : ℝ := z.d2 + z.d3 + z.lam

theorem brM1_T (z : Zc) (h2 : 0 ≤ z.d2) (h3 : 0 ≤ z.d3) (ha : 0 ≤ z.a) (hb : 0 ≤ z.b) (hc : 0 ≤ z.c) :
    (brM1 z).T ≤ 2 * z.T := by
  simp only [Zc.T, Zc.lam, brM1]; linarith
theorem brM2_lam (z : Zc) : (brM2 z).lam = z.lam := by simp only [Zc.lam, brM2]; ring
theorem brM3_lam (z : Zc) : (brM3 z).lam = z.lam := by simp only [Zc.lam, brM3]; ring
theorem brM3_spread (z : Zc) (h : brC3 z) (h3 : 0 ≤ z.d3) : (brM3 z).d2 + (brM3 z).d3 ≤ z.d2 + z.d3 := by
  simp only [brM3]; simp only [brC3] at h; linarith [h.1]

theorem zc_nonneg (t : Tri) (hs : sorted t) :
    0 ≤ (zc t).d2 ∧ 0 ≤ (zc t).d3 ∧ 0 ≤ (zc t).a ∧ 0 ≤ (zc t).b ∧ 0 ≤ (zc t).c := by
  unfold sorted at hs; simp only [zc, D12, D13, D23]
  exact ⟨by linarith [hs.1], by linarith [hs.2], dist2_nonneg _ _, dist2_nonneg _ _, dist2_nonneg _ _⟩

theorem zc_lam (t : Tri) : (zc t).lam = lam t := by simp only [Zc.lam, zc, lam]
theorem zc_T (t : Tri) : (zc t).T = T t := by simp only [Zc.T, Zc.lam, zc, T, lam]; ring

end NM
end
