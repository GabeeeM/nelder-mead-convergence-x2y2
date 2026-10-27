import Mathlib

/-! Reflective checker, part 1: signed integers as pairs of naturals (fast in the kernel) and the
soundness of one cell check `fcheck`. -/

namespace NMC

/-- `p - n` -/
structure Z where
  p : Nat
  n : Nat

namespace Z
def neg (x : Z) : Z := ⟨x.n, x.p⟩
def add (x y : Z) : Z := ⟨Nat.add x.p y.p, Nat.add x.n y.n⟩
def sub (x y : Z) : Z := ⟨Nat.add x.p y.n, Nat.add x.n y.p⟩
def mul (x y : Z) : Z :=
  ⟨Nat.add (Nat.mul x.p y.p) (Nat.mul x.n y.n), Nat.add (Nat.mul x.p y.n) (Nat.mul x.n y.p)⟩
def nonneg (x : Z) : Bool := Nat.ble x.n x.p
def pos (x : Z) : Bool := Nat.blt x.n x.p
def le (x y : Z) : Bool := Nat.ble (Nat.add x.p y.n) (Nat.add y.p x.n)
def min (x y : Z) : Z := cond (le x y) x y
def ofN (k : Nat) : Z := ⟨k, 0⟩
noncomputable def val (x : Z) : ℝ := (x.p : ℝ) - x.n

@[simp] theorem val_neg (x : Z) : (neg x).val = - x.val := by simp [neg, val]
@[simp] theorem val_add (x y : Z) : (add x y).val = x.val + y.val := by simp [add, val]; ring
@[simp] theorem val_sub (x y : Z) : (sub x y).val = x.val - y.val := by simp [sub, val]; ring
@[simp] theorem val_mul (x y : Z) : (mul x y).val = x.val * y.val := by simp [mul, val]; ring
@[simp] theorem val_ofN (k : Nat) : (ofN k).val = k := by simp [ofN, val]
theorem nonneg_iff (x : Z) : x.nonneg = true ↔ 0 ≤ x.val := by
  simp [nonneg, val, Nat.ble_eq]
theorem pos_iff (x : Z) : x.pos = true ↔ 0 < x.val := by
  simp [pos, val, Nat.blt_eq]
theorem le_iff (x y : Z) : x.le y = true ↔ x.val ≤ y.val := by
  simp only [le, val, Nat.ble_eq]; constructor <;> intro h
  · have : ((x.p + y.n : ℕ) : ℝ) ≤ ((y.p + x.n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((x.p + y.n : ℕ) : ℝ) ≤ ((y.p + x.n : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
theorem min_le_left (x y : Z) : (min x y).val ≤ x.val := by
  unfold min; cases h : le x y <;> simp
  · rw [Bool.eq_false_iff, ne_eq, le_iff] at h; linarith
theorem min_le_right (x y : Z) : (min x y).val ≤ y.val := by
  unfold min; cases h : le x y <;> simp
  · exact (le_iff x y).mp h
end Z

/-- a half-plane `n1 a + n2 b ≤ h` in shape coordinates -/
structure Con where
  n1 : Z
  n2 : Z
  h : Z

/-- a linear functional on `(Δ2, Δ3, D12, D13, D23)` -/
structure F5 where
  c1 : Z
  c2 : Z
  c3 : Z
  c4 : Z
  c5 : Z

noncomputable def F5.ev (c : F5) (x1 x2 x3 x4 x5 : ℝ) : ℝ :=
  c.c1.val * x1 + c.c2.val * x2 + c.c3.val * x3 + c.c4.val * x4 + c.c5.val * x5

/-- the grid denominator of box coordinates -/
def G : Nat := 4096

/-- one cell check: `c·z ≥ 0` (or `> 0`) on the cell `s ∈ [S0,S1]/G, ψ ∈ [P0,P1]/G, (a,b) ∈ ci ∩ cj`,
certified by the Farkas pair `ci, cj` -/
def fcheck (S0 S1 P0 P1 : Nat) (ci cj : Con) (c : F5) (strict : Bool) : Bool :=
  let Lm := Z.min (Z.add (Z.mul c.c1 (Z.ofN P0)) (Z.mul c.c2 (Z.ofN (G - P0))))
                  (Z.add (Z.mul c.c1 (Z.ofN P1)) (Z.mul c.c2 (Z.ofN (G - P1))))
  let d1 := Z.sub c.c3 c.c5
  let d2 := Z.sub c.c4 c.c5
  let det := Z.sub (Z.mul ci.n1 cj.n2) (Z.mul ci.n2 cj.n1)
  let Yi := Z.add (Z.neg (Z.mul d1 cj.n2)) (Z.mul d2 cj.n1)
  let Yj := Z.add (Z.neg (Z.mul d2 ci.n1)) (Z.mul d1 ci.n2)
  let sg := Z.pos det
  let D := cond sg det (Z.neg det)
  let Yi := cond sg Yi (Z.neg Yi)
  let Yj := cond sg Yj (Z.neg Yj)
  let mD := Z.sub (Z.mul D c.c5) (Z.add (Z.mul Yi ci.h) (Z.mul Yj cj.h))
  let E0 := Z.add (Z.mul (Z.mul (Z.ofN (G - S0)) Lm) D) (Z.mul (Z.ofN (S0 * G)) mD)
  let E1 := Z.add (Z.mul (Z.mul (Z.ofN (G - S1)) Lm) D) (Z.mul (Z.ofN (S1 * G)) mD)
  Z.pos D && Z.nonneg Yi && Z.nonneg Yj &&
    cond strict (Z.pos E0 && Z.pos E1) (Z.nonneg E0 && Z.nonneg E1)

/-- affine interpolation in `lam ∈ [S0 T/g, S1 T/g]` -/
theorem interp (α β T lam g S0 S1 : ℝ) (hT : 0 < T) (hg : 0 < g)
    (hs0 : S0 * T ≤ g * lam) (hs1 : g * lam ≤ S1 * T) :
    (0 ≤ α * (g - S0) + S0 * β → 0 ≤ α * (g - S1) + S1 * β → 0 ≤ α * (T - lam) + β * lam) ∧
    (0 < α * (g - S0) + S0 * β → 0 < α * (g - S1) + S1 * β → 0 < α * (T - lam) + β * lam) := by
  set E0 := α * (g - S0) + S0 * β
  set E1 := α * (g - S1) + S1 * β
  set R := α * (T - lam) + β * lam
  have id : g * (S1 - S0) * T * R = (S1 * T - g * lam) * (T * E0) + (g * lam - S0 * T) * (T * E1) := by
    simp only [E0, E1, R]; ring
  have hA : 0 ≤ S1 * T - g * lam := by linarith
  have hB : 0 ≤ g * lam - S0 * T := by linarith
  have hS : S0 ≤ S1 := le_of_mul_le_mul_right (le_trans hs0 hs1) hT
  constructor
  · intro h0 h1
    rcases eq_or_lt_of_le hS with hEq | hlt
    · have hl' : g * lam = S0 * T := le_antisymm (hEq ▸ hs1) hs0
      have e : g * R = T * E0 := by simp only [R, E0]; linear_combination (β - α) * hl'
      have : 0 ≤ g * R := by rw [e]; exact mul_nonneg hT.le h0
      exact (mul_nonneg_iff_of_pos_left hg).mp this
    · have hpos : 0 < g * (S1 - S0) * T := mul_pos (mul_pos hg (by linarith)) hT
      have : 0 ≤ g * (S1 - S0) * T * R := by
        rw [id]; exact add_nonneg (mul_nonneg hA (mul_nonneg hT.le h0)) (mul_nonneg hB (mul_nonneg hT.le h1))
      exact (mul_nonneg_iff_of_pos_left hpos).mp this
  · intro h0 h1
    rcases eq_or_lt_of_le hS with hEq | hlt
    · have hl' : g * lam = S0 * T := le_antisymm (hEq ▸ hs1) hs0
      have e : g * R = T * E0 := by simp only [R, E0]; linear_combination (β - α) * hl'
      have : 0 < g * R := by rw [e]; exact mul_pos hT h0
      exact pos_of_mul_pos_right this hg.le
    · have hpos : 0 < g * (S1 - S0) * T := mul_pos (mul_pos hg (by linarith)) hT
      have hsum : 0 < (S1 * T - g * lam) + (g * lam - S0 * T) := by nlinarith
      have h2 : 0 < (S1 * T - g * lam) * (T * E0) + (g * lam - S0 * T) * (T * E1) := by
        have p0 := mul_pos hT h0; have p1 := mul_pos hT h1
        rcases eq_or_lt_of_le hA with hA0 | hA0
        · have : 0 < g * lam - S0 * T := by linarith
          have := mul_pos this p1; have := mul_nonneg hA p0.le; linarith
        · have := mul_pos hA0 p0; have := mul_nonneg hB p1.le; linarith
      rw [← id] at h2
      exact pos_of_mul_pos_right h2 hpos.le

/-- shape part via a Farkas pair -/
theorem shape_part (a b c lam c3 c4 c5 D Yi Yj ni1 ni2 hi nj1 nj2 hj : ℝ) (hlam : lam = a + b + c)
    (hci : ni1 * a + ni2 * b ≤ hi * lam) (hcj : nj1 * a + nj2 * b ≤ hj * lam)
    (hYi : 0 ≤ Yi) (hYj : 0 ≤ Yj)
    (e1 : D * (c3 - c5) = -(Yi * ni1 + Yj * nj1)) (e2 : D * (c4 - c5) = -(Yi * ni2 + Yj * nj2)) :
    (D * c5 - (Yi * hi + Yj * hj)) * lam ≤ D * (c3 * a + c4 * b + c5 * c) := by
  have e : D * (c3 * a + c4 * b + c5 * c) = D * c5 * lam + (D * (c3 - c5)) * a + (D * (c4 - c5)) * b := by
    rw [hlam]; ring
  rw [e, e1, e2]
  have := mul_le_mul_of_nonneg_left hci hYi; have := mul_le_mul_of_nonneg_left hcj hYj
  linarith

/-- value part: linear in `Δ2 ∈ [P0 V, P1 V]/g` -/
theorem value_part (Δ2 Δ3 V g P0 P1 c1 c2 Lm : ℝ) (hV : V = Δ2 + Δ3) (hV0 : 0 ≤ V)
    (hp0 : P0 * V ≤ g * Δ2) (hp1 : g * Δ2 ≤ P1 * V)
    (hL0 : Lm ≤ c1 * P0 + c2 * (g - P0)) (hL1 : Lm ≤ c1 * P1 + c2 * (g - P1)) :
    Lm * V ≤ g * (c1 * Δ2 + c2 * Δ3) := by
  have e : g * (c1 * Δ2 + c2 * Δ3) = (c1 - c2) * (g * Δ2) + c2 * g * V := by rw [hV]; ring
  rw [e]
  have m0 := mul_le_mul_of_nonneg_left hL0 hV0; have m1 := mul_le_mul_of_nonneg_left hL1 hV0
  rcases le_total 0 (c1 - c2) with h | h
  · have := mul_le_mul_of_nonneg_left hp0 h; nlinarith
  · have := mul_le_mul_of_nonpos_left hp1 h; nlinarith

/-- real-number core of `fcheck` -/
theorem fcore (Δ2 Δ3 a b c lam T V g S0 S1 P0 P1 c1 c2 c3 c4 c5 Lm D Yi Yj ni1 ni2 hi nj1 nj2 hj : ℝ)
    (hV : V = Δ2 + Δ3) (hlam : lam = a + b + c) (hT : T = V + lam)
    (hΔ2 : 0 ≤ Δ2) (hΔ3 : 0 ≤ Δ3) (hl : 0 < lam) (hg : 0 < g)
    (hs0 : S0 * T ≤ g * lam) (hs1 : g * lam ≤ S1 * T)
    (hp0 : P0 * V ≤ g * Δ2) (hp1 : g * Δ2 ≤ P1 * V)
    (hL0 : Lm ≤ c1 * P0 + c2 * (g - P0)) (hL1 : Lm ≤ c1 * P1 + c2 * (g - P1))
    (hci : ni1 * a + ni2 * b ≤ hi * lam) (hcj : nj1 * a + nj2 * b ≤ hj * lam)
    (hD : 0 < D) (hYi : 0 ≤ Yi) (hYj : 0 ≤ Yj)
    (e1 : D * (c3 - c5) = -(Yi * ni1 + Yj * nj1)) (e2 : D * (c4 - c5) = -(Yi * ni2 + Yj * nj2)) :
    let mD := D * c5 - (Yi * hi + Yj * hj)
    let E0 := (g - S0) * Lm * D + S0 * g * mD
    let E1 := (g - S1) * Lm * D + S1 * g * mD
    (0 ≤ E0 → 0 ≤ E1 → 0 ≤ c1 * Δ2 + c2 * Δ3 + c3 * a + c4 * b + c5 * c) ∧
    (0 < E0 → 0 < E1 → 0 < c1 * Δ2 + c2 * Δ3 + c3 * a + c4 * b + c5 * c) := by
  intro mD E0 E1
  have hsh := shape_part a b c lam c3 c4 c5 D Yi Yj ni1 ni2 hi nj1 nj2 hj hlam hci hcj hYi hYj e1 e2
  have hV0 : 0 ≤ V := by rw [hV]; linarith
  have hva := value_part Δ2 Δ3 V g P0 P1 c1 c2 Lm hV hV0 hp0 hp1 hL0 hL1
  have hTpos : 0 < T := by rw [hT]; linarith
  have hi := interp (D * Lm) (g * mD) T lam g S0 S1 hTpos hg hs0 hs1
  have eE0 : D * Lm * (g - S0) + S0 * (g * mD) = E0 := by simp only [E0]; ring
  have eE1 : D * Lm * (g - S1) + S1 * (g * mD) = E1 := by simp only [E1]; ring
  rw [eE0, eE1] at hi
  -- g D (c·z) ≥ D Lm V + g mD lam
  have hVT : V = T - lam := by rw [hT]; ring
  have hc : D * Lm * (T - lam) + g * mD * lam ≤ g * D * (c1 * Δ2 + c2 * Δ3 + c3 * a + c4 * b + c5 * c) := by
    rw [← hVT]
    have := mul_le_mul_of_nonneg_left hva hD.le
    have := mul_le_mul_of_nonneg_left hsh hg.le
    have e : g * D * (c1 * Δ2 + c2 * Δ3 + c3 * a + c4 * b + c5 * c) =
      D * (g * (c1 * Δ2 + c2 * Δ3)) + g * (D * (c3 * a + c4 * b + c5 * c)) := by ring
    rw [e]; simp only [mD] at *; nlinarith
  have hgD : 0 < g * D := mul_pos hg hD
  constructor
  · intro h0 h1
    have := le_trans (hi.1 h0 h1) hc
    exact (mul_nonneg_iff_of_pos_left hgD).mp this
  · intro h0 h1
    have := lt_of_lt_of_le (hi.2 h0 h1) hc
    exact pos_of_mul_pos_right this hgD.le


/-- soundness of `fcheck` -/
theorem fcheck_sound (S0 S1 P0 P1 : Nat) (ci cj : Con) (c : F5) (strict : Bool)
    (hS0 : S0 ≤ G) (hS1 : S1 ≤ G) (hP0 : P0 ≤ G) (hP1 : P1 ≤ G)
    (Δ2 Δ3 a b cc : ℝ) (hΔ2 : 0 ≤ Δ2) (hΔ3 : 0 ≤ Δ3) (hl : 0 < a + b + cc)
    (hs0 : (S0 : ℝ) * (Δ2 + Δ3 + (a + b + cc)) ≤ (G : ℝ) * (a + b + cc))
    (hs1 : (G : ℝ) * (a + b + cc) ≤ (S1 : ℝ) * (Δ2 + Δ3 + (a + b + cc)))
    (hp0 : (P0 : ℝ) * (Δ2 + Δ3) ≤ (G : ℝ) * Δ2) (hp1 : (G : ℝ) * Δ2 ≤ (P1 : ℝ) * (Δ2 + Δ3))
    (hci : ci.n1.val * a + ci.n2.val * b ≤ ci.h.val * (a + b + cc))
    (hcj : cj.n1.val * a + cj.n2.val * b ≤ cj.h.val * (a + b + cc))
    (h : fcheck S0 S1 P0 P1 ci cj c strict = true) :
    0 ≤ c.ev Δ2 Δ3 a b cc ∧ (strict = true → 0 < c.ev Δ2 Δ3 a b cc) := by
  unfold fcheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hD, hYi⟩, hYj⟩, hE⟩ := h
  have cG : ((G - S0 : ℕ) : ℝ) = (G : ℝ) - S0 := by push_cast [Nat.cast_sub hS0]; ring
  have cG1 : ((G - S1 : ℕ) : ℝ) = (G : ℝ) - S1 := by push_cast [Nat.cast_sub hS1]; ring
  have cP0 : ((G - P0 : ℕ) : ℝ) = (G : ℝ) - P0 := by push_cast [Nat.cast_sub hP0]; ring
  have cP1 : ((G - P1 : ℕ) : ℝ) = (G : ℝ) - P1 := by push_cast [Nat.cast_sub hP1]; ring
  have hG : (0 : ℝ) < G := by norm_num [G]
  set L0 := Z.add (Z.mul c.c1 (Z.ofN P0)) (Z.mul c.c2 (Z.ofN (G - P0)))
  set L1 := Z.add (Z.mul c.c1 (Z.ofN P1)) (Z.mul c.c2 (Z.ofN (G - P1)))
  have hL0 : (Z.min L0 L1).val ≤ c.c1.val * P0 + c.c2.val * ((G : ℝ) - P0) := by
    have := Z.min_le_left L0 L1; simp only [L0, Z.val_add, Z.val_mul, Z.val_ofN, cP0] at this; exact this
  have hL1 : (Z.min L0 L1).val ≤ c.c1.val * P1 + c.c2.val * ((G : ℝ) - P1) := by
    have := Z.min_le_right L0 L1; simp only [L1, Z.val_add, Z.val_mul, Z.val_ofN, cP1] at this; exact this
  set det := Z.sub (Z.mul ci.n1 cj.n2) (Z.mul ci.n2 cj.n1)
  set Yi0 := Z.add (Z.neg (Z.mul (Z.sub c.c3 c.c5) cj.n2)) (Z.mul (Z.sub c.c4 c.c5) cj.n1)
  set Yj0 := Z.add (Z.neg (Z.mul (Z.sub c.c4 c.c5) ci.n1)) (Z.mul (Z.sub c.c3 c.c5) ci.n2)
  -- the generic conclusion for any sign choice
  have main : ∀ (D Yi Yj : Z), 0 < D.val → 0 ≤ Yi.val → 0 ≤ Yj.val →
      D.val * (c.c3.val - c.c5.val) = -(Yi.val * ci.n1.val + Yj.val * cj.n1.val) →
      D.val * (c.c4.val - c.c5.val) = -(Yi.val * ci.n2.val + Yj.val * cj.n2.val) →
      cond strict
        (Z.pos (Z.add (Z.mul (Z.mul (Z.ofN (G - S0)) (Z.min L0 L1)) D)
            (Z.mul (Z.ofN (S0 * G)) (Z.sub (Z.mul D c.c5) (Z.add (Z.mul Yi ci.h) (Z.mul Yj cj.h))))) &&
         Z.pos (Z.add (Z.mul (Z.mul (Z.ofN (G - S1)) (Z.min L0 L1)) D)
            (Z.mul (Z.ofN (S1 * G)) (Z.sub (Z.mul D c.c5) (Z.add (Z.mul Yi ci.h) (Z.mul Yj cj.h))))))
        (Z.nonneg (Z.add (Z.mul (Z.mul (Z.ofN (G - S0)) (Z.min L0 L1)) D)
            (Z.mul (Z.ofN (S0 * G)) (Z.sub (Z.mul D c.c5) (Z.add (Z.mul Yi ci.h) (Z.mul Yj cj.h))))) &&
         Z.nonneg (Z.add (Z.mul (Z.mul (Z.ofN (G - S1)) (Z.min L0 L1)) D)
            (Z.mul (Z.ofN (S1 * G)) (Z.sub (Z.mul D c.c5) (Z.add (Z.mul Yi ci.h) (Z.mul Yj cj.h)))))) = true →
      0 ≤ c.ev Δ2 Δ3 a b cc ∧ (strict = true → 0 < c.ev Δ2 Δ3 a b cc) := by
    intro D Yi Yj hD hYi hYj e1 e2 hE
    have core := fcore Δ2 Δ3 a b cc (a + b + cc) (Δ2 + Δ3 + (a + b + cc)) (Δ2 + Δ3) (G : ℝ) S0 S1 P0 P1
      c.c1.val c.c2.val c.c3.val c.c4.val c.c5.val (Z.min L0 L1).val D.val Yi.val Yj.val
      ci.n1.val ci.n2.val ci.h.val cj.n1.val cj.n2.val cj.h.val rfl rfl rfl hΔ2 hΔ3 hl hG
      hs0 hs1 hp0 hp1 hL0 hL1 hci hcj hD hYi hYj e1 e2
    simp only at core
    have ev : c.ev Δ2 Δ3 a b cc = c.c1.val * Δ2 + c.c2.val * Δ3 + c.c3.val * a + c.c4.val * b + c.c5.val * cc := rfl
    rw [ev]
    cases strict with
    | false =>
      simp only [cond, Bool.and_eq_true, Z.nonneg_iff, Z.val_add, Z.val_mul, Z.val_ofN, Z.val_sub, cG, cG1,
        Nat.cast_mul] at hE
      exact ⟨core.1 (by linarith [hE.1]) (by linarith [hE.2]), by simp⟩
    | true =>
      simp only [cond, Bool.and_eq_true, Z.pos_iff, Z.val_add, Z.val_mul, Z.val_ofN, Z.val_sub, cG, cG1,
        Nat.cast_mul] at hE
      have := core.2 (by linarith [hE.1]) (by linarith [hE.2])
      exact ⟨this.le, fun _ => this⟩
  cases hsg : Z.pos det with
  | true =>
    simp only [hsg, cond] at hYi hYj hE
    rw [Z.nonneg_iff] at hYi hYj
    refine main det Yi0 Yj0 ((Z.pos_iff det).mp hsg) hYi hYj ?_ ?_ hE <;>
      simp only [det, Yi0, Yj0, Z.val_add, Z.val_sub, Z.val_mul, Z.val_neg] <;> ring
  | false =>
    simp only [hsg, cond] at hD hYi hYj hE
    rw [Z.pos_iff] at hD; rw [Z.nonneg_iff] at hYi hYj
    refine main (Z.neg det) (Z.neg Yi0) (Z.neg Yj0) hD hYi hYj ?_ ?_ hE <;>
      simp only [det, Yi0, Yj0, Z.val_add, Z.val_sub, Z.val_mul, Z.val_neg] <;> ring


/-! ## The computational checker -/

/-- enclosure grid -/
def E : Nat := 16777216

def zN (k : Nat) : Z := ⟨k, 0⟩
def zM (k : Nat) : Z := ⟨0, k⟩

/-- a cell box on the grid `G`: `s ∈ [s0,s1]/G, ψ ∈ [p0,p1]/G, a ∈ [a0,a1]/G, b ∈ [b0,b1]/G` -/
structure Box where
  s0 : Nat
  s1 : Nat
  p0 : Nat
  p1 : Nat
  a0 : Nat
  a1 : Nat
  b0 : Nat
  b1 : Nat

def isStrip (b : Box) : Bool := Nat.ble 8 b.s0
/-- strip tiers: `heron ≤ λ²/tierDen` for `s ≥ 1/8, 1/64, 1/512` -/
def tierDen (b : Box) : Nat := cond (Nat.ble 512 b.s0) 1048576 (cond (Nat.ble 64 b.s0) 8192 128)

/-- the half-planes of a cell (scaled to integers): box sides, `a + b ≤ 1`, the outer tangent cut and,
for strip cells, the inner cut -/
def con (b : Box) (k : Nat) : Con :=
  let X := b.a0 + b.a1
  let Y := b.b0 + b.b1
  let g1 := Z.sub (zN (8 * G)) (zN (8 * X + 4 * Y))
  let g2 := Z.sub (zN (8 * G)) (zN (4 * X + 8 * Y))
  let H := Z.sub (zN (8 * G * X + 8 * G * Y)) (zN (4 * X * X + 4 * X * Y + 4 * Y * Y + 4 * G * G))
  let gc := Z.add (Z.mul g1 (zN X)) (Z.mul g2 (zN Y))
  let WA := b.a1 - b.a0
  let WB := b.b1 - b.b0
  match k with
  | 0 => ⟨zM G, zN 0, zM b.a0⟩
  | 1 => ⟨zN G, zN 0, zN b.a1⟩
  | 2 => ⟨zN 0, zM G, zM b.b0⟩
  | 3 => ⟨zN 0, zN G, zN b.b1⟩
  | 4 => ⟨zN 1, zN 1, zN 1⟩
  | 5 => ⟨Z.neg (Z.mul (zN (2 * G)) g1), Z.neg (Z.mul (zN (2 * G)) g2), Z.add (Z.neg gc) H⟩
  | 6 => cond (isStrip b)
      ⟨Z.mul (zN (2 * G)) g1, Z.mul (zN (2 * G)) g2,
        Z.add (Z.sub gc H) (zN (G * G / tierDen b * 4 + 4 * (WA * WA + WA * WB + WB * WB)))⟩
      ⟨zN 0, zN 0, zN 0⟩
  | _ => ⟨zN 0, zN 0, zN 0⟩

def F5.lin (x : Z) (c : F5) (y : Z) (d : F5) : F5 :=
  ⟨Z.add (Z.mul x c.c1) (Z.mul y d.c1), Z.add (Z.mul x c.c2) (Z.mul y d.c2), Z.add (Z.mul x c.c3) (Z.mul y d.c3),
   Z.add (Z.mul x c.c4) (Z.mul y d.c4), Z.add (Z.mul x c.c5) (Z.mul y d.c5)⟩
def F5.add (c d : F5) : F5 := ⟨Z.add c.c1 d.c1, Z.add c.c2 d.c2, Z.add c.c3 d.c3, Z.add c.c4 d.c4, Z.add c.c5 d.c5⟩
def F5.neg (c : F5) : F5 := ⟨Z.neg c.c1, Z.neg c.c2, Z.neg c.c3, Z.neg c.c4, Z.neg c.c5⟩
def F5.zero : F5 := ⟨zN 0, zN 0, zN 0, zN 0, zN 0⟩
/-- `λ = D12 + D13 + D23` -/
def LL : F5 := ⟨zN 0, zN 0, zN 1, zN 1, zN 1⟩

/-- check on the cell of box `b` with the Farkas pair encoded as `8 i + j` -/
def chk (b : Box) (pr : Nat) (c : F5) (strict : Bool) : Bool :=
  fcheck b.s0 b.s1 b.p0 b.p1 (con b (pr / 8)) (con b (pr % 8)) c strict

/-! ### bit-field decoding -/

def rd (x k : Nat) : Nat := x % 2 ^ k
def sh (x k : Nat) : Nat := x / 2 ^ k

/-- certificate of a feasible branch -/
structure Feas where
  lo1 : Nat
  hi1 : Nat
  lo2 : Nat
  hi2 : Nat
  lo3 : Nat
  hi3 : Nat
  lo4 : Nat
  hi4 : Nat
  U : Nat
  wneg : Nat
  wpos : Nat
  prs : Nat        -- ten 6-bit Farkas pairs
  prunes : List Nat


/-! ### branch data (16-scaled functionals of `z = (Δ2, Δ3, D12, D13, D23)`):
`T'`, `λ'`, `V' = Δ2' + Δ3'`, `Δ2'`, `D12'`, `D13'` of the new state, and the decision conjuncts -/
def brT : Nat → F5
  | 1 => ⟨⟨24, 0⟩, ⟨32, 0⟩, ⟨28, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩
  | 2 => ⟨⟨16, 0⟩, ⟨16, 0⟩, ⟨32, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 3 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩
  | 4 => ⟨⟨12, 0⟩, ⟨8, 0⟩, ⟨31, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩⟩
  | 5 => ⟨⟨4, 0⟩, ⟨0, 8⟩, ⟨23, 0⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩
  | 6 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨22, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩⟩
  | 7 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨22, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩⟩
  | 8 => ⟨⟨4, 0⟩, ⟨0, 8⟩, ⟨13, 0⟩, ⟨10, 0⟩, ⟨10, 0⟩⟩
  | 9 => ⟨⟨12, 0⟩, ⟨8, 0⟩, ⟨21, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  | _ => F5.zero
def brL : Nat → F5
  | 1 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 8⟩, ⟨64, 0⟩, ⟨64, 0⟩⟩
  | 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩
  | 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩
  | 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨22, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩⟩
  | 5 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨22, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩⟩
  | 6 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨22, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩⟩
  | 7 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨22, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩⟩
  | 8 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨22, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩⟩
  | 9 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨22, 0⟩, ⟨4, 0⟩, ⟨4, 0⟩⟩
  | _ => F5.zero
def brV : Nat → F5
  | 1 => ⟨⟨24, 0⟩, ⟨32, 0⟩, ⟨36, 0⟩, ⟨0, 48⟩, ⟨0, 48⟩⟩
  | 2 => ⟨⟨16, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩, ⟨0, 16⟩, ⟨0, 16⟩⟩
  | 3 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 4 => ⟨⟨12, 0⟩, ⟨8, 0⟩, ⟨9, 0⟩, ⟨0, 6⟩, ⟨0, 6⟩⟩
  | 5 => ⟨⟨4, 0⟩, ⟨0, 8⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  | 6 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 7 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 8 => ⟨⟨4, 0⟩, ⟨0, 8⟩, ⟨0, 9⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩
  | 9 => ⟨⟨12, 0⟩, ⟨8, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩⟩
  | _ => F5.zero
def brD : Nat → F5
  | 1 => ⟨⟨8, 0⟩, ⟨32, 0⟩, ⟨36, 0⟩, ⟨0, 48⟩, ⟨0, 48⟩⟩
  | 2 => ⟨⟨0, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩, ⟨0, 16⟩, ⟨0, 16⟩⟩
  | 3 => ⟨⟨0, 0⟩, ⟨0, 16⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩
  | 4 => ⟨⟨0, 4⟩, ⟨8, 0⟩, ⟨9, 0⟩, ⟨0, 6⟩, ⟨0, 6⟩⟩
  | 5 => ⟨⟨0, 12⟩, ⟨0, 8⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  | 6 => ⟨⟨4, 0⟩, ⟨0, 8⟩, ⟨0, 9⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩
  | 7 => ⟨⟨12, 0⟩, ⟨8, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩⟩
  | 8 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 9 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | _ => F5.zero
def brA : Nat → F5
  | 1 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 12⟩, ⟨16, 0⟩, ⟨48, 0⟩⟩
  | 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩⟩
  | 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩⟩
  | 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | 5 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | 6 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | 7 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | 8 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 9 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | _ => F5.zero
def brB : Nat → F5
  | 1 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 12⟩, ⟨48, 0⟩, ⟨16, 0⟩⟩
  | 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩⟩
  | 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | 5 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | 6 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 7 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 8 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | 9 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | _ => F5.zero
/-- decision conjuncts: `(c, true)` means `0 ≤ c·z`, `(c, false)` means `c·z < 0` (16-scaled) -/
def brConds : Nat → List (F5 × Bool)
  | 1 => [(⟨⟨0, 0⟩, ⟨0, 16⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, false), (⟨⟨0, 8⟩, ⟨0, 16⟩, ⟨0, 20⟩, ⟨32, 0⟩, ⟨32, 0⟩⟩, false)]
  | 2 => [(⟨⟨0, 0⟩, ⟨0, 16⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, false), (⟨⟨0, 8⟩, ⟨0, 16⟩, ⟨0, 20⟩, ⟨32, 0⟩, ⟨32, 0⟩⟩, true)]
  | 3 => [(⟨⟨0, 0⟩, ⟨0, 16⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, true), (⟨⟨0, 16⟩, ⟨0, 16⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, false)]
  | 4 => [(⟨⟨0, 16⟩, ⟨0, 16⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, true), (⟨⟨0, 16⟩, ⟨0, 32⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, false), (⟨⟨4, 0⟩, ⟨0, 8⟩, ⟨0, 9⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩, false)]
  | 5 => [(⟨⟨0, 16⟩, ⟨0, 32⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, true), (⟨⟨12, 0⟩, ⟨8, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩⟩, false)]
  | 6 => [(⟨⟨0, 16⟩, ⟨0, 16⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, true), (⟨⟨0, 16⟩, ⟨0, 32⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, false), (⟨⟨4, 0⟩, ⟨0, 8⟩, ⟨0, 9⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩, true), (⟨⟨0, 12⟩, ⟨0, 8⟩, ⟨0, 9⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩, false)]
  | 7 => [(⟨⟨0, 16⟩, ⟨0, 32⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, true), (⟨⟨12, 0⟩, ⟨8, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩⟩, true), (⟨⟨0, 4⟩, ⟨8, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩⟩, false)]
  | 8 => [(⟨⟨0, 16⟩, ⟨0, 16⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, true), (⟨⟨0, 16⟩, ⟨0, 32⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, false), (⟨⟨0, 12⟩, ⟨0, 8⟩, ⟨0, 9⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩, true)]
  | 9 => [(⟨⟨0, 16⟩, ⟨0, 32⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩, true), (⟨⟨0, 4⟩, ⟨8, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩⟩, true)]
  | _ => []

/-- `log2 α` per branch: `+1` (expansion), `0` (reflections), `-1` (contractions) -/
def alphaUp (k : Nat) : Bool := Nat.beq k 1
def alphaDown (k : Nat) : Bool := Nat.ble 4 k

/-- infeasibility from the s-range: Rx needs `s ≥ 1/5`, contractions need `s > 1/2` -/
def sInfeasible (b : Box) (k : Nat) : Bool :=
  (Nat.beq k 2 && Nat.blt (5 * b.s1) G) || (Nat.ble 4 k && Nat.ble (2 * b.s1) G)

def nth {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, i + 1 => nth l i

/-- infeasibility from one decision conjunct -/
def conjInfeasible (b : Box) (k i pr : Nat) : Bool :=
  match nth (brConds k) i with
  | some (c, true) => chk b pr (F5.neg c) true
  | some (c, false) => chk b pr c false
  | none => false

/-! ### k-d tree -/

inductive KT
  | leaf (n : Nat) (hole : Bool)
  | node (d : Nat) (v : Nat) (mx : Nat) (l r : KT)

def Box.lo (b : Box) (d : Nat) : Nat :=
  match d with | 0 => b.s0 | 1 => b.p0 | 2 => b.a0 | _ => b.b0
def Box.hi (b : Box) (d : Nat) : Nat :=
  match d with | 0 => b.s1 | 1 => b.p1 | 2 => b.a1 | _ => b.b1
def Box.setHi (b : Box) (d v : Nat) : Box :=
  match d with
  | 0 => { b with s1 := v } | 1 => { b with p1 := v } | 2 => { b with a1 := v } | _ => { b with b1 := v }
def Box.setLo (b : Box) (d v : Nat) : Box :=
  match d with
  | 0 => { b with s0 := v } | 1 => { b with p0 := v } | 2 => { b with a0 := v } | _ => { b with b0 := v }

def rootBox : Box := ⟨0, G, 0, G, 0, G, 0, G⟩

def KT.top : KT → Nat
  | .leaf n hole => cond hole 0 n
  | .node _ _ mx _ _ => mx

def mxOK : KT → Bool
  | .leaf _ _ => true
  | .node _ _ mx l r => Nat.ble l.top mx && Nat.ble r.top mx && mxOK l && mxOK r

/-- the `i`-th decision conjunct as a functional that is `≥ 0` on the branch -/
def scF (cs : List (F5 × Bool)) (i : Nat) : F5 :=
  match nth cs i with
  | some (c, true) => c
  | some (c, false) => F5.neg c
  | none => F5.zero

/-- prune certificate check: no state of cell `b` following branch `k` lands in the target box `tb` -/
def pruneOK (b : Box) (k : Nat) (p : Nat) (tb : Box) : Bool :=
  let w := fun i => zN (rd (sh p (32 * i)) 32)
  let cs := brConds k
  let sc := fun i => scF cs i
  let T1 := brT k
  let L1 := brL k
  let V1 := brV k
  let D2 := brD k
  let A1 := brA k
  let B1 := brB k
  let S := F5.add (F5.lin (w 0) (sc 0) (w 1) (sc 1)) (F5.lin (w 2) (sc 2) (w 3) (sc 3))
  let S := F5.add S (F5.lin (w 4) (F5.lin (zN G) L1 (zM tb.s0) T1) (w 5) (F5.lin (zN tb.s1) T1 (zM G) L1))
  let S := F5.add S (F5.lin (w 6) (F5.lin (zN G) D2 (zM tb.p0) V1) (w 7) (F5.lin (zN tb.p1) V1 (zM G) D2))
  let S := F5.add S (F5.lin (w 8) (F5.lin (zN G) A1 (zM tb.a0) L1) (w 9) (F5.lin (zN tb.a1) L1 (zM G) A1))
  let S := F5.add S (F5.lin (w 10) (F5.lin (zN G) B1 (zM tb.b0) L1) (w 11) (F5.lin (zN tb.b1) L1 (zM G) B1))
  chk b (rd (sh p 384) 6) (F5.neg S) true

/-- all non-hole leaves meeting the enclosure `enc` (on the grid `E = 4096 G`) have `n + wneg ≤ bound`,
except those excluded, in traversal order, by the prune certificates -/
def query (ok : Nat → Box → Bool) (enc : Box) (bound wneg : Nat) : KT → Box → List Nat → Option (List Nat)
  | .leaf n hole, b, ps =>
      cond (hole || Nat.ble (n + wneg) bound) (some ps)
        (match ps with
         | [] => none
         | p :: ps' => cond (ok p b) (some ps') none)
  | .node d v mx l r, b, ps =>
      cond (Nat.ble (mx + wneg) bound) (some ps)
        (match cond (Nat.ble (enc.lo d) (v * 4096)) (query ok enc bound wneg l (b.setHi d v) ps) (some ps) with
         | none => none
         | some ps' => cond (Nat.ble (v * 4096) (enc.hi d)) (query ok enc bound wneg r (b.setLo d v) ps') (some ps'))

/-- the potential-factor check `(α⁸ U⁻⁷ (m'/M)⁷)²⁵⁶ ≥ 2^w`, or an exact override with `w ≤ 0` -/
def wOK (b : Box) (k : Nat) (f : Feas) : Bool :=
  let mN := Nat.min (5 * f.lo1) E
  let MN := Nat.min (5 * b.s1) G
  let num := (mN * G) ^ 1792 * 2 ^ (cond (alphaUp k) 2048 0 + f.wneg)
  let den := (f.U * MN) ^ 1792 * 2 ^ (cond (alphaDown k) 2048 0 + f.wpos)
  Nat.ble den num ||
    (Nat.beq f.wpos 0 &&
      (Nat.beq k 3 || (Nat.beq k 1 && Nat.ble (5 * b.s1) G && Nat.ble (5 * f.hi1) E) ||
        (Nat.beq k 2 && Nat.ble G (5 * b.s0) && Nat.ble E (5 * f.lo1))))

def Feas.enc (f : Feas) : Box := ⟨f.lo1, f.hi1, f.lo2, f.hi2, f.lo3, f.hi3, f.lo4, f.hi4⟩

/-- the checks of a feasible branch -/
def chkFeas (tr : KT) (b : Box) (n k : Nat) (f : Feas) : Bool :=
  let pr := fun i => rd (sh f.prs (6 * i)) 6
  let T1 := brT k
  let L1 := brL k
  let V1 := brV k
  let D2 := brD k
  let A1 := brA k
  let B1 := brB k
  (Nat.beq f.lo1 0 || chk b (pr 0) (F5.lin (zN E) L1 (zM f.lo1) T1) false) &&
  (Nat.ble E f.hi1 || chk b (pr 1) (F5.lin (zN f.hi1) T1 (zM E) L1) false) &&
  (Nat.beq f.lo2 0 || chk b (pr 2) (F5.lin (zN E) D2 (zM f.lo2) V1) false) &&
  (Nat.ble E f.hi2 || chk b (pr 3) (F5.lin (zN f.hi2) V1 (zM E) D2) false) &&
  (Nat.beq f.lo3 0 || chk b (pr 4) (F5.lin (zN E) A1 (zM f.lo3) L1) false) &&
  (Nat.ble E f.hi3 || chk b (pr 5) (F5.lin (zN f.hi3) L1 (zM E) A1) false) &&
  (Nat.beq f.lo4 0 || chk b (pr 6) (F5.lin (zN E) B1 (zM f.lo4) L1) false) &&
  (Nat.ble E f.hi4 || chk b (pr 7) (F5.lin (zN f.hi4) L1 (zM E) B1) false) &&
  chk b (pr 8) (F5.lin (zN (16 * f.U)) LL (zM E) L1) false &&
  (Nat.beq f.lo2 0 || chk b (pr 9) V1 true) &&
  wOK b k f &&
  (query (pruneOK b k) f.enc (n + f.wpos) f.wneg tr rootBox f.prunes).isSome

/-! ### decoding -/

def readList : Nat → Nat → List Nat × Nat
  | 0, x => ([], x)
  | m + 1, x => let r := readList m (sh x 390); (rd x 390 :: r.1, r.2)

def readFeas (x : Nat) : Feas × Nat :=
  let np := rd (sh x 313) 16
  let r := readList np (sh x 329)
  (⟨rd x 25, rd (sh x 25) 25, rd (sh x 50) 25, rd (sh x 75) 25, rd (sh x 100) 25, rd (sh x 125) 25,
    rd (sh x 150) 25, rd (sh x 175) 25, rd (sh x 200) 32,
    cond (Nat.beq (rd (sh x 232) 1) 1) (rd (sh x 233) 20) 0,
    cond (Nat.beq (rd (sh x 232) 1) 1) 0 (rd (sh x 233) 20),
    rd (sh x 253) 60, r.1⟩, r.2)

/-- one branch: tag 0 = s-range infeasible, 1 = conjunct infeasible, 2 = feasible -/
def chkBranch (tr : KT) (b : Box) (n k x : Nat) : Bool × Nat :=
  let tag := rd x 2
  let y := sh x 2
  cond (Nat.beq tag 0) (sInfeasible b k, y)
    (cond (Nat.beq tag 1) (conjInfeasible b k (rd y 2) (rd (sh y 2) 6), sh y 8)
      (let r := readFeas y; (chkFeas tr b n k r.1, r.2)))

def chkLeaf (tr : KT) (b : Box) (n x : Nat) : Bool :=
  let r1 := chkBranch tr b n 1 x
  let r2 := chkBranch tr b n 2 r1.2
  let r3 := chkBranch tr b n 3 r2.2
  let r4 := chkBranch tr b n 4 r3.2
  let r5 := chkBranch tr b n 5 r4.2
  let r6 := chkBranch tr b n 6 r5.2
  let r7 := chkBranch tr b n 7 r6.2
  let r8 := chkBranch tr b n 8 r7.2
  let r9 := chkBranch tr b n 9 r8.2
  Nat.ble b.s0 b.s1 && Nat.ble b.s1 G && Nat.ble b.p0 b.p1 && Nat.ble b.p1 G &&
  r1.1 && r2.1 && r3.1 && r4.1 && r5.1 && r6.1 && r7.1 && r8.1 && r9.1

/-- a hole: the cell is empty, certified by three half-planes -/
def chkHole (b : Box) (x : Nat) : Bool :=
  let ci := con b (rd x 3)
  let cj := con b (rd (sh x 3) 3)
  let ck := con b (rd (sh x 6) 3)
  let yi := Z.sub (Z.mul cj.n1 ck.n2) (Z.mul cj.n2 ck.n1)
  let yj := Z.sub (Z.mul ck.n1 ci.n2) (Z.mul ck.n2 ci.n1)
  let yk := Z.sub (Z.mul ci.n1 cj.n2) (Z.mul ci.n2 cj.n1)
  let S := Z.add (Z.add (Z.mul yi ci.h) (Z.mul yj cj.h)) (Z.mul yk ck.h)
  (Z.nonneg yi && Z.nonneg yj && Z.nonneg yk && Z.pos (Z.neg S)) ||
  (Z.nonneg (Z.neg yi) && Z.nonneg (Z.neg yj) && Z.nonneg (Z.neg yk) && Z.pos S)

/-- walk the leaves of a subtree, consuming one certificate per leaf -/
def walk (tr : KT) : KT → Box → List Nat → Option (List Nat)
  | .leaf n hole, b, c :: cs => cond (cond hole (chkHole b c) (chkLeaf tr b n c)) (some cs) none
  | .leaf _ _, _, [] => none
  | .node d v _ l r, b, cs =>
      match walk tr l (b.setHi d v) cs with
      | none => none
      | some cs' => walk tr r (b.setLo d v) cs'

end NMC
