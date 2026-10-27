import Mathlib

/-! Generic soundness lemma for the cell checks:
a linear functional `c·z` is nonnegative on a cell given by
  s0·T ≤ λ ≤ s1·T,   ψ0·V ≤ Δ2 ≤ ψ1·V  (V = Δ2+Δ3),   n_i·(D12,D13) ≤ h_i·λ  (polygon half-planes),
from a lower bound `L` for the value part, a Farkas pair for the shape part, and two endpoint checks. -/

namespace NMCheck

theorem functional_nonneg
    (Δ2 Δ3 D12 D13 D23 : ℝ) (hΔ2 : 0 ≤ Δ2) (hΔ3 : 0 ≤ Δ3)
    (s0 s1 c1 c2 c3 c4 c5 L ni1 ni2 hi nj1 nj2 hj yi yj : ℝ)
    (hlam0 : 0 < D12 + D13 + D23)
    (hs0 : s0 * (Δ2 + Δ3 + (D12 + D13 + D23)) ≤ D12 + D13 + D23)
    (hs1 : D12 + D13 + D23 ≤ s1 * (Δ2 + Δ3 + (D12 + D13 + D23)))
    (hL : L * (Δ2 + Δ3) ≤ c1 * Δ2 + c2 * Δ3)
    (hpi : ni1 * D12 + ni2 * D13 ≤ hi * (D12 + D13 + D23))
    (hpj : nj1 * D12 + nj2 * D13 ≤ hj * (D12 + D13 + D23))
    (hyi : 0 ≤ yi) (hyj : 0 ≤ yj)
    (hf1 : c3 - c5 = -(yi * ni1 + yj * nj1)) (hf2 : c4 - c5 = -(yi * ni2 + yj * nj2))
    (hE0 : 0 ≤ (1 - s0) * L + s0 * (c5 - yi * hi - yj * hj))
    (hE1 : 0 ≤ (1 - s1) * L + s1 * (c5 - yi * hi - yj * hj)) :
    0 ≤ c1 * Δ2 + c2 * Δ3 + c3 * D12 + c4 * D13 + c5 * D23 := by
  set lam := D12 + D13 + D23 with hlam
  set T := Δ2 + Δ3 + lam
  set m := c5 - yi * hi - yj * hj
  -- shape part ≥ m λ
  have hshape : m * lam ≤ c3 * D12 + c4 * D13 + c5 * D23 := by
    have e : c3 * D12 + c4 * D13 + c5 * D23 = c5 * lam + (c3 - c5) * D12 + (c4 - c5) * D13 := by
      rw [hlam]; ring
    rw [e, hf1, hf2]
    nlinarith [mul_le_mul_of_nonneg_left hpi hyi, mul_le_mul_of_nonneg_left hpj hyj]
  -- value part ≥ L (T - λ)
  have hT : Δ2 + Δ3 = T - lam := by simp only [T]; ring
  rw [hT] at hL
  -- combine: L (T - λ) + m λ is affine in λ ∈ [s0 T, s1 T], nonneg at both ends
  have hTpos : 0 ≤ T := by simp only [T]; linarith
  have key : 0 ≤ L * (T - lam) + m * lam := by
    -- write λ = θ s0 T + (1-θ) s1 T ... use linear interpolation via nlinarith
    have h0 : 0 ≤ (1 - s0) * L * T + s0 * m * T := by nlinarith
    have h1 : 0 ≤ (1 - s1) * L * T + s1 * m * T := by nlinarith
    by_cases hd : s1 * T - s0 * T = 0
    · -- λ = s0 T
      have : lam = s0 * T := by linarith
      rw [this]; nlinarith
    · have hpos : 0 < s1 * T - s0 * T := lt_of_le_of_ne (by linarith) (Ne.symm hd)
      have X0 : 0 ≤ ((1 - s0) * L + s0 * m) * T := mul_nonneg hE0 hTpos
      have X1 : 0 ≤ ((1 - s1) * L + s1 * m) * T := mul_nonneg hE1 hTpos
      have id : (s1 * T - s0 * T) * (L * (T - lam) + m * lam) =
          (s1 * T - lam) * (((1 - s0) * L + s0 * m) * T) + (lam - s0 * T) * (((1 - s1) * L + s1 * m) * T) := by
        ring
      have : 0 ≤ (s1 * T - s0 * T) * (L * (T - lam) + m * lam) := by
        rw [id]; exact add_nonneg (mul_nonneg (by linarith) X0) (mul_nonneg (by linarith) X1)
      exact nonneg_of_mul_nonneg_right this hpos
  linarith
end NMCheck

namespace NMCheck

/-- normalized Heron function in shape coordinates (a, b) = (D12, D13)/λ -/
def heronab (a b : ℝ) : ℝ := -4*a^2 - 4*a*b - 4*b^2 + 4*a + 4*b - 1

def Bq (u v : ℝ) : ℝ := 4*u^2 + 4*u*v + 4*v^2

theorem heron_expand (a b c1 c2 : ℝ) :
    heronab a b = heronab c1 c2 + ((-8*c1 - 4*c2 + 4) * (a - c1) + (-4*c1 - 8*c2 + 4) * (b - c2))
      - Bq (a - c1) (b - c2) := by
  simp only [heronab, Bq]; ring

theorem Bq_nonneg (u v : ℝ) : 0 ≤ Bq u v := by
  unfold Bq; nlinarith [sq_nonneg (u+v), sq_nonneg u, sq_nonneg v]

/-- outer cut: valid shapes lie on one side of the tangent plane at any centre -/
theorem outer_cut (a b c1 c2 : ℝ) (h : 0 ≤ heronab a b) :
    -heronab c1 c2 ≤ (-8*c1 - 4*c2 + 4) * (a - c1) + (-4*c1 - 8*c2 + 4) * (b - c2) := by
  have := heron_expand a b c1 c2; have := Bq_nonneg (a - c1) (b - c2); linarith

/-- the Hessian form on a box is bounded by its values at the corners (convex in each variable) -/
theorem Bq_le_corners (u v u0 u1 v0 v1 M : ℝ) (hu0 : u0 ≤ u) (hu1 : u ≤ u1) (hv0 : v0 ≤ v) (hv1 : v ≤ v1)
    (h00 : Bq u0 v0 ≤ M) (h01 : Bq u0 v1 ≤ M) (h10 : Bq u1 v0 ≤ M) (h11 : Bq u1 v1 ≤ M) : Bq u v ≤ M := by
  -- secant bounds: u^2 ≤ (u0+u1)u - u0 u1,  v^2 ≤ (v0+v1)v - v0 v1
  have su : u^2 ≤ (u0+u1)*u - u0*u1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu0) (sub_nonneg.mpr hu1)]
  have sv : v^2 ≤ (v0+v1)*v - v0*v1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hv0) (sub_nonneg.mpr hv1)]
  -- the bilinear interpolant I(u,v) is ≤ M (bilinear, so a convex combination of corner values)
  set I := 4*((u0+u1)*u - u0*u1) + 4*u*v + 4*((v0+v1)*v - v0*v1)
  have hI : I ≤ M := by
    -- affine in u (slope 4(u0+u1)+4v) and then affine in v
    have fv : ∀ uu, uu = u0 ∨ uu = u1 →
        4*((u0+u1)*uu - u0*u1) + 4*uu*v + 4*((v0+v1)*v - v0*v1) ≤ M := by
      intro uu huu
      have hc0 : 4*((u0+u1)*uu - u0*u1) + 4*uu*v0 + 4*((v0+v1)*v0 - v0*v1) ≤ M := by
        rcases huu with rfl | rfl
        · have : 4*((uu+u1)*uu - uu*u1) + 4*uu*v0 + 4*((v0+v1)*v0 - v0*v1) = Bq uu v0 := by unfold Bq; ring
          linarith
        · have : 4*((u0+uu)*uu - u0*uu) + 4*uu*v0 + 4*((v0+v1)*v0 - v0*v1) = Bq uu v0 := by unfold Bq; ring
          linarith
      have hc1 : 4*((u0+u1)*uu - u0*u1) + 4*uu*v1 + 4*((v0+v1)*v1 - v0*v1) ≤ M := by
        rcases huu with rfl | rfl
        · have : 4*((uu+u1)*uu - uu*u1) + 4*uu*v1 + 4*((v0+v1)*v1 - v0*v1) = Bq uu v1 := by unfold Bq; ring
          linarith
        · have : 4*((u0+uu)*uu - u0*uu) + 4*uu*v1 + 4*((v0+v1)*v1 - v0*v1) = Bq uu v1 := by unfold Bq; ring
          linarith
      -- affine in v with slope 4 uu + 4 (v0+v1)
      rcases le_total 0 (4*uu + 4*(v0+v1)) with hs | hs
      · nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.mpr hv1) hs]
      · nlinarith [mul_le_mul_of_nonpos_left (sub_nonneg.mpr hv0) hs]
    have f0 := fv u0 (Or.inl rfl); have f1 := fv u1 (Or.inr rfl)
    simp only [I]
    rcases le_total 0 (4*(u0+u1) + 4*v) with hs | hs
    · nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.mpr hu1) hs]
    · nlinarith [mul_le_mul_of_nonpos_left (sub_nonneg.mpr hu0) hs]
  have : Bq u v ≤ I := by unfold Bq; simp only [I]; nlinarith
  linarith

/-- inner cut for strip cells -/
theorem inner_cut (a b c1 c2 τ M : ℝ) (h : heronab a b ≤ τ) (hB : Bq (a - c1) (b - c2) ≤ M) :
    (-8*c1 - 4*c2 + 4) * (a - c1) + (-4*c1 - 8*c2 + 4) * (b - c2) ≤ τ - heronab c1 c2 + M := by
  have := heron_expand a b c1 c2; linarith

end NMCheck
