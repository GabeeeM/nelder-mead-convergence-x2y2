import NMBase
open NM NMC

namespace NMS
noncomputable section

def brM : Nat → Zc → Zc
  | 1 => brM1 | 2 => brM2 | 3 => brM3 | 4 => brM4 | 5 => brM5 | 6 => brM6 | 7 => brM7 | 8 => brM8
  | 9 => brM9 | _ => id
def brC : Nat → Zc → Prop
  | 1 => brC1 | 2 => brC2 | 3 => brC3 | 4 => brC4 | 5 => brC5 | 6 => brC6 | 7 => brC7 | 8 => brC8
  | 9 => brC9 | _ => fun _ => False
def alpha (k : Nat) : ℝ := if k = 1 then 2 else if k ≤ 3 then 1 else 1/2

theorem step_branch' (t : Tri) (hs : sorted t) (hn : nondeg t) :
    ∃ k, 1 ≤ k ∧ k ≤ 9 ∧ brC k (zc t) ∧ zc (step t) = brM k (zc t) ∧ A (step t) = alpha k * A t := by
  rcases step_branch t hs hn with h | h | h | h | h | h | h | h | h
  · exact ⟨1, by norm_num, by norm_num, h.1, h.2.1, by rw [h.2.2]; simp [alpha]⟩
  · exact ⟨2, by norm_num, by norm_num, h.1, h.2.1, by rw [h.2.2]; simp [alpha]⟩
  · exact ⟨3, by norm_num, by norm_num, h.1, h.2.1, by rw [h.2.2]; simp [alpha]⟩
  · exact ⟨4, by norm_num, by norm_num, h.1, h.2.1, by rw [h.2.2]; simp [alpha]⟩
  · exact ⟨5, by norm_num, by norm_num, h.1, h.2.1, by rw [h.2.2]; simp [alpha]⟩
  · exact ⟨6, by norm_num, by norm_num, h.1, h.2.1, by rw [h.2.2]; simp [alpha]⟩
  · exact ⟨7, by norm_num, by norm_num, h.1, h.2.1, by rw [h.2.2]; simp [alpha]⟩
  · exact ⟨8, by norm_num, by norm_num, h.1, h.2.1, by rw [h.2.2]; simp [alpha]⟩
  · exact ⟨9, by norm_num, by norm_num, h.1, h.2.1, by rw [h.2.2]; simp [alpha]⟩

def evz (c : F5) (z : Zc) : ℝ := c.ev z.d2 z.d3 z.a z.b z.c

@[simp] theorem evz_lin (x y : Z) (c d : F5) (z : Zc) :
    evz (F5.lin x c y d) z = x.val * evz c z + y.val * evz d z := by
  simp only [evz, F5.ev, F5.lin, Z.val_add, Z.val_mul]; ring
@[simp] theorem evz_add (c d : F5) (z : Zc) : evz (F5.add c d) z = evz c z + evz d z := by
  simp only [evz, F5.ev, F5.add, Z.val_add]; ring
@[simp] theorem evz_neg (c : F5) (z : Zc) : evz (F5.neg c) z = - evz c z := by
  simp only [evz, F5.ev, F5.neg, Z.val_neg]; ring
@[simp] theorem evz_zero (z : Zc) : evz F5.zero z = 0 := by
  simp [evz, F5.ev, F5.zero, zN, Z.val]
theorem evz_LL (z : Zc) : evz LL z = z.lam := by
  simp [evz, F5.ev, LL, zN, Z.val, Zc.lam]
@[simp] theorem val_zN (k : Nat) : (zN k).val = k := by simp [zN, Z.val]
@[simp] theorem val_zM (k : Nat) : (zM k).val = -k := by simp [zM, Z.val]

theorem br_funs (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (z : Zc) :
    evz (brT k) z = 16 * (brM k z).T ∧ evz (brL k) z = 16 * (brM k z).lam ∧
    evz (brV k) z = 16 * ((brM k z).d2 + (brM k z).d3) ∧ evz (brD k) z = 16 * (brM k z).d2 ∧
    evz (brA k) z = 16 * (brM k z).a ∧ evz (brB k) z = 16 * (brM k z).b := by
  interval_cases k <;>
    simp only [evz, F5.ev, brT, brL, brV, brD, brA, brB, brM, brM1, brM2, brM3, brM4, brM5, brM6, brM7,
      brM8, brM9, Zc.T, Zc.lam, Z.val] <;> push_cast <;> refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

theorem br_conds (k : Nat) (z : Zc) (h : brC k z) (i : Nat) (c : F5) (need : Bool)
    (hc : nth (brConds k) i = some (c, need)) :
    (need = true → 0 ≤ evz c z) ∧ (need = false → evz c z < 0) := by
  rcases Nat.lt_or_ge k 10 with hk | hk
  · interval_cases k <;> simp only [brC] at h <;>
      (try simp only [brConds, nth] at hc) <;>
      (rcases i with _ | _ | _ | _ | i <;> simp only [nth, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc) <;>
      (obtain ⟨rfl, rfl⟩ := hc) <;>
      simp only [brC1, brC2, brC3, brC4, brC5, brC6, brC7, brC8, brC9] at h <;>
      simp only [evz, F5.ev, Z.val] <;> push_cast <;> refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
      first | (exfalso; contradiction) | linarith [h] | linarith [h.1] | linarith [h.2] | linarith [h.2.1] |
        linarith [h.2.2] | linarith [h.2.2.1] | linarith [h.2.2.2] | simp_all
  · have : brConds k = [] := by
      rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | omega | rfl
    rw [this] at hc; simp [nth] at hc


/-! ## Cells -/

def heronZ (z : Zc) : ℝ := 2 * (z.a * z.b + z.a * z.c + z.b * z.c) - z.a ^ 2 - z.b ^ 2 - z.c ^ 2

theorem outer_identity (a b c X Y g : ℝ) :
    let lam := a + b + c
    let g1 := 8 * g - 8 * X - 4 * Y
    let g2 := 8 * g - 4 * X - 8 * Y
    let H := (8 * g * X + 8 * g * Y) - (4 * X * X + 4 * X * Y + 4 * Y * Y + 4 * g * g)
    lam * ((-(g1 * X + g2 * Y) + H) * lam - ((-(2 * g * g1)) * a + (-(2 * g * g2)) * b)) =
      4 * g ^ 2 * (2 * (a * b + a * c + b * c) - a ^ 2 - b ^ 2 - c ^ 2) +
        NMCheck.Bq (2 * g * a - X * lam) (2 * g * b - Y * lam) := by
  intro lam g1 g2 H; simp only [lam, g1, g2, H, NMCheck.Bq]; ring

theorem Bq_nonneg' (u v : ℝ) : 0 ≤ NMCheck.Bq u v := NMCheck.Bq_nonneg u v

set_option maxHeartbeats 4000000 in
/-- validity of the seven half-planes for a state in the box -/
theorem con_valid (bx : Box) (z : Zc) (ha : 0 ≤ z.a) (hb : 0 ≤ z.b) (hc : 0 ≤ z.c) (hl : 0 < z.lam)
    (hh : 0 ≤ heronZ z)
    (ha0 : (bx.a0 : ℝ) * z.lam ≤ G * z.a) (ha1 : (G : ℝ) * z.a ≤ bx.a1 * z.lam)
    (hb0 : (bx.b0 : ℝ) * z.lam ≤ G * z.b) (hb1 : (G : ℝ) * z.b ≤ bx.b1 * z.lam)
    (hstrip : isStrip bx = true → (tierDen bx : ℝ) * heronZ z ≤ z.lam ^ 2) (k : Nat) :
    (con bx k).n1.val * z.a + (con bx k).n2.val * z.b ≤ (con bx k).h.val * z.lam := by
  have hlam : z.lam = z.a + z.b + z.c := rfl
  have hA : bx.a0 ≤ bx.a1 := by
    have : (bx.a0 : ℝ) * z.lam ≤ bx.a1 * z.lam := le_trans ha0 ha1
    exact_mod_cast le_of_mul_le_mul_right this hl
  have hB : bx.b0 ≤ bx.b1 := by
    have : (bx.b0 : ℝ) * z.lam ≤ bx.b1 * z.lam := le_trans hb0 hb1
    exact_mod_cast le_of_mul_le_mul_right this hl
  have oid := outer_identity z.a z.b z.c ((bx.a0 + bx.a1 : ℕ) : ℝ) ((bx.b0 + bx.b1 : ℕ) : ℝ) (G : ℝ)
  simp only at oid
  rcases k with _ | _ | _ | _ | _ | _ | _ | k
  · simp [con, zN, zM, Z.val]; linarith
  · simp [con, zN, zM, Z.val]; linarith
  · simp [con, zN, zM, Z.val]; linarith
  · simp [con, zN, zM, Z.val]; linarith
  · simp [con, zN, zM, Z.val]; linarith
  · -- outer cut
    simp only [con, Z.val_neg, Z.val_mul, Z.val_add, Z.val_sub, val_zN]
    push_cast
    have hB2 := Bq_nonneg' (2 * (G : ℝ) * z.a - ((bx.a0 : ℝ) + bx.a1) * (z.a + z.b + z.c))
      (2 * (G : ℝ) * z.b - ((bx.b0 : ℝ) + bx.b1) * (z.a + z.b + z.c))
    push_cast at oid
    have hhz : 0 ≤ 2 * (z.a * z.b + z.a * z.c + z.b * z.c) - z.a ^ 2 - z.b ^ 2 - z.c ^ 2 := hh
    have key : 0 ≤ z.lam * (((-((8 * (G:ℝ) - (8 * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.b0:ℝ) + bx.b1))) * ((bx.a0:ℝ) + bx.a1) +
        (8 * (G:ℝ) - (4 * ((bx.a0:ℝ) + bx.a1) + 8 * ((bx.b0:ℝ) + bx.b1))) * ((bx.b0:ℝ) + bx.b1))) + 
        ((8 * (G:ℝ) * ((bx.a0:ℝ) + bx.a1) + 8 * (G:ℝ) * ((bx.b0:ℝ) + bx.b1)) -
          (4 * ((bx.a0:ℝ) + bx.a1) * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.a0:ℝ) + bx.a1) * ((bx.b0:ℝ) + bx.b1) +
           4 * ((bx.b0:ℝ) + bx.b1) * ((bx.b0:ℝ) + bx.b1) + 4 * (G:ℝ) * (G:ℝ)))) * z.lam -
        ((-(2 * (G:ℝ) * (8 * (G:ℝ) - (8 * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.b0:ℝ) + bx.b1))))) * z.a +
         (-(2 * (G:ℝ) * (8 * (G:ℝ) - (4 * ((bx.a0:ℝ) + bx.a1) + 8 * ((bx.b0:ℝ) + bx.b1))))) * z.b)) := by
      rw [hlam]; rw [show (8 * (G:ℝ) - (8 * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.b0:ℝ) + bx.b1))) =
        8 * (G:ℝ) - 8 * ((bx.a0:ℝ) + bx.a1) - 4 * ((bx.b0:ℝ) + bx.b1) by ring,
        show (8 * (G:ℝ) - (4 * ((bx.a0:ℝ) + bx.a1) + 8 * ((bx.b0:ℝ) + bx.b1))) =
        8 * (G:ℝ) - 4 * ((bx.a0:ℝ) + bx.a1) - 8 * ((bx.b0:ℝ) + bx.b1) by ring]
      rw [oid]; positivity
    have := (mul_nonneg_iff_of_pos_left hl).mp key
    linarith
  · -- inner cut (strip cells only)
    cases hs : isStrip bx with
    | false => simp [con, hs, zN, Z.val]
    | true =>
      have hst := hstrip hs
      simp only [con, hs, cond, Z.val_neg, Z.val_mul, Z.val_add, Z.val_sub, val_zN]
      have cWA : ((bx.a1 - bx.a0 : ℕ) : ℝ) = bx.a1 - bx.a0 := Nat.cast_sub hA
      have cWB : ((bx.b1 - bx.b0 : ℕ) : ℝ) = bx.b1 - bx.b0 := Nat.cast_sub hB
      have cK : ((G * G / tierDen bx * 4 : ℕ) : ℝ) = 4 * (G : ℝ) ^ 2 / (tierDen bx : ℝ) := by
        unfold tierDen; cases Nat.ble 512 bx.s0 <;> cases Nat.ble 64 bx.s0 <;> norm_num [G, cond]
      have hτ : (0 : ℝ) < (tierDen bx : ℝ) := by
        unfold tierDen; cases Nat.ble 512 bx.s0 <;> cases Nat.ble 64 bx.s0 <;> norm_num [cond]
      push_cast [cWA, cWB, cK]
      push_cast at oid
      set u := 2 * (G : ℝ) * z.a - ((bx.a0 : ℝ) + bx.a1) * (z.a + z.b + z.c)
      set v := 2 * (G : ℝ) * z.b - ((bx.b0 : ℝ) + bx.b1) * (z.a + z.b + z.c)
      set WA := (bx.a1 : ℝ) - bx.a0
      set WB := (bx.b1 : ℝ) - bx.b0
      have hWA : 0 ≤ WA := by simp only [WA]; exact sub_nonneg.mpr (by exact_mod_cast hA)
      have hWB : 0 ≤ WB := by simp only [WB]; exact sub_nonneg.mpr (by exact_mod_cast hB)
      have hu0 : -(WA * z.lam) ≤ u := by
        have e : u + WA * z.lam = 2 * ((G:ℝ) * z.a - bx.a0 * z.lam) := by simp only [u, WA]; rw [hlam]; ring
        linarith
      have hu1 : u ≤ WA * z.lam := by
        have e : WA * z.lam - u = 2 * (bx.a1 * z.lam - (G:ℝ) * z.a) := by simp only [u, WA]; rw [hlam]; ring
        linarith
      have hv0 : -(WB * z.lam) ≤ v := by
        have e : v + WB * z.lam = 2 * ((G:ℝ) * z.b - bx.b0 * z.lam) := by simp only [v, WB]; rw [hlam]; ring
        linarith
      have hv1 : v ≤ WB * z.lam := by
        have e : WB * z.lam - v = 2 * (bx.b1 * z.lam - (G:ℝ) * z.b) := by simp only [v, WB]; rw [hlam]; ring
        linarith
      have hM : NMCheck.Bq u v ≤ 4 * (WA ^ 2 + WA * WB + WB ^ 2) * z.lam ^ 2 := by
        have hWW : 0 ≤ WA * WB := mul_nonneg hWA hWB
        apply NMCheck.Bq_le_corners u v (-(WA * z.lam)) (WA * z.lam) (-(WB * z.lam)) (WB * z.lam) _ hu0 hu1 hv0 hv1 <;>
          simp only [NMCheck.Bq] <;> nlinarith [sq_nonneg z.lam, mul_nonneg hWW (sq_nonneg z.lam)]
      have hhz : 2 * (z.a * z.b + z.a * z.c + z.b * z.c) - z.a ^ 2 - z.b ^ 2 - z.c ^ 2 = heronZ z := rfl
      rw [hhz] at oid
      -- λ (h λ - n·x) = K λ² - λ (h_out λ - n_out·x) ≥ 0
      have key : 0 ≤ z.lam * (4 * (G : ℝ) ^ 2 / (tierDen bx : ℝ) + 4 * (WA * WA + WA * WB + WB * WB)) * z.lam
          - (4 * (G : ℝ) ^ 2 * heronZ z + NMCheck.Bq u v) := by
        have : 4 * (G : ℝ) ^ 2 * heronZ z ≤ 4 * (G : ℝ) ^ 2 / (tierDen bx : ℝ) * z.lam ^ 2 := by
          have : (0:ℝ) ≤ 4 * (G : ℝ) ^ 2 / (tierDen bx : ℝ) := by positivity
          have e : 4 * (G : ℝ) ^ 2 / (tierDen bx : ℝ) * z.lam ^ 2 = 4 * (G : ℝ) ^ 2 * (z.lam ^ 2 / (tierDen bx : ℝ)) := by
            field_simp
          have h2 : heronZ z ≤ z.lam ^ 2 / (tierDen bx : ℝ) := by rw [le_div_iff₀ hτ]; linarith
          rw [e]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
        nlinarith
      rw [← oid] at key
      have key2 : 0 ≤ z.lam * ((((8 * (G:ℝ) - (8 * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.b0:ℝ) + bx.b1))) * ((bx.a0:ℝ) + bx.a1) +
          (8 * (G:ℝ) - (4 * ((bx.a0:ℝ) + bx.a1) + 8 * ((bx.b0:ℝ) + bx.b1))) * ((bx.b0:ℝ) + bx.b1)) -
          ((8 * (G:ℝ) * ((bx.a0:ℝ) + bx.a1) + 8 * (G:ℝ) * ((bx.b0:ℝ) + bx.b1)) -
            (4 * ((bx.a0:ℝ) + bx.a1) * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.a0:ℝ) + bx.a1) * ((bx.b0:ℝ) + bx.b1) +
             4 * ((bx.b0:ℝ) + bx.b1) * ((bx.b0:ℝ) + bx.b1) + 4 * (G:ℝ) * (G:ℝ))) +
          (4 * (G : ℝ) ^ 2 / (tierDen bx : ℝ) + 4 * (WA * WA + WA * WB + WB * WB))) * z.lam -
          ((2 * (G:ℝ) * (8 * (G:ℝ) - (8 * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.b0:ℝ) + bx.b1)))) * z.a +
           (2 * (G:ℝ) * (8 * (G:ℝ) - (4 * ((bx.a0:ℝ) + bx.a1) + 8 * ((bx.b0:ℝ) + bx.b1)))) * z.b)) := by
        have e : z.lam * ((((8 * (G:ℝ) - (8 * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.b0:ℝ) + bx.b1))) * ((bx.a0:ℝ) + bx.a1) +
          (8 * (G:ℝ) - (4 * ((bx.a0:ℝ) + bx.a1) + 8 * ((bx.b0:ℝ) + bx.b1))) * ((bx.b0:ℝ) + bx.b1)) -
          ((8 * (G:ℝ) * ((bx.a0:ℝ) + bx.a1) + 8 * (G:ℝ) * ((bx.b0:ℝ) + bx.b1)) -
            (4 * ((bx.a0:ℝ) + bx.a1) * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.a0:ℝ) + bx.a1) * ((bx.b0:ℝ) + bx.b1) +
             4 * ((bx.b0:ℝ) + bx.b1) * ((bx.b0:ℝ) + bx.b1) + 4 * (G:ℝ) * (G:ℝ))) +
          (4 * (G : ℝ) ^ 2 / (tierDen bx : ℝ) + 4 * (WA * WA + WA * WB + WB * WB))) * z.lam -
          ((2 * (G:ℝ) * (8 * (G:ℝ) - (8 * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.b0:ℝ) + bx.b1)))) * z.a +
           (2 * (G:ℝ) * (8 * (G:ℝ) - (4 * ((bx.a0:ℝ) + bx.a1) + 8 * ((bx.b0:ℝ) + bx.b1)))) * z.b)) =
          z.lam * (4 * (G : ℝ) ^ 2 / (tierDen bx : ℝ) + 4 * (WA * WA + WA * WB + WB * WB)) * z.lam -
          z.lam * ((-((8 * (G:ℝ) - 8 * ((bx.a0:ℝ) + bx.a1) - 4 * ((bx.b0:ℝ) + bx.b1)) * ((bx.a0:ℝ) + bx.a1) +
            (8 * (G:ℝ) - 4 * ((bx.a0:ℝ) + bx.a1) - 8 * ((bx.b0:ℝ) + bx.b1)) * ((bx.b0:ℝ) + bx.b1)) +
            ((8 * (G:ℝ) * ((bx.a0:ℝ) + bx.a1) + 8 * (G:ℝ) * ((bx.b0:ℝ) + bx.b1)) -
              (4 * ((bx.a0:ℝ) + bx.a1) * ((bx.a0:ℝ) + bx.a1) + 4 * ((bx.a0:ℝ) + bx.a1) * ((bx.b0:ℝ) + bx.b1) +
               4 * ((bx.b0:ℝ) + bx.b1) * ((bx.b0:ℝ) + bx.b1) + 4 * (G:ℝ) * (G:ℝ)))) * (z.a + z.b + z.c) -
            ((-(2 * (G:ℝ) * (8 * (G:ℝ) - 8 * ((bx.a0:ℝ) + bx.a1) - 4 * ((bx.b0:ℝ) + bx.b1)))) * z.a +
             (-(2 * (G:ℝ) * (8 * (G:ℝ) - 4 * ((bx.a0:ℝ) + bx.a1) - 8 * ((bx.b0:ℝ) + bx.b1)))) * z.b)) := by
          rw [hlam]; ring
        rw [e]; rw [hlam] at key ⊢; linarith
      have := (mul_nonneg_iff_of_pos_left hl).mp key2
      linarith
  · simp [con, zN, Z.val]


/-- `z` lies in the cell of the box `bx` -/
structure InCell (bx : Box) (z : Zc) : Prop where
  d2 : 0 ≤ z.d2
  d3 : 0 ≤ z.d3
  lam : 0 < z.lam
  s0 : (bx.s0 : ℝ) * z.T ≤ G * z.lam
  s1 : (G : ℝ) * z.lam ≤ bx.s1 * z.T
  p0 : (bx.p0 : ℝ) * (z.d2 + z.d3) ≤ G * z.d2
  p1 : (G : ℝ) * z.d2 ≤ bx.p1 * (z.d2 + z.d3)
  cons : ∀ k, (con bx k).n1.val * z.a + (con bx k).n2.val * z.b ≤ (con bx k).h.val * z.lam
  bs0 : bx.s0 ≤ G
  bs1 : bx.s1 ≤ G
  bp0 : bx.p0 ≤ G
  bp1 : bx.p1 ≤ G

theorem chk_sound (bx : Box) (pr : Nat) (c : F5) (strict : Bool) (z : Zc) (hz : InCell bx z)
    (h : chk bx pr c strict = true) : 0 ≤ evz c z ∧ (strict = true → 0 < evz c z) :=
  fcheck_sound bx.s0 bx.s1 bx.p0 bx.p1 _ _ c strict hz.bs0 hz.bs1 hz.bp0 hz.bp1 z.d2 z.d3 z.a z.b z.c
    hz.d2 hz.d3 hz.lam hz.s0 hz.s1 hz.p0 hz.p1 (hz.cons _) (hz.cons _) h

theorem hole_sound (bx : Box) (x : Nat) (h : chkHole bx x = true) (z : Zc) (hl : 0 < z.lam)
    (hc : ∀ k, (con bx k).n1.val * z.a + (con bx k).n2.val * z.b ≤ (con bx k).h.val * z.lam) : False := by
  unfold chkHole at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Z.nonneg_iff, Z.pos_iff, Z.val_neg, Z.val_sub, Z.val_mul,
    Z.val_add] at h
  have hi := hc (rd x 3); have hj := hc (rd (sh x 3) 3); have hk := hc (rd (sh x 6) 3)
  set ci := con bx (rd x 3); set cj := con bx (rd (sh x 3) 3); set ck := con bx (rd (sh x 6) 3)
  -- Σ y n = 0 identically
  have e1 : (cj.n1.val * ck.n2.val - cj.n2.val * ck.n1.val) * ci.n1.val +
      (ck.n1.val * ci.n2.val - ck.n2.val * ci.n1.val) * cj.n1.val +
      (ci.n1.val * cj.n2.val - ci.n2.val * cj.n1.val) * ck.n1.val = 0 := by ring
  have e2 : (cj.n1.val * ck.n2.val - cj.n2.val * ck.n1.val) * ci.n2.val +
      (ck.n1.val * ci.n2.val - ck.n2.val * ci.n1.val) * cj.n2.val +
      (ci.n1.val * cj.n2.val - ci.n2.val * cj.n1.val) * ck.n2.val = 0 := by ring
  rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · have m1 := mul_le_mul_of_nonneg_left hi h1
    have m2 := mul_le_mul_of_nonneg_left hj h2
    have m3 := mul_le_mul_of_nonneg_left hk h3
    have : 0 ≤ ((cj.n1.val * ck.n2.val - cj.n2.val * ck.n1.val) * ci.h.val +
      (ck.n1.val * ci.n2.val - ck.n2.val * ci.n1.val) * cj.h.val +
      (ci.n1.val * cj.n2.val - ci.n2.val * cj.n1.val) * ck.h.val) * z.lam := by
      have : 0 = (cj.n1.val * ck.n2.val - cj.n2.val * ck.n1.val) * (ci.n1.val * z.a + ci.n2.val * z.b) +
        (ck.n1.val * ci.n2.val - ck.n2.val * ci.n1.val) * (cj.n1.val * z.a + cj.n2.val * z.b) +
        (ci.n1.val * cj.n2.val - ci.n2.val * cj.n1.val) * (ck.n1.val * z.a + ck.n2.val * z.b) := by
        linear_combination (-z.a) * e1 - z.b * e2
      nlinarith
    have := (mul_nonneg_iff_of_pos_right hl).mp this
    linarith
  · have m1 := mul_le_mul_of_nonneg_left hi h1
    have m2 := mul_le_mul_of_nonneg_left hj h2
    have m3 := mul_le_mul_of_nonneg_left hk h3
    have : 0 ≤ -((cj.n1.val * ck.n2.val - cj.n2.val * ck.n1.val) * ci.h.val +
      (ck.n1.val * ci.n2.val - ck.n2.val * ci.n1.val) * cj.h.val +
      (ci.n1.val * cj.n2.val - ci.n2.val * cj.n1.val) * ck.h.val) * z.lam := by
      have : 0 = (cj.n1.val * ck.n2.val - cj.n2.val * ck.n1.val) * (ci.n1.val * z.a + ci.n2.val * z.b) +
        (ck.n1.val * ci.n2.val - ck.n2.val * ci.n1.val) * (cj.n1.val * z.a + cj.n2.val * z.b) +
        (ci.n1.val * cj.n2.val - ci.n2.val * cj.n1.val) * (ck.n1.val * z.a + ck.n2.val * z.b) := by
        linear_combination (-z.a) * e1 - z.b * e2
      nlinarith
    have := (mul_nonneg_iff_of_pos_right hl).mp this
    linarith

/-! ## Coordinates, lookup, tree walks -/

def zcoord (z : Zc) : Nat → ℝ
  | 0 => z.lam / z.T
  | 1 => z.d2 / (z.d2 + z.d3)
  | 2 => z.a / z.lam
  | _ => z.b / z.lam

/-- `z` lies in the box `b`, whose coordinates are on the grid `g` -/
def inBox (g : ℝ) (b : Box) (z : Zc) : Prop :=
  ∀ d, d < 4 → (b.lo d : ℝ) / g ≤ zcoord z d ∧ zcoord z d ≤ (b.hi d : ℝ) / g

theorem inBox_any (g : ℝ) (b : Box) (z : Zc) (h : inBox g b z) (d : Nat) :
    (b.lo d : ℝ) / g ≤ zcoord z d ∧ zcoord z d ≤ (b.hi d : ℝ) / g := by
  rcases d with _ | _ | _ | _ | d
  · exact h 0 (by norm_num)
  · exact h 1 (by norm_num)
  · exact h 2 (by norm_num)
  · exact h 3 (by norm_num)
  · have := h 3 (by norm_num); simpa [Box.lo, Box.hi, zcoord] using this

def look (z : Zc) : KT → Box → Nat × Bool × Box
  | .leaf n h, b => (n, h, b)
  | .node d v _ l r, b => if zcoord z d ≤ (v : ℝ) / G then look z l (b.setHi d v) else look z r (b.setLo d v)

theorem look_mem (z : Zc) : ∀ (t : KT) (b : Box), inBox G b z → inBox G (look z t b).2.2 z := by
  intro t
  induction t with
  | leaf n h => intro b hb; exact hb
  | node d v mx l r ihl ihr =>
    intro b hb
    simp only [look]
    split_ifs with hc
    · apply ihl
      intro d' hd'
      have := hb d' hd'
      rcases d with _ | _ | _ | _ | d <;> interval_cases d' <;>
        simp_all [Box.setHi, Box.lo, Box.hi, zcoord]
    · apply ihr
      push_neg at hc
      intro d' hd'
      have := hb d' hd'
      rcases d with _ | _ | _ | _ | d <;> interval_cases d' <;>
        simp_all [Box.setLo, Box.lo, Box.hi, zcoord, le_of_lt]

theorem walk_ok (tr : KT) (z : Zc) : ∀ (t : KT) (b : Box) (cs rest : List Nat), walk tr t b cs = some rest →
    ∃ c, cond (look z t b).2.1 (chkHole (look z t b).2.2 c) (chkLeaf tr (look z t b).2.2 (look z t b).1 c) = true := by
  intro t
  induction t with
  | leaf n h =>
    intro b cs rest hw
    rcases cs with _ | ⟨c, cs⟩
    · simp [walk] at hw
    · refine ⟨c, ?_⟩
      simp only [walk] at hw
      simp only [look]
      cases hc : cond h (chkHole b c) (chkLeaf tr b n c)
      · rw [hc] at hw; simp at hw
      · rfl
  | node d v mx l r ihl ihr =>
    intro b cs rest hw
    simp only [walk] at hw
    cases hl : walk tr l (b.setHi d v) cs with
    | none => rw [hl] at hw; simp at hw
    | some cs' =>
      rw [hl] at hw
      simp only [look]
      split_ifs
      · exact ihl _ _ _ hl
      · exact ihr _ _ _ hw

theorem top_ge (z : Zc) : ∀ (t : KT) (b : Box), mxOK t = true → (look z t b).2.1 = false →
    (look z t b).1 ≤ t.top := by
  intro t
  induction t with
  | leaf n h => intro b _ hh; simp only [look] at hh ⊢; simp [KT.top, hh]
  | node d v mx l r ihl ihr =>
    intro b hm hh
    simp only [mxOK, Bool.and_eq_true, Nat.ble_eq] at hm
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hm
    simp only [look] at hh ⊢
    simp only [KT.top]
    split_ifs at hh ⊢
    · exact le_trans (ihl _ h3 hh) h1
    · exact le_trans (ihr _ h4 hh) h2

theorem query_ok (ok : Nat → Box → Bool) (enc : Box) (bound wneg : Nat) (z : Zc) (henc : inBox E enc z) :
    ∀ (t : KT) (b : Box) (ps : List Nat) (rest : List Nat), mxOK t = true →
      query ok enc bound wneg t b ps = some rest →
      (look z t b).2.1 = true ∨ (look z t b).1 + wneg ≤ bound ∨ ∃ p, ok p (look z t b).2.2 = true := by
  intro t
  induction t with
  | leaf n h =>
    intro b ps rest _ hq
    simp only [query] at hq
    simp only [look]
    cases h with
    | true => left; rfl
    | false =>
      by_cases hn : n + wneg ≤ bound
      · right; left; exact hn
      · have : Nat.ble (n + wneg) bound = false := Bool.eq_false_iff.mpr (by rw [ne_eq, Nat.ble_eq]; exact hn)
        simp only [Bool.false_or, this, cond] at hq
        rcases ps with _ | ⟨p, ps'⟩
        · simp at hq
        · right; right; refine ⟨p, ?_⟩
          simp only at hq
          cases hp : ok p b
          · rw [hp] at hq; simp at hq
          · rfl
  | node d v mx l r ihl ihr =>
    intro b ps rest hm hq
    have hm' := hm
    simp only [mxOK, Bool.and_eq_true] at hm'
    obtain ⟨⟨_, hml⟩, hmr⟩ := hm'
    by_cases hb : mx + wneg ≤ bound
    · -- all leaves below are fine
      cases hh : (look z (.node d v mx l r) b).2.1
      · right; left
        have := top_ge z (.node d v mx l r) b hm hh
        simp only [KT.top] at this; omega
      · left; rfl
    · have hb' : Nat.ble (mx + wneg) bound = false := Bool.eq_false_iff.mpr (by rw [ne_eq, Nat.ble_eq]; exact hb)
      simp only [query] at hq; rw [hb', cond_false] at hq
      have hE : (0 : ℝ) < E := by norm_num [E]
      have hG : (0 : ℝ) < G := by norm_num [G]
      have hEG : (E : ℝ) = G * 4096 := by norm_num [E, G]
      simp only [look]
      split_ifs with hc
      · -- went left: the left query was run
        have hlo : Nat.ble (enc.lo d) (v * 4096) = true := by
          rw [Nat.ble_eq]
          have h1 : (enc.lo d : ℝ) / E ≤ zcoord z d := (inBox_any _ _ _ henc d).1
          have h2 : (enc.lo d : ℝ) / E ≤ v / G := le_trans h1 hc
          rw [hEG, div_le_div_iff₀ (by positivity) hG] at h2
          have : (enc.lo d : ℝ) ≤ v * 4096 := by nlinarith
          exact_mod_cast this
        rw [hlo, cond_true] at hq
        cases hql : query ok enc bound wneg l (b.setHi d v) ps with
        | none => rw [hql] at hq; simp at hq
        | some ps' => exact ihl _ _ _ hml hql
      · push_neg at hc
        have hhi : Nat.ble (v * 4096) (enc.hi d) = true := by
          rw [Nat.ble_eq]
          have h1 : zcoord z d ≤ (enc.hi d : ℝ) / E := (inBox_any _ _ _ henc d).2
          have h2 : (v : ℝ) / G ≤ enc.hi d / E := le_trans hc.le h1
          rw [hEG, div_le_div_iff₀ hG (by positivity)] at h2
          have : (v : ℝ) * 4096 ≤ enc.hi d := by nlinarith
          exact_mod_cast this
        cases hql : cond (Nat.ble (enc.lo d) (v * 4096)) (query ok enc bound wneg l (b.setHi d v) ps) (some ps) with
        | none => rw [hql] at hq; simp at hq
        | some ps' =>
          rw [hql] at hq
          simp only at hq
          rw [hhi, cond_true] at hq
          exact ihr _ _ _ hmr hq


/-! ## Valid states -/

structure ValidZ (z : Zc) : Prop where
  d2 : 0 ≤ z.d2
  d3 : 0 ≤ z.d3
  a : 0 < z.a
  b : 0 ≤ z.b
  c : 0 ≤ z.c
  h : 0 ≤ heronZ z

theorem ValidZ.lam {z : Zc} (hz : ValidZ z) : 0 < z.lam := by
  have := hz.a; have := hz.b; have := hz.c; simp only [Zc.lam]; linarith
theorem ValidZ.T {z : Zc} (hz : ValidZ z) : 0 < z.T := by
  have := hz.lam; have := hz.d2; have := hz.d3; simp only [Zc.T]; linarith
theorem ValidZ.lam_le_T {z : Zc} (hz : ValidZ z) : z.lam ≤ z.T := by
  have := hz.d2; have := hz.d3; simp only [Zc.T]; linarith

theorem coord_range {z : Zc} (hz : ValidZ z) (d : Nat) : 0 ≤ zcoord z d ∧ zcoord z d ≤ 1 := by
  have hl := hz.lam; have hT := hz.T
  rcases d with _ | _ | _ | d
  · simp only [zcoord]
    exact ⟨div_nonneg hl.le hT.le, (div_le_one hT).mpr hz.lam_le_T⟩
  · simp only [zcoord]
    have h2 := hz.d2; have h3 := hz.d3
    rcases eq_or_lt_of_le (add_nonneg h2 h3) with h | h
    · rw [← h]; simp
    · exact ⟨div_nonneg h2 h.le, (div_le_one h).mpr (by linarith)⟩
  · simp only [zcoord]
    have := hz.b; have := hz.c
    exact ⟨div_nonneg hz.a.le hl.le, (div_le_one hl).mpr (by simp only [Zc.lam]; linarith)⟩
  · simp only [zcoord]
    have := hz.a; have := hz.c
    exact ⟨div_nonneg hz.b hl.le, (div_le_one hl).mpr (by simp only [Zc.lam]; linarith)⟩

theorem inBox_root {z : Zc} (hz : ValidZ z) : inBox G rootBox z := by
  intro d hd
  have := coord_range hz d
  have hG : (G : ℝ) ≠ 0 := by norm_num [G]
  interval_cases d <;> simp [rootBox, Box.lo, Box.hi, hG] <;> constructor <;> linarith

/-- a box on the grid `g` gives homogeneous bounds -/
theorem box_s {g : ℝ} (hg : 0 < g) {z : Zc} (hz : ValidZ z) {b : Box} (hb : inBox g b z) :
    (b.s0 : ℝ) * z.T ≤ g * z.lam ∧ g * z.lam ≤ b.s1 * z.T := by
  have h := hb 0 (by norm_num); simp only [zcoord, Box.lo, Box.hi] at h
  rw [div_le_div_iff₀ hg hz.T, div_le_div_iff₀ hz.T hg] at h
  constructor <;> linarith [h.1, h.2]
theorem box_a {g : ℝ} (hg : 0 < g) {z : Zc} (hz : ValidZ z) {b : Box} (hb : inBox g b z) :
    (b.a0 : ℝ) * z.lam ≤ g * z.a ∧ g * z.a ≤ b.a1 * z.lam := by
  have h := hb 2 (by norm_num); simp only [zcoord, Box.lo, Box.hi] at h
  rw [div_le_div_iff₀ hg hz.lam, div_le_div_iff₀ hz.lam hg] at h
  constructor <;> linarith [h.1, h.2]
theorem box_b {g : ℝ} (hg : 0 < g) {z : Zc} (hz : ValidZ z) {b : Box} (hb : inBox g b z) :
    (b.b0 : ℝ) * z.lam ≤ g * z.b ∧ g * z.b ≤ b.b1 * z.lam := by
  have h := hb 3 (by norm_num); simp only [zcoord, Box.lo, Box.hi] at h
  rw [div_le_div_iff₀ hg hz.lam, div_le_div_iff₀ hz.lam hg] at h
  constructor <;> linarith [h.1, h.2]
theorem box_p {g : ℝ} (hg : 0 < g) {z : Zc} (hz : ValidZ z) {b : Box} (hb : inBox g b z) :
    (b.p0 : ℝ) * (z.d2 + z.d3) ≤ g * z.d2 ∧ g * z.d2 ≤ b.p1 * (z.d2 + z.d3) := by
  have h := hb 1 (by norm_num); simp only [zcoord, Box.lo, Box.hi] at h
  have h2 := hz.d2; have h3 := hz.d3
  rcases eq_or_lt_of_le (add_nonneg h2 h3) with hV | hV
  · have : z.d2 = 0 := by linarith
    rw [← hV, this]; simp
  · rw [div_le_div_iff₀ hg hV, div_le_div_iff₀ hV hg] at h
    constructor <;> linarith [h.1, h.2]

theorem cons_of_box {z : Zc} (hz : ValidZ z) {b : Box} (hb : inBox G b z)
    (hst : isStrip b = true → (tierDen b : ℝ) * heronZ z ≤ z.lam ^ 2) (k : Nat) :
    (con b k).n1.val * z.a + (con b k).n2.val * z.b ≤ (con b k).h.val * z.lam := by
  have hG : (0 : ℝ) < G := by norm_num [G]
  have ha := box_a hG hz hb; have hb' := box_b hG hz hb
  exact con_valid b z hz.a.le hz.b hz.c hz.lam hz.h ha.1 ha.2 hb'.1 hb'.2 hst k

theorem inCell_of {z : Zc} (hz : ValidZ z) {b : Box} (hb : inBox G b z)
    (hst : isStrip b = true → (tierDen b : ℝ) * heronZ z ≤ z.lam ^ 2)
    (hbd : b.s0 ≤ G ∧ b.s1 ≤ G ∧ b.p0 ≤ G ∧ b.p1 ≤ G) : InCell b z := by
  have hG : (0 : ℝ) < G := by norm_num [G]
  have hs := box_s hG hz hb; have hp := box_p hG hz hb
  exact ⟨hz.d2, hz.d3, hz.lam, hs.1, hs.2, hp.1, hp.2, cons_of_box hz hb hst, hbd.1, hbd.2.1, hbd.2.2.1, hbd.2.2.2⟩

/-- the strip conditions of a far state, per tier -/
def StripZ (z : Zc) : Prop :=
  (8 * z.lam ≥ z.T → 1048576 * heronZ z ≤ z.lam ^ 2) ∧ (64 * z.lam ≥ z.T → 8192 * heronZ z ≤ z.lam ^ 2) ∧
    (512 * z.lam ≥ z.T → 128 * heronZ z ≤ z.lam ^ 2)

/-- strip condition from the state's own `s` -/
theorem strip_of_s {z : Zc} (hz : ValidZ z) (hfar : StripZ z)
    {b : Box} (hb : inBox G b z) : isStrip b = true → (tierDen b : ℝ) * heronZ z ≤ z.lam ^ 2 := by
  intro hs
  have hG : (0 : ℝ) < G := by norm_num [G]
  have h1 := (box_s hG hz hb).1
  have hT := hz.T
  obtain ⟨f1, f2, f3⟩ := hfar
  have h8 : (8 : ℝ) ≤ b.s0 := by simp only [isStrip, Nat.ble_eq] at hs; exact_mod_cast hs
  unfold tierDen
  cases h512 : Nat.ble 512 b.s0
  · cases h64 : Nat.ble 64 b.s0
    · simp only [cond]; push_cast
      apply f3
      have : (8 : ℝ) * z.T ≤ G * z.lam := le_trans (mul_le_mul_of_nonneg_right h8 hT.le) h1
      norm_num [G] at this; linarith
    · simp only [cond]; push_cast
      apply f2
      have h64' : (64 : ℝ) ≤ b.s0 := by simp only [Nat.ble_eq] at h64; exact_mod_cast h64
      have : (64 : ℝ) * z.T ≤ G * z.lam := le_trans (mul_le_mul_of_nonneg_right h64' hT.le) h1
      norm_num [G] at this; linarith
  · simp only [cond]; push_cast
    apply f1
    have h512' : (512 : ℝ) ≤ b.s0 := by simp only [Nat.ble_eq] at h512; exact_mod_cast h512
    have : (512 : ℝ) * z.T ≤ G * z.lam := le_trans (mul_le_mul_of_nonneg_right h512' hT.le) h1
    norm_num [G] at this; linarith


/-! ## Feasible branches -/

theorem sc_nonneg (k : Nat) (z : Zc) (h : brC k z) (i : Nat) :
    (0 : ℝ) ≤ evz (scF (brConds k) i) z := by
  unfold scF
  rcases hn : nth (brConds k) i with _ | ⟨c, need⟩
  · simp
  · have := br_conds k z h i c need hn
    cases need
    · simp only [evz_neg]; linarith [this.2 rfl]
    · exact this.1 rfl

theorem tf_nonneg (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (z z' : Zc) (hz' : z' = brM k z) (hv : ValidZ z')
    (tb : Box) (htb : inBox G tb z') :
    0 ≤ evz (F5.lin (zN G) (brL k) (zM tb.s0) (brT k)) z ∧ 0 ≤ evz (F5.lin (zN tb.s1) (brT k) (zM G) (brL k)) z ∧
    0 ≤ evz (F5.lin (zN G) (brD k) (zM tb.p0) (brV k)) z ∧ 0 ≤ evz (F5.lin (zN tb.p1) (brV k) (zM G) (brD k)) z ∧
    0 ≤ evz (F5.lin (zN G) (brA k) (zM tb.a0) (brL k)) z ∧ 0 ≤ evz (F5.lin (zN tb.a1) (brL k) (zM G) (brA k)) z ∧
    0 ≤ evz (F5.lin (zN G) (brB k) (zM tb.b0) (brL k)) z ∧ 0 ≤ evz (F5.lin (zN tb.b1) (brL k) (zM G) (brB k)) z := by
  obtain ⟨eT, eL, eV, eD, eA, eB⟩ := br_funs k hk1 hk9 z
  rw [← hz'] at eT eL eV eD eA eB
  have hG : (0 : ℝ) < G := by norm_num [G]
  have hs := box_s hG hv htb; have hp := box_p hG hv htb; have ha := box_a hG hv htb; have hb := box_b hG hv htb
  simp only [evz_lin, val_zN, val_zM, eT, eL, eV, eD, eA, eB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [hs.1, hs.2, hp.1, hp.2, ha.1, ha.2, hb.1, hb.2]

theorem prune_sound (bl : Box) (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (p : Nat) (tb : Box) (z z' : Zc)
    (hc : InCell bl z) (hbr : brC k z) (hz' : z' = brM k z) (hv : ValidZ z') (htb : inBox G tb z')
    (h : pruneOK bl k p tb = true) : False := by
  unfold pruneOK at h
  dsimp only at h
  have := (chk_sound _ _ _ _ z hc h).2 rfl
  simp only [evz_neg, evz_add, evz_lin, val_zN, val_zM] at this
  have s0 := sc_nonneg k z hbr 0; have s1 := sc_nonneg k z hbr 1
  have s2 := sc_nonneg k z hbr 2; have s3 := sc_nonneg k z hbr 3
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩ := tf_nonneg k hk1 hk9 z z' hz' hv tb htb
  simp only [evz_lin, val_zN, val_zM] at t0 t1 t2 t3 t4 t5 t6 t7
  have w : ∀ i : ℕ, (0 : ℝ) ≤ (rd (sh p (32 * i)) 32 : ℕ) := fun i => Nat.cast_nonneg _
  have := mul_nonneg (w 0) s0; have := mul_nonneg (w 1) s1; have := mul_nonneg (w 2) s2
  have := mul_nonneg (w 3) s3; have := mul_nonneg (w 4) t0; have := mul_nonneg (w 5) t1
  have := mul_nonneg (w 6) t2; have := mul_nonneg (w 7) t3; have := mul_nonneg (w 8) t4
  have := mul_nonneg (w 9) t5; have := mul_nonneg (w 10) t6; have := mul_nonneg (w 11) t7
  linarith


theorem ratio_lo {lo : ℕ} {num den : ℝ} (hden : 0 < den) (hnum : 0 ≤ num)
    (h : lo = 0 ∨ (lo : ℝ) * den ≤ E * num) : (lo : ℝ) / E ≤ num / den := by
  have hE : (0 : ℝ) < E := by norm_num [E]
  rcases h with h | h
  · rw [h]; simp; exact div_nonneg hnum hden.le
  · rw [div_le_div_iff₀ hE hden]; linarith

theorem ratio_hi {hi : ℕ} {num den : ℝ} (hden : 0 < den) (hle : num ≤ den)
    (h : E ≤ hi ∨ E * num ≤ (hi : ℝ) * den) : num / den ≤ (hi : ℝ) / E := by
  have hE : (0 : ℝ) < E := by norm_num [E]
  rcases h with h | h
  · have h1 : num / den ≤ 1 := (div_le_one hden).mpr hle
    have h2 : (1 : ℝ) ≤ hi / E := by rw [le_div_iff₀ hE]; simp; exact_mod_cast h
    linarith
  · rw [div_le_div_iff₀ hden hE]; linarith

theorem enc_sound (tr : KT) (bl : Box) (n k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (f : Feas) (z z' : Zc)
    (hc : InCell bl z) (hz' : z' = brM k z) (hv : ValidZ z') (h : chkFeas tr bl n k f = true) :
    inBox E f.enc z' ∧ z'.lam * E ≤ f.U * z.lam ∧ wOK bl k f = true ∧
      (query (pruneOK bl k) f.enc (n + f.wpos) f.wneg tr rootBox f.prunes).isSome = true := by
  unfold chkFeas at h
  dsimp only at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, cw⟩, cq⟩ := h
  obtain ⟨eT, eL, eV, eD, eA, eB⟩ := br_funs k hk1 hk9 z
  rw [← hz'] at eT eL eV eD eA eB
  have hl' := hv.lam; have hT' := hv.T; have hl := hc.lam
  have hd2 := hv.d2; have hd3 := hv.d3
  -- turn a passing check into an inequality
  have K : ∀ (pr : Nat) (c : F5), chk bl pr c false = true → 0 ≤ evz c z := fun pr c hh =>
    (chk_sound bl pr c false z hc hh).1
  refine ⟨?_, ?_, cw, cq⟩
  · intro d hd
    interval_cases d
    · simp only [Feas.enc, Box.lo, Box.hi, zcoord]
      constructor
      · apply ratio_lo hT' hl'.le
        rcases c0 with c | c
        · exact Or.inl c
        · right; have := K _ _ c; simp only [evz_lin, val_zN, val_zM, eL, eT] at this; linarith
      · apply ratio_hi hT' hv.lam_le_T
        rcases c1 with c | c
        · exact Or.inl c
        · right; have := K _ _ c; simp only [evz_lin, val_zN, val_zM, eL, eT] at this; linarith
    · simp only [Feas.enc, Box.lo, Box.hi, zcoord]
      have hE : (0 : ℝ) < E := by norm_num [E]
      constructor
      · rcases c2 with c | c
        · rw [c]; simp; exact div_nonneg hd2 (by linarith)
        · have h1 := K _ _ c; simp only [evz_lin, val_zN, val_zM, eD, eV] at h1
          rcases c9 with c' | c'
          · rw [c']; simp; exact div_nonneg hd2 (by linarith)
          · have h2 := (chk_sound bl _ _ true z hc c').2 rfl
            rw [eV] at h2
            have hV : 0 < z'.d2 + z'.d3 := by linarith
            rw [div_le_div_iff₀ hE hV]; linarith
      · rcases eq_or_lt_of_le (add_nonneg hd2 hd3) with hV | hV
        · rw [← hV]; simp; positivity
        · apply ratio_hi hV (by linarith)
          rcases c3 with c | c
          · exact Or.inl c
          · right; have := K _ _ c; simp only [evz_lin, val_zN, val_zM, eD, eV] at this; linarith
    · simp only [Feas.enc, Box.lo, Box.hi, zcoord]
      have := hv.b; have := hv.c
      constructor
      · apply ratio_lo hl' hv.a.le
        rcases c4 with c | c
        · exact Or.inl c
        · right; have := K _ _ c; simp only [evz_lin, val_zN, val_zM, eA, eL] at this; linarith
      · apply ratio_hi hl' (by simp only [Zc.lam]; linarith)
        rcases c5 with c | c
        · exact Or.inl c
        · right; have := K _ _ c; simp only [evz_lin, val_zN, val_zM, eA, eL] at this; linarith
    · simp only [Feas.enc, Box.lo, Box.hi, zcoord]
      have := hv.a; have := hv.c
      constructor
      · apply ratio_lo hl' hv.b
        rcases c6 with c | c
        · exact Or.inl c
        · right; have := K _ _ c; simp only [evz_lin, val_zN, val_zM, eB, eL] at this; linarith
      · apply ratio_hi hl' (by simp only [Zc.lam]; linarith)
        rcases c7 with c | c
        · exact Or.inl c
        · right; have := K _ _ c; simp only [evz_lin, val_zN, val_zM, eB, eL] at this; linarith
  · have := K _ _ c8
    simp only [evz_lin, val_zN, val_zM, eL, evz_LL] at this
    push_cast at this
    linarith


/-! ## The potential factor -/

def mz (z : Zc) : ℝ := min (z.lam / z.T) (1/5)
/-- the factor `P'^10 / P^10` without the `q` part -/
def Fac (k : Nat) (z z' : Zc) : ℝ := alpha k ^ 8 * (z.lam / z'.lam) ^ 7 * (mz z' / mz z) ^ 7

theorem mz_pos {z : Zc} (hz : ValidZ z) : 0 < mz z := lt_min (div_pos hz.lam hz.T) (by norm_num)

theorem alpha_pow (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) :
    alpha k ^ 2048 * (2 : ℝ) ^ (cond (alphaDown k) 2048 0) = 2 ^ (cond (alphaUp k) 2048 0) := by
  interval_cases k <;> simp [alpha, alphaUp, alphaDown] <;> norm_num

theorem alpha_pos (k : Nat) : 0 < alpha k := by
  unfold alpha; split_ifs <;> norm_num

theorem Fac_ge_one_of (k : Nat) (z z' : Zc) (h : 1 ≤ Fac k z z') (wneg : Nat) :
    (2 : ℝ) ^ 0 ≤ 2 ^ wneg * Fac k z z' ^ 256 := by
  have h1 : (1 : ℝ) ≤ 2 ^ wneg := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ Fac k z z' ^ 256 := one_le_pow₀ h
  simp only [pow_zero]; nlinarith

theorem wOK_sound (bl : Box) (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (f : Feas) (z z' : Zc)
    (hc : InCell bl z) (hvz : ValidZ z) (hv : ValidZ z') (hbr : brC k z) (hz' : z' = brM k z)
    (hs'lo : (f.lo1 : ℝ) / E ≤ z'.lam / z'.T) (hs'hi : z'.lam / z'.T ≤ (f.hi1 : ℝ) / E)
    (hU : z'.lam * E ≤ f.U * z.lam) (h : wOK bl k f = true) :
    (2 : ℝ) ^ f.wpos ≤ 2 ^ f.wneg * Fac k z z' ^ 256 := by
  have hl := hvz.lam; have hT := hvz.T; have hl' := hv.lam; have hT' := hv.T
  have hE : (0 : ℝ) < E := by norm_num [E]
  have hG : (0 : ℝ) < G := by norm_num [G]
  have hm := mz_pos hvz; have hm' := mz_pos hv
  have hsG : z.lam / z.T ≤ (bl.s1 : ℝ) / G := by
    rw [div_le_div_iff₀ hT hG]; have := hc.s1; simp only [Zc.T] at this ⊢; linarith
  unfold wOK at h
  dsimp only at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  rcases h with hnum | ⟨hw0, hov⟩
  · -- the generic bound
    set mN := Nat.min (5 * f.lo1) E
    set MN := Nat.min (5 * bl.s1) G
    have hU0 : (0 : ℝ) < f.U := by
      have : 0 < z'.lam * E := mul_pos hl' hE
      by_contra hc0; push_neg at hc0
      have : (f.U : ℝ) * z.lam ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hl.le
      linarith
    have hs1 : (0 : ℝ) < bl.s1 := by
      have := hc.s1; have : 0 < (G : ℝ) * z.lam := mul_pos hG hl
      by_contra hc0; push_neg at hc0
      have : (bl.s1 : ℝ) * z.T ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hT.le
      simp only [Zc.T] at *; linarith
    have hMN : (0 : ℝ) < MN := by
      simp only [MN, Nat.cast_min]; apply lt_min
      · push_cast; linarith
      · exact hG
    -- m ≤ MN / (5 G), m' ≥ mN / (5 E)
    have hmM : mz z ≤ (MN : ℝ) / (5 * G) := by
      simp only [mz, MN, Nat.cast_min]; push_cast
      rcases le_total ((5 : ℝ) * bl.s1) G with h5 | h5
      · rw [min_eq_left h5]
        have : (bl.s1 : ℝ) / G = 5 * bl.s1 / (5 * G) := by field_simp
        exact le_trans (min_le_left _ _) (this ▸ hsG)
      · rw [min_eq_right h5]
        have : (G : ℝ) / (5 * G) = 1 / 5 := by field_simp
        rw [this]; exact min_le_right _ _
    have hmN : (mN : ℝ) / (5 * E) ≤ mz z' := by
      simp only [mz, mN, Nat.cast_min]; push_cast
      apply le_min
      · rcases le_total ((5 : ℝ) * f.lo1) E with h5 | h5
        · rw [min_eq_left h5]
          have : (5 : ℝ) * f.lo1 / (5 * E) = f.lo1 / E := by field_simp
          rw [this]; exact hs'lo
        · rw [min_eq_right h5]
          have : (E : ℝ) / (5 * E) = 1 / 5 := by field_simp
          rw [this]
          have : (1 : ℝ) / 5 ≤ f.lo1 / E := by rw [div_le_div_iff₀ (by norm_num) hE]; linarith
          linarith
      · rcases le_total ((5 : ℝ) * f.lo1) E with h5 | h5
        · rw [min_eq_left h5, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        · rw [min_eq_right h5]; have : (E : ℝ) / (5 * E) = 1 / 5 := by field_simp
          rw [this]
    have hmN0 : (0 : ℝ) ≤ mN := Nat.cast_nonneg _
    -- the base ratio
    set F0 := ((mN : ℝ) * G) / ((f.U : ℝ) * MN)
    have hF0 : 0 ≤ F0 := by positivity
    have hFac : alpha k ^ 8 * F0 ^ 7 ≤ Fac k z z' := by
      unfold Fac
      have hr : F0 ≤ (z.lam / z'.lam) * (mz z' / mz z) := by
        have e1 : (E : ℝ) / f.U ≤ z.lam / z'.lam := by rw [div_le_div_iff₀ hU0 hl']; linarith
        have e2 : ((mN : ℝ) / (5 * E)) / ((MN : ℝ) / (5 * G)) ≤ mz z' / mz z :=
          div_le_div₀ (le_trans (by positivity) hmN) hmN hm hmM
        have e3 : F0 = ((E : ℝ) / f.U) * (((mN : ℝ) / (5 * E)) / ((MN : ℝ) / (5 * G))) := by
          simp only [F0]; field_simp
        rw [e3]
        exact mul_le_mul e1 e2 (by positivity) (by positivity)
      have := pow_le_pow_left₀ hF0 hr 7
      rw [mul_pow] at this
      have ha := pow_pos (alpha_pos k) 8
      nlinarith
    -- from the Nat inequality
    have hnumR : ((f.U : ℝ) * MN) ^ 1792 * 2 ^ (cond (alphaDown k) 2048 0 + f.wpos) ≤
        ((mN : ℝ) * G) ^ 1792 * 2 ^ (cond (alphaUp k) 2048 0 + f.wneg) := by
      exact_mod_cast hnum
    have hap := alpha_pow k hk1 hk9
    have hY : (0 : ℝ) < ((f.U : ℝ) * MN) ^ 1792 := by positivity
    have key : (2 : ℝ) ^ f.wpos ≤ 2 ^ f.wneg * (alpha k ^ 8 * F0 ^ 7) ^ 256 := by
      have e : (alpha k ^ 8 * F0 ^ 7) ^ 256 = alpha k ^ 2048 * (((mN : ℝ) * G) ^ 1792 / ((f.U : ℝ) * MN) ^ 1792) := by
        simp only [F0]; ring
      rw [pow_add, pow_add, ← hap] at hnumR
      have h2 : (0 : ℝ) < 2 ^ (cond (alphaDown k) 2048 0) := by positivity
      have h3 : (2 : ℝ) ^ f.wpos * ((f.U : ℝ) * MN) ^ 1792 * 2 ^ (cond (alphaDown k) 2048 0) ≤
          2 ^ f.wneg * alpha k ^ 2048 * ((mN : ℝ) * G) ^ 1792 * 2 ^ (cond (alphaDown k) 2048 0) := by
        linarith
      have h4 := le_of_mul_le_mul_right h3 h2
      rw [e, show (2 : ℝ) ^ f.wneg * (alpha k ^ 2048 * (((mN : ℝ) * G) ^ 1792 / ((f.U : ℝ) * MN) ^ 1792)) =
        (2 ^ f.wneg * alpha k ^ 2048 * ((mN : ℝ) * G) ^ 1792) / ((f.U : ℝ) * MN) ^ 1792 by ring, le_div_iff₀ hY]
      exact h4
    have : (alpha k ^ 8 * F0 ^ 7) ^ 256 ≤ Fac k z z' ^ 256 :=
      pow_le_pow_left₀ (by have := pow_pos (alpha_pos k) 8; positivity) hFac 256
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) f.wneg]
  · -- exact overrides
    rw [hw0]
    apply Fac_ge_one_of
    rcases hov with (h3 | ⟨⟨h1, hs5⟩, hh5⟩) | ⟨⟨h2, hs5⟩, hl5⟩
    · -- reflection: λ' = λ, T' ≤ T
      subst h3
      have elam : z'.lam = z.lam := by rw [hz']; exact brM3_lam z
      have eT : z'.T ≤ z.T := by
        have h := brM3_spread z hbr hvz.d3
        have hl3 := brM3_lam z
        rw [hz']; simp only [brM, Zc.T] at h hl3 ⊢; linarith
      have hmm : mz z ≤ mz z' := by
        unfold mz; apply min_le_min_right
        rw [elam]; exact div_le_div_of_nonneg_left hl.le hT' eT
      unfold Fac; rw [elam, div_self hl.ne']; simp [alpha]
      exact one_le_pow₀ ((one_le_div hm).mpr hmm)
    · -- expansion with s, s' ≤ 1/5
      subst h1
      have hs : z.lam / z.T ≤ 1 / 5 := by
        have : (bl.s1 : ℝ) / G ≤ 1 / 5 := by
          rw [div_le_div_iff₀ hG (by norm_num)]; have : (5 * bl.s1 : ℝ) ≤ G := by exact_mod_cast hs5
          linarith
        linarith
      have hs' : z'.lam / z'.T ≤ 1 / 5 := by
        have : (f.hi1 : ℝ) / E ≤ 1 / 5 := by
          rw [div_le_div_iff₀ hE (by norm_num)]; have : (5 * f.hi1 : ℝ) ≤ E := by exact_mod_cast hh5
          linarith
        linarith
      have eT : z'.T ≤ 2 * z.T := by
        rw [hz']; exact brM1_T z hvz.d2 hvz.d3 hvz.a.le hvz.b hvz.c
      unfold Fac mz; rw [min_eq_left hs, min_eq_left hs']
      simp only [alpha, if_pos]
      have e : z.lam / z'.lam * (z'.lam / z'.T / (z.lam / z.T)) = z.T / z'.T := by field_simp
      rw [mul_assoc, ← mul_pow, e]
      have : (1 : ℝ) / 2 ≤ z.T / z'.T := by rw [div_le_div_iff₀ (by norm_num) hT']; linarith
      have : ((1 : ℝ) / 2) ^ 7 ≤ (z.T / z'.T) ^ 7 := pow_le_pow_left₀ (by norm_num) this 7
      norm_num at this ⊢; nlinarith
    · -- expanded reflection with s, s' ≥ 1/5
      subst h2
      have elam : z'.lam = z.lam := by rw [hz']; exact brM2_lam z
      have hs : 1 / 5 ≤ z.lam / z.T := by
        have h0 := hc.s0
        rw [div_le_div_iff₀ (by norm_num) hT]
        have : (G : ℝ) ≤ 5 * bl.s0 := by exact_mod_cast hs5
        simp only [Zc.T] at h0 ⊢; nlinarith
      have hs' : 1 / 5 ≤ z'.lam / z'.T := by
        have : (1 : ℝ) / 5 ≤ f.lo1 / E := by
          rw [div_le_div_iff₀ (by norm_num) hE]; have : (E : ℝ) ≤ 5 * f.lo1 := by exact_mod_cast hl5
          linarith
        linarith
      unfold Fac mz; rw [min_eq_right hs, min_eq_right hs', elam, div_self hl.ne']
      simp [alpha]


/-! ## Branch certificates -/

theorem sInf_false (bx : Box) (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (z : Zc) (hc : InCell bx z) (hvz : ValidZ z)
    (hbr : brC k z) (h : sInfeasible bx k = true) : False := by
  unfold sInfeasible at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h
  have hs1 := hc.s1; have hl := hvz.lam; have ha := hvz.a; have hb := hvz.b; have hcc := hvz.c
  have hd2 := hvz.d2; have hd3 := hvz.d3
  have hG : (G : ℝ) = 4096 := by norm_num [G]
  simp only [Zc.T, Zc.lam] at hs1 hl
  rcases h with ⟨rfl, h5⟩ | ⟨h4, h2⟩
  · have h5' : (5 : ℝ) * bx.s1 < G := by exact_mod_cast h5
    simp only [brC, brC2] at hbr
    have hT : z.d2 + z.d3 + (z.a + z.b + z.c) ≤ 5 * (z.a + z.b + z.c) := by linarith [hbr.2]
    have : (G : ℝ) * (z.a + z.b + z.c) ≤ bx.s1 * (5 * (z.a + z.b + z.c)) :=
      le_trans hs1 (mul_le_mul_of_nonneg_left hT (by positivity))
    nlinarith
  · have h2' : (2 : ℝ) * bx.s1 ≤ G := by exact_mod_cast h2
    have hT : z.d2 + z.d3 + (z.a + z.b + z.c) < 2 * (z.a + z.b + z.c) := by
      interval_cases k <;> simp only [brC, brC4, brC5, brC6, brC7, brC8, brC9] at hbr <;> linarith [hbr.1]
    have : (G : ℝ) * (z.a + z.b + z.c) < bx.s1 * (2 * (z.a + z.b + z.c)) := by
      have hs1p : (0 : ℝ) < bx.s1 := by
        by_contra hc0; push_neg at hc0
        have : (bx.s1 : ℝ) * (z.d2 + z.d3 + (z.a + z.b + z.c)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hc0 (by linarith)
        have : (0 : ℝ) < G * (z.a + z.b + z.c) := by rw [hG]; linarith
        linarith
      exact lt_of_le_of_lt hs1 (mul_lt_mul_of_pos_left hT hs1p)
    nlinarith

theorem conjInf_false (bx : Box) (k i pr : Nat) (z : Zc) (hc : InCell bx z) (hbr : brC k z)
    (h : conjInfeasible bx k i pr = true) : False := by
  unfold conjInfeasible at h
  rcases hn : nth (brConds k) i with _ | ⟨c, need⟩
  · rw [hn] at h; simp at h
  · rw [hn] at h
    have hb := br_conds k z hbr i c need hn
    cases need
    · simp only at h
      have := (chk_sound bx pr c false z hc h).1
      linarith [hb.2 rfl]
    · simp only at h
      have := (chk_sound bx pr _ true z hc h).2 rfl
      simp only [evz_neg] at this
      linarith [hb.1 rfl]

theorem chkLeaf_dec (tr : KT) (b : Box) (n x : Nat) (h : chkLeaf tr b n x = true) :
    (b.s0 ≤ b.s1 ∧ b.s1 ≤ G ∧ b.p0 ≤ b.p1 ∧ b.p1 ≤ G) ∧
      ∀ k, 1 ≤ k → k ≤ 9 → ∃ y, (chkBranch tr b n k y).1 = true := by
  unfold chkLeaf at h
  dsimp only at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩, r8⟩, r9⟩ := h
  refine ⟨⟨b1, b2, b3, b4⟩, fun k hk1 hk9 => ?_⟩
  interval_cases k
  exacts [⟨_, r1⟩, ⟨_, r2⟩, ⟨_, r3⟩, ⟨_, r4⟩, ⟨_, r5⟩, ⟨_, r6⟩, ⟨_, r7⟩, ⟨_, r8⟩, ⟨_, r9⟩]

theorem chkBranch_cases (tr : KT) (b : Box) (n k y : Nat) (h : (chkBranch tr b n k y).1 = true) :
    sInfeasible b k = true ∨ (∃ i pr, conjInfeasible b k i pr = true) ∨ ∃ f, chkFeas tr b n k f = true := by
  unfold chkBranch at h
  dsimp only at h
  cases h0 : Nat.beq (rd y 2) 0
  · rw [h0] at h; simp only [cond] at h
    cases h1 : Nat.beq (rd y 2) 1
    · rw [h1] at h; simp only [cond] at h; exact Or.inr (Or.inr ⟨_, h⟩)
    · rw [h1] at h; simp only [cond] at h; exact Or.inr (Or.inl ⟨_, _, h⟩)
  · rw [h0] at h; simp only [cond] at h; exact Or.inl h


/-! ## The potential from a certificate -/

/-- every leaf of the subtree `t` (with box `b`) carries a passing certificate -/
def AllOK (tr t : KT) (b : Box) : Prop :=
  ∀ z, ∃ c, cond (look z t b).2.1 (chkHole (look z t b).2.2 c) (chkLeaf tr (look z t b).2.2 (look z t b).1 c) = true

theorem allOK_of_walk (tr t : KT) (b : Box) (cs : List Nat) (h : walk tr t b cs = some []) : AllOK tr t b :=
  fun z => walk_ok tr z t b cs [] h

theorem allOK_node (tr : KT) (d v mx : Nat) (l r : KT) (b : Box)
    (hl : AllOK tr l (b.setHi d v)) (hr : AllOK tr r (b.setLo d v)) : AllOK tr (.node d v mx l r) b := by
  intro z
  simp only [look]
  split_ifs
  · exact hl z
  · exact hr z

def maxAll : KT → Nat
  | .leaf n _ => n
  | .node _ _ _ l r => max (maxAll l) (maxAll r)

theorem look_le_maxAll (z : Zc) : ∀ (t : KT) (b : Box), (look z t b).1 ≤ maxAll t := by
  intro t
  induction t with
  | leaf n h => intro b; simp [look, maxAll]
  | node d v mx l r ihl ihr =>
    intro b; simp only [look, maxAll]
    split_ifs
    · exact le_trans (ihl _) (le_max_left _ _)
    · exact le_trans (ihr _) (le_max_right _ _)

def nOf (tr : KT) (t : Tri) : Nat := (look (zc t) tr rootBox).1
def qOf (tr : KT) (t : Tri) : ℝ := (2 : ℝ) ^ (-(nOf tr t : ℝ) / 2560)

theorem validZ_of (t : Tri) (hs : sorted t) (hn : nondeg t) : ValidZ (zc t) := by
  have h := zc_nonneg t hs
  refine ⟨h.1, h.2.1, D12_pos t hn, h.2.2.2.1, h.2.2.2.2, ?_⟩
  have : heronZ (zc t) = heron t := by simp only [heronZ, heron, zc]
  rw [this, heron_eq]; positivity

theorem strip_of_far (t : Tri) (hs : sorted t) (hn : nondeg t) (hfar : 169869312 * lam t ≤ f t.p1) :
    StripZ (zc t) := by
  have e : heronZ (zc t) = heron t := by simp only [heronZ, heron, zc]
  have hl := lam_pos t hn
  have hh : 0 ≤ heron t := by rw [heron_eq]; positivity
  refine ⟨?_, ?_, ?_⟩ <;> intro h8 <;> rw [zc_lam, zc_T] at * <;> rw [e]
  · have := far_strip_m t hs 169869312 (by norm_num) hfar hn 7 (by norm_num) (by linarith)
    nlinarith
  · have := far_strip_m t hs 169869312 (by norm_num) hfar hn 63 (by norm_num) (by linarith)
    nlinarith
  · have := far_strip_m t hs 169869312 (by norm_num) hfar hn 511 (by norm_num) (by linarith)
    nlinarith

theorem q_ineq (n n' wpos wneg : ℕ) (F : ℝ) (hF : 0 ≤ F) (h1 : n' + wneg ≤ n + wpos)
    (h2 : (2 : ℝ) ^ wpos ≤ 2 ^ wneg * F ^ 256) :
    ((2 : ℝ) ^ (-(n : ℝ) / 2560)) ^ 10 ≤ ((2 : ℝ) ^ (-(n' : ℝ) / 2560)) ^ 10 * F := by
  have e : ∀ m : ℕ, ((2 : ℝ) ^ (-(m : ℝ) / 2560)) ^ 10 = (2 : ℝ) ^ (-(m : ℝ) / 256) := by
    intro m; rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
  rw [e, e]
  set r : ℝ := ((wpos : ℝ) - wneg) / 256
  have h3 : (2 : ℝ) ^ r ≤ F := by
    have : ((2 : ℝ) ^ r) ^ 256 ≤ F ^ 256 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : r * ((256 : ℕ) : ℝ) = (wpos : ℝ) - wneg := by simp only [r]; push_cast; ring
      rw [this, Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast, div_le_iff₀ (by positivity)]
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hF (by norm_num)).mp this
  have h4 : (2 : ℝ) ^ (-(n : ℝ) / 256) ≤ 2 ^ (-(n' : ℝ) / 256) * 2 ^ r := by
    rw [← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (n' : ℝ) + wneg ≤ n + wpos := by exact_mod_cast h1
    simp only [r]; linarith
  exact le_trans h4 (mul_le_mul_of_nonneg_left h3 (by positivity))

theorem final_alg (A α q q' m m' l l' F : ℝ) (hA : 0 ≤ A) (hm : 0 < m) (hl' : 0 < l') (hl : 0 < l)
    (hF : F = α ^ 8 * (l / l') ^ 7 * (m' / m) ^ 7) (hq : q ^ 10 ≤ q' ^ 10 * F) (hq0 : 0 ≤ q) :
    A ^ 8 * q ^ 10 * m ^ 7 * l' ^ 7 ≤ (α * A) ^ 8 * q' ^ 10 * m' ^ 7 * l ^ 7 := by
  have h1 : A ^ 8 * q ^ 10 * m ^ 7 * l' ^ 7 ≤ A ^ 8 * (q' ^ 10 * F) * m ^ 7 * l' ^ 7 := by
    have := pow_nonneg hA 8; have := pow_pos hm 7; have := pow_pos hl' 7
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have h2 : A ^ 8 * (q' ^ 10 * F) * m ^ 7 * l' ^ 7 = (α * A) ^ 8 * q' ^ 10 * m' ^ 7 * l ^ 7 := by
    rw [hF]; field_simp
  linarith

set_option maxHeartbeats 1000000 in
theorem step_ineq (tr : KT) (hmx : mxOK tr = true) (hall : AllOK tr tr rootBox) (t : Tri)
    (hs : sorted t) (hn : nondeg t) (hfar : 169869312 * lam t ≤ f t.p1)
    (hfar' : 169869312 * lam (step t) ≤ f (step t).p1) :
    A t ^ 8 * qOf tr t ^ 10 * mS t ^ 7 * lam (step t) ^ 7 ≤
      A (step t) ^ 8 * qOf tr (step t) ^ 10 * mS (step t) ^ 7 * lam t ^ 7 := by
  have hs' := step_sorted t hs hn; have hn' := step_nondeg t hs hn
  set z := zc t with hzdef
  set z' := zc (step t) with hz'def
  have hv := validZ_of t hs hn; have hv' := validZ_of (step t) hs' hn'
  have hst := strip_of_far t hs hn hfar; have hst' := strip_of_far (step t) hs' hn' hfar'
  obtain ⟨k, hk1, hk9, hbr, hzeq, hA⟩ := step_branch' t hs hn
  set L := look z tr rootBox with hL
  have hLbox : inBox G L.2.2 z := look_mem z tr rootBox (inBox_root hv)
  obtain ⟨c, hcL⟩ := hall z
  cases hhole : L.2.1 with
  | true =>
    rw [← hL, hhole] at hcL
    exact (hole_sound _ c hcL z hv.lam (cons_of_box hv hLbox (strip_of_s hv hst hLbox))).elim
  | false =>
    rw [← hL, hhole] at hcL
    simp only [cond] at hcL
    obtain ⟨hbd, hbrs⟩ := chkLeaf_dec tr L.2.2 L.1 c hcL
    have hcell : InCell L.2.2 z := inCell_of hv hLbox (strip_of_s hv hst hLbox)
      ⟨le_trans hbd.1 hbd.2.1, hbd.2.1, le_trans hbd.2.2.1 hbd.2.2.2, hbd.2.2.2⟩
    obtain ⟨y, hy⟩ := hbrs k hk1 hk9
    rcases chkBranch_cases tr L.2.2 L.1 k y hy with h0 | ⟨i, pr, h1⟩ | ⟨fc, h2⟩
    · exact (sInf_false L.2.2 k hk1 hk9 z hcell hv hbr h0).elim
    · exact (conjInf_false L.2.2 k i pr z hcell hbr h1).elim
    · obtain ⟨henc, hU, hw, hq⟩ := enc_sound tr L.2.2 L.1 k hk1 hk9 fc z z' hcell hzeq hv' h2
      obtain ⟨rest, hrest⟩ := Option.isSome_iff_exists.mp hq
      have hQ := query_ok (pruneOK L.2.2 k) fc.enc (L.1 + fc.wpos) fc.wneg z' henc tr rootBox fc.prunes rest
        hmx hrest
      set L' := look z' tr rootBox with hL'
      have hL'box : inBox G L'.2.2 z' := look_mem z' tr rootBox (inBox_root hv')
      have hnn : L'.1 + fc.wneg ≤ L.1 + fc.wpos := by
        rcases hQ with hh | hh | ⟨p, hp⟩
        · exfalso
          obtain ⟨c', hc'⟩ := hall z'
          rw [← hL', hh] at hc'
          exact hole_sound _ c' hc' z' hv'.lam (cons_of_box hv' hL'box (strip_of_s hv' hst' hL'box))
        · exact hh
        · exact (prune_sound L.2.2 k hk1 hk9 p L'.2.2 z z' hcell hbr hzeq hv' hL'box hp).elim
      have h0 := henc 0 (by norm_num)
      simp only [Feas.enc, Box.lo, Box.hi, zcoord] at h0
      have hW := wOK_sound L.2.2 k hk1 hk9 fc z z' hcell hv hv' hbr hzeq h0.1 h0.2 hU hw
      have hF0 : 0 ≤ Fac k z z' := by
        unfold Fac
        have := alpha_pos k; have := mz_pos hv; have := mz_pos hv'; have := hv.lam; have := hv'.lam
        positivity
      have hqq := q_ineq L.1 L'.1 fc.wpos fc.wneg (Fac k z z') hF0 hnn hW
      have em : mS t = mz z := by simp only [mS, mz, hzdef, zc_lam, zc_T]
      have em' : mS (step t) = mz z' := by simp only [mS, mz, hz'def, zc_lam, zc_T]
      have el : lam t = z.lam := by rw [hzdef, zc_lam]
      have el' : lam (step t) = z'.lam := by rw [hz'def, zc_lam]
      have eq : qOf tr t = (2 : ℝ) ^ (-(L.1 : ℝ) / 2560) := rfl
      have eq' : qOf tr (step t) = (2 : ℝ) ^ (-(L'.1 : ℝ) / 2560) := rfl
      rw [em, em', el, el', eq, eq', hA]
      exact final_alg (A t) (alpha k) _ _ (mz z) (mz z') z.lam z'.lam (Fac k z z') (abs_nonneg _)
        (mz_pos hv) hv'.lam hv.lam rfl hqq (by positivity)

theorem goodPotential_of_cert (tr : KT) (hmx : mxOK tr = true) (hall : AllOK tr tr rootBox) :
    GoodPotential 169869312 (qOf tr) := by
  refine ⟨⟨(2 : ℝ) ^ (-(maxAll tr : ℝ) / 2560), by positivity, fun t => ⟨?_, ?_⟩⟩, ?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (nOf tr t : ℝ) ≤ maxAll tr := by exact_mod_cast look_le_maxAll (zc t) tr rootBox
    linarith
  · apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) ≤ nOf tr t := Nat.cast_nonneg _
    linarith
  · intro t hs hn hf hf'
    exact step_ineq tr hmx hall t hs hn hf hf'

/-- the conditional main theorem, reduced to the two certificate facts -/
theorem nm_converges_of_cert (tr : KT) (hmx : mxOK tr = true) (hall : AllOK tr tr rootBox)
    (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :
    Filter.Tendsto (fun k => (traj t0 k).p1) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p2) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p3) Filter.atTop (nhds 0) :=
  nm_converges_of_potential 169869312 (qOf tr) (goodPotential_of_cert tr hmx hall) t0 h0 hn0


/-! ## Initial ordering -/

theorem sort3_sorted (x y z : Pt) : sorted (sort3 x y z) := by
  unfold sort3 sorted
  split_ifs <;> simp only <;> constructor <;> linarith

theorem sort3_nondeg (x y z : Pt) (h : nondeg ⟨x, y, z⟩) : nondeg (sort3 x y z) := by
  unfold nondeg area2 at *
  unfold sort3
  split_ifs <;> simp only <;> intro h' <;> apply h <;> linarith

end
end NMS
