import NMSound
open NM Filter

namespace NM
noncomputable section

/-- `max(T, 5·lam)`; the potential is `P = A^(4/5) / max(T, 5 lam)^(7/10)`, used as `P^10 = A^8 / Mx^7`. -/
def Mx (t : Tri) : ℝ := max (T t) (5 * lam t)

/-- recovery in the far region: from every far state the potential returns to at least its current value
after finitely many (≥ 1) steps -/
def Recovery (K : ℝ) : Prop :=
  ∀ t, sorted t → nondeg t → K * lam t ≤ f t.p1 →
    ∃ k, 1 ≤ k ∧ A t ^ 8 * Mx (step^[k] t) ^ 7 ≤ A (step^[k] t) ^ 8 * Mx t ^ 7

theorem traj_add (t0 : Tri) (k j : ℕ) : traj t0 (k + j) = step^[j] (traj t0 k) := by
  simp only [traj]; rw [add_comm, Function.iterate_add_apply]

theorem converge_of_recovery (K : ℝ) (hR : Recovery K)
    (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :
    Tendsto (fun k => f (traj t0 k).p3) atTop (nhds 0) := by
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
  have far : ∀ᶠ k in atTop, K * lam (traj t0 k) ≤ f (traj t0 k).p1 := by
    have hK : Tendsto (fun k => K * lam (traj t0 k)) atTop (nhds 0) := by
      simpa using L.const_mul K
    filter_upwards [hK.eventually (Iio_mem_nhds hfs)] with k hk
    exact le_trans hk.le (iInf_le' hb1 k)
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp far
  have lpos : ∀ k, 0 < lam (traj t0 k) := fun k => lam_pos _ (traj_inv t0 h0 hn0 k).2
  have Mpos : ∀ k, 0 < Mx (traj t0 k) := fun k => lt_of_lt_of_le (by linarith [lpos k]) (le_max_right _ _)
  set P := fun k => A (traj t0 k) ^ 8 / Mx (traj t0 k) ^ 7
  have Ppos : ∀ k, 0 < P k := fun k =>
    div_pos (pow_pos (A_pos _ (traj_inv t0 h0 hn0 k).2) 8) (pow_pos (Mpos k) 7)
  -- one recovery step from any far time
  have hrec : ∀ m, k0 ≤ m → ∃ m', m + 1 ≤ m' ∧ P m ≤ P m' := by
    intro m hm
    have i := traj_inv t0 h0 hn0 m
    obtain ⟨k, hk1, hk⟩ := hR _ i.1 i.2 (hk0 m hm)
    refine ⟨m + k, by omega, ?_⟩
    simp only [P]
    rw [traj_add, div_le_div_iff₀ (pow_pos (Mpos m) 7) (by rw [← traj_add]; exact pow_pos (Mpos _) 7)]
    linarith
  have reach : ∀ n, ∃ m, k0 + n ≤ m ∧ P k0 ≤ P m := by
    intro n; induction n with
    | zero => exact ⟨k0, le_refl _, le_refl _⟩
    | succ n ih =>
      obtain ⟨m, hm, hP⟩ := ih
      obtain ⟨m', hm', hP'⟩ := hrec m (by omega)
      exact ⟨m', by omega, le_trans hP hP'⟩
  -- P ≤ lam / 5^7 → 0
  have Ple : ∀ k, P k ≤ lam (traj t0 k) / 5 ^ 7 := by
    intro k
    have i := traj_inv t0 h0 hn0 k
    have hA := A_le_lam (traj t0 k); have hA0 := A_pos _ i.2
    have hl := lpos k
    have hM : 5 * lam (traj t0 k) ≤ Mx (traj t0 k) := le_max_right _ _
    simp only [P]
    rw [div_le_div_iff₀ (pow_pos (Mpos k) 7) (by norm_num)]
    calc A (traj t0 k) ^ 8 * 5 ^ 7 ≤ lam (traj t0 k) ^ 8 * 5 ^ 7 := by
          gcongr
      _ = lam (traj t0 k) * (5 * lam (traj t0 k)) ^ 7 := by ring
      _ ≤ lam (traj t0 k) * Mx (traj t0 k) ^ 7 := by gcongr
  have hsmall : ∀ᶠ k in atTop, lam (traj t0 k) / 5 ^ 7 < P k0 := by
    have : Tendsto (fun k => lam (traj t0 k) / 5 ^ 7) atTop (nhds 0) := by simpa using L.div_const (5 ^ 7)
    exact this.eventually (Iio_mem_nhds (Ppos k0))
  obtain ⟨k1, hk1⟩ := eventually_atTop.mp hsmall
  obtain ⟨m, hm, hPm⟩ := reach k1
  have := Ple m; have := hk1 m (by omega)
  linarith

theorem nm_converges_of_recovery (K : ℝ) (hR : Recovery K)
    (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :
    Tendsto (fun k => (traj t0 k).p1) atTop (nhds 0) ∧
    Tendsto (fun k => (traj t0 k).p2) atTop (nhds 0) ∧
    Tendsto (fun k => (traj t0 k).p3) atTop (nhds 0) := by
  have T3 := converge_of_recovery K hR t0 h0 hn0
  have hs := fun k => (traj_inv t0 h0 hn0 k).1
  have T1 : Tendsto (fun k => f (traj t0 k).p1) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds T3 (fun k => f_nonneg _)
      (fun k => le_trans (hs k).1 (hs k).2)
  have T2 : Tendsto (fun k => f (traj t0 k).p2) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds T3 (fun k => f_nonneg _)
      (fun k => (hs k).2)
  exact ⟨pt_tendsto_zero T1, pt_tendsto_zero T2, pt_tendsto_zero T3⟩

end
end NM


open NM NMC NMS

/-! Recovery-tree checker, part 1: integer branch matrices and state tracking.
The state after `j` steps along a branch word is tracked as five functionals `W` of the start state `z0`
(scaled by `16^j`): `evz (W.get r) z0 = 16^j · coordinate r of z_j`. -/

namespace NMR

/-- row `r` of `16 · brM k` as a functional of z -/
def Mrow : Nat → Nat → F5
  | 1, 0 => ⟨⟨8, 0⟩, ⟨32, 0⟩, ⟨36, 0⟩, ⟨0, 48⟩, ⟨0, 48⟩⟩
  | 1, 1 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 1, 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 12⟩, ⟨16, 0⟩, ⟨48, 0⟩⟩
  | 1, 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 12⟩, ⟨48, 0⟩, ⟨16, 0⟩⟩
  | 1, 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 2, 0 => ⟨⟨0, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩, ⟨0, 16⟩, ⟨0, 16⟩⟩
  | 2, 1 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 2, 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩⟩
  | 2, 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩⟩
  | 2, 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 3, 0 => ⟨⟨0, 0⟩, ⟨0, 16⟩, ⟨0, 16⟩, ⟨16, 0⟩, ⟨16, 0⟩⟩
  | 3, 1 => ⟨⟨16, 0⟩, ⟨16, 0⟩, ⟨16, 0⟩, ⟨0, 16⟩, ⟨0, 16⟩⟩
  | 3, 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩⟩
  | 3, 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 3, 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩⟩
  | 4, 0 => ⟨⟨0, 4⟩, ⟨8, 0⟩, ⟨9, 0⟩, ⟨0, 6⟩, ⟨0, 6⟩⟩
  | 4, 1 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 4, 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | 4, 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | 4, 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 5, 0 => ⟨⟨0, 12⟩, ⟨0, 8⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  | 5, 1 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 5, 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | 5, 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | 5, 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 6, 0 => ⟨⟨4, 0⟩, ⟨0, 8⟩, ⟨0, 9⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩
  | 6, 1 => ⟨⟨12, 0⟩, ⟨8, 0⟩, ⟨9, 0⟩, ⟨0, 6⟩, ⟨0, 6⟩⟩
  | 6, 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | 6, 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 6, 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | 7, 0 => ⟨⟨12, 0⟩, ⟨8, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩⟩
  | 7, 1 => ⟨⟨4, 0⟩, ⟨0, 8⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩⟩
  | 7, 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | 7, 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 7, 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | 8, 0 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 8, 1 => ⟨⟨0, 12⟩, ⟨0, 8⟩, ⟨0, 9⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩
  | 8, 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 8, 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | 8, 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | 9, 0 => ⟨⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 9, 1 => ⟨⟨0, 4⟩, ⟨8, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 2⟩⟩
  | 9, 2 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨16, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  | 9, 3 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨0, 2⟩⟩
  | 9, 4 => ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 2⟩, ⟨6, 0⟩⟩
  | _, _ => F5.zero

/-- coordinate `r` of a state -/
noncomputable def zco (z : Zc) : Nat → ℝ
  | 0 => z.d2 | 1 => z.d3 | 2 => z.a | 3 => z.b | _ => z.c

theorem Mrow_ev (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (r : Nat) (hr : r < 5) (z : Zc) :
    evz (Mrow k r) z = 16 * zco (brM k z) r := by
  interval_cases k <;> interval_cases r <;>
    simp [Mrow, evz, F5.ev, Z.val, brM, brM1, brM2, brM3, brM4, brM5, brM6, brM7, brM8, brM9, zco] <;> ring

/-- five functionals -/
structure W5 where
  w0 : F5
  w1 : F5
  w2 : F5
  w3 : F5
  w4 : F5

def W5.get (W : W5) : Nat → F5
  | 0 => W.w0 | 1 => W.w1 | 2 => W.w2 | 3 => W.w3 | _ => W.w4

def F5.smul (x : Z) (c : F5) : F5 := ⟨Z.mul x c.c1, Z.mul x c.c2, Z.mul x c.c3, Z.mul x c.c4, Z.mul x c.c5⟩

/-- `Σ_r c_r · W_r`: the functional `c` of the tracked state, as a functional of `z0` -/
def comb5 (c : F5) (W : W5) : F5 :=
  F5.add (F5.add (F5.add (F5.add (F5.smul c.c1 W.w0) (F5.smul c.c2 W.w1)) (F5.smul c.c3 W.w2))
    (F5.smul c.c4 W.w3)) (F5.smul c.c5 W.w4)

def stepW (k : Nat) (W : W5) : W5 :=
  ⟨comb5 (Mrow k 0) W, comb5 (Mrow k 1) W, comb5 (Mrow k 2) W, comb5 (Mrow k 3) W, comb5 (Mrow k 4) W⟩

/-- the identity tracking at depth 0 -/
def W5.id : W5 :=
  ⟨⟨zN 1, zN 0, zN 0, zN 0, zN 0⟩, ⟨zN 0, zN 1, zN 0, zN 0, zN 0⟩, ⟨zN 0, zN 0, zN 1, zN 0, zN 0⟩,
   ⟨zN 0, zN 0, zN 0, zN 1, zN 0⟩, ⟨zN 0, zN 0, zN 0, zN 0, zN 1⟩⟩

/-- `W` tracks `zj` from `z0` with scale `σ` -/
def Tracks (W : W5) (z0 zj : Zc) (σ : ℝ) : Prop := ∀ r, r < 5 → evz (W.get r) z0 = σ * zco zj r

theorem evz_smul (x : Z) (c : F5) (z : Zc) : evz (F5.smul x c) z = x.val * evz c z := by
  simp only [evz, F5.ev, F5.smul, Z.val_mul]; ring

theorem comb5_ev (c : F5) (W : W5) (z0 zj : Zc) (σ : ℝ) (h : Tracks W z0 zj σ) :
    evz (comb5 c W) z0 = σ * evz c zj := by
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num); have h4 := h 4 (by norm_num)
  simp only [W5.get, zco] at h0 h1 h2 h3 h4
  unfold comb5
  simp only [evz_add, evz_smul]
  rw [h0, h1, h2, h3, h4]
  simp only [evz, F5.ev]; ring

theorem tracks_id (z : Zc) : Tracks W5.id z z 1 := by
  intro r hr; interval_cases r <;> simp [W5.id, W5.get, evz, F5.ev, zN, Z.val, zco]

theorem tracks_step (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (W : W5) (z0 zj : Zc) (σ : ℝ)
    (h : Tracks W z0 zj σ) : Tracks (stepW k W) z0 (brM k zj) (16 * σ) := by
  intro r hr
  have e : (stepW k W).get r = comb5 (Mrow k r) W := by interval_cases r <;> rfl
  rw [e, comb5_ev _ _ _ _ _ h, Mrow_ev k hk1 hk9 r hr]; ring

/-! Part 2: rows, recovery-tree certificates, soundness -/

/-- branch rows: functionals of `z0` that are `≥ 0` when the tracked state takes branch `k` -/
def brRows (k : Nat) (W : W5) : List F5 :=
  (brConds k).map (fun p => cond p.2 (comb5 p.1 W) (F5.neg (comb5 p.1 W)))

def getR (rows : List F5) (i : Nat) : F5 := (nth rows i).getD F5.zero

/-- sparse Farkas combination `Σ y · rows[i]` -/
def farkas (rows : List F5) : List (Nat × Nat) → F5
  | [] => F5.zero
  | (i, y) :: ys => F5.add (F5.smul (zN y) (getR rows i)) (farkas rows ys)

def TT : F5 := ⟨zN 1, zN 1, zN 1, zN 1, zN 1⟩
def L5 : F5 := ⟨zN 0, zN 0, zN 5, zN 5, zN 5⟩

mutual
/-- recovery tree: a leaf certifies `P(z_j) ≥ P(z0)`; a node lists, for branches `1 … 9`, either an
infeasibility certificate or a subtree -/
inductive RT where
  | leaf (den : Bool) (rn rd : Nat) (y1 : List (Nat × Nat)) (p1 : Nat) (y2 : List (Nat × Nat)) (p2 : Nat)
  | node (c1 c2 c3 c4 c5 c6 c7 c8 c9 : RC)
inductive RC where
  | inf (ys : List (Nat × Nat)) (pr : Nat)
  | sub (t : RT)
end

def eUp (k : Nat) : Nat := cond (Nat.beq k 1) 1 0
def eDn (k : Nat) : Nat := cond (Nat.ble 4 k) 1 0

mutual
def chkRT (b : Box) : RT → W5 → List F5 → Nat → Nat → Nat → Bool
  | .leaf den rn rd y1 p1 y2 p2, W, rows, j, nE, nC =>
    Nat.ble 1 j && Nat.ble 1 rd &&
    chk b p1 (F5.add (F5.lin (zN rn) (cond den TT L5) (zM rd) (comb5 TT W)) (F5.neg (farkas rows y1))) false &&
    chk b p2 (F5.add (F5.lin (zN rn) (cond den TT L5) (zM rd) (comb5 L5 W)) (F5.neg (farkas rows y2))) false &&
    Nat.ble (2 ^ (8 * nC) * rn ^ 7) (2 ^ (8 * nE) * (rd * 16 ^ j) ^ 7)
  | .node c1 c2 c3 c4 c5 c6 c7 c8 c9, W, rows, j, nE, nC =>
    chkRC b 1 c1 W rows j nE nC && chkRC b 2 c2 W rows j nE nC && chkRC b 3 c3 W rows j nE nC &&
    chkRC b 4 c4 W rows j nE nC && chkRC b 5 c5 W rows j nE nC && chkRC b 6 c6 W rows j nE nC &&
    chkRC b 7 c7 W rows j nE nC && chkRC b 8 c8 W rows j nE nC && chkRC b 9 c9 W rows j nE nC
def chkRC (b : Box) (k : Nat) : RC → W5 → List F5 → Nat → Nat → Nat → Bool
  | .inf ys pr, W, rows, _, _, _ => chk b pr (F5.neg (farkas (rows ++ brRows k W) ys)) true
  | .sub t, W, rows, j, nE, nC => chkRT b t (stepW k W) (rows ++ brRows k W) (j + 1) (nE + eUp k) (nC + eDn k)
end

def RT.child : RT → Nat → Option RC
  | .node c1 c2 c3 c4 c5 c6 c7 c8 c9, k =>
    match k with
    | 1 => some c1 | 2 => some c2 | 3 => some c3 | 4 => some c4 | 5 => some c5 | 6 => some c6
    | 7 => some c7 | 8 => some c8 | 9 => some c9 | _ => none
  | .leaf .., _ => none

theorem chkRT_node (b : Box) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : RC) (W : W5) (rows : List F5) (j nE nC : Nat)
    (h : chkRT b (.node c1 c2 c3 c4 c5 c6 c7 c8 c9) W rows j nE nC = true) (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) :
    ∃ c, (RT.node c1 c2 c3 c4 c5 c6 c7 c8 c9).child k = some c ∧ chkRC b k c W rows j nE nC = true := by
  simp only [chkRT, Bool.and_eq_true] at h
  interval_cases k <;> simp only [RT.child] <;> exact ⟨_, rfl, by tauto⟩

/-! ### evaluation lemmas -/

theorem nth_mem {α : Type} : ∀ (l : List α) (i : Nat) (x : α), nth l i = some x → x ∈ l
  | [], _, _, h => by simp [nth] at h
  | a :: l, 0, x, h => by simp [nth] at h; simp [h]
  | a :: l, i + 1, x, h => by simp only [nth] at h; exact List.mem_cons_of_mem _ (nth_mem l i x h)

theorem mem_nth {α : Type} : ∀ (l : List α) (x : α), x ∈ l → ∃ i, nth l i = some x
  | [], _, h => by simp at h
  | a :: l, x, h => by
    rcases List.mem_cons.mp h with h | h
    · exact ⟨0, by simp [nth, h]⟩
    · obtain ⟨i, hi⟩ := mem_nth l x h; exact ⟨i + 1, by simp [nth, hi]⟩

theorem getR_nonneg (rows : List F5) (z : Zc) (h : ∀ r ∈ rows, 0 ≤ evz r z) (i : Nat) : 0 ≤ evz (getR rows i) z := by
  unfold getR
  cases hn : nth rows i with
  | none => simp
  | some r => simpa using h r (nth_mem rows i r hn)

theorem farkas_nonneg (rows : List F5) (z : Zc) (h : ∀ r ∈ rows, 0 ≤ evz r z) :
    ∀ ys, 0 ≤ evz (farkas rows ys) z
  | [] => by simp [farkas]
  | (i, y) :: ys => by
    simp only [farkas, evz_add, evz_smul]
    have := getR_nonneg rows z h i; have := farkas_nonneg rows z h ys
    have hy : (0 : ℝ) ≤ (zN y).val := by simp [zN, Z.val]
    positivity

theorem brRows_nonneg (k : Nat) (W : W5) (z0 zj : Zc) (σ : ℝ) (hσ : 0 < σ) (hW : Tracks W z0 zj σ)
    (hbr : brC k zj) : ∀ r ∈ brRows k W, 0 ≤ evz r z0 := by
  intro r hr
  simp only [brRows, List.mem_map] at hr
  obtain ⟨⟨c, need⟩, hmem, rfl⟩ := hr
  obtain ⟨i, hi⟩ := mem_nth _ _ hmem
  have hb := br_conds k zj hbr i c need hi
  cases need with
  | true => simp only [cond]; rw [comb5_ev _ _ _ _ _ hW]; exact mul_nonneg hσ.le (hb.1 rfl)
  | false => simp only [cond, evz_neg]; rw [comb5_ev _ _ _ _ _ hW]; nlinarith [hb.2 rfl]

theorem evz_TT (z : Zc) : evz TT z = z.T := by simp [evz, F5.ev, TT, zN, Z.val, Zc.T, Zc.lam]; ring
theorem evz_L5 (z : Zc) : evz L5 z = 5 * z.lam := by simp [evz, F5.ev, L5, zN, Z.val, Zc.lam]; ring

/-! ### soundness -/

noncomputable def Mxz (z : Zc) : ℝ := max z.T (5 * z.lam)
theorem Mx_eq (t : Tri) : Mx t = Mxz (zc t) := by simp only [Mx, Mxz, zc_T, zc_lam]

theorem alpha_e (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) : alpha k = (2 : ℝ) ^ eUp k / 2 ^ eDn k := by
  interval_cases k <;> norm_num [alpha, eUp, eDn]

/-- the recovery goal for the start state -/
def Goal (t0 : Tri) : Prop := ∃ k, 1 ≤ k ∧ A t0 ^ 8 * Mx (step^[k] t0) ^ 7 ≤ A (step^[k] t0) ^ 8 * Mx t0 ^ 7

structure Inv (t0 : Tri) (W : W5) (rows : List F5) (j nE nC : Nat) : Prop where
  srt : sorted (step^[j] t0)
  ndg : nondeg (step^[j] t0)
  trk : Tracks W (zc t0) (zc (step^[j] t0)) (16 ^ j)
  rws : ∀ r ∈ rows, 0 ≤ evz r (zc t0)
  area : A (step^[j] t0) = (2 : ℝ) ^ nE / 2 ^ nC * A t0

theorem leaf_goal (t0 : Tri) (hn0 : nondeg t0) (hs0 : sorted t0) (j nE nC rn rd : Nat) (hj : 1 ≤ j) (hrd : 1 ≤ rd)
    (hT : (rd : ℝ) * 16 ^ j * Mxz (zc (step^[j] t0)) ≤ rn * Mxz (zc t0))
    (hexp : 2 ^ (8 * nC) * rn ^ 7 ≤ 2 ^ (8 * nE) * (rd * 16 ^ j) ^ 7)
    (hA : A (step^[j] t0) = (2 : ℝ) ^ nE / 2 ^ nC * A t0)
    (hX : 0 ≤ Mxz (zc (step^[j] t0))) (hY : 0 < Mxz (zc t0)) : Goal t0 := by
  refine ⟨j, hj, ?_⟩
  rw [Mx_eq, Mx_eq, hA]
  set X := Mxz (zc (step^[j] t0)); set Y := Mxz (zc t0)
  set q : ℝ := (rd : ℝ) * 16 ^ j
  have hq : 0 < q := by positivity
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
  have h2C : (0 : ℝ) < 2 ^ nC := by positivity
  rw [show ((2 : ℝ) ^ nE / 2 ^ nC * A t0) ^ 8 * Y ^ 7 = ((2 ^ nE) ^ 8 * A t0 ^ 8 * Y ^ 7) / (2 ^ nC) ^ 8 by
    rw [div_mul_eq_mul_div, div_pow, mul_pow]; ring]
  rw [le_div_iff₀ (by positivity)]
  calc A t0 ^ 8 * X ^ 7 * (2 ^ nC) ^ 8 = A t0 ^ 8 * ((2 ^ nC) ^ 8 * X ^ 7) := by ring
    _ ≤ A t0 ^ 8 * ((2 ^ nE) ^ 8 * Y ^ 7) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = (2 ^ nE) ^ 8 * A t0 ^ 8 * Y ^ 7 := by ring

theorem Mxz_nonneg {z : Zc} (hz : ValidZ z) : 0 ≤ Mxz z := le_trans (by linarith [hz.lam]) (le_max_right _ _)
theorem Mxz_pos {z : Zc} (hz : ValidZ z) : 0 < Mxz z := lt_of_lt_of_le (by linarith [hz.lam]) (le_max_right _ _)

theorem rec_sound (b : Box) (t0 : Tri) (hs0 : sorted t0) (hn0 : nondeg t0) (hc : InCell b (zc t0)) :
    ∀ (T : RT) (W : W5) (rows : List F5) (j nE nC : Nat), chkRT b T W rows j nE nC = true →
      Inv t0 W rows j nE nC → Goal t0 := by
  intro T
  induction T using RT.rec (motive_2 := fun C => ∀ (k : Nat) (W : W5) (rows : List F5) (j nE nC : Nat),
      1 ≤ k → k ≤ 9 → chkRC b k C W rows j nE nC = true → Inv t0 W rows j nE nC →
      brC k (zc (step^[j] t0)) → zc (step (step^[j] t0)) = brM k (zc (step^[j] t0)) →
      A (step (step^[j] t0)) = alpha k * A (step^[j] t0) → Goal t0) with
  | leaf den rn rd y1 p1 y2 p2 =>
    intro W rows j nE nC h hI
    simp only [chkRT, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨hj, hrd⟩, h1⟩, h2⟩, hexp⟩ := h
    have c1 := (chk_sound b p1 _ false (zc t0) hc h1).1
    have c2 := (chk_sound b p2 _ false (zc t0) hc h2).1
    have f1 := farkas_nonneg rows (zc t0) hI.rws y1
    have f2 := farkas_nonneg rows (zc t0) hI.rws y2
    simp only [evz_add, evz_neg, evz_lin] at c1 c2
    rw [comb5_ev _ _ _ _ _ hI.trk, evz_TT] at c1
    rw [comb5_ev _ _ _ _ _ hI.trk, evz_L5] at c2
    have hv0 := validZ_of t0 hs0 hn0
    have hvj := validZ_of _ hI.srt hI.ndg
    have hden : evz (cond den TT L5) (zc t0) ≤ Mxz (zc t0) := by
      cases den <;> simp only [cond, evz_TT, evz_L5, Mxz] <;> first | exact le_max_left _ _ | exact le_max_right _ _
    have hrn : (0 : ℝ) ≤ (zN rn).val := by simp [zN, Z.val]
    have hzm : (zM rd).val = -(rd : ℝ) := by simp [zM, Z.val]
    rw [hzm] at c1 c2
    have hdenR := mul_le_mul_of_nonneg_left hden hrn
    have hzn : (zN rn).val = (rn : ℝ) := by simp [zN, Z.val]
    rw [hzn] at c1 c2 hdenR
    have hT : (rd : ℝ) * 16 ^ j * Mxz (zc (step^[j] t0)) ≤ rn * Mxz (zc t0) := by
      have eq : (rd : ℝ) * 16 ^ j * Mxz (zc (step^[j] t0)) =
          max ((rd : ℝ) * (16 ^ j * (zc (step^[j] t0)).T)) ((rd : ℝ) * (16 ^ j * (5 * (zc (step^[j] t0)).lam))) := by
        simp only [Mxz]; rw [← mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ rd), ← mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 16 ^ j)]; ring
      rw [eq]; exact max_le (by linarith) (by linarith)
    exact leaf_goal t0 hn0 hs0 j nE nC rn rd hj hrd hT hexp hI.area (Mxz_nonneg hvj) (Mxz_pos hv0)
  | node c1 c2 c3 c4 c5 c6 c7 c8 c9 ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9 =>
    intro W rows j nE nC h hI
    obtain ⟨k, hk1, hk9, hbr, hM, hA⟩ := step_branch' _ hI.srt hI.ndg
    obtain ⟨c, hcK, hcC⟩ := chkRT_node b c1 c2 c3 c4 c5 c6 c7 c8 c9 W rows j nE nC h k hk1 hk9
    interval_cases k <;> simp only [RT.child, Option.some.injEq] at hcK <;> subst hcK
    · exact ih1 1 W rows j nE nC (by norm_num) (by norm_num) hcC hI hbr hM hA
    · exact ih2 2 W rows j nE nC (by norm_num) (by norm_num) hcC hI hbr hM hA
    · exact ih3 3 W rows j nE nC (by norm_num) (by norm_num) hcC hI hbr hM hA
    · exact ih4 4 W rows j nE nC (by norm_num) (by norm_num) hcC hI hbr hM hA
    · exact ih5 5 W rows j nE nC (by norm_num) (by norm_num) hcC hI hbr hM hA
    · exact ih6 6 W rows j nE nC (by norm_num) (by norm_num) hcC hI hbr hM hA
    · exact ih7 7 W rows j nE nC (by norm_num) (by norm_num) hcC hI hbr hM hA
    · exact ih8 8 W rows j nE nC (by norm_num) (by norm_num) hcC hI hbr hM hA
    · exact ih9 9 W rows j nE nC (by norm_num) (by norm_num) hcC hI hbr hM hA
  | inf ys pr =>
    rename_i k W rows j nE nC hk1 hk9 h hI hbr _ _
    simp only [chkRC] at h
    have hneg := (chk_sound b pr _ true (zc t0) hc h).2 rfl
    have hrows : ∀ r ∈ rows ++ brRows k W, 0 ≤ evz r (zc t0) := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hI.rws r hr
      · exact brRows_nonneg k W _ _ _ (by positivity) hI.trk hbr r hr
    have := farkas_nonneg _ _ hrows ys
    simp only [evz_neg] at hneg
    linarith
  | sub t ih =>
    rename_i k W rows j nE nC hk1 hk9 h hI hbr hM hA
    simp only [chkRC] at h
    apply ih (stepW k W) (rows ++ brRows k W) (j + 1) (nE + eUp k) (nC + eDn k) h
    have e : step^[j + 1] t0 = step (step^[j] t0) := Function.iterate_succ_apply' step j t0
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e]; exact step_sorted _ hI.srt hI.ndg
    · rw [e]; exact step_nondeg _ hI.srt hI.ndg
    · rw [e, hM, pow_succ, mul_comm]; exact tracks_step k hk1 hk9 W _ _ _ hI.trk
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hI.rws r hr
      · exact brRows_nonneg k W _ _ _ (by positivity) hI.trk hbr r hr
    · rw [e, hA, hI.area, alpha_e k hk1 hk9, pow_add, pow_add]; ring

/-- a certified recovery tree at the root of cell `b` gives the recovery goal for every start state in the cell -/
theorem goal_of_chk (b : Box) (T : RT) (h : chkRT b T W5.id [] 0 0 0 = true) (t0 : Tri) (hs0 : sorted t0)
    (hn0 : nondeg t0) (hc : InCell b (zc t0)) : Goal t0 :=
  rec_sound b t0 hs0 hn0 hc T W5.id [] 0 0 0 h
    ⟨hs0, hn0, by simpa using tracks_id (zc t0), by simp, by simp⟩

end NMR


namespace NMR
open NM NMC NMS

/-! Part 4: certificates on the k-d tree of cells, and the conditional main theorem -/

inductive LC where
  | hole (x : Nat)
  | tree (t : RT)

def bdOK (b : Box) : Bool := Nat.ble b.s0 b.s1 && Nat.ble b.s1 G && Nat.ble b.p0 b.p1 && Nat.ble b.p1 G

def leafOK (b : Box) : LC → Bool
  | .hole x => chkHole b x
  | .tree t => bdOK b && chkRT b t W5.id [] 0 0 0

/-- walk the leaves, consuming one certificate per leaf -/
def walkR : KT → Box → List LC → Option (List LC)
  | .leaf _ _, b, c :: cs => cond (leafOK b c) (some cs) none
  | .leaf _ _, _, [] => none
  | .node d v _ l r, b, cs =>
    match walkR l (b.setHi d v) cs with
    | none => none
    | some cs' => walkR r (b.setLo d v) cs'

theorem walkR_ok (z : Zc) : ∀ (t : KT) (b : Box) (cs rest : List LC), walkR t b cs = some rest →
    ∃ c, leafOK (look z t b).2.2 c = true := by
  intro t
  induction t with
  | leaf n h =>
    intro b cs rest hw
    rcases cs with _ | ⟨c, cs⟩
    · simp [walkR] at hw
    · refine ⟨c, ?_⟩
      simp only [walkR] at hw
      simp only [look]
      cases hc : leafOK b c
      · rw [hc] at hw; simp at hw
      · rfl
  | node d v mx l r ihl ihr =>
    intro b cs rest hw
    simp only [walkR] at hw
    cases hl : walkR l (b.setHi d v) cs with
    | none => rw [hl] at hw; simp at hw
    | some cs' =>
      rw [hl] at hw
      simp only [look]
      split_ifs
      · exact ihl _ _ _ hl
      · exact ihr _ _ _ hw

theorem walkR_append : ∀ (t : KT) (b : Box) (cs rest extra : List LC), walkR t b cs = some rest →
    walkR t b (cs ++ extra) = some (rest ++ extra) := by
  intro t
  induction t with
  | leaf n h =>
    intro b cs rest extra hw
    rcases cs with _ | ⟨c, cs⟩
    · simp [walkR] at hw
    · cases hc : leafOK b c
      · simp [walkR, hc] at hw
      · simp only [walkR, hc, cond, Option.some.injEq] at hw
        simp only [List.cons_append, walkR, hc, cond, hw]
  | node d v mx l r ihl ihr =>
    intro b cs rest extra hw
    simp only [walkR] at hw ⊢
    cases hl : walkR l (b.setHi d v) cs with
    | none => rw [hl] at hw; simp at hw
    | some cs' =>
      rw [hl] at hw
      rw [ihl _ _ _ _ hl]
      exact ihr _ _ _ _ hw

/-- composition of chunk certificates along the k-d tree -/
theorem walkR_node (d v mx : Nat) (l r : KT) (b : Box) (cl cr : List LC)
    (hl : walkR l (b.setHi d v) cl = some []) (hr : walkR r (b.setLo d v) cr = some []) :
    walkR (.node d v mx l r) b (cl ++ cr) = some [] := by
  simp only [walkR]
  rw [walkR_append _ _ _ _ _ hl]
  simpa using hr

theorem recovery_of_cert (kt : KT) (cs : List LC) (hw : walkR kt rootBox cs = some []) :
    Recovery 169869312 := by
  intro t hs hn hfar
  have hv := validZ_of t hs hn
  have hst := strip_of_far t hs hn hfar
  set z := zc t
  set L := look z kt rootBox with hL
  have hLbox : inBox G L.2.2 z := look_mem z kt rootBox (inBox_root hv)
  obtain ⟨c, hc⟩ := walkR_ok z kt rootBox cs [] hw
  rw [← hL] at hc
  cases c with
  | hole x =>
    exact (hole_sound _ x hc z hv.lam (cons_of_box hv hLbox (strip_of_s hv hst hLbox))).elim
  | tree T =>
    simp only [leafOK, bdOK, Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hT⟩ := hc
    have hcell : InCell L.2.2 z := inCell_of hv hLbox (strip_of_s hv hst hLbox)
      ⟨le_trans h1 h2, h2, le_trans h3 h4, h4⟩
    exact goal_of_chk L.2.2 T hT t hs hn hcell

/-- the conditional main theorem: convergence follows from the certificate fact `walkR kt rootBox cs = some []` -/
theorem nm_converges_of_reccert (kt : KT) (cs : List LC) (hw : walkR kt rootBox cs = some [])
    (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :
    Filter.Tendsto (fun k => (traj t0 k).p1) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p2) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p3) Filter.atTop (nhds 0) :=
  nm_converges_of_recovery 169869312 (recovery_of_cert kt cs hw) t0 h0 hn0

end NMR

#print axioms NMR.nm_converges_of_reccert
