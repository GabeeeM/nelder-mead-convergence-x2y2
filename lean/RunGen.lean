import NMRec2
open NM NMC NMS NMR NMR2

/-! Generic neutral-word runs, part 1: pattern walks, the period map `z ↦ z + N z`, finiteness, κ-pieces and
the triangle lemmas. -/

namespace NMR3

/-- the nine branch conditions are mutually exclusive on states with `Δ2, Δ3 ≥ 0` -/
theorem brC_unique (z : Zc) (k k' : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) (hk1' : 1 ≤ k') (hk9' : k' ≤ 9)
    (h : brC k z) (h' : brC k' z) (hd2 : 0 ≤ z.d2) (hd3 : 0 ≤ z.d3) : k = k' := by
  interval_cases k <;> interval_cases k' <;>
    simp only [brC, brC1, brC2, brC3, brC4, brC5, brC6, brC7, brC8, brC9] at h h' <;>
    first | rfl | (exfalso; casesm* _ ∧ _ <;> linarith)

/-- the step taken is the branch whose conditions hold -/
theorem step_of_brC (t : Tri) (hs : sorted t) (hn : nondeg t) (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9)
    (hk : brC k (zc t)) : zc (step t) = brM k (zc t) ∧ A (step t) = alpha k * A t := by
  obtain ⟨k', hk1', hk9', hbr, hM, hA⟩ := step_branch' t hs hn
  have hz := zc_nonneg t hs
  have := brC_unique (zc t) k k' hk1 hk9 hk1' hk9' hk hbr hz.1 hz.2.1
  subst this; exact ⟨hM, hA⟩

/-! ### walks along a word -/

def walkParts : List Nat → List W5 → List W5
  | [], qs => qs
  | k :: ks, qs => walkParts ks (qs.map (stepW k))

def walkRows : List Nat → List W5 → List (List F5)
  | [], _ => []
  | k :: ks, qs => brRowsP k qs ++ walkRows ks (qs.map (stepW k))

def upC : List Nat → Nat
  | [] => 0
  | k :: ks => eUp k + upC ks
def dnC : List Nat → Nat
  | [] => 0
  | k :: ks => eDn k + dnC ks

def lettersOK : List Nat → Bool
  | [] => true
  | k :: ks => Nat.ble 1 k && Nat.ble k 9 && lettersOK ks

def letter (ks : List Nat) (i : Nat) : Nat := (nth ks i).getD 0

/-- the orbit of `t` follows the letters `ks` -/
def Follows (t : Tri) (ks : List Nat) : Prop := ∀ i < ks.length, brC (letter ks i) (zc (step^[i] t))

theorem length_walkParts : ∀ (ks : List Nat) (qs : List W5), (walkParts ks qs).length = qs.length
  | [], _ => rfl
  | k :: ks, qs => by simp only [walkParts]; rw [length_walkParts ks]; simp

theorem walk_sound : ∀ (ks : List Nat), lettersOK ks = true →
    ∀ (t : Tri) (qs : List W5) (c : Nat → ℝ) (z0 : Zc) (σ : ℝ), sorted t → nondeg t → 0 < σ →
      TrackP qs c z0 (zc t) σ → Follows t ks →
      TrackP (walkParts ks qs) c z0 (zc (step^[ks.length] t)) (16 ^ ks.length * σ) ∧
      RowsOK (walkRows ks qs) c qs.length z0 ∧
      A (step^[ks.length] t) = (2 : ℝ) ^ upC ks / 2 ^ dnC ks * A t
  | [], _, t, qs, c, z0, σ, _, _, _, htr, _ => by
    refine ⟨?_, fun row hr => by simp [walkRows] at hr, by simp [upC, dnC]⟩
    simpa [walkParts] using htr
  | k :: ks, hl, t, qs, c, z0, σ, hs, hn, hσ, htr, hf => by
    simp only [lettersOK, Bool.and_eq_true, Nat.ble_eq] at hl
    obtain ⟨⟨hk1, hk9⟩, hl'⟩ := hl
    have h0 : brC k (zc t) := by
      have := hf 0 (by simp); simpa [letter, nth] using this
    obtain ⟨hM, hA⟩ := step_of_brC t hs hn k hk1 hk9 h0
    have htr' : TrackP (qs.map (stepW k)) c z0 (zc (step t)) (16 * σ) := by
      rw [hM]; exact trackP_step k hk1 hk9 qs c z0 _ σ htr
    have hf' : Follows (step t) ks := by
      intro i hi
      have := hf (i + 1) (by simp; omega)
      simpa [letter, nth, Function.iterate_succ_apply] using this
    obtain ⟨a1, a2, a3⟩ := walk_sound ks hl' (step t) _ c z0 (16 * σ) (step_sorted t hs hn) (step_nondeg t hs hn)
      (by positivity) htr' hf'
    refine ⟨?_, ?_, ?_⟩
    · simp only [walkParts, List.length_cons, Function.iterate_succ_apply]
      rw [pow_succ, mul_assoc]; exact a1
    · simp only [walkRows]
      refine rowsOK_append (brRowsP_ok k qs c z0 _ σ hσ htr h0) ?_
      rw [List.length_map] at a2; exact a2
    · simp only [List.length_cons, Function.iterate_succ_apply, upC, dnC]
      rw [a3, hA, alpha_e k hk1 hk9, pow_add, pow_add]; ring

/-! ### the period map -/

def zToI (x : Z) : Int := (x.p : Int) - x.n
theorem val_zToI (x : Z) : x.val = (zToI x : ℝ) := by simp [Z.val, zToI]

def zIs (x : Z) (k : Int) : Bool := decide (zToI x = k)
theorem zIs_val {x : Z} {k : Int} (h : zIs x k = true) : x.val = k := by
  simp only [zIs, decide_eq_true_eq] at h; rw [val_zToI, h]

/-- the tracked full-period matrix -/
def wFull (P : List Nat) : W5 := gW (walkParts P [W5.id]) 0

/-- `W = s·I + N` with `N` mapping D into Δ only -/
def nilOK (W : W5) (s : Int) : Bool :=
  zIs W.w0.c1 s && zIs W.w0.c2 0 && zIs W.w1.c1 0 && zIs W.w1.c2 s &&
  zIs W.w2.c1 0 && zIs W.w2.c2 0 && zIs W.w2.c3 s && zIs W.w2.c4 0 && zIs W.w2.c5 0 &&
  zIs W.w3.c1 0 && zIs W.w3.c2 0 && zIs W.w3.c3 0 && zIs W.w3.c4 s && zIs W.w3.c5 0 &&
  zIs W.w4.c1 0 && zIs W.w4.c2 0 && zIs W.w4.c3 0 && zIs W.w4.c4 0 && zIs W.w4.c5 s

def nRow0 (W : W5) : F5 := ⟨zN 0, zN 0, W.w0.c3, W.w0.c4, W.w0.c5⟩
def nRow1 (W : W5) : F5 := ⟨zN 0, zN 0, W.w1.c3, W.w1.c4, W.w1.c5⟩

/-- the state after `q` periods: `z + q N z` (N given by the rows `n0, n1` scaled by `s`) -/
noncomputable def addN (n0 n1 : F5) (s : ℝ) (z : Zc) (q : ℝ) : Zc :=
  ⟨z.d2 + q * evz n0 z / s, z.d3 + q * evz n1 z / s, z.a, z.b, z.c⟩

theorem evz_nD (n : F5) (h1 : n.c1 = zN 0) (h2 : n.c2 = zN 0) (z z' : Zc) (ha : z'.a = z.a) (hb : z'.b = z.b)
    (hc : z'.c = z.c) : evz n z' = evz n z := by
  simp only [evz, F5.ev, h1, h2, ha, hb, hc, zN, Z.val]; push_cast; ring

theorem addN_addN (n0 n1 : F5) (h01 : n0.c1 = zN 0) (h02 : n0.c2 = zN 0) (h11 : n1.c1 = zN 0) (h12 : n1.c2 = zN 0)
    (s : ℝ) (z : Zc) (q : ℝ) : addN n0 n1 s (addN n0 n1 s z q) 1 = addN n0 n1 s z (q + 1) := by
  have e0 := evz_nD n0 h01 h02 z (addN n0 n1 s z q) rfl rfl rfl
  have e1 := evz_nD n1 h11 h12 z (addN n0 n1 s z q) rfl rfl rfl
  simp only [addN] at e0 e1 ⊢
  rw [e0, e1]; congr 1 <;> ring

theorem addN_zero (n0 n1 : F5) (s : ℝ) (z : Zc) : addN n0 n1 s z 0 = z := by simp [addN]

theorem trackP_id (z : Zc) : TrackP [W5.id] (fun _ => 1) z z 1 := by
  intro r hr
  have := tracks_id z r hr
  simp only [List.length_singleton, Finset.sum_range_one, one_mul] at this ⊢
  simpa [gW, nth] using this.symm

/-- one period: `zc (step^[PL] t) = z + N z` -/
theorem period_lin (P : List Nat) (hl : lettersOK P = true) (hnil : nilOK (wFull P) (16 ^ P.length) = true)
    (t : Tri) (hs : sorted t) (hn : nondeg t) (hf : Follows t P) :
    zc (step^[P.length] t) = addN (nRow0 (wFull P)) (nRow1 (wFull P)) (16 ^ P.length) (zc t) 1 ∧
      A (step^[P.length] t) = (2 : ℝ) ^ upC P / 2 ^ dnC P * A t := by
  obtain ⟨h1, -, h3⟩ := walk_sound P hl t [W5.id] (fun _ => 1) (zc t) 1 hs hn one_pos (trackP_id (zc t)) hf
  refine ⟨?_, h3⟩
  set W := wFull P
  have hw : ∀ r, r < 5 → (16 : ℝ) ^ P.length * zco (zc (step^[P.length] t)) r = evz (W.get r) (zc t) := by
    intro r hr
    have := h1 r hr
    rw [length_walkParts] at this
    simp only [List.length_singleton, Finset.sum_range_one, one_mul, mul_one] at this
    exact this
  simp only [nilOK, Bool.and_eq_true] at hnil
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩, a15⟩, a16⟩, a17⟩,
    a18⟩, a19⟩ := hnil
  have v1 := zIs_val a1; have v2 := zIs_val a2; have v3 := zIs_val a3; have v4 := zIs_val a4
  have v5 := zIs_val a5; have v6 := zIs_val a6; have v7 := zIs_val a7; have v8 := zIs_val a8
  have v9 := zIs_val a9; have v10 := zIs_val a10; have v11 := zIs_val a11; have v12 := zIs_val a12
  have v13 := zIs_val a13; have v14 := zIs_val a14; have v15 := zIs_val a15; have v16 := zIs_val a16
  have v17 := zIs_val a17; have v18 := zIs_val a18; have v19 := zIs_val a19
  have hs16 : (0 : ℝ) < 16 ^ P.length := by positivity
  have r0 := hw 0 (by norm_num); have r1 := hw 1 (by norm_num); have r2 := hw 2 (by norm_num)
  have r3 := hw 3 (by norm_num); have r4 := hw 4 (by norm_num)
  simp only [zco, W5.get, evz, F5.ev] at r0 r1 r2 r3 r4
  simp only [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19] at r0 r1 r2 r3 r4
  push_cast at r0 r1 r2 r3 r4
  generalize zc (step^[P.length] t) = w at r0 r1 r2 r3 r4 ⊢
  cases w
  simp only [addN, nRow0, nRow1, evz, F5.ev, zN, Z.val, Zc.mk.injEq] at r0 r1 r2 r3 r4 ⊢
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first | (field_simp; linarith) | exact mul_left_cancel₀ hs16.ne' (by linarith)

/-- the pattern letter at index `i` (periodic) -/
def pat (P : List Nat) (i : Nat) : Nat := letter P (i % P.length)

theorem iter_add' (t : Tri) (j n : Nat) : step^[j + n] t = step^[n] (step^[j] t) := by
  rw [add_comm, Function.iterate_add_apply]

/-- `q` periods: `z + q N z`, area unchanged when `upC P = dnC P` -/
theorem periods_lin (P : List Nat) (hP : 0 < P.length) (hl : lettersOK P = true)
    (hnil : nilOK (wFull P) (16 ^ P.length) = true) (hud : upC P = dnC P)
    (t : Tri) (hs : sorted t) (hn : nondeg t) :
    ∀ q : Nat, (∀ i < P.length * q, brC (pat P i) (zc (step^[i] t))) →
      zc (step^[P.length * q] t) = addN (nRow0 (wFull P)) (nRow1 (wFull P)) (16 ^ P.length) (zc t) q ∧
      A (step^[P.length * q] t) = A t := by
  intro q
  induction q with
  | zero => intro _; simp [addN_zero]
  | succ q ih =>
    intro hr
    obtain ⟨h1, h2⟩ := ih (fun i hi => hr i (by nlinarith))
    have si := iter_sorted t hs hn (P.length * q)
    have hf : Follows (step^[P.length * q] t) P := by
      intro i hi
      have := hr (P.length * q + i) (by nlinarith)
      rw [iter_add'] at this
      have hm : (P.length * q + i) % P.length = i := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
      simpa [pat, hm] using this
    obtain ⟨e1, e2⟩ := period_lin P hl hnil _ si.1 si.2 hf
    have e : P.length * (q + 1) = P.length * q + P.length := by ring
    refine ⟨?_, ?_⟩
    · rw [e, iter_add', e1, h1, addN_addN _ _ rfl rfl rfl rfl]; push_cast; ring_nf
    · rw [e, iter_add', e2, h2, hud]; field_simp

/-! ### the bound functional and finiteness -/

def sumF : F5 := ⟨zN 1, zN 1, zN 0, zN 0, zN 0⟩

/-- bound functional: `Δ2`, `Δ3`, `Δ2 + Δ3`, or a (signed) condition row of the first pattern branch `k` -/
def fSel (k fs : Nat) : F5 :=
  match fs with
  | 0 => unitF 0
  | 1 => unitF 1
  | 2 => sumF
  | j + 3 => match nth (brConds k) j with
    | some cn => cond cn.2 cn.1 (F5.neg cn.1)
    | none => F5.zero

theorem fSel_nonneg (k fs : Nat) (z : Zc) (hk : brC k z) (h2 : 0 ≤ z.d2) (h3 : 0 ≤ z.d3) :
    0 ≤ evz (fSel k fs) z := by
  match fs with
  | 0 => simp only [fSel]; rw [unitF_ev 0 (by norm_num)]; exact h2
  | 1 => simp only [fSel]; rw [unitF_ev 1 (by norm_num)]; exact h3
  | 2 => simp only [fSel, sumF, evz, F5.ev, zN, Z.val]; push_cast; linarith
  | j + 3 =>
    simp only [fSel]
    cases hc : nth (brConds k) j with
    | none => simp
    | some cn =>
      obtain ⟨c, need⟩ := cn
      have hb := br_conds k z hk j c need hc
      cases need with
      | true => exact hb.1 rfl
      | false => simp only [cond, evz_neg]; linarith [hb.2 rfl]

/-- `ℓ = −F∘N` and `hN = −b N₂ + a N₃` (scaled by `s`), `(a, b)` the Δ-part of `F` -/
def ellR (F n0 n1 : F5) : F5 := F5.neg (F5.add (F5.smul F.c1 n0) (F5.smul F.c2 n1))
def hnR (F n0 n1 : F5) : F5 := F5.add (F5.smul (Z.neg F.c2) n0) (F5.smul F.c1 n1)

theorem evz_F_addN (F n0 n1 : F5) (s : ℝ) (hs : 0 < s) (z : Zc) (q : ℝ) :
    evz F (addN n0 n1 s z q) = evz F z - q * evz (ellR F n0 n1) z / s := by
  simp only [addN, ellR, evz_neg, evz_add, evz_smul]
  simp only [evz, F5.ev]; field_simp; ring

theorem run_finite_gen (P : List Nat) (hP : 0 < P.length) (hl : lettersOK P = true)
    (hnil : nilOK (wFull P) (16 ^ P.length) = true) (hud : upC P = dnC P) (fs : Nat)
    (t : Tri) (hs : sorted t) (hn : nondeg t)
    (hpos : 0 < evz (ellR (fSel (letter P 0) fs) (nRow0 (wFull P)) (nRow1 (wFull P))) (zc t)) :
    ∃ n, ¬ brC (pat P n) (zc (step^[n] t)) := by
  by_contra hall
  push_neg at hall
  set F := fSel (letter P 0) fs
  set n0 := nRow0 (wFull P); set n1 := nRow1 (wFull P)
  set s : ℝ := 16 ^ P.length
  have hs0 : 0 < s := by positivity
  set L := evz (ellR F n0 n1) (zc t)
  obtain ⟨q, hq⟩ := exists_nat_gt (evz F (zc t) * s / L)
  obtain ⟨h1, -⟩ := periods_lin P hP hl hnil hud t hs hn q (fun i _ => hall i)
  have hb := hall (P.length * q)
  have hm : P.length * q % P.length = 0 := Nat.mul_mod_right _ _
  simp only [pat, hm] at hb
  rw [h1] at hb
  have hz := zc_nonneg _ (iter_sorted t hs hn (P.length * q)).1
  rw [h1] at hz
  have hF := fSel_nonneg (letter P 0) fs _ hb hz.1 hz.2.1
  rw [evz_F_addN F n0 n1 s hs0] at hF
  rw [div_lt_iff₀ hpos] at hq
  have : (q : ℝ) * L / s ≤ evz F (zc t) := by linarith
  rw [div_le_iff₀ hs0] at this
  linarith

/-! ### κ-pieces of `κ = hN/ℓ` -/

def loG (j : Nat) (l h : F5) : F5 := F5.add (F5.smul (zN (kq j).2) h) (F5.smul (zI (-(kq j).1)) l)
def hiG (j : Nat) (l h : F5) : F5 := F5.add (F5.smul (zI (kq j).1) l) (F5.smul (zM (kq j).2) h)
def pieceRowsG (i : Nat) (l h : F5) : List F5 :=
  (if 1 ≤ i then [loG (i - 1) l h] else []) ++ (if i ≤ 24 then [hiG i l h] else [])

theorem evz_loG (j : Nat) (l h : F5) (z : Zc) :
    evz (loG j l h) z = ((kq j).2 : ℝ) * evz h z - ((kq j).1 : ℝ) * evz l z := by
  simp only [loG, evz_add, evz_smul, zI_val, zN_val]; push_cast; ring
theorem evz_hiG (j : Nat) (l h : F5) (z : Zc) :
    evz (hiG j l h) z = ((kq j).1 : ℝ) * evz l z - ((kq j).2 : ℝ) * evz h z := by
  simp only [hiG, evz_add, evz_smul, zI_val]; simp [zM, Z.val]; ring

theorem piece_coverG (l h : F5) (z : Zc) : ∃ i, i ≤ 25 ∧ ∀ f ∈ pieceRowsG i l h, 0 ≤ evz f z := by
  classical
  by_cases hex : ∃ j, j ≤ 24 ∧ 0 ≤ ((kq j).1 : ℝ) * evz l z - ((kq j).2 : ℝ) * evz h z
  · let i := Nat.find hex
    have hi := Nat.find_spec hex
    have hmin := fun j (hj : j < i) => Nat.find_min hex hj
    refine ⟨i, by omega, ?_⟩
    intro f hf
    simp only [pieceRowsG, List.mem_append] at hf
    rcases hf with hf | hf
    · split_ifs at hf with h1
      · simp only [List.mem_singleton] at hf; subst hf
        rw [evz_loG]
        have := hmin (i - 1) (by omega)
        push_neg at this
        have := this (by omega)
        linarith
      · simp at hf
    · split_ifs at hf with h2
      · simp only [List.mem_singleton] at hf; subst hf; rw [evz_hiG]; exact hi.2
      · simp at hf
  · push_neg at hex
    refine ⟨25, le_refl _, ?_⟩
    intro f hf
    simp only [pieceRowsG, List.mem_append] at hf
    rcases hf with hf | hf
    · simp only [show (1 : Nat) ≤ 25 from by norm_num, if_true, List.mem_singleton] at hf
      subst hf; rw [evz_loG]; have := hex 24 (le_refl _)
      simp only [show 25 - 1 = 24 from rfl] at *; linarith
    · simp at hf

/-! ### triangles in the `(ρ, τ)` plane -/

theorem tri2_fin (ρ τ G p1 q1 p2 q2 : ℝ) (hq1 : 0 < q1) (hq2 : 0 < q2) (hlt : p1 * q2 < p2 * q1)
    (hρ : 0 ≤ ρ) (hG : ρ ≤ G) (h1 : p1 * ρ ≤ q1 * τ) (h2 : q2 * τ ≤ p2 * ρ) :
    ∃ l0 l1 l2 : ℝ, 0 ≤ l0 ∧ 0 ≤ l1 ∧ 0 ≤ l2 ∧ l0 + l1 + l2 = 1 ∧ ρ = (l1 + l2) * G ∧
      q1 * q2 * τ = (l1 * q2 * p1 + l2 * q1 * p2) * G := by
  rcases eq_or_lt_of_le (le_trans hρ hG) with h0 | h0
  · have hρ0 : ρ = 0 := by linarith
    subst hρ0
    have : τ = 0 := by
      have a1 : 0 ≤ q1 * τ := by linarith
      have a2 : q2 * τ ≤ 0 := by linarith
      have b1 : 0 ≤ τ := by
        by_contra hc; push_neg at hc; nlinarith
      have b2 : τ ≤ 0 := by
        by_contra hc; push_neg at hc; nlinarith
      linarith
    subst this
    exact ⟨1, 0, 0, by norm_num, le_refl _, le_refl _, by norm_num, by rw [← h0]; ring, by rw [← h0]; ring⟩
  · set Dk := p2 * q1 - p1 * q2
    have hD : 0 < Dk := by simp only [Dk]; linarith
    refine ⟨1 - ρ / G, q1 * (p2 * ρ - q2 * τ) / (G * Dk), q2 * (q1 * τ - p1 * ρ) / (G * Dk), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sub_nonneg, div_le_one h0]; exact hG
    · apply div_nonneg (mul_nonneg hq1.le (by linarith)) (by positivity)
    · apply div_nonneg (mul_nonneg hq2.le (by linarith)) (by positivity)
    · field_simp; ring
    · field_simp; ring
    · field_simp; ring

theorem tri2_lo (ρ τ X a b p q : ℝ) (ha : 0 < a) (hq : 0 < q) (hD : 0 < q * b - a * p)
    (hρ : 0 ≤ ρ) (hpq : q * τ ≤ p * ρ) (hX : 0 ≤ X + a * τ - b * ρ) :
    ∃ l0 l1 l2 : ℝ, 0 ≤ l0 ∧ 0 ≤ l1 ∧ 0 ≤ l2 ∧ l0 + l1 + l2 = 1 ∧
      a * (q * b - a * p) * ρ = l2 * (a * q * X) ∧
      a * (q * b - a * p) * τ = l1 * (-(q * b - a * p) * X) + l2 * (a * p * X) := by
  set D := q * b - a * p
  have hXρ : ρ * D ≤ q * X := by
    have : a * (q * τ) ≤ a * (p * ρ) := mul_le_mul_of_nonneg_left hpq ha.le
    simp only [D]; nlinarith
  have hX0 : 0 ≤ X := by
    have : 0 ≤ ρ * D := mul_nonneg hρ hD.le
    nlinarith
  rcases eq_or_lt_of_le hX0 with h0 | h0
  · subst h0
    have hρ0 : ρ = 0 := by
      have : ρ * D ≤ 0 := by nlinarith
      have : ρ * D = 0 := le_antisymm this (mul_nonneg hρ hD.le)
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (ne_of_gt hD)
    subst hρ0
    have : τ = 0 := by
      have b1 : 0 ≤ τ := by
        by_contra hc; push_neg at hc; nlinarith
      have b2 : τ ≤ 0 := by
        by_contra hc; push_neg at hc; nlinarith
      linarith
    subst this
    exact ⟨1, 0, 0, by norm_num, le_refl _, le_refl _, by norm_num, by ring, by ring⟩
  · refine ⟨(X + a * τ - b * ρ) / X, a * (p * ρ - q * τ) / (q * X), D * ρ / (q * X), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact div_nonneg hX h0.le
    · apply div_nonneg (mul_nonneg ha.le (by linarith)) (by positivity)
    · apply div_nonneg (mul_nonneg hD.le hρ) (by positivity)
    · have hD' : D = q * b - a * p := rfl; field_simp; (try rw [hD']); ring
    · field_simp
    · have hD' : D = q * b - a * p := rfl; field_simp; (try rw [hD']); ring

theorem tri2_up (ρ τ Y a b p q : ℝ) (hb : 0 < b) (hq : 0 < q) (hD : 0 < a * q + b * p)
    (hρ : 0 ≤ ρ) (hpq : p * ρ ≤ q * τ) (hY : 0 ≤ Y - a * ρ - b * τ) :
    ∃ l0 l1 l2 : ℝ, 0 ≤ l0 ∧ 0 ≤ l1 ∧ 0 ≤ l2 ∧ l0 + l1 + l2 = 1 ∧
      b * (a * q + b * p) * ρ = l2 * (b * q * Y) ∧
      b * (a * q + b * p) * τ = l1 * ((a * q + b * p) * Y) + l2 * (b * p * Y) := by
  set D := a * q + b * p
  have hYρ : ρ * D ≤ q * Y := by
    have : b * (p * ρ) ≤ b * (q * τ) := mul_le_mul_of_nonneg_left hpq hb.le
    simp only [D]; nlinarith
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ ρ * D := mul_nonneg hρ hD.le
    nlinarith
  rcases eq_or_lt_of_le hY0 with h0 | h0
  · subst h0
    have hρ0 : ρ = 0 := by
      have : ρ * D ≤ 0 := by nlinarith
      have : ρ * D = 0 := le_antisymm this (mul_nonneg hρ hD.le)
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (ne_of_gt hD)
    subst hρ0
    have : τ = 0 := by
      have b1 : 0 ≤ τ := by
        by_contra hc; push_neg at hc; nlinarith
      have b2 : τ ≤ 0 := by
        by_contra hc; push_neg at hc; nlinarith
      linarith
    subst this
    exact ⟨1, 0, 0, by norm_num, le_refl _, le_refl _, by norm_num, by ring, by ring⟩
  · refine ⟨(Y - a * ρ - b * τ) / Y, b * (q * τ - p * ρ) / (q * Y), D * ρ / (q * Y), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact div_nonneg hY h0.le
    · apply div_nonneg (mul_nonneg hb.le (by linarith)) (by positivity)
    · apply div_nonneg (mul_nonneg hD.le hρ) (by positivity)
    · have hD' : D = a * q + b * p := rfl; field_simp; (try rw [hD']); ring
    · field_simp
    · have hD' : D = a * q + b * p := rfl; field_simp; (try rw [hD']); ring

/-! ### vertex maps of the pieces -/

def unitSF (S : Int) (r : Nat) : F5 := F5.smul (zI S) (unitF r)
/-- `S·I` plus `(x, y)·G` in the Δ rows -/
def mkR (S x y : Int) (G : F5) : W5 :=
  ⟨F5.add (unitSF S 0) (F5.smul (zI x) G), F5.add (unitSF S 1) (F5.smul (zI y) G), unitSF S 2, unitSF S 3, unitSF S 4⟩

theorem evalE_mkR (S x y : Int) (G : F5) (z : Zc) :
    evalE (mkR S x y G) z = ⟨S * z.d2 + x * evz G z, S * z.d3 + y * evz G z, S * z.a, S * z.b, S * z.c⟩ := by
  simp only [evalE, mkR, unitSF, evz_add, evz_smul, zI_val]
  rw [unitF_ev 0 (by norm_num), unitF_ev 1 (by norm_num), unitF_ev 2 (by norm_num), unitF_ev 3 (by norm_num),
    unitF_ev 4 (by norm_num)]
  simp only [zco]

def gA (a b p q : Int) : Int × Int := (-q * a - p * b, -q * b + p * a)

def gS (a b : Int) (i : Nat) : Int :=
  if i = 0 then a * (((kq 0).2 : Int) * b - a * (kq 0).1)
  else if i < 25 then ((kq (i - 1)).2 : Int) * ((kq i).2 : Int) * (a * a + b * b)
  else b * (a * ((kq 24).2 : Int) + b * (kq 24).1)

def gV (a b : Int) (i e : Nat) : Int × Int :=
  if e = 0 then (0, 0)
  else if i = 0 then
    (let D := ((kq 0).2 : Int) * b - a * (kq 0).1
     if e = 1 then (D * b, -D * a)
     else (a * (gA a b (kq 0).1 (kq 0).2).1, a * (gA a b (kq 0).1 (kq 0).2).2))
  else if i < 25 then
    (if e = 1 then (((kq i).2 : Int) * (gA a b (kq (i - 1)).1 (kq (i - 1)).2).1,
                    ((kq i).2 : Int) * (gA a b (kq (i - 1)).1 (kq (i - 1)).2).2)
     else (((kq (i - 1)).2 : Int) * (gA a b (kq i).1 (kq i).2).1, ((kq (i - 1)).2 : Int) * (gA a b (kq i).1 (kq i).2).2))
  else
    (let D := a * ((kq 24).2 : Int) + b * (kq 24).1
     if e = 1 then (-D * b, D * a)
     else (b * (gA a b (kq 24).1 (kq 24).2).1, b * (gA a b (kq 24).1 (kq 24).2).2))

def gG (F : F5) (i : Nat) : F5 := if i = 0 then unitF 1 else if i < 25 then F else unitF 0

def gE (a b : Int) (F : F5) (i e : Nat) : W5 := mkR (gS a b i) (gV a b i e).1 (gV a b i e).2 (gG F i)

/-- the infinite pieces are bounded only under sign conditions -/
def gBnd (a b : Int) (i : Nat) : Bool :=
  if i = 0 then decide (0 < a) && decide (0 < ((kq 0).2 : Int) * b - a * (kq 0).1)
  else if i < 25 then true
  else decide (0 < b) && decide (0 < a * ((kq 24).2 : Int) + b * (kq 24).1)

theorem gS_pos (a b : Int) (i : Nat) (hi : i ≤ 25) (hb : gBnd a b i = true) (hW : 0 < a * a + b * b) :
    0 < gS a b i := by
  unfold gS
  unfold gBnd at hb
  split_ifs at hb ⊢ with h0 h25
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb; exact mul_pos hb.1 hb.2
  · have h1 := kq_q_pos (i - 1) (by omega); have h2 := kq_q_pos i (by omega)
    have : (0 : Int) < (kq (i - 1)).2 := by exact_mod_cast h1
    have : (0 : Int) < (kq i).2 := by exact_mod_cast h2
    positivity
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb; exact mul_pos hb.1 hb.2

/-- the exit `u = z + (−ρ(a,b) + τ(−b,a))/W` lies in the piece triangle -/
theorem piece_triG (a b : Int) (F : F5) (z u : Zc) (ρ τ : ℝ) (i : Nat) (hi : i ≤ 25) (hbnd : gBnd a b i = true)
    (hW : 0 < a * a + b * b)
    (h2 : ((a * a + b * b : Int) : ℝ) * (u.d2 - z.d2) = -(a : ℝ) * ρ - (b : ℝ) * τ)
    (h3 : ((a * a + b * b : Int) : ℝ) * (u.d3 - z.d3) = -(b : ℝ) * ρ + (a : ℝ) * τ)
    (ha : u.a = z.a) (hb : u.b = z.b) (hc : u.c = z.c) (hρ : 0 ≤ ρ) (hF : ρ ≤ evz F z)
    (hlo : 1 ≤ i → ((kq (i - 1)).1 : ℝ) * ρ ≤ ((kq (i - 1)).2 : ℝ) * τ)
    (hhi : i ≤ 24 → ((kq i).2 : ℝ) * τ ≤ ((kq i).1 : ℝ) * ρ) (hu2 : 0 ≤ u.d2) (hu3 : 0 ≤ u.d3) :
    Tri3 (gS a b i) u (evalE (gE a b F i 0) z) (evalE (gE a b F i 1) z) (evalE (gE a b F i 2) z) := by
  have hWR : (0 : ℝ) < ((a * a + b * b : Int) : ℝ) := by exact_mod_cast hW
  set W : ℝ := ((a * a + b * b : Int) : ℝ) with hWdef
  have hWe : W = (a : ℝ) * a + (b : ℝ) * b := by simp only [hWdef]; push_cast; ring
  simp only [gE, evalE_mkR]
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · -- lower piece
    subst h0
    simp only [gBnd, if_pos, Bool.and_eq_true, decide_eq_true_eq] at hbnd
    obtain ⟨hapos, hDpos⟩ := hbnd
    set p : ℝ := ((kq 0).1 : ℝ) with hpd; set q : ℝ := ((kq 0).2 : ℝ) with hqd
    have hq : 0 < q := by simp only [q]; exact_mod_cast kq_q_pos 0 (by norm_num)
    have haR : (0 : ℝ) < a := by exact_mod_cast hapos
    have hDR : 0 < q * b - a * p := by simp only [p, q]; exact_mod_cast hDpos
    have hpq := hhi (by norm_num)
    have hX : 0 ≤ W * z.d3 + a * τ - b * ρ := by nlinarith
    obtain ⟨l0, l1, l2, hl0, hl1, hl2, hsum, eρ, eτ⟩ := tri2_lo ρ τ (W * z.d3) a b p q haR hq hDR hρ hpq hX
    refine ⟨l0, l1, l2, hl0, hl1, hl2, hsum, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [gS, gV, gG, gA, if_pos, show (1 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 0 from by norm_num,
      show (2 : Nat) ≠ 1 from by norm_num, if_false, if_true, ite_true, ite_false]
    all_goals (try rw [unitF_ev 1 (by norm_num)])
    all_goals (try simp only [zco]); push_cast; (try simp only [← hpd, ← hqd])
    · apply mul_left_cancel₀ hWR.ne'
      linear_combination (↑a * (q * ↑b - ↑a * p)) * h2 - (W * (↑a * (q * ↑b - ↑a * p)) * z.d2) * hsum + (-(a : ℝ)) * eρ + (-(b : ℝ)) * eτ
    · apply mul_left_cancel₀ hWR.ne'
      linear_combination (↑a * (q * ↑b - ↑a * p)) * h3 - (W * (↑a * (q * ↑b - ↑a * p)) * z.d3) * hsum + (-(b : ℝ)) * eρ + (a : ℝ) * eτ
    · rw [ha]; linear_combination (-(↑a * (q * ↑b - ↑a * p)) * z.a) * hsum
    · rw [hb]; linear_combination (-(↑a * (q * ↑b - ↑a * p)) * z.b) * hsum
    · rw [hc]; linear_combination (-(↑a * (q * ↑b - ↑a * p)) * z.c) * hsum
  · rcases lt_or_eq_of_le hi with hlt25 | h25
    · -- finite piece
      have hne : i ≠ 0 := by omega
      set p1 : ℝ := ((kq (i - 1)).1 : ℝ) with hp1d; set q1 : ℝ := ((kq (i - 1)).2 : ℝ) with hq1d
      set p2 : ℝ := ((kq i).1 : ℝ) with hp2d; set q2 : ℝ := ((kq i).2 : ℝ) with hq2d
      have hq1 : 0 < q1 := by simp only [q1]; exact_mod_cast kq_q_pos (i - 1) (by omega)
      have hq2 : 0 < q2 := by simp only [q2]; exact_mod_cast kq_q_pos i (by omega)
      have hinc := KQ_incr (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at hinc
      have hlt : p1 * q2 < p2 * q1 := by simp only [p1, q1, p2, q2]; exact_mod_cast hinc
      obtain ⟨l0, l1, l2, hl0, hl1, hl2, hsum, eρ, eτ⟩ :=
        tri2_fin ρ τ (evz F z) p1 q1 p2 q2 hq1 hq2 hlt hρ hF (hlo (by omega)) (hhi (by omega))
      refine ⟨l0, l1, l2, hl0, hl1, hl2, hsum, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp only [gS, gV, gG, gA, if_neg hne, if_pos hlt25, show (1 : Nat) ≠ 0 from by norm_num,
        show (2 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 1 from by norm_num, if_false, if_true]
      all_goals push_cast; (try simp only [← hp1d, ← hq1d, ← hp2d, ← hq2d])
      · apply mul_left_cancel₀ hWR.ne'
        rw [hWe] at h2 ⊢
        linear_combination (q1 * q2 * (↑a * ↑a + ↑b * ↑b)) * h2 - ((↑a * ↑a + ↑b * ↑b) * (q1 * q2 * (↑a * ↑a + ↑b * ↑b)) * z.d2) * hsum + (-(a : ℝ) * q1 * q2 * (↑a * ↑a + ↑b * ↑b)) * eρ + (-(b : ℝ) * (↑a * ↑a + ↑b * ↑b)) * eτ
      · apply mul_left_cancel₀ hWR.ne'
        rw [hWe] at h3 ⊢
        linear_combination (q1 * q2 * (↑a * ↑a + ↑b * ↑b)) * h3 - ((↑a * ↑a + ↑b * ↑b) * (q1 * q2 * (↑a * ↑a + ↑b * ↑b)) * z.d3) * hsum + (-(b : ℝ) * q1 * q2 * (↑a * ↑a + ↑b * ↑b)) * eρ + ((a : ℝ) * (↑a * ↑a + ↑b * ↑b)) * eτ
      · rw [ha]; linear_combination (-(q1 * q2 * (↑a * ↑a + ↑b * ↑b)) * z.a) * hsum
      · rw [hb]; linear_combination (-(q1 * q2 * (↑a * ↑a + ↑b * ↑b)) * z.b) * hsum
      · rw [hc]; linear_combination (-(q1 * q2 * (↑a * ↑a + ↑b * ↑b)) * z.c) * hsum
    · -- upper piece
      subst h25
      simp only [gBnd, show (25 : Nat) ≠ 0 from by norm_num, show ¬ (25 : Nat) < 25 from by norm_num, if_false,
        Bool.and_eq_true, decide_eq_true_eq] at hbnd
      obtain ⟨hbpos, hDpos⟩ := hbnd
      set p : ℝ := ((kq 24).1 : ℝ) with hpd; set q : ℝ := ((kq 24).2 : ℝ) with hqd
      have hq : 0 < q := by simp only [q]; exact_mod_cast kq_q_pos 24 (by norm_num)
      have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
      have hDR : 0 < a * q + b * p := by simp only [p, q]; exact_mod_cast hDpos
      have hpq := hlo (by norm_num)
      try simp only [show 25 - 1 = 24 from rfl] at hpq
      have hY : 0 ≤ W * z.d2 - a * ρ - b * τ := by nlinarith
      obtain ⟨l0, l1, l2, hl0, hl1, hl2, hsum, eρ, eτ⟩ := tri2_up ρ τ (W * z.d2) a b p q hbR hq hDR hρ hpq hY
      refine ⟨l0, l1, l2, hl0, hl1, hl2, hsum, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp only [gS, gV, gG, gA, show (25 : Nat) ≠ 0 from by norm_num, show ¬ (25 : Nat) < 25 from by norm_num,
        show (1 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 1 from by norm_num,
        if_false, if_true]
      all_goals (try rw [unitF_ev 0 (by norm_num)])
      all_goals (try simp only [zco]); push_cast; (try simp only [← hpd, ← hqd])
      · apply mul_left_cancel₀ hWR.ne'
        linear_combination (↑b * (↑a * q + ↑b * p)) * h2 - (W * (↑b * (↑a * q + ↑b * p)) * z.d2) * hsum + (-(a : ℝ)) * eρ + (-(b : ℝ)) * eτ
      · apply mul_left_cancel₀ hWR.ne'
        linear_combination (↑b * (↑a * q + ↑b * p)) * h3 - (W * (↑b * (↑a * q + ↑b * p)) * z.d3) * hsum + (-(b : ℝ)) * eρ + (a : ℝ) * eτ
      · rw [ha]; linear_combination (-(↑b * (↑a * q + ↑b * p)) * z.a) * hsum
      · rw [hb]; linear_combination (-(↑b * (↑a * q + ↑b * p)) * z.b) * hsum
      · rw [hc]; linear_combination (-(↑b * (↑a * q + ↑b * p)) * z.c) * hsum

end NMR3
