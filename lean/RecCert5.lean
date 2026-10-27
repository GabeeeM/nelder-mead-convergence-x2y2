import NMRunExit
open NM NMC NMS NMR NMR2

/-! Recovery trees with symbolic Rx runs (as in `RecCert2`) and generic neutral-word runs (`grun`), kernel-efficient
format: rows stored newest-first with their count (`RS`), Farkas multiplier lists and pair codes packed into natural
numbers, Farkas sums with direct row lookup. -/

namespace NMR3

/-! ### compact certificate primitives -/

/-- pair code of part `p`, packed in base 64 -/
def gD (code p : Nat) : Nat := code / 64 ^ p % 64

/-- Farkas combination with direct row lookup -/
def farkasQ (rows : List (List F5)) : List (Nat × Nat) → Nat → F5
  | [], _ => F5.zero
  | (i, y) :: ys, p => F5.add (F5.smul (zN y) (gF ((nth rows i).getD []) p)) (farkasQ rows ys p)

theorem farkasQ_eq (rows : List (List F5)) : ∀ (ys : List (Nat × Nat)) (p : Nat), farkasQ rows ys p = farkasP rows ys p
  | [], _ => rfl
  | (i, y) :: ys, p => by
    simp only [farkasQ, farkasP, farkas] at *
    rw [show farkas (List.map (fun r => gF r p) rows) ys = farkasP rows ys p from rfl, ← farkasQ_eq rows ys p]
    congr 2
    rw [getR_map]
    cases nth rows i with
    | none => simp [gF, nth]
    | some r => simp

def leafFQ (den : Bool) (rn rd : Nat) (fn : F5) (W : W5) (rows : List (List F5)) (ys : List (Nat × Nat)) (p : Nat) : F5 :=
  F5.add (F5.lin (zN rn) (cond den TT L5) (zM rd) (comb5 fn W)) (F5.neg (farkasQ rows ys p))

theorem leafFQ_eq (den : Bool) (rn rd : Nat) (fn : F5) (W : W5) (rows : List (List F5)) (ys : List (Nat × Nat)) (p : Nat) :
    leafFQ den rn rd fn W rows ys p = leafF den rn rd fn W rows ys p := by
  simp only [leafFQ, leafF, farkasQ_eq]

theorem leaf_boundQ (b : Box) (t0 : Tri) (hc : InCell b (zc t0)) (ps : List W5) (rows : List (List F5)) (c : Nat → ℝ)
    (z : Zc) (σ : ℝ) (hc0 : ∀ p < ps.length, 0 ≤ c p) (hc1 : ∑ p ∈ Finset.range ps.length, c p = 1)
    (htr : TrackP ps c (zc t0) z σ) (hrw : RowsOK rows c ps.length (zc t0)) (den : Bool) (rn rd : Nat)
    (fn : F5) (y : List (Nat × Nat)) (code : Nat)
    (h : allP ps.length (fun p => chk b (gD code p) (leafFQ den rn rd fn (gW ps p) rows y p) false) = true) :
    (rd : ℝ) * (σ * evz fn z) ≤ rn * evz (cond den TT L5) (zc t0) := by
  have hp := allP_spec h
  have hpos : ∀ p < ps.length, 0 ≤ evz (leafF den rn rd fn (gW ps p) rows y p) (zc t0) := by
    intro p hpl; have := (chk_sound b _ _ false (zc t0) hc (hp p hpl)).1; rwa [leafFQ_eq] at this
  have hs : 0 ≤ ∑ p ∈ Finset.range ps.length, c p * evz (leafF den rn rd fn (gW ps p) rows y p) (zc t0) :=
    Finset.sum_nonneg (fun p hpm => mul_nonneg (hc0 p (Finset.mem_range.mp hpm)) (hpos p (Finset.mem_range.mp hpm)))
  have e : ∀ p, evz (leafF den rn rd fn (gW ps p) rows y p) (zc t0) =
      (rn : ℝ) * evz (cond den TT L5) (zc t0) - rd * evz (comb5 fn (gW ps p)) (zc t0) - evz (farkasP rows y p) (zc t0) := by
    intro p; simp only [leafF, evz_add, evz_neg, evz_lin, zN_val]; simp [zM, Z.val]; ring
  have hf := farkasP_nonneg rows c ps.length (zc t0) hc0 hrw y
  simp only [e, mul_sub, Finset.sum_sub_distrib] at hs
  have h1 : ∑ p ∈ Finset.range ps.length, c p * ((rn : ℝ) * evz (cond den TT L5) (zc t0)) =
      (rn : ℝ) * evz (cond den TT L5) (zc t0) := by rw [← Finset.sum_mul, hc1, one_mul]
  have h2 : ∑ p ∈ Finset.range ps.length, c p * ((rd : ℝ) * evz (comb5 fn (gW ps p)) (zc t0)) =
      (rd : ℝ) * (σ * evz fn z) := by
    rw [← comb_trackP ps c (zc t0) z σ htr fn, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [h1, h2] at hs; linarith

theorem inf_falseQ (b : Box) (t0 : Tri) (hc : InCell b (zc t0)) (ps : List W5) (rows : List (List F5)) (c : Nat → ℝ)
    (hc0 : ∀ p < ps.length, 0 ≤ c p) (hc1 : ∑ p ∈ Finset.range ps.length, c p = 1) (hrw : RowsOK rows c ps.length (zc t0))
    (ys : List (Nat × Nat)) (code : Nat)
    (h : allP ps.length (fun p => chk b (gD code p) (F5.neg (farkasQ rows ys p)) true) = true) : False := by
  have hp := allP_spec h
  have hneg : ∀ p < ps.length, evz (farkasP rows ys p) (zc t0) < 0 := by
    intro p hpl; have := (chk_sound b _ _ true (zc t0) hc (hp p hpl)).2 rfl
    rw [farkasQ_eq] at this; simp only [evz_neg] at this; linarith
  have h1 := wsum_neg ps.length c (fun p => evz (farkasP rows ys p) (zc t0)) hc0 hc1 hneg
  have h2 := farkasP_nonneg rows c ps.length (zc t0) hc0 hrw ys
  linarith

/-! ### row stores (newest first) and packed multipliers -/

structure RS where
  l : List (List F5)
  n : Nat

/-- the rows in forward order (the denotation used by the soundness proof) -/
def fw (r : RS) : List (List F5) := r.l.reverse

def rsPush (r : RS) (x : List (List F5)) : RS := ⟨x.reverse ++ r.l, r.n + x.length⟩
def rsMapPush (r : RS) (f : List F5 → List F5) (x : List (List F5)) : RS := ⟨x.reverse ++ r.l.map f, r.n + x.length⟩

theorem fw_push (r : RS) (x : List (List F5)) : fw (rsPush r x) = fw r ++ x := by
  simp [fw, rsPush, List.reverse_append]
theorem rowsOK_push {r : RS} {x : List (List F5)} {c : Nat → ℝ} {n : Nat} {z0 : Zc}
    (h1 : RowsOK (fw r) c n z0) (h2 : RowsOK x c n z0) : RowsOK (fw (rsPush r x)) c n z0 := by
  rw [fw_push]; exact rowsOK_append h1 h2
theorem fw_mapPush (r : RS) (f : List F5 → List F5) (x : List (List F5)) :
    fw (rsMapPush r f x) = (fw r).map f ++ x := by
  simp [fw, rsMapPush, List.reverse_append, List.map_reverse]
theorem mem_fw (r : RS) (x : List F5) : x ∈ fw r ↔ x ∈ r.l := by simp [fw]

/-- packed multiplier list: `m` entries `e = i + 2^20·y`, base `B` -/
structure PY where
  m : Nat
  B : Nat
  c : Nat

def decY : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | m + 1, B, c => (c % B % 1048576, c % B / 1048576) :: decY m B (c / B)

def pyL (y : PY) : List (Nat × Nat) := decY y.m y.B y.c

/-- Farkas combination: forward row index `i` is position `n − 1 − i` of the newest-first store -/
def farkasR (rows : RS) : List (Nat × Nat) → Nat → F5
  | [], _ => F5.zero
  | (i, y) :: ys, p => F5.add (F5.smul (zN y) (gF ((nth rows.l (rows.n - 1 - i)).getD []) p)) (farkasR rows ys p)

theorem farkasR_nonneg (rows : RS) (c : Nat → ℝ) (n : Nat) (z0 : Zc) (hr : RowsOK (fw rows) c n z0) :
    ∀ ys, 0 ≤ ∑ p ∈ Finset.range n, c p * evz (farkasR rows ys p) z0
  | [] => by simp [farkasR]
  | (i, y) :: ys => by
    have ih := farkasR_nonneg rows c n z0 hr ys
    have e : ∀ p, evz (farkasR rows ((i, y) :: ys) p) z0 =
        (zN y).val * evz (gF ((nth rows.l (rows.n - 1 - i)).getD []) p) z0 + evz (farkasR rows ys p) z0 := by
      intro p; simp only [farkasR, evz_add, evz_smul]
    simp only [e, mul_add, Finset.sum_add_distrib]
    have hy : (0 : ℝ) ≤ (zN y).val := by simp [zN, Z.val]
    have hrow : 0 ≤ ∑ p ∈ Finset.range n, c p * ((zN y).val * evz (gF ((nth rows.l (rows.n - 1 - i)).getD []) p) z0) := by
      cases hn : nth rows.l (rows.n - 1 - i) with
      | none => simp [gF, nth]
      | some row =>
        have := hr row ((mem_fw rows row).mpr (nth_mem _ _ row hn))
        simp only [Option.getD_some]
        have e2 : ∑ p ∈ Finset.range n, c p * ((zN y).val * evz (gF row p) z0) =
            (zN y).val * ∑ p ∈ Finset.range n, c p * evz (gF row p) z0 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
        rw [e2]; exact mul_nonneg hy this
    linarith

def leafFR (den : Bool) (rn rd : Nat) (fn : F5) (W : W5) (rows : RS) (ys : List (Nat × Nat)) (p : Nat) : F5 :=
  F5.add (F5.lin (zN rn) (cond den TT L5) (zM rd) (comb5 fn W)) (F5.neg (farkasR rows ys p))

theorem leaf_boundR (b : Box) (t0 : Tri) (hc : InCell b (zc t0)) (ps : List W5) (rows : RS) (c : Nat → ℝ)
    (z : Zc) (σ : ℝ) (hc0 : ∀ p < ps.length, 0 ≤ c p) (hc1 : ∑ p ∈ Finset.range ps.length, c p = 1)
    (htr : TrackP ps c (zc t0) z σ) (hrw : RowsOK (fw rows) c ps.length (zc t0)) (den : Bool) (rn rd : Nat)
    (fn : F5) (y : List (Nat × Nat)) (code : Nat)
    (h : allP ps.length (fun p => chk b (gD code p) (leafFR den rn rd fn (gW ps p) rows y p) false) = true) :
    (rd : ℝ) * (σ * evz fn z) ≤ rn * evz (cond den TT L5) (zc t0) := by
  have hp := allP_spec h
  have hpos : ∀ p < ps.length, 0 ≤ evz (leafFR den rn rd fn (gW ps p) rows y p) (zc t0) :=
    fun p hpl => (chk_sound b _ _ false (zc t0) hc (hp p hpl)).1
  have hs : 0 ≤ ∑ p ∈ Finset.range ps.length, c p * evz (leafFR den rn rd fn (gW ps p) rows y p) (zc t0) :=
    Finset.sum_nonneg (fun p hpm => mul_nonneg (hc0 p (Finset.mem_range.mp hpm)) (hpos p (Finset.mem_range.mp hpm)))
  have e : ∀ p, evz (leafFR den rn rd fn (gW ps p) rows y p) (zc t0) =
      (rn : ℝ) * evz (cond den TT L5) (zc t0) - rd * evz (comb5 fn (gW ps p)) (zc t0) - evz (farkasR rows y p) (zc t0) := by
    intro p; simp only [leafFR, evz_add, evz_neg, evz_lin, zN_val]; simp [zM, Z.val]; ring
  have hf := farkasR_nonneg rows c ps.length (zc t0) hrw y
  simp only [e, mul_sub, Finset.sum_sub_distrib] at hs
  have h1 : ∑ p ∈ Finset.range ps.length, c p * ((rn : ℝ) * evz (cond den TT L5) (zc t0)) =
      (rn : ℝ) * evz (cond den TT L5) (zc t0) := by rw [← Finset.sum_mul, hc1, one_mul]
  have h2 : ∑ p ∈ Finset.range ps.length, c p * ((rd : ℝ) * evz (comb5 fn (gW ps p)) (zc t0)) =
      (rd : ℝ) * (σ * evz fn z) := by
    rw [← comb_trackP ps c (zc t0) z σ htr fn, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [h1, h2] at hs; linarith

theorem inf_falseR (b : Box) (t0 : Tri) (hc : InCell b (zc t0)) (ps : List W5) (rows : RS) (c : Nat → ℝ)
    (hc0 : ∀ p < ps.length, 0 ≤ c p) (hc1 : ∑ p ∈ Finset.range ps.length, c p = 1)
    (hrw : RowsOK (fw rows) c ps.length (zc t0)) (ys : List (Nat × Nat)) (code : Nat)
    (h : allP ps.length (fun p => chk b (gD code p) (F5.neg (farkasR rows ys p)) true) = true) : False := by
  have hp := allP_spec h
  have hneg : ∀ p < ps.length, evz (farkasR rows ys p) (zc t0) < 0 := by
    intro p hpl; have := (chk_sound b _ _ true (zc t0) hc (hp p hpl)).2 rfl
    simp only [evz_neg] at this; linarith
  have h1 := wsum_neg ps.length c (fun p => evz (farkasR rows ys p) (zc t0)) hc0 hc1 hneg
  have h2 := farkasR_nonneg rows c ps.length (zc t0) hrw ys
  linarith

/-! ### exact cycles: patterns with `M_P = I` (followed forever ⇒ periodic orbit, impossible since λ → 0) -/

def idOK (W : W5) (s : Int) : Bool :=
  nilOK W s && zIs W.w0.c3 0 && zIs W.w0.c4 0 && zIs W.w0.c5 0 && zIs W.w1.c3 0 && zIs W.w1.c4 0 && zIs W.w1.c5 0

def cStatic (k : Nat) (P : List Nat) : Bool :=
  Nat.blt 0 P.length && lettersOK P && Nat.beq (letter P 0) k && idOK (wFull P) (16 ^ P.length) &&
    Nat.beq (upC P) (dnC P)

def cExParts (P : List Nat) (r : Nat) (ps : List W5) : List W5 := walkParts (P.take r) ps
def cExRows (P : List Nat) (r : Nat) (ps : List W5) (rows : List (List F5)) : List (List F5) :=
  rows ++ walkRows (P.take r) ps ++ unitRows (cExParts P r ps)

def rsRun (i : Nat) (odd : Bool) (ps : List W5) (rows : RS) : RS :=
  rsMapPush rows (repRow ps.length) ((pieceRows i).map (fun f => repRow ps.length (ps.map (comb5 f))) ++
    brRowsP 2 (prevpartsOf i odd ps) ++ (List.range 5).map (fun r => (wpartsOf i odd ps).map (comb5 (unitF r))))
def rsEx (P : List Nat) (fs i r : Nat) (ps : List W5) (rows : RS) : RS :=
  rsMapPush rows (repRow ps.length) ((onParts (gPRows P fs i) ps).map (repRow ps.length) ++ unitRows (gUp P fs i ps) ++
    walkRows (P.take r) (gUp P fs i ps) ++ unitRows (gExParts P fs i r ps))
def rsC (P : List Nat) (r : Nat) (ps : List W5) (rows : RS) : RS :=
  rsPush rows (walkRows (P.take r) ps ++ unitRows (cExParts P r ps))

theorem fw_run (i : Nat) (odd : Bool) (ps : List W5) (rows : RS) :
    fw (rsRun i odd ps rows) = runRows i odd ps (fw rows) := by
  simp only [rsRun, fw_mapPush, runRows, List.append_assoc]
theorem fw_ex (P : List Nat) (fs i r : Nat) (ps : List W5) (rows : RS) :
    fw (rsEx P fs i r ps rows) = gExRows P fs i r ps (fw rows) := by
  simp only [rsEx, fw_mapPush, gExRows, List.append_assoc]
theorem fw_c (P : List Nat) (r : Nat) (ps : List W5) (rows : RS) :
    fw (rsC P r ps rows) = cExRows P r ps (fw rows) := by
  simp only [rsC, fw_push, cExRows, List.append_assoc]

theorem lettersOK_take : ∀ (l : List Nat) (m : Nat), lettersOK l = true → lettersOK (l.take m) = true
  | [], _, _ => by simp [lettersOK]
  | x :: l, 0, _ => by simp [lettersOK]
  | x :: l, m + 1, h => by
    simp only [lettersOK, Bool.and_eq_true] at h
    simp only [List.take_succ_cons, lettersOK, Bool.and_eq_true]; exact ⟨h.1, lettersOK_take l m h.2⟩

theorem cyc_exit (t0 : Tri) (ps : List W5) (rows : List (List F5)) (σ j nE nC k : Nat) (P : List Nat)
    (hI : InvP t0 ps rows σ j nE nC) (hk : brC k (zc (step^[j] t0))) (hst : cStatic k P = true) :
    ∃ (n r : Nat), 1 ≤ n ∧ 1 ≤ r ∧ r ≤ P.length ∧
      InvP t0 (cExParts P r ps) (cExRows P r ps (rows ++ brRowsP k ps)) (σ * 16 ^ r) (j + n)
        (nE + upC (P.take r)) (nC + dnC (P.take r)) ∧
      ¬ brC (letter P (r % P.length)) (zc (step^[j + n] t0)) := by
  classical
  simp only [cStatic, idOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hst
  obtain ⟨⟨⟨⟨hP, hl⟩, hk0⟩, ⟨⟨⟨⟨⟨⟨hnil, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩⟩, hud⟩ := hst
  obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
  set tj := step^[j] t0 with htj
  set z := zc tj with hz
  have hσ : (0 : ℝ) < σ := by have := hI.sig; exact_mod_cast (show 0 < σ by omega)
  have hrw' : RowsOK (rows ++ brRowsP k ps) c ps.length (zc t0) := rowsOK_append hrw (brRowsP_ok k ps c _ _ _ hσ htr hk)
  have hzero : ∀ (y : Zc) (q : ℝ), addN (nRow0 (wFull P)) (nRow1 (wFull P)) (16 ^ P.length) y q = y := by
    intro y q
    have e0 : evz (nRow0 (wFull P)) y = 0 := by
      simp only [nRow0, evz, F5.ev]; rw [zIs_val z1, zIs_val z2, zIs_val z3]; simp [zN, Z.val]
    have e1 : evz (nRow1 (wFull P)) y = 0 := by
      simp only [nRow1, evz, F5.ev]; rw [zIs_val z4, zIs_val z5, zIs_val z6]; simp [zN, Z.val]
    simp only [addN, e0, e1, mul_zero, zero_div, add_zero]
  have hpat0 : pat P 0 = k := by simp only [pat, Nat.zero_mod]; exact hk0
  -- finiteness from λ → 0
  have hex : ∃ n, ¬ brC (pat P n) (zc (step^[n] tj)) := by
    by_contra hall
    push_neg at hall
    have hlam := lam_to_zero tj hI.srt hI.ndg
    have hl0 := lam_pos tj hI.ndg
    rw [Metric.tendsto_atTop] at hlam
    obtain ⟨K, hK⟩ := hlam (lam tj) hl0
    have hk' := hK (P.length * K) (by nlinarith)
    obtain ⟨hu, -⟩ := periods_lin P hP hl hnil hud tj hI.srt hI.ndg K (fun i _ => hall i)
    rw [hzero] at hu
    have : lam (traj tj (P.length * K)) = lam tj := by
      simp only [traj]; rw [← zc_lam, hu, zc_lam]
    rw [this, Real.dist_eq, sub_zero, abs_of_pos hl0] at hk'
    linarith
  set n := Nat.find hex with hndef
  have hn : ¬ brC (pat P n) (zc (step^[n] tj)) := Nat.find_spec hex
  have hmin : ∀ i < n, brC (pat P i) (zc (step^[i] tj)) := by
    intro i hi; have := Nat.find_min hex hi; push_neg at this; exact this
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso; rw [h0] at hn; rw [hpat0] at hn; exact hn hk
    · exact h0
  set q := (n - 1) / P.length with hqdef
  set r := n - P.length * q with hrdef
  have hq1 : P.length * q ≤ n - 1 := Nat.mul_div_le (n - 1) P.length
  have hq2 : n - 1 < P.length * q + P.length := by
    calc n - 1 < P.length * (q + 1) := Nat.lt_mul_div_succ (n - 1) hP
      _ = P.length * q + P.length := by ring
  have hr1 : 1 ≤ r := by omega
  have hrP : r ≤ P.length := by omega
  have hnqr : n = P.length * q + r := by omega
  obtain ⟨hu, hAu⟩ := periods_lin P hP hl hnil hud tj hI.srt hI.ndg q (fun i hi => hmin i (by omega))
  rw [hzero] at hu
  have hsu := iter_sorted tj hI.srt hI.ndg (P.length * q)
  have hfol : Follows (step^[P.length * q] tj) (P.take r) := by
    intro i' hi'
    rw [List.length_take, min_eq_left hrP] at hi'
    have := hmin (P.length * q + i') (by omega)
    rw [pat_period P q i' (by omega), iter_add'] at this
    simpa [letter, nth_take P r i' hi'] using this
  have htrU : TrackP ps c (zc t0) (zc (step^[P.length * q] tj)) σ := by rw [hu]; exact htr
  obtain ⟨w1, w2, w3⟩ := walk_sound (P.take r) (lettersOK_take P r hl) _ ps c (zc t0) σ hsu.1 hsu.2 hσ htrU hfol
  rw [List.length_take, min_eq_left hrP, ← iter_add', ← hnqr] at w1 w3
  have hlenX : (cExParts P r ps).length = ps.length := by simp only [cExParts]; rw [length_walkParts]
  have hsn := iter_sorted tj hI.srt hI.ndg n
  refine ⟨n, r, hn1, hr1, hrP, ⟨?_, ?_, ⟨c, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [iter_add, ← htj]; exact hsn.1
  · rw [iter_add, ← htj]; exact hsn.2
  · rw [hlenX]; exact hc0
  · rw [hlenX]; exact hc1
  · rw [iter_add, ← htj]; push_cast; simp only [cExParts]; rw [mul_comm]; exact w1
  · simp only [cExRows]
    rw [hlenX]
    refine rowsOK_append (rowsOK_append hrw' w2) ?_
    have hv := zc_nonneg _ hsn.1
    have := unitRows_ok (cExParts P r ps) c (zc t0) _ _ (by positivity) w1 hv
    rwa [hlenX] at this
  · rw [iter_add, ← htj, w3, hAu, hI.area, pow_add, pow_add]; ring
  · have h1 := hI.sig; have h3 : 1 ≤ 16 ^ r := Nat.one_le_pow _ _ (by norm_num)
    calc 1 = 1 * 1 := by norm_num
      _ ≤ σ * 16 ^ r := Nat.mul_le_mul h1 h3
  · rw [iter_add, ← htj]
    have : pat P n = letter P (r % P.length) := by
      simp only [pat]; rw [hnqr, Nat.add_comm, Nat.add_mul_mod_self_left]
    rw [← this]; exact hn

mutual
inductive RT3 where
  | leaf (den : Bool) (rn rd : Nat) (y1 : PY) (p1 : Nat) (y2 : PY) (p2 : Nat)
  | node (c1 c2 c3 c4 c5 c6 c7 c8 c9 : RC3)
inductive RC3 where
  | inf (ys : PY) (prs : Nat)
  | sub (t : RT3)
  | subu (t : RT3)
  | skip
  | run (pcs : RL3)
  | grun (P : List Nat) (fs : Nat) (ld : Nat) (ly : PY) (lp : Nat) (pcs : RL3)
  | gcyc (P : List Nat) (pcs : RL3)
inductive RL3 where
  | nil
  | cons (c : RC3) (rest : RL3)
end

/-- `ℓ > 0` for nondegenerate states, read off the coefficients -/
def autoPos (l : F5) : Bool :=
  zIs l.c1 0 && zIs l.c2 0 && decide (0 ≤ zToI l.c3) && decide (0 ≤ zToI l.c4) && decide (0 ≤ zToI l.c5) &&
    decide (0 < zToI l.c3 + zToI l.c4 + zToI l.c5)

def posOK (b : Box) (l : F5) (ld : Nat) (ps : List W5) (rows : RS) (ly : List (Nat × Nat)) (lp : Nat) : Bool :=
  autoPos l || (Nat.ble 1 ld &&
    allP ps.length (fun p => chk b (gD lp p) (F5.add (F5.smul (zN ld) (comb5 l (gW ps p))) (F5.neg (farkasR rows ly p))) true))

mutual
def chkRT3 (b : Box) : RT3 → List W5 → RS → Nat → Bool → Nat → Nat → Nat → Bool
  | .leaf den rn rd y1 p1 y2 p2, ps, rows, σ, moved, _, nE, nC =>
    moved && Nat.ble 1 rd &&
    allP ps.length (fun p => chk b (gD p1 p) (leafFR den rn rd TT (gW ps p) rows (pyL y1) p) false) &&
    allP ps.length (fun p => chk b (gD p2 p) (leafFR den rn rd L5 (gW ps p) rows (pyL y2) p) false) &&
    Nat.ble (2 ^ (8 * nC) * rn ^ 7) (2 ^ (8 * nE) * (rd * σ) ^ 7)
  | .node c1 c2 c3 c4 c5 c6 c7 c8 c9, ps, rows, σ, _, post, nE, nC =>
    chkRC3 b 1 post c1 ps rows σ nE nC && chkRC3 b 2 post c2 ps rows σ nE nC && chkRC3 b 3 post c3 ps rows σ nE nC &&
    chkRC3 b 4 post c4 ps rows σ nE nC && chkRC3 b 5 post c5 ps rows σ nE nC && chkRC3 b 6 post c6 ps rows σ nE nC &&
    chkRC3 b 7 post c7 ps rows σ nE nC && chkRC3 b 8 post c8 ps rows σ nE nC && chkRC3 b 9 post c9 ps rows σ nE nC
def chkRC3 (b : Box) (k : Nat) (post : Nat) : RC3 → List W5 → RS → Nat → Nat → Nat → Bool
  | .inf ys prs, ps, rows, _, _, _ =>
    allP ps.length (fun p => chk b (gD prs p) (F5.neg (farkasR (rsPush rows (brRowsP k ps)) (pyL ys) p)) true)
  | .sub t, ps, rows, σ, nE, nC =>
    chkRT3 b t (ps.map (stepW k)) (rsPush rows (brRowsP k ps)) (16 * σ) true 0 (nE + eUp k) (nC + eDn k)
  | .subu t, ps, rows, σ, nE, nC =>
    chkRT3 b t (ps.map (stepW k)) (rsPush (rsPush rows (brRowsP k ps)) (unitRows (ps.map (stepW k)))) (16 * σ) true 0
      (nE + eUp k) (nC + eDn k)
  | .skip, _, _, _, _, _ => Nat.beq k post
  | .run pcs, ps, rows, σ, nE, nC => Nat.beq k 2 && chkRL3 b pcs 0 ps (rsPush rows (brRowsP 2 ps)) σ nE nC
  | .grun P fs ld ly lp pcs, ps, rows, σ, nE, nC =>
    gStatic k P fs && posOK b (gEll P fs) ld ps (rsPush rows (brRowsP k ps)) (pyL ly) lp &&
      chkGL b P fs pcs 0 ps (rsPush rows (brRowsP k ps)) σ nE nC
  | .gcyc P pcs, ps, rows, σ, nE, nC => cStatic k P && chkCL b P pcs 0 ps (rsPush rows (brRowsP k ps)) σ nE nC
def pieceOK3 (b : Box) : RC3 → List W5 → RS → Nat → Nat → Nat → Bool
  | .inf ys prs, ps, rows, _, _, _ =>
    allP ps.length (fun p => chk b (gD prs p) (F5.neg (farkasR rows (pyL ys) p)) true)
  | .sub t, ps, rows, σ, nE, nC => chkRT3 b t ps rows σ true 2 nE nC
  | .subu _, _, _, _, _, _ => false
  | .skip, _, _, _, _, _ => false
  | .run _, _, _, _, _, _ => false
  | .grun _ _ _ _ _ _, _, _, _, _, _ => false
  | .gcyc _ _, _, _, _, _, _ => false
def chkRL3 (b : Box) : RL3 → Nat → List W5 → RS → Nat → Nat → Nat → Bool
  | .nil, idx, _, _, _, _, _ => Nat.beq idx 52
  | .cons c rest, idx, ps, rows, σ, nE, nC =>
    pieceOK3 b c (wpartsOf (idx / 2) (oddOf idx) ps) (rsRun (idx / 2) (oddOf idx) ps rows)
      (runSig (idx / 2) (oddOf idx) σ) nE nC && chkRL3 b rest (idx + 1) ps rows σ nE nC
def gPieceOK (b : Box) (P : List Nat) (fs i r : Nat) : RC3 → List W5 → RS → Nat → Nat → Nat → Bool
  | .inf ys prs, ps, rows, _, _, _ =>
    cond (gBnd (ga P fs) (gb P fs) i)
      (allP (3 * ps.length) (fun p => chk b (gD prs p) (F5.neg (farkasR (rsEx P fs i r ps rows) (pyL ys) p)) true))
      (allP ps.length (fun p => chk b (gD prs p) (F5.neg (farkasR (rsPush rows (onParts (gPRows P fs i) ps)) (pyL ys) p)) true))
  | .sub t, ps, rows, σ, nE, nC =>
    gBnd (ga P fs) (gb P fs) i &&
      chkRT3 b t (gExParts P fs i r ps) (rsEx P fs i r ps rows) (gSig P fs i r σ) true (letter P (r % P.length))
        (nE + upC (P.take r)) (nC + dnC (P.take r))
  | .subu _, _, _, _, _, _ => false
  | .skip, _, _, _, _, _ => false
  | .run _, _, _, _, _, _ => false
  | .grun _ _ _ _ _ _, _, _, _, _, _ => false
  | .gcyc _ _, _, _, _, _, _ => false
def chkGL (b : Box) (P : List Nat) (fs : Nat) : RL3 → Nat → List W5 → RS → Nat → Nat → Nat → Bool
  | .nil, idx, _, _, _, _, _ => Nat.beq idx (26 * P.length)
  | .cons c rest, idx, ps, rows, σ, nE, nC =>
    gPieceOK b P fs (idx / P.length) (idx % P.length + 1) c ps rows σ nE nC && chkGL b P fs rest (idx + 1) ps rows σ nE nC
def cPieceOK (b : Box) (P : List Nat) (r : Nat) : RC3 → List W5 → RS → Nat → Nat → Nat → Bool
  | .inf ys prs, ps, rows, _, _, _ =>
    allP ps.length (fun p => chk b (gD prs p) (F5.neg (farkasR (rsC P r ps rows) (pyL ys) p)) true)
  | .sub t, ps, rows, σ, nE, nC =>
    chkRT3 b t (cExParts P r ps) (rsC P r ps rows) (σ * 16 ^ r) true (letter P (r % P.length))
      (nE + upC (P.take r)) (nC + dnC (P.take r))
  | .subu _, _, _, _, _, _ => false
  | .skip, _, _, _, _, _ => false
  | .run _, _, _, _, _, _ => false
  | .grun _ _ _ _ _ _, _, _, _, _, _ => false
  | .gcyc _ _, _, _, _, _, _ => false
def chkCL (b : Box) (P : List Nat) : RL3 → Nat → List W5 → RS → Nat → Nat → Nat → Bool
  | .nil, idx, _, _, _, _, _ => Nat.beq idx P.length
  | .cons c rest, idx, ps, rows, σ, nE, nC =>
    cPieceOK b P (idx + 1) c ps rows σ nE nC && chkCL b P rest (idx + 1) ps rows σ nE nC
end

/-! ### soundness -/

theorem chkRT3_node (b : Box) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : RC3) (ps : List W5) (rows : RS) (σ : Nat)
    (moved : Bool) (post nE nC : Nat) (h : chkRT3 b (.node c1 c2 c3 c4 c5 c6 c7 c8 c9) ps rows σ moved post nE nC = true)
    (k : Nat) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) :
    chkRC3 b k post (match k with | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | 5 => c5 | 6 => c6 | 7 => c7 | 8 => c8 | _ => c9)
      ps rows σ nE nC = true := by
  simp only [chkRT3, Bool.and_eq_true] at h
  interval_cases k <;> simp only <;> tauto

theorem wsum_pos (n : Nat) (c x : Nat → ℝ) (hc : ∀ p < n, 0 ≤ c p) (h1 : ∑ p ∈ Finset.range n, c p = 1)
    (hx : ∀ p < n, 0 < x p) : 0 < ∑ p ∈ Finset.range n, c p * x p := by
  have := wsum_neg n c (fun p => - x p) hc h1 (fun p hp => by linarith [hx p hp])
  simp only [mul_neg, Finset.sum_neg_distrib] at this; linarith

theorem pos_of_posOK (b : Box) (t0 : Tri) (hc : InCell b (zc t0)) (tj : Tri) (hn : nondeg tj) (l : F5)
    (ps : List W5) (rows : RS) (c : Nat → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hc0 : ∀ p < ps.length, 0 ≤ c p) (hc1 : ∑ p ∈ Finset.range ps.length, c p = 1)
    (htr : TrackP ps c (zc t0) (zc tj) σ) (hrw : RowsOK (fw rows) c ps.length (zc t0)) (ld : Nat) (ly : List (Nat × Nat))
    (lp : Nat) (h : posOK b l ld ps rows ly lp = true) : 0 < evz l (zc tj) := by
  simp only [posOK, Bool.or_eq_true] at h
  rcases h with h | h
  · simp only [autoPos, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    have v1 := zIs_val h1; have v2 := zIs_val h2
    have pa : 0 < (zc tj).a := D12_pos tj hn
    have pb : 0 < (zc tj).b := D13_pos tj hn
    have pc : 0 < (zc tj).c := D23_pos tj hn
    simp only [evz, F5.ev, v1, v2, val_zToI]
    have h3' : (0 : ℝ) ≤ (zToI l.c3 : ℝ) := by exact_mod_cast h3
    have h4' : (0 : ℝ) ≤ (zToI l.c4 : ℝ) := by exact_mod_cast h4
    have h5' : (0 : ℝ) ≤ (zToI l.c5 : ℝ) := by exact_mod_cast h5
    have h6' : (0 : ℝ) < (zToI l.c3 : ℝ) + (zToI l.c4 : ℝ) + (zToI l.c5 : ℝ) := by exact_mod_cast h6
    set m := min (zc tj).a (min (zc tj).b (zc tj).c)
    have hm : 0 < m := lt_min pa (lt_min pb pc)
    have ma : m ≤ (zc tj).a := min_le_left _ _
    have mb : m ≤ (zc tj).b := le_trans (min_le_right _ _) (min_le_left _ _)
    have mc : m ≤ (zc tj).c := le_trans (min_le_right _ _) (min_le_right _ _)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ma h3', mul_le_mul_of_nonneg_left mb h4', mul_le_mul_of_nonneg_left mc h5',
      mul_pos hm h6']
  · simp only [Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hld, h⟩ := h
    have hp := allP_spec h
    have hx : ∀ p < ps.length,
        0 < evz (F5.add (F5.smul (zN ld) (comb5 l (gW ps p))) (F5.neg (farkasR rows ly p))) (zc t0) :=
      fun p hpl => (chk_sound b _ _ true (zc t0) hc (hp p hpl)).2 rfl
    have h1 := wsum_pos ps.length c _ hc0 hc1 hx
    simp only [evz_add, evz_neg, evz_smul, zN_val, mul_add, mul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib] at h1
    have h2 := farkasR_nonneg rows c ps.length (zc t0) hrw ly
    have e : ∑ p ∈ Finset.range ps.length, c p * ((ld : ℝ) * evz (comb5 l (gW ps p)) (zc t0)) =
        (ld : ℝ) * (σ * evz l (zc tj)) := by
      rw [← comb_trackP ps c (zc t0) (zc tj) σ htr l, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p _; ring
    rw [e] at h1
    have h3 : 0 < (ld : ℝ) * (σ * evz l (zc tj)) := by linarith
    have hld' : (0 : ℝ) < ld := by exact_mod_cast hld
    exact pos_of_mul_pos_right (pos_of_mul_pos_right h3 hld'.le) hσ.le

theorem rec3_sound (b : Box) (t0 : Tri) (hs0 : sorted t0) (hn0 : nondeg t0) (hc : InCell b (zc t0)) :
    ∀ (T : RT3) (ps : List W5) (rows : RS) (σ : Nat) (moved : Bool) (post nE nC j : Nat),
      chkRT3 b T ps rows σ moved post nE nC = true → InvP t0 ps (fw rows) σ j nE nC → (moved = true → 1 ≤ j) →
      (1 ≤ post → ¬ brC post (zc (step^[j] t0))) → Goal t0 := by
  intro T
  induction T using RT3.rec
    (motive_2 := fun C =>
      (∀ (k post : Nat) (ps : List W5) (rows : RS) (σ nE nC j : Nat), 1 ≤ k → k ≤ 9 →
        chkRC3 b k post C ps rows σ nE nC = true → InvP t0 ps (fw rows) σ j nE nC →
        (1 ≤ post → ¬ brC post (zc (step^[j] t0))) → brC k (zc (step^[j] t0)) →
        zc (step (step^[j] t0)) = brM k (zc (step^[j] t0)) → A (step (step^[j] t0)) = alpha k * A (step^[j] t0) →
        Goal t0) ∧
      (∀ (ps : List W5) (rows : RS) (σ nE nC j : Nat), pieceOK3 b C ps rows σ nE nC = true →
        InvP t0 ps (fw rows) σ j nE nC → 1 ≤ j → ¬ brC 2 (zc (step^[j] t0)) → Goal t0) ∧
      (∀ (P : List Nat) (fs i r : Nat) (ps : List W5) (rows : RS) (σ nE nC j : Nat),
        gPieceOK b P fs i r C ps rows σ nE nC = true → 1 ≤ j →
        (gBnd (ga P fs) (gb P fs) i = true →
          InvP t0 (gExParts P fs i r ps) (fw (rsEx P fs i r ps rows)) (gSig P fs i r σ) j
            (nE + upC (P.take r)) (nC + dnC (P.take r)) ∧
          ¬ brC (letter P (r % P.length)) (zc (step^[j] t0))) →
        (gBnd (ga P fs) (gb P fs) i = false →
          ∃ c : Nat → ℝ, (∀ p < ps.length, 0 ≤ c p) ∧ (∑ p ∈ Finset.range ps.length, c p = 1) ∧
            RowsOK (fw (rsPush rows (onParts (gPRows P fs i) ps))) c ps.length (zc t0)) → Goal t0) ∧
      (∀ (P : List Nat) (r : Nat) (ps : List W5) (rows : RS) (σ nE nC j : Nat),
        cPieceOK b P r C ps rows σ nE nC = true → 1 ≤ j →
        InvP t0 (cExParts P r ps) (fw (rsC P r ps rows)) (σ * 16 ^ r) j (nE + upC (P.take r)) (nC + dnC (P.take r)) →
        ¬ brC (letter P (r % P.length)) (zc (step^[j] t0)) → Goal t0))
    (motive_3 := fun L =>
      (∀ (idx : Nat) (ps : List W5) (rows : RS) (σ nE nC j : Nat), chkRL3 b L idx ps rows σ nE nC = true →
        ∀ m, idx ≤ m → m < 52 → ∀ n, 1 ≤ n →
          InvP t0 (wpartsOf (m / 2) (oddOf m) ps) (fw (rsRun (m / 2) (oddOf m) ps rows)) (runSig (m / 2) (oddOf m) σ)
            (j + n) nE nC → ¬ brC 2 (zc (step^[j + n] t0)) → Goal t0) ∧
      (∀ (P : List Nat) (fs idx : Nat) (ps : List W5) (rows : RS) (σ nE nC j : Nat),
        chkGL b P fs L idx ps rows σ nE nC = true →
        ∀ m, idx ≤ m → m < 26 * P.length → 1 ≤ j →
          (gBnd (ga P fs) (gb P fs) (m / P.length) = true →
            InvP t0 (gExParts P fs (m / P.length) (m % P.length + 1) ps)
              (fw (rsEx P fs (m / P.length) (m % P.length + 1) ps rows)) (gSig P fs (m / P.length) (m % P.length + 1) σ) j
              (nE + upC (P.take (m % P.length + 1))) (nC + dnC (P.take (m % P.length + 1))) ∧
            ¬ brC (letter P ((m % P.length + 1) % P.length)) (zc (step^[j] t0))) →
          (gBnd (ga P fs) (gb P fs) (m / P.length) = false →
            ∃ c : Nat → ℝ, (∀ p < ps.length, 0 ≤ c p) ∧ (∑ p ∈ Finset.range ps.length, c p = 1) ∧
              RowsOK (fw (rsPush rows (onParts (gPRows P fs (m / P.length)) ps))) c ps.length (zc t0)) → Goal t0) ∧
      (∀ (P : List Nat) (idx : Nat) (ps : List W5) (rows : RS) (σ nE nC j : Nat),
        chkCL b P L idx ps rows σ nE nC = true → ∀ m, idx ≤ m → m < P.length → 1 ≤ j →
          InvP t0 (cExParts P (m + 1) ps) (fw (rsC P (m + 1) ps rows)) (σ * 16 ^ (m + 1)) j
            (nE + upC (P.take (m + 1))) (nC + dnC (P.take (m + 1))) →
          ¬ brC (letter P ((m + 1) % P.length)) (zc (step^[j] t0)) → Goal t0)) with
  | leaf den rn rd y1 p1 y2 p2 =>
    intro ps rows σ moved post nE nC j h hI hmv _
    simp only [chkRT3, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨hm, hrd⟩, h1⟩, h2⟩, hexp⟩ := h
    obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
    have b1 := leaf_boundR b t0 hc ps rows c _ _ hc0 hc1 htr hrw den rn rd TT (pyL y1) p1 h1
    have b2 := leaf_boundR b t0 hc ps rows c _ _ hc0 hc1 htr hrw den rn rd L5 (pyL y2) p2 h2
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
    have hck := chkRT3_node b c1 c2 c3 c4 c5 c6 c7 c8 c9 ps rows σ moved post nE nC h k hk1 hk9
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
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI _ hbr _ _
      simp only [chkRC3] at h
      obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
      have hσ : (0 : ℝ) < σ := by have := hI.sig; exact_mod_cast (show 0 < σ by omega)
      have hrw' := rowsOK_push hrw (brRowsP_ok k ps c _ _ _ hσ htr hbr)
      exact (inf_falseR b t0 hc ps _ c hc0 hc1 hrw' (pyL ys) prs h).elim
    · intro ps rows σ nE nC j h hI _ _
      simp only [pieceOK3] at h
      obtain ⟨c, hc0, hc1, _, hrw⟩ := hI.wts
      exact (inf_falseR b t0 hc ps rows c hc0 hc1 hrw (pyL ys) prs h).elim
    · intro P fs i r ps rows σ nE nC j h _ hB hU
      simp only [gPieceOK] at h
      cases hb : gBnd (ga P fs) (gb P fs) i with
      | true =>
        rw [hb] at h; simp only [cond] at h
        obtain ⟨hI', _⟩ := hB hb
        obtain ⟨c, hc0, hc1, _, hrw⟩ := hI'.wts
        have hl : (gExParts P fs i r ps).length = 3 * ps.length := by
          simp only [gExParts, gUp]; rw [length_walkParts, length_upartsE]
        rw [hl] at hc0 hc1 hrw
        exact (inf_falseR b t0 hc (gExParts P fs i r ps) _ c (by rwa [hl]) (by rwa [hl]) (by rwa [hl]) (pyL ys) prs
          (by rw [hl]; exact h)).elim
      | false =>
        rw [hb] at h; simp only [cond] at h
        obtain ⟨c, hc0, hc1, hrw⟩ := hU hb
        exact (inf_falseR b t0 hc ps _ c hc0 hc1 hrw (pyL ys) prs h).elim
    · intro P r ps rows σ nE nC j h _ hI _
      simp only [cPieceOK] at h
      obtain ⟨c, hc0, hc1, _, hrw⟩ := hI.wts
      have hl : (cExParts P r ps).length = ps.length := by simp only [cExParts]; rw [length_walkParts]
      rw [hl] at hc0 hc1 hrw
      exact (inf_falseR b t0 hc ps _ c hc0 hc1 hrw (pyL ys) prs h).elim
  | sub t ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI _ hbr hM hA
      simp only [chkRC3] at h
      obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
      have hσ : (0 : ℝ) < σ := by have := hI.sig; exact_mod_cast (show 0 < σ by omega)
      have e : step^[j + 1] t0 = step (step^[j] t0) := Function.iterate_succ_apply' step j t0
      apply ih _ _ _ _ _ _ _ (j + 1) h _ (fun _ => by omega) (fun hf => by omega)
      refine ⟨?_, ?_, ⟨c, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [e]; exact step_sorted _ hI.srt hI.ndg
      · rw [e]; exact step_nondeg _ hI.srt hI.ndg
      · rw [List.length_map]; exact hc0
      · rw [List.length_map]; exact hc1
      · rw [e, hM]; push_cast; exact trackP_step k hk1 hk9 ps c _ _ _ htr
      · rw [List.length_map]; exact rowsOK_push hrw (brRowsP_ok k ps c _ _ _ hσ htr hbr)
      · rw [e, hA, hI.area, alpha_e k hk1 hk9, pow_add, pow_add]; ring
      · have := hI.sig; omega
    · intro ps rows σ nE nC j h hI hj hn2
      simp only [pieceOK3] at h
      exact ih ps rows σ true 2 nE nC j h hI (fun _ => hj) (fun _ => hn2)
    · intro P fs i r ps rows σ nE nC j h hj hB _
      simp only [gPieceOK, Bool.and_eq_true] at h
      obtain ⟨hb, h⟩ := h
      obtain ⟨hI', hpost⟩ := hB hb
      exact ih _ _ _ _ _ _ _ j h hI' (fun _ => hj) (fun _ => hpost)
    · intro P r ps rows σ nE nC j h hj hI hpost
      simp only [cPieceOK] at h
      exact ih _ _ _ _ _ _ _ j h hI (fun _ => hj) (fun _ => hpost)
  | subu t ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI _ hbr hM hA
      simp only [chkRC3] at h
      obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
      have hσ : (0 : ℝ) < σ := by have := hI.sig; exact_mod_cast (show 0 < σ by omega)
      have e : step^[j + 1] t0 = step (step^[j] t0) := Function.iterate_succ_apply' step j t0
      have htr' : TrackP (ps.map (stepW k)) c (zc t0) (zc (step^[j + 1] t0)) ((16 * σ : Nat) : ℝ) := by
        rw [e, hM]; push_cast; exact trackP_step k hk1 hk9 ps c _ _ _ htr
      have hsrt : sorted (step^[j + 1] t0) := by rw [e]; exact step_sorted _ hI.srt hI.ndg
      apply ih _ _ _ _ _ _ _ (j + 1) h _ (fun _ => by omega) (fun hf => by omega)
      refine ⟨hsrt, ?_, ⟨c, ?_, ?_, htr', ?_⟩, ?_, ?_⟩
      · rw [e]; exact step_nondeg _ hI.srt hI.ndg
      · rw [List.length_map]; exact hc0
      · rw [List.length_map]; exact hc1
      · rw [List.length_map]
        refine rowsOK_push (rowsOK_push hrw (brRowsP_ok k ps c _ _ _ hσ htr hbr)) ?_
        have := unitRows_ok (ps.map (stepW k)) c (zc t0) _ _ (by positivity) htr' (zc_nonneg _ hsrt)
        rwa [List.length_map] at this
      · rw [e, hA, hI.area, alpha_e k hk1 hk9, pow_add, pow_add]; ring
      · have := hI.sig; omega
    · intro ps rows σ nE nC j h; simp [pieceOK3] at h
    · intro P fs i r ps rows σ nE nC j h; simp [gPieceOK] at h
    · intro P r ps rows σ nE nC j h; simp [cPieceOK] at h
  | skip =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI hpost hbr _ _
      simp only [chkRC3, Nat.beq_eq] at h
      subst h
      exact (hpost hk1 hbr).elim
    · intro ps rows σ nE nC j h; simp [pieceOK3] at h
    · intro P fs i r ps rows σ nE nC j h; simp [gPieceOK] at h
    · intro P r ps rows σ nE nC j h; simp [cPieceOK] at h
  | run pcs ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI _ hbr _ _
      simp only [chkRC3, Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨rfl, hL⟩ := h
      obtain ⟨n, i, odd, hn1, hi, hI', hn2⟩ := run_exit t0 ps (fw rows) σ j nE nC hI hbr
      set m := 2 * i + cond odd 1 0 with hm
      have hmi : m / 2 = i := by cases odd <;> simp [hm, cond] <;> omega
      have hmod : m % 2 = cond odd 1 0 := by cases odd <;> simp only [hm, cond] <;> omega
      have hmo : oddOf m = odd := by simp only [oddOf, hmod]; cases odd <;> rfl
      apply ih.1 0 ps (rsPush rows (brRowsP 2 ps)) σ nE nC j hL m (Nat.zero_le _) (by cases odd <;> simp [hm, cond] <;> omega) n hn1
      · rw [hmi, hmo, fw_run, fw_push]; exact hI'
      · exact hn2
    · intro ps rows σ nE nC j h; simp [pieceOK3] at h
    · intro P fs i r ps rows σ nE nC j h; simp [gPieceOK] at h
    · intro P r ps rows σ nE nC j h; simp [cPieceOK] at h
  | grun P fs ld ly lp pcs ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI _ hbr _ _
      simp only [chkRC3, Bool.and_eq_true] at h
      obtain ⟨⟨hst, hpo⟩, hL⟩ := h
      obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
      have hσ : (0 : ℝ) < σ := by have := hI.sig; exact_mod_cast (show 0 < σ by omega)
      have hrw' := rowsOK_push hrw (brRowsP_ok k ps c _ _ _ hσ htr hbr)
      have hpos := pos_of_posOK b t0 hc _ hI.ndg (gEll P fs) ps _ c σ hσ hc0 hc1 htr hrw' ld (pyL ly) lp hpo
      obtain ⟨n, i, r, hn1, hi, hr1, hrP, hB, hU⟩ := grun_exit t0 ps (fw rows) σ j nE nC k P fs hI hbr hst hpos
      have hP : 0 < P.length := by omega
      set m := P.length * i + (r - 1) with hm
      have hmi : m / P.length = i := by
        rw [hm, Nat.add_comm, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (by omega)]; simp
      have hmr : m % P.length + 1 = r := by
        have h1 : (P.length * i + (r - 1)) % P.length = r - 1 := by
          rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
        rw [hm, h1]; omega
      apply ih.2.1 P fs 0 ps (rsPush rows (brRowsP k ps)) σ nE nC (j + n) hL m (Nat.zero_le _) (by
        have : P.length * i ≤ P.length * 25 := Nat.mul_le_mul_left _ hi
        omega) (by omega)
      · rw [hmi, hmr, fw_ex, fw_push]; exact hB
      · rw [hmi, fw_push, fw_push]; exact hU
    · intro ps rows σ nE nC j h; simp [pieceOK3] at h
    · intro P fs i r ps rows σ nE nC j h; simp [gPieceOK] at h
    · intro P r ps rows σ nE nC j h; simp [cPieceOK] at h
  | gcyc P pcs ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k post ps rows σ nE nC j hk1 hk9 h hI _ hbr _ _
      simp only [chkRC3, Bool.and_eq_true] at h
      obtain ⟨hst, hL⟩ := h
      obtain ⟨n, r, hn1, hr1, hrP, hI', hn2⟩ := cyc_exit t0 ps (fw rows) σ j nE nC k P hI hbr hst
      have hr : r - 1 + 1 = r := by omega
      apply ih.2.2 P 0 ps (rsPush rows (brRowsP k ps)) σ nE nC (j + n) hL (r - 1) (Nat.zero_le _) (by omega) (by omega)
      · rw [hr, fw_c, fw_push]; exact hI'
      · rw [hr]; exact hn2
    · intro ps rows σ nE nC j h; simp [pieceOK3] at h
    · intro P fs i r ps rows σ nE nC j h; simp [gPieceOK] at h
    · intro P r ps rows σ nE nC j h; simp [cPieceOK] at h
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · intro idx ps rows σ nE nC j h m hm1 hm2 _ _ _ _
      simp only [chkRL3, Nat.beq_eq] at h; omega
    · intro P fs idx ps rows σ nE nC j h m hm1 hm2 _ _ _
      simp only [chkGL, Nat.beq_eq] at h; omega
    · intro P idx ps rows σ nE nC j h m hm1 hm2 _ _ _
      simp only [chkCL, Nat.beq_eq] at h; omega
  | cons c rest ihc ihr =>
    refine ⟨?_, ?_, ?_⟩
    · intro idx ps rows σ nE nC j h m hm1 hm2 n hn1 hI hn2
      simp only [chkRL3, Bool.and_eq_true] at h
      rcases eq_or_lt_of_le hm1 with heq | hlt
      · subst heq
        exact ihc.2.1 _ _ _ nE nC (j + n) h.1 hI (by omega) hn2
      · exact ihr.1 (idx + 1) ps rows σ nE nC j h.2 m hlt hm2 n hn1 hI hn2
    · intro P fs idx ps rows σ nE nC j h m hm1 hm2 hj hB hU
      simp only [chkGL, Bool.and_eq_true] at h
      rcases eq_or_lt_of_le hm1 with heq | hlt
      · subst heq
        exact ihc.2.2.1 P fs _ _ ps rows σ nE nC j h.1 hj hB hU
      · exact ihr.2.1 P fs (idx + 1) ps rows σ nE nC j h.2 m hlt hm2 hj hB hU
    · intro P idx ps rows σ nE nC j h m hm1 hm2 hj hI hpost
      simp only [chkCL, Bool.and_eq_true] at h
      rcases eq_or_lt_of_le hm1 with heq | hlt
      · subst heq
        exact ihc.2.2.2 P _ ps rows σ nE nC j h.1 hj hI hpost
      · exact ihr.2.2 P (idx + 1) ps rows σ nE nC j h.2 m hlt hm2 hj hI hpost

theorem goal_of_chk3 (b : Box) (T : RT3) (h : chkRT3 b T [W5.id] ⟨[], 0⟩ 1 false 0 0 0 = true) (t0 : Tri)
    (hs0 : sorted t0) (hn0 : nondeg t0) (hc : InCell b (zc t0)) : Goal t0 := by
  apply rec3_sound b t0 hs0 hn0 hc T [W5.id] ⟨[], 0⟩ 1 false 0 0 0 0 h _ (fun hf => by simp at hf) (fun hf => by omega)
  refine ⟨hs0, hn0, ⟨fun _ => 1, fun _ _ => by norm_num, by simp, ?_, fun row hr => by simp [fw] at hr⟩, by simp, le_refl _⟩
  simp only [Function.iterate_zero, id, Nat.cast_one]; exact trackP_id (zc t0)

/-! ### assembly lemmas: a tree check split into several kernel checks -/

theorem node_of (b : Box) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : RC3) (ps : List W5) (rows : RS) (σ : Nat) (moved : Bool)
    (post nE nC : Nat) (h1 : chkRC3 b 1 post c1 ps rows σ nE nC = true) (h2 : chkRC3 b 2 post c2 ps rows σ nE nC = true)
    (h3 : chkRC3 b 3 post c3 ps rows σ nE nC = true) (h4 : chkRC3 b 4 post c4 ps rows σ nE nC = true)
    (h5 : chkRC3 b 5 post c5 ps rows σ nE nC = true) (h6 : chkRC3 b 6 post c6 ps rows σ nE nC = true)
    (h7 : chkRC3 b 7 post c7 ps rows σ nE nC = true) (h8 : chkRC3 b 8 post c8 ps rows σ nE nC = true)
    (h9 : chkRC3 b 9 post c9 ps rows σ nE nC = true) :
    chkRT3 b (.node c1 c2 c3 c4 c5 c6 c7 c8 c9) ps rows σ moved post nE nC = true := by
  simp only [chkRT3, h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.and_self]

theorem sub_of (b : Box) (k post : Nat) (t : RT3) (ps : List W5) (rows : RS) (σ nE nC : Nat)
    (h : chkRT3 b t (ps.map (stepW k)) (rsPush rows (brRowsP k ps)) (16 * σ) true 0 (nE + eUp k) (nC + eDn k) = true) :
    chkRC3 b k post (.sub t) ps rows σ nE nC = true := by
  simp only [chkRC3]; exact h

theorem subu_of (b : Box) (k post : Nat) (t : RT3) (ps : List W5) (rows : RS) (σ nE nC : Nat)
    (h : chkRT3 b t (ps.map (stepW k)) (rsPush (rsPush rows (brRowsP k ps)) (unitRows (ps.map (stepW k)))) (16 * σ) true 0
      (nE + eUp k) (nC + eDn k) = true) :
    chkRC3 b k post (.subu t) ps rows σ nE nC = true := by
  simp only [chkRC3]; exact h

theorem grun_of (b : Box) (k post : Nat) (P : List Nat) (fs ld : Nat) (ly : PY) (lp : Nat) (pcs : RL3) (ps : List W5)
    (rows : RS) (σ nE nC : Nat) (hs : gStatic k P fs = true)
    (hp : posOK b (gEll P fs) ld ps (rsPush rows (brRowsP k ps)) (pyL ly) lp = true)
    (hl : chkGL b P fs pcs 0 ps (rsPush rows (brRowsP k ps)) σ nE nC = true) :
    chkRC3 b k post (.grun P fs ld ly lp pcs) ps rows σ nE nC = true := by
  simp only [chkRC3, hs, hp, hl, Bool.and_self]

theorem gl_cons_of (b : Box) (P : List Nat) (fs : Nat) (c : RC3) (rest : RL3) (idx : Nat) (ps : List W5) (rows : RS)
    (σ nE nC : Nat) (h1 : gPieceOK b P fs (idx / P.length) (idx % P.length + 1) c ps rows σ nE nC = true)
    (h2 : chkGL b P fs rest (idx + 1) ps rows σ nE nC = true) :
    chkGL b P fs (.cons c rest) idx ps rows σ nE nC = true := by
  simp only [chkGL, h1, h2, Bool.and_self]

theorem gp_sub_of (b : Box) (P : List Nat) (fs i r : Nat) (t : RT3) (ps : List W5) (rows : RS) (σ nE nC : Nat)
    (hb : gBnd (ga P fs) (gb P fs) i = true)
    (h : chkRT3 b t (gExParts P fs i r ps) (rsEx P fs i r ps rows) (gSig P fs i r σ) true (letter P (r % P.length))
      (nE + upC (P.take r)) (nC + dnC (P.take r)) = true) :
    gPieceOK b P fs i r (.sub t) ps rows σ nE nC = true := by
  simp only [gPieceOK, hb, h, Bool.and_self]

theorem gcyc_of (b : Box) (k post : Nat) (P : List Nat) (pcs : RL3) (ps : List W5) (rows : RS) (σ nE nC : Nat)
    (hs : cStatic k P = true) (hl : chkCL b P pcs 0 ps (rsPush rows (brRowsP k ps)) σ nE nC = true) :
    chkRC3 b k post (.gcyc P pcs) ps rows σ nE nC = true := by
  simp only [chkRC3, hs, hl, Bool.and_self]

theorem cl_cons_of (b : Box) (P : List Nat) (c : RC3) (rest : RL3) (idx : Nat) (ps : List W5) (rows : RS)
    (σ nE nC : Nat) (h1 : cPieceOK b P (idx + 1) c ps rows σ nE nC = true)
    (h2 : chkCL b P rest (idx + 1) ps rows σ nE nC = true) :
    chkCL b P (.cons c rest) idx ps rows σ nE nC = true := by
  simp only [chkCL, h1, h2, Bool.and_self]

theorem cp_sub_of (b : Box) (P : List Nat) (r : Nat) (t : RT3) (ps : List W5) (rows : RS) (σ nE nC : Nat)
    (h : chkRT3 b t (cExParts P r ps) (rsC P r ps rows) (σ * 16 ^ r) true (letter P (r % P.length))
      (nE + upC (P.take r)) (nC + dnC (P.take r)) = true) :
    cPieceOK b P r (.sub t) ps rows σ nE nC = true := by
  simp only [cPieceOK]; exact h

theorem run_of (b : Box) (post : Nat) (pcs : RL3) (ps : List W5) (rows : RS) (σ nE nC : Nat)
    (hl : chkRL3 b pcs 0 ps (rsPush rows (brRowsP 2 ps)) σ nE nC = true) :
    chkRC3 b 2 post (.run pcs) ps rows σ nE nC = true := by
  simp only [chkRC3, hl, Bool.and_self]; rfl

theorem rl_cons_of (b : Box) (c : RC3) (rest : RL3) (idx : Nat) (ps : List W5) (rows : RS) (σ nE nC : Nat)
    (h1 : pieceOK3 b c (wpartsOf (idx / 2) (oddOf idx) ps) (rsRun (idx / 2) (oddOf idx) ps rows)
      (runSig (idx / 2) (oddOf idx) σ) nE nC = true)
    (h2 : chkRL3 b rest (idx + 1) ps rows σ nE nC = true) :
    chkRL3 b (.cons c rest) idx ps rows σ nE nC = true := by
  simp only [chkRL3, h1, h2, Bool.and_self]

theorem rp_sub_of (b : Box) (t : RT3) (ps : List W5) (rows : RS) (σ nE nC : Nat)
    (h : chkRT3 b t ps rows σ true 2 nE nC = true) : pieceOK3 b (.sub t) ps rows σ nE nC = true := by
  simp only [pieceOK3]; exact h

/-! ### cells, walk, main theorem -/

inductive LC3 where
  | hole (x : Nat)
  | tree (t : RT3)

def leafOK3 (b : Box) : LC3 → Bool
  | .hole x => chkHole b x
  | .tree t => bdOK b && chkRT3 b t [W5.id] ⟨[], 0⟩ 1 false 0 0 0

def walkR3 : KT → Box → List LC3 → Option (List LC3)
  | .leaf _ _, b, c :: cs => cond (leafOK3 b c) (some cs) none
  | .leaf _ _, _, [] => none
  | .node d v _ l r, b, cs =>
    match walkR3 l (b.setHi d v) cs with
    | none => none
    | some cs' => walkR3 r (b.setLo d v) cs'

theorem walkR3_ok (z : Zc) : ∀ (t : KT) (b : Box) (cs rest : List LC3), walkR3 t b cs = some rest →
    ∃ c, leafOK3 (look z t b).2.2 c = true := by
  intro t
  induction t with
  | leaf n h =>
    intro b cs rest hw
    rcases cs with _ | ⟨c, cs⟩
    · simp [walkR3] at hw
    · refine ⟨c, ?_⟩
      simp only [walkR3] at hw
      simp only [look]
      cases hc : leafOK3 b c
      · rw [hc] at hw; simp at hw
      · rfl
  | node d v mx l r ihl ihr =>
    intro b cs rest hw
    simp only [walkR3] at hw
    cases hl : walkR3 l (b.setHi d v) cs with
    | none => rw [hl] at hw; simp at hw
    | some cs' =>
      rw [hl] at hw
      simp only [look]
      split_ifs
      · exact ihl _ _ _ hl
      · exact ihr _ _ _ hw

theorem walkR3_append : ∀ (t : KT) (b : Box) (cs rest extra : List LC3), walkR3 t b cs = some rest →
    walkR3 t b (cs ++ extra) = some (rest ++ extra) := by
  intro t
  induction t with
  | leaf n h =>
    intro b cs rest extra hw
    rcases cs with _ | ⟨c, cs⟩
    · simp [walkR3] at hw
    · cases hc : leafOK3 b c
      · simp [walkR3, hc] at hw
      · simp only [walkR3, hc, cond, Option.some.injEq] at hw
        simp only [List.cons_append, walkR3, hc, cond, hw]
  | node d v mx l r ihl ihr =>
    intro b cs rest extra hw
    simp only [walkR3] at hw ⊢
    cases hl : walkR3 l (b.setHi d v) cs with
    | none => rw [hl] at hw; simp at hw
    | some cs' =>
      rw [hl] at hw
      rw [ihl _ _ _ _ hl]
      exact ihr _ _ _ _ hw

theorem walk_one (b : Box) (n : Nat) (t : RT3) (hb : bdOK b = true)
    (h : chkRT3 b t [W5.id] ⟨[], 0⟩ 1 false 0 0 0 = true) : walkR3 (KT.leaf n false) b [.tree t] = some [] := by
  simp [walkR3, leafOK3, hb, h, cond]

theorem walkR3_node (d v mx : Nat) (l r : KT) (b : Box) (cl cr : List LC3)
    (hl : walkR3 l (b.setHi d v) cl = some []) (hr : walkR3 r (b.setLo d v) cr = some []) :
    walkR3 (.node d v mx l r) b (cl ++ cr) = some [] := by
  simp only [walkR3]
  rw [walkR3_append _ _ _ _ _ hl]
  simpa using hr

theorem recovery_of_cert3 (kt : KT) (cs : List LC3) (hw : walkR3 kt rootBox cs = some []) :
    Recovery 169869312 := by
  intro t hs hn hfar
  have hv := validZ_of t hs hn
  have hst := strip_of_far t hs hn hfar
  set z := zc t
  set L := look z kt rootBox with hL
  have hLbox : inBox G L.2.2 z := look_mem z kt rootBox (inBox_root hv)
  obtain ⟨c, hc⟩ := walkR3_ok z kt rootBox cs [] hw
  rw [← hL] at hc
  cases c with
  | hole x =>
    exact (hole_sound _ x hc z hv.lam (cons_of_box hv hLbox (strip_of_s hv hst hLbox))).elim
  | tree T =>
    simp only [leafOK3, bdOK, Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hT⟩ := hc
    have hcell : InCell L.2.2 z := inCell_of hv hLbox (strip_of_s hv hst hLbox)
      ⟨le_trans h1 h2, h2, le_trans h3 h4, h4⟩
    exact goal_of_chk3 L.2.2 T hT t hs hn hcell

/-- the conditional main theorem (recovery trees with symbolic Rx runs and generic neutral-word runs) -/
theorem nm_converges_of_reccert3 (kt : KT) (cs : List LC3) (hw : walkR3 kt rootBox cs = some [])
    (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :
    Filter.Tendsto (fun k => (traj t0 k).p1) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p2) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p3) Filter.atTop (nhds 0) :=
  nm_converges_of_recovery 169869312 (recovery_of_cert3 kt cs hw) t0 h0 hn0

end NMR3

#print axioms NMR3.nm_converges_of_reccert3
