import NMRunGen
open NM NMC NMS NMR NMR2

/-! Generic neutral-word runs, part 2: the exit of a maximal run as a multi-part state. -/

namespace NMR3

def upartsE (E0 E1 E2 : W5) (ps : List W5) : List W5 :=
  ps.map (applyM E0) ++ ps.map (applyM E1) ++ ps.map (applyM E2)

theorem length_upartsE (E0 E1 E2 : W5) (ps : List W5) : (upartsE E0 E1 E2 ps).length = 3 * ps.length := by
  simp [upartsE]; ring

theorem nth_eq_getElem? {α : Type} : ∀ (l : List α) (q : Nat), q < l.length → nth l q = l[q]?
  | [], _, hq => by simp at hq
  | a :: l, 0, _ => rfl
  | a :: l, q + 1, hq => by
    simp only [nth, List.getElem?_cons_succ]; exact nth_eq_getElem? l q (by simp at hq; omega)

theorem gW_upartsE (E0 E1 E2 : W5) (ps : List W5) (e p : Nat) (he : e < 3) (hp : p < ps.length) :
    gW (upartsE E0 E1 E2 ps) (e * ps.length + p) =
      applyM (if e = 0 then E0 else if e = 1 then E1 else E2) (gW ps p) := by
  obtain ⟨x, hx⟩ := nth_lt ps p hp
  have hlen : e * ps.length + p < (upartsE E0 E1 E2 ps).length := by rw [length_upartsE]; nlinarith
  simp only [gW, nth_eq_getElem? _ _ hlen, nth_eq_getElem? _ _ hp] at hx ⊢
  interval_cases e
  · simp only [upartsE, zero_mul, zero_add, List.append_assoc]
    rw [List.getElem?_append_left (by simpa using hp)]; simp [hx]
  · simp only [upartsE, one_mul, List.append_assoc]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp; omega)]; simp [hx]
  · simp only [upartsE, List.append_assoc]
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.getElem?_map]
    rw [show 2 * ps.length + p - ps.length - ps.length = p by omega]; simp [hx]

theorem track_upartsE (E0 E1 E2 : W5) (ps : List W5) (c : Nat → ℝ) (z0 z u : Zc) (σ S : ℝ) (l0 l1 l2 : ℝ)
    (hnp : 0 < ps.length) (htr : TrackP ps c z0 z σ)
    (htri : S * u.d2 = l0 * (evalE E0 z).d2 + l1 * (evalE E1 z).d2 + l2 * (evalE E2 z).d2 ∧
      S * u.d3 = l0 * (evalE E0 z).d3 + l1 * (evalE E1 z).d3 + l2 * (evalE E2 z).d3 ∧
      S * u.a = l0 * (evalE E0 z).a + l1 * (evalE E1 z).a + l2 * (evalE E2 z).a ∧
      S * u.b = l0 * (evalE E0 z).b + l1 * (evalE E1 z).b + l2 * (evalE E2 z).b ∧
      S * u.c = l0 * (evalE E0 z).c + l1 * (evalE E1 z).c + l2 * (evalE E2 z).c) :
    TrackP (upartsE E0 E1 E2 ps) (triW ps.length l0 l1 l2 c) z0 u (S * σ) := by
  intro r hr
  rw [length_upartsE]
  set Es : Nat → W5 := fun e => if e = 0 then E0 else if e = 1 then E1 else E2
  rw [sum3_triW ps.length hnp l0 l1 l2 c (fun e p => evz ((applyM (Es e) (gW ps p)).get r) z0)
    (fun q => evz ((gW (upartsE E0 E1 E2 ps) q).get r) z0) (fun e p he hp => by simp only [gW_upartsE E0 E1 E2 ps e p he hp, Es])]
  have inner : ∀ e, ∑ p ∈ Finset.range ps.length, c p * evz ((applyM (Es e) (gW ps p)).get r) z0 =
      σ * zco (evalE (Es e) z) r := by
    intro e
    have : ∀ p ∈ Finset.range ps.length, c p * evz ((applyM (Es e) (gW ps p)).get r) z0 =
        c p * evz (comb5 ((Es e).get r) (gW ps p)) z0 := by intro p _; rw [applyM_get _ _ r hr]
    rw [Finset.sum_congr rfl this, comb_trackP ps c z0 z σ htr, zco_evalE _ _ r hr]
  rw [inner 0, inner 1, inner 2]
  have := tri3_coord htri r hr
  simp only [Es, if_pos, show (1 : Nat) ≠ 0 from by norm_num, show (2 : Nat) ≠ 0 from by norm_num,
    show (2 : Nat) ≠ 1 from by norm_num, if_false, if_true]
  linear_combination σ * this

/-- rows asserting that every coordinate of the tracked state is nonnegative -/
def unitRows (qs : List W5) : List (List F5) := (List.range 5).map (fun r => qs.map (comb5 (unitF r)))

theorem unitRows_ok (qs : List W5) (c : Nat → ℝ) (z0 w : Zc) (σ : ℝ) (hσ : 0 ≤ σ) (htr : TrackP qs c z0 w σ)
    (hw : 0 ≤ w.d2 ∧ 0 ≤ w.d3 ∧ 0 ≤ w.a ∧ 0 ≤ w.b ∧ 0 ≤ w.c) : RowsOK (unitRows qs) c qs.length z0 := by
  intro row hrow
  simp only [unitRows, List.mem_map, List.mem_range] at hrow
  obtain ⟨r, hr, rfl⟩ := hrow
  have : ∀ q ∈ Finset.range qs.length, c q * evz (gF (qs.map (comb5 (unitF r))) q) z0 =
      c q * evz (comb5 (unitF r) (gW qs q)) z0 := by
    intro q hq; rw [gF_map _ _ _ (Finset.mem_range.mp hq)]
  rw [Finset.sum_congr rfl this, comb_trackP qs c z0 w σ htr, unitF_ev r hr]
  have hz : 0 ≤ zco w r := by
    interval_cases r <;> simp only [zco] <;> linarith [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2]
  positivity

/-- replicated rows stay valid for the tripled weights -/
theorem rep_ok (ps : List W5) (rows : List (List F5)) (c : Nat → ℝ) (z0 : Zc) (l0 l1 l2 : ℝ)
    (hnp : 0 < ps.length) (hl : l0 + l1 + l2 = 1) (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2)
    (hrw : RowsOK rows c ps.length z0) :
    RowsOK (rows.map (repRow ps.length)) (triW ps.length l0 l1 l2 c) (3 * ps.length) z0 := by
  intro row hrow
  simp only [List.mem_map] at hrow
  obtain ⟨r0, hr0, rfl⟩ := hrow
  have e := sum3_triW ps.length hnp l0 l1 l2 c (fun _ p => evz (gF r0 p) z0)
    (fun q => evz (gF (repRow ps.length r0) q) z0) (fun e p he hp => by simp only [gF_rep ps.length hnp r0 e p he hp])
  rw [e]
  have := hrw r0 hr0
  have : (0 : ℝ) ≤ (l0 + l1 + l2) * ∑ p ∈ Finset.range ps.length, c p * evz (gF r0 p) z0 := mul_nonneg (by linarith) this
  linarith

/-- rows on the current state (functionals of `z`) mapped to the parts -/
def onParts (fs : List F5) (ps : List W5) : List (List F5) := fs.map (fun f => ps.map (comb5 f))

theorem onParts_ok (fs : List F5) (ps : List W5) (c : Nat → ℝ) (z0 z : Zc) (σ : ℝ) (hσ : 0 ≤ σ)
    (htr : TrackP ps c z0 z σ) (h : ∀ f ∈ fs, 0 ≤ evz f z) : RowsOK (onParts fs ps) c ps.length z0 := by
  intro row hrow
  simp only [onParts, List.mem_map] at hrow
  obtain ⟨f, hf, rfl⟩ := hrow
  have : ∀ p ∈ Finset.range ps.length, c p * evz (gF (ps.map (comb5 f)) p) z0 = c p * evz (comb5 f (gW ps p)) z0 := by
    intro p hp; rw [gF_map _ _ _ (Finset.mem_range.mp hp)]
  rw [Finset.sum_congr rfl this, comb_trackP ps c z0 z σ htr]
  exact mul_nonneg hσ (h f hf)

/-! ### run data and the exit theorem -/

def gFF (P : List Nat) (fs : Nat) : F5 := fSel (letter P 0) fs
def gN0 (P : List Nat) : F5 := nRow0 (wFull P)
def gN1 (P : List Nat) : F5 := nRow1 (wFull P)
def gEll (P : List Nat) (fs : Nat) : F5 := ellR (gFF P fs) (gN0 P) (gN1 P)
def gHn (P : List Nat) (fs : Nat) : F5 := hnR (gFF P fs) (gN0 P) (gN1 P)
def ga (P : List Nat) (fs : Nat) : Int := zToI (gFF P fs).c1
def gb (P : List Nat) (fs : Nat) : Int := zToI (gFF P fs).c2

def gStatic (k : Nat) (P : List Nat) (fs : Nat) : Bool :=
  Nat.blt 0 P.length && lettersOK P && Nat.beq (letter P 0) k && nilOK (wFull P) (16 ^ P.length) &&
  Nat.beq (upC P) (dnC P) && decide (0 < ga P fs * ga P fs + gb P fs * gb P fs)

def gUp (P : List Nat) (fs i : Nat) (ps : List W5) : List W5 :=
  upartsE (gE (ga P fs) (gb P fs) (gFF P fs) i 0) (gE (ga P fs) (gb P fs) (gFF P fs) i 1)
    (gE (ga P fs) (gb P fs) (gFF P fs) i 2) ps
def gExParts (P : List Nat) (fs i r : Nat) (ps : List W5) : List W5 := walkParts (P.take r) (gUp P fs i ps)
def gPRows (P : List Nat) (fs i : Nat) : List F5 := pieceRowsG i (gEll P fs) (gHn P fs)
def gExRows (P : List Nat) (fs i r : Nat) (ps : List W5) (rows : List (List F5)) : List (List F5) :=
  rows.map (repRow ps.length) ++ (onParts (gPRows P fs i) ps).map (repRow ps.length) ++ unitRows (gUp P fs i ps) ++
    walkRows (P.take r) (gUp P fs i ps) ++ unitRows (gExParts P fs i r ps)
def gSig (P : List Nat) (fs i r σ : Nat) : Nat := σ * (gS (ga P fs) (gb P fs) i).toNat * 16 ^ r

theorem nth_take {α : Type} : ∀ (l : List α) (r i : Nat), i < r → nth (l.take r) i = nth l i
  | [], _, _, _ => by simp [nth]
  | a :: l, r + 1, 0, _ => rfl
  | a :: l, r + 1, i + 1, h => by simp only [List.take_succ_cons, nth]; exact nth_take l r i (by omega)
  | _ :: _, 0, _, h => by omega

theorem pat_period (P : List Nat) (q i : Nat) (hi : i < P.length) : pat P (P.length * q + i) = letter P i := by
  simp only [pat]; rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

theorem evz_n_rel (F n0 n1 : F5) (z : Zc) :
    (((zToI F.c1) * (zToI F.c1) + (zToI F.c2) * (zToI F.c2) : Int) : ℝ) * evz n0 z =
      -((zToI F.c1 : Int) : ℝ) * evz (ellR F n0 n1) z - ((zToI F.c2 : Int) : ℝ) * evz (hnR F n0 n1) z ∧
    (((zToI F.c1) * (zToI F.c1) + (zToI F.c2) * (zToI F.c2) : Int) : ℝ) * evz n1 z =
      -((zToI F.c2 : Int) : ℝ) * evz (ellR F n0 n1) z + ((zToI F.c1 : Int) : ℝ) * evz (hnR F n0 n1) z := by
  simp only [ellR, hnR, evz_neg, evz_add, evz_smul, Z.val_neg]
  simp only [val_zToI]
  push_cast; constructor <;> ring

theorem grun_exit (t0 : Tri) (ps : List W5) (rows : List (List F5)) (σ j nE nC k : Nat) (P : List Nat) (fs : Nat)
    (hI : InvP t0 ps rows σ j nE nC) (hk : brC k (zc (step^[j] t0))) (hst : gStatic k P fs = true)
    (hpos : 0 < evz (gEll P fs) (zc (step^[j] t0))) :
    ∃ (n i r : Nat), 1 ≤ n ∧ i ≤ 25 ∧ 1 ≤ r ∧ r ≤ P.length ∧
      (gBnd (ga P fs) (gb P fs) i = true →
        InvP t0 (gExParts P fs i r ps) (gExRows P fs i r ps (rows ++ brRowsP k ps)) (gSig P fs i r σ) (j + n)
          (nE + upC (P.take r)) (nC + dnC (P.take r)) ∧
        ¬ brC (letter P (r % P.length)) (zc (step^[j + n] t0))) ∧
      (gBnd (ga P fs) (gb P fs) i = false →
        ∃ c : Nat → ℝ, (∀ p < ps.length, 0 ≤ c p) ∧ (∑ p ∈ Finset.range ps.length, c p = 1) ∧
          RowsOK (rows ++ brRowsP k ps ++ onParts (gPRows P fs i) ps) c ps.length (zc t0)) := by
  classical
  simp only [gStatic, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, decide_eq_true_eq] at hst
  obtain ⟨⟨⟨⟨⟨hP, hl⟩, hk0⟩, hnil⟩, hud⟩, hW⟩ := hst
  obtain ⟨c, hc0, hc1, htr, hrw⟩ := hI.wts
  set tj := step^[j] t0 with htj
  set z := zc tj with hz
  have hnp := np_pos ps c hc1
  set np := ps.length with hnpdef
  have hσ : (0 : ℝ) < σ := by have := hI.sig; exact_mod_cast (show 0 < σ by omega)
  have hrw' : RowsOK (rows ++ brRowsP k ps) c np (zc t0) := rowsOK_append hrw (brRowsP_ok k ps c _ _ _ hσ htr hk)
  set F := gFF P fs; set n0 := gN0 P; set n1 := gN1 P
  set a := ga P fs; set b := gb P fs
  set s : ℝ := 16 ^ P.length with hsdef
  have hs0 : 0 < s := by positivity
  -- the maximal run
  have hex := run_finite_gen P hP hl hnil hud fs tj hI.srt hI.ndg hpos
  set n := Nat.find hex with hndef
  have hn : ¬ brC (pat P n) (zc (step^[n] tj)) := Nat.find_spec hex
  have hmin : ∀ i < n, brC (pat P i) (zc (step^[i] tj)) := by
    intro i hi; have := Nat.find_min hex hi; push_neg at this; exact this
  have hpat0 : pat P 0 = k := by simp only [pat, Nat.zero_mod]; exact hk0
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
  -- the state after q periods
  obtain ⟨hu, hAu⟩ := periods_lin P hP hl hnil hud tj hI.srt hI.ndg q (fun i hi => hmin i (by omega))
  set u := addN n0 n1 s z q with hudef
  have hsu := iter_sorted tj hI.srt hI.ndg (P.length * q)
  have hvu := zc_nonneg _ hsu.1
  rw [hu] at hvu
  -- ρ, τ
  set L := evz (gEll P fs) z; set H := evz (gHn P fs) z
  set ρ : ℝ := q * L / s; set τ : ℝ := q * H / s
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hρ : 0 ≤ ρ := by positivity
  obtain ⟨er0, er1⟩ := evz_n_rel F n0 n1 z
  have h2 : ((a * a + b * b : Int) : ℝ) * (u.d2 - z.d2) = -(a : ℝ) * ρ - (b : ℝ) * τ := by
    simp only [hudef, addN, ρ, τ]; field_simp
    simp only [a, b, ga, gb, L, H, gEll, gHn] at er0 ⊢; linear_combination (q : ℝ) * er0
  have h3 : ((a * a + b * b : Int) : ℝ) * (u.d3 - z.d3) = -(b : ℝ) * ρ + (a : ℝ) * τ := by
    simp only [hudef, addN, ρ, τ]; field_simp
    simp only [a, b, ga, gb, L, H, gEll, gHn] at er1 ⊢; linear_combination (q : ℝ) * er1
  -- the bound F(u) ≥ 0
  have hbu : brC k u := by
    have := hmin (P.length * q) (by omega)
    rw [show P.length * q = P.length * q + 0 by ring, pat_period P q 0 hP] at this
    simp only [Nat.add_zero] at this; rw [hu] at this; rw [← hk0]; exact this
  have hFu := fSel_nonneg k fs u hbu hvu.1 hvu.2.1
  have hF : ρ ≤ evz F z := by
    have e := evz_F_addN F n0 n1 s hs0 z q
    rw [← hk0] at hFu
    have : evz F u = evz F z - ρ := by rw [hudef, e]; rfl
    simp only [F, gFF] at this ⊢; rw [← hudef] at e; linarith
  -- the piece
  obtain ⟨i, hi, hrows⟩ := piece_coverG (gEll P fs) (gHn P fs) z
  have hlo : 1 ≤ i → ((kq (i - 1)).1 : ℝ) * ρ ≤ ((kq (i - 1)).2 : ℝ) * τ := by
    intro h1
    have := hrows (loG (i - 1) (gEll P fs) (gHn P fs)) (by simp [pieceRowsG, h1])
    rw [evz_loG] at this
    have h0 : 0 ≤ (q / s) * (((kq (i - 1)).2 : ℝ) * H - ((kq (i - 1)).1 : ℝ) * L) := mul_nonneg (by positivity) this
    have e1 : ((kq (i - 1)).2 : ℝ) * τ - ((kq (i - 1)).1 : ℝ) * ρ =
        (q / s) * (((kq (i - 1)).2 : ℝ) * H - ((kq (i - 1)).1 : ℝ) * L) := by simp only [ρ, τ]; ring
    linarith
  have hhi : i ≤ 24 → ((kq i).2 : ℝ) * τ ≤ ((kq i).1 : ℝ) * ρ := by
    intro h1
    have := hrows (hiG i (gEll P fs) (gHn P fs)) (by simp [pieceRowsG, h1])
    rw [evz_hiG] at this
    have h0 : 0 ≤ (q / s) * (((kq i).1 : ℝ) * L - ((kq i).2 : ℝ) * H) := mul_nonneg (by positivity) this
    have e1 : ((kq i).1 : ℝ) * ρ - ((kq i).2 : ℝ) * τ = (q / s) * (((kq i).1 : ℝ) * L - ((kq i).2 : ℝ) * H) := by
      simp only [ρ, τ]; ring
    linarith
  refine ⟨n, i, r, hn1, hi, hr1, hrP, ?_, ?_⟩
  swap
  · intro _
    exact ⟨c, hc0, hc1, rowsOK_append hrw' (onParts_ok _ ps c _ z σ hσ.le htr hrows)⟩
  intro hbnd
  obtain ⟨l0, l1, l2, hl0, hl1, hl2, hlsum, htri⟩ :=
    piece_triG a b F z u ρ τ i hi hbnd hW h2 h3 rfl rfl rfl hρ hF hlo hhi hvu.1 hvu.2.1
  have hS := gS_pos a b i hi hbnd hW
  set S := gS a b i with hSdef
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  set c' := triW np l0 l1 l2 c
  have htrU := track_upartsE _ _ _ ps c (zc t0) z u σ (S : ℝ) l0 l1 l2 hnp htr htri
  have hc'0 : ∀ q < 3 * np, 0 ≤ c' q := by
    intro q hq
    simp only [c', triW]
    have hc := hc0 (q % np) (Nat.mod_lt _ hnp)
    split_ifs <;> positivity
  have hc'1 : ∑ q ∈ Finset.range (3 * np), c' q = 1 := by
    have := sum3_triW np hnp l0 l1 l2 c (fun _ _ => 1) (fun _ => 1) (fun _ _ _ _ => rfl)
    simp only [mul_one] at this; rw [this, hc1]; linarith
  -- the prefix walk from u
  have hfol : Follows (step^[P.length * q] tj) (P.take r) := by
    intro i' hi'
    rw [List.length_take, min_eq_left hrP] at hi'
    have := hmin (P.length * q + i') (by omega)
    rw [pat_period P q i' (by omega), iter_add'] at this
    simpa [letter, nth_take P r i' hi'] using this
  have hltake : lettersOK (P.take r) = true := by
    have : ∀ (l : List Nat) (m : Nat), lettersOK l = true → lettersOK (l.take m) = true := by
      intro l; induction l with
      | nil => intro m _; simp [lettersOK]
      | cons x l ih =>
        intro m h; cases m with
        | zero => simp [lettersOK]
        | succ m =>
          simp only [lettersOK, Bool.and_eq_true] at h
          simp only [List.take_succ_cons, lettersOK, Bool.and_eq_true]; exact ⟨h.1, ih m h.2⟩
    exact this P r hl
  have htrU' : TrackP (gUp P fs i ps) c' (zc t0) (zc (step^[P.length * q] tj)) ((S : ℝ) * σ) := by
    rw [hu]; exact htrU
  obtain ⟨w1, w2, w3⟩ := walk_sound (P.take r) hltake _ (gUp P fs i ps) c' (zc t0) ((S : ℝ) * σ) hsu.1 hsu.2
    (by positivity) htrU' hfol
  rw [List.length_take, min_eq_left hrP, ← iter_add', ← hnqr] at w1 w3
  have hlenU : (gUp P fs i ps).length = 3 * np := length_upartsE _ _ _ ps
  have hlenX : (gExParts P fs i r ps).length = 3 * np := by
    simp only [gExParts]; rw [length_walkParts, hlenU]
  have hsn := iter_sorted tj hI.srt hI.ndg n
  refine ⟨⟨?_, ?_, ⟨c', ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [iter_add, ← htj]; exact hsn.1
  · rw [iter_add, ← htj]; exact hsn.2
  · rw [hlenX]; exact hc'0
  · rw [hlenX]; exact hc'1
  · simp only [gSig]
    rw [iter_add, ← htj]
    have e : ((σ * S.toNat * 16 ^ r : Nat) : ℝ) = 16 ^ r * ((S : ℝ) * σ) := by
      have hc : ((S.toNat : ℕ) : ℝ) = (S : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hS.le
      push_cast; rw [hc]; ring
    rw [e]; simp only [gExParts]; exact w1
  · simp only [gExRows]
    rw [hlenX]
    refine rowsOK_append (rowsOK_append (rowsOK_append (rowsOK_append ?_ ?_) ?_) ?_) ?_
    · exact rep_ok ps _ c (zc t0) l0 l1 l2 hnp hlsum hl0 hl1 hl2 hrw'
    · exact rep_ok ps _ c (zc t0) l0 l1 l2 hnp hlsum hl0 hl1 hl2 (onParts_ok _ ps c _ z σ hσ.le htr hrows)
    · have := unitRows_ok (gUp P fs i ps) c' (zc t0) _ _ (by positivity) htrU' (by rw [hu]; exact hvu)
      rwa [hlenU] at this
    · rwa [hlenU] at w2
    · have hv := zc_nonneg _ hsn.1
      have := unitRows_ok (gExParts P fs i r ps) c' (zc t0) _ _ (by positivity) w1 hv
      rwa [hlenX] at this
  · rw [iter_add, ← htj, w3, hAu, hI.area, pow_add, pow_add]; ring
  · simp only [gSig]
    have h1 := hI.sig; have h2 : 1 ≤ S.toNat := by omega
    have h3 : 1 ≤ 16 ^ r := Nat.one_le_pow _ _ (by norm_num)
    calc 1 = 1 * 1 * 1 := by norm_num
      _ ≤ σ * S.toNat * 16 ^ r := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  · rw [iter_add, ← htj]
    have : pat P n = letter P (r % P.length) := by
      simp only [pat]; rw [hnqr, Nat.add_comm, Nat.add_mul_mod_self_left]
    rw [← this]; exact hn

end NMR3
