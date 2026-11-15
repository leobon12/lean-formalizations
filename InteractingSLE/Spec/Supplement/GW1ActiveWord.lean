/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Exist.StagedLaw3Main

/-!
# Lemma GW1's active-word classification: the stop word of one piece

Packet PROVE-T14-GW1W. Lemma GW1, proof (`source/spec/p577-624.md` L949–L971, pp. 618–620). The conditional field
after an ordinary piece of a boundary walk, read in the chart at the piece's stop, is the GFF with the **stop word**
`stopWord κ (c, θ, record)` of PROVE-STAGEDLAW3 (the force word of the piece at the mark positions read from the
record, shifted by `−θχ`). This file proves the deterministic facts about that word that GW1's active-word
classification uses:

* **the exposed left side of the piece and everything left of it stay admissible** (`stopWord_fn_add_lt_of_neg`):
  if the launch word `c` satisfies `c + θχ < λ` left of the seed, so does the stop word, at **every** negative point
  (the left heights of the stop word are `−λ(1 + Σ_{i<m} ρ^{i,L})`, and the left partial sums of an admissible
  flow-line word exceed `−2`, (GW1.1)); and the mirror `stopWord_fn_add_gt_of_pos` for the left walk;
* **the untouched original right ray keeps its heights** (`stopWord_fn_fwdMap`): for a real point `y > 0` alive at
  the stop, the stop word at the image `f_T(y)` equals the launch word at `y` (the right marks are read at
  `markPos`, which is `≤ f_T(y)` exactly for the marks `≤ y`); and the mirror `stopWord_fn_fwdMap_neg`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

namespace InteractingSLE

namespace Theorem14

namespace GW1W

open Exist Exist.StagedLaw Exist.Staged Restart GW1Conn

/-! ### The heights of a force word left and right of the seed -/

section ForceWord

variable {κ : ℝ} {nL nR : ℕ} {pL pR ρL ρR : ℕ → ℝ} {s : ℝ}

theorem rawPos_nL : rawPos nL pL pR nL = 0 := by
  simp [rawPos]

/-- A negative point has at most `nL` positions of a force word strictly left of it. -/
theorem index_forceWord_le_of_neg {y : ℝ} (hy : y < 0) :
    (forceWord κ nL nR pL pR ρL ρR s).index y ≤ nL := by
  unfold BoundaryWord.index
  change ((Finset.range (nL + 1 + nR)).filter fun i => cumMax (rawPos nL pL pR) i < y).card ≤ nL
  calc ((Finset.range (nL + 1 + nR)).filter fun i => cumMax (rawPos nL pL pR) i < y).card
      ≤ (Finset.range nL).card := by
        refine Finset.card_le_card fun i hi => ?_
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_range]
        by_contra hni
        have h1 : cumMax (rawPos nL pL pR) nL ≤ cumMax (rawPos nL pL pR) i :=
          monotone_cumMax _ (not_lt.1 hni)
        have h2 : rawPos nL pL pR nL ≤ cumMax (rawPos nL pL pR) nL := le_cumMax _ nL
        rw [rawPos_nL] at h2
        linarith [hi.2]
    _ = nL := Finset.card_range nL

/-- **The height of a force word at a negative point** is one of its left heights. -/
theorem exists_fn_forceWord_of_neg {y : ℝ} (hy : y < 0) : ∃ m ≤ nL,
    (forceWord κ nL nR pL pR ρL ρR s).fn y = -(Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ Finset.range m, ρL i) - s := by
  have hk := index_forceWord_le_of_neg (κ := κ) (nL := nL) (nR := nR) (pL := pL) (pR := pR) (ρL := ρL)
    (ρR := ρR) (s := s) hy
  refine ⟨nL - (forceWord κ nL nR pL pR ρL ρR s).index y, Nat.sub_le _ _, ?_⟩
  change wordHeight κ nL ρL ρR s ((forceWord κ nL nR pL pR ρL ρR s).index y) = _
  unfold wordHeight
  simp only [hk, ↓reduceIte]

/-- The positions of a force word right of the seed, when the left positions are nonpositive: a positive point has
at least `nL + 1` positions strictly left of it. -/
theorem le_index_forceWord_of_pos (hL0 : ∀ i < nL, pL i ≤ 0) {y : ℝ} (hy : 0 < y) :
    nL + 1 ≤ (forceWord κ nL nR pL pR ρL ρR s).index y := by
  unfold BoundaryWord.index
  change nL + 1 ≤ ((Finset.range (nL + 1 + nR)).filter fun i => cumMax (rawPos nL pL pR) i < y).card
  have hle : ∀ k ≤ nL, cumMax (rawPos nL pL pR) k ≤ 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      change rawPos nL pL pR 0 ≤ 0
      unfold rawPos
      split_ifs with h1 h2
      · exact hL0 _ (by omega)
      · exact le_rfl
      · omega
    | succ k ih =>
      intro hk
      change max (cumMax (rawPos nL pL pR) k) (rawPos nL pL pR (k + 1)) ≤ 0
      refine max_le (ih (by omega)) ?_
      unfold rawPos
      split_ifs with h1 h2
      · exact hL0 _ (by omega)
      · exact le_rfl
      · omega
  calc nL + 1 = (Finset.range (nL + 1)).card := (Finset.card_range _).symm
    _ ≤ _ := by
        refine Finset.card_le_card fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, lt_of_le_of_lt (hle i (by omega)) hy⟩

/-- **The height of a force word at a positive point** is one of its right heights (left positions nonpositive). -/
theorem exists_fn_forceWord_of_pos (hL0 : ∀ i < nL, pL i ≤ 0) {y : ℝ} (hy : 0 < y) : ∃ m ≤ nR,
    (forceWord κ nL nR pL pR ρL ρR s).fn y = Real.pi / Real.sqrt κ * (1 + ∑ i ∈ Finset.range m, ρR i) - s := by
  have hk := le_index_forceWord_of_pos (κ := κ) (nR := nR) (pR := pR) (ρL := ρL) (ρR := ρR) (s := s) hL0 hy
  have hk' : (forceWord κ nL nR pL pR ρL ρR s).index y ≤ nL + 1 + nR := BoundaryWord.index_le _ _
  refine ⟨(forceWord κ nL nR pL pR ρL ρR s).index y - nL - 1, by omega, ?_⟩
  change wordHeight κ nL ρL ρR s ((forceWord κ nL nR pL pR ρL ρR s).index y) = _
  unfold wordHeight
  simp only [show ¬ (forceWord κ nL nR pL pR ρL ρR s).index y ≤ nL by omega, ↓reduceIte]

end ForceWord

/-! ### The position of a mark read from the driver, against the real flow -/

section MarkPos

variable {w : ℝ → ℝ} {T : ℝ}

/-- The alive real points at time `T` and the real flow have the real-half structure. -/
theorem isRealHalf_of (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) :
    IsRealHalf (fun y : ℝ => ∃ u, IsForwardSol w (y : ℂ) T u) (fun y => (fwdMap w T y).re) :=
  isRealHalf_fwd hw hw0 hT

theorem markTerm_eq {x : ℝ} {q : ℚ} (hxq : x < q) (hq : ∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u) :
    markTerm w T x q = (((fwdMap w T ((q : ℝ) : ℂ)).re : ℝ) : EReal) := by
  classical
  unfold markTerm
  exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hxq, hq⟩)

/-- Some alive rational point lies right of any `x`. -/
theorem exists_rat_alive (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) (x : ℝ) :
    ∃ q : ℚ, x < q ∧ ∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u := by
  obtain ⟨M, hM⟩ := (isRealHalf_of hw hw0 hT).2.2.1
  obtain ⟨q, hq⟩ := exists_rat_gt (max M x)
  exact ⟨q, lt_of_le_of_lt (le_max_right _ _) hq, hM _ (lt_of_le_of_lt (le_max_left _ _) hq).le⟩

theorem iInf_markTerm_ne_top (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) (x : ℝ) :
    (⨅ q : ℚ, markTerm w T x q) ≠ ⊤ := by
  obtain ⟨q, hxq, hq⟩ := exists_rat_alive hw hw0 hT x
  refine ne_top_of_le_ne_top (EReal.coe_ne_top ((fwdMap w T ((q : ℝ) : ℂ)).re)) ?_
  rw [← markTerm_eq hxq hq]
  exact iInf_le _ q

/-- A lower bound of the flow at the alive rational points right of `x` bounds `markPos w T x`. -/
theorem le_markPos (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x c : ℝ}
    (hc : ∀ q : ℚ, x < q → (∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u) → c ≤ (fwdMap w T ((q : ℝ) : ℂ)).re) :
    c ≤ markPos w T x := by
  have h : (c : EReal) ≤ ⨅ q : ℚ, markTerm w T x q := le_iInf fun q => by
    classical
    unfold markTerm
    split_ifs with hq
    · exact_mod_cast hc q hq.1 hq.2
    · exact le_top
  have := EReal.toReal_le_toReal h (EReal.coe_ne_bot c) (iInf_markTerm_ne_top hw hw0 hT x)
  rwa [EReal.toReal_coe] at this

/-- `markPos` is nonnegative for a nonnegative starting point. -/
theorem markPos_nonneg (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ markPos w T x :=
  le_markPos hw hw0 hT fun q hxq hq =>
    ((isRealHalf_of hw hw0 hT).2.2.2.1 q (lt_of_le_of_lt hx hxq) hq).le

/-- `markPos w T x` is at most the flow at every alive rational point right of `x` (for `x ≥ 0`). -/
theorem markPos_le_rat (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : 0 ≤ x) {q : ℚ}
    (hxq : x < q) (hq : ∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u) :
    markPos w T x ≤ (fwdMap w T ((q : ℝ) : ℂ)).re := by
  have h0 : (0 : EReal) ≤ ⨅ q : ℚ, markTerm w T x q := le_iInf fun q' => by
    classical
    unfold markTerm
    split_ifs with hq'
    · exact_mod_cast ((isRealHalf_of hw hw0 hT).2.2.2.1 q' (lt_of_le_of_lt hx hq'.1) hq'.2).le
    · exact le_top
  have h1 : (⨅ q : ℚ, markTerm w T x q) ≤ (((fwdMap w T ((q : ℝ) : ℂ)).re : ℝ) : EReal) := by
    rw [← markTerm_eq hxq hq]
    exact iInf_le _ q
  have := EReal.toReal_le_toReal h1 (ne_bot_of_le_ne_bot EReal.zero_ne_bot h0) (EReal.coe_ne_top _)
  rwa [EReal.toReal_coe] at this

/-- **A mark lies at or left of an alive point exactly when its position is at most the point's image.** -/
theorem markPos_le_iff (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    (hay : ∃ u, IsForwardSol w (y : ℂ) T u) : markPos w T x ≤ (fwdMap w T y).re ↔ x ≤ y := by
  have hH := isRealHalf_of hw hw0 hT
  constructor
  · intro hle
    by_contra hyx
    push Not at hyx
    have hax : ∃ u, IsForwardSol w (x : ℂ) T u := hH.2.1 y x hy hyx hay
    have hfx : (fwdMap w T x).re ≤ markPos w T x := le_markPos hw hw0 hT fun q hxq hq =>
      (hH.2.2.2.2.1 x q (hy.trans hyx) hxq hax hq).le
    have hlt := hH.2.2.2.2.1 y x hy hyx hay hax
    linarith
  · intro hxy
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨η, hη, hηf⟩ := hH.2.2.2.2.2.1 y hy hay ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y < y + η by linarith)
    have haq : ∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u := hH.2.1 y q hy hq1 hay
    have h1 := markPos_le_rat hw hw0 hT hx (lt_of_le_of_lt hxy hq1) haq
    have h2 := hηf q haq (by rw [abs_lt]; constructor <;> linarith)
    rw [abs_lt] at h2
    linarith [h2.2]

/-- `markPos` is monotone in the starting point (on `[0, ∞)`). -/
theorem markPos_mono (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x ≤ x') :
    markPos w T x ≤ markPos w T x' :=
  le_markPos hw hw0 hT fun _ hq haq => markPos_le_rat hw hw0 hT hx (lt_of_le_of_lt hxx' hq) haq

/-- `markPosL` is nonpositive for a nonpositive starting point. -/
theorem markPosL_nonpos (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : x ≤ 0) :
    markPosL w T x ≤ 0 := by
  unfold markPosL
  have := markPos_nonneg (w := fun s => -w s) hw.neg (by simp [hw0]) hT (x := -x) (by linarith)
  linarith

/-- `markPosL` is monotone in the starting point (on `(−∞, 0]`). -/
theorem markPosL_mono (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x x' : ℝ} (hx' : x' ≤ 0)
    (hxx' : x ≤ x') : markPosL w T x ≤ markPosL w T x' := by
  unfold markPosL
  have := markPos_mono (w := fun s => -w s) hw.neg (by simp [hw0]) hT (x := -x') (x' := -x) (by linarith)
    (by linarith)
  linarith

/-- **A left mark lies at or right of an alive negative point exactly when its position is at least the point's
image** (the mirror of `markPos_le_iff`, by reflection). -/
theorem le_markPosL_iff (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x y : ℝ} (hx : x ≤ 0) (hy : y < 0)
    (hay : ∃ u, IsForwardSol w (y : ℂ) T u) : (fwdMap w T y).re ≤ markPosL w T x ↔ y ≤ x := by
  have hay' : ∃ u, IsForwardSol (-w) ((-y : ℝ) : ℂ) T u := (alive_neg_iff w T (-y)).2 (by rwa [neg_neg])
  have h := markPos_le_iff (w := -w) hw.neg (by simp [hw0]) hT (x := -x) (y := -y) (by linarith) (by linarith) hay'
  have hr : (fwdMap (-w) T ((-y : ℝ) : ℂ)).re = -(fwdMap w T y).re := by
    rw [QuantumZipper.F1.fwdMap_reflect_ofReal w hT y, Complex.neg_re]
  have e : markPosL w T x = -markPos (-w) T (-x) := rfl
  rw [hr] at h
  rw [e]
  constructor
  · intro h1
    have := h.1 (by linarith)
    linarith
  · intro h1
    have := h.2 (by linarith)
    linarith

end MarkPos

/-! ### The stop word -/

section StopWord

variable {κ : ℝ}

/-- The positions of the stop word (left marks at `markPosL`, right marks at `markPos`) are in mark order. -/
theorem isMarkOrder_stopWord (c : BoundaryWord) (r : RecData) :
    IsMarkOrder (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0)
      (fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) := by
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hord := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hxL : ∀ i (hi : i < flowLineNL c.fn c.jumps 0),
      (padFL 0 0 c.fn c.jumps).1.1 i = flowLineXL c.fn c.jumps 0 ⟨i, hi⟩ := fun i hi =>
    padFL_fst_fst_fin c.fn c.jumps ⟨i, hi⟩
  have hxR : ∀ j (hj : j < flowLineNR c.fn c.jumps 0),
      (padFL 0 0 c.fn c.jumps).1.2 j = flowLineXR c.fn c.jumps 0 ⟨j, hj⟩ := fun j hj =>
    padFL_fst_snd_fin c.fn c.jumps ⟨j, hj⟩
  refine ⟨fun i j hij hj => ?_, fun i hi => ?_, fun i j hij hj => ?_, fun i hi => ?_⟩
  · beta_reduce
    rw [hxL i (by omega), hxL j hj]
    exact markPosL_mono hw hw0 hT (hord.2.1 _)
      (hord.1 (show (⟨i, by omega⟩ : Fin (flowLineNL c.fn c.jumps 0)) ≤ ⟨j, hj⟩ from hij))
  · beta_reduce
    rw [hxL i hi]
    exact markPosL_nonpos hw hw0 hT (hord.2.1 _)
  · beta_reduce
    rw [hxR i (by omega), hxR j hj]
    exact markPos_mono hw hw0 hT (hord.2.2.2 _)
      (hord.2.2.1 (show (⟨i, by omega⟩ : Fin (flowLineNR c.fn c.jumps 0)) ≤ ⟨j, hj⟩ from hij))
  · beta_reduce
    rw [hxR i hi]
    exact markPos_nonneg hw hw0 hT (hord.2.2.2 _)

/-- A sum of the first `j + 1` padded left weights is a left partial sum of the flow-line word. -/
theorem sum_range_padFL_left (κ θ : ℝ) (c : BoundaryWord) {j : ℕ} (hj : j < flowLineNL c.fn c.jumps 0) :
    ∑ i ∈ Finset.range (j + 1), (padFL κ θ c.fn c.jumps).2.1 i =
      ∑ l ∈ univ.filter (fun l : Fin (flowLineNL c.fn c.jumps 0) => l ≤ ⟨j, hj⟩),
        flowLineRhoL κ c.fn c.jumps 0 θ l := by
  rw [show (univ.filter fun l : Fin (flowLineNL c.fn c.jumps 0) => l ≤ ⟨j, hj⟩) =
      univ.filter fun l : Fin (flowLineNL c.fn c.jumps 0) => (l : ℕ) ≤ j from
    Finset.filter_congr fun l _ => Fin.le_def]
  rw [Finset.sum_congr rfl fun l _ => (padFL_snd_fst_fin κ θ c.fn c.jumps l).symm,
    sum_fin_filter_eq (flowLineNL c.fn c.jumps 0) (fun l => l ≤ j) (padFL κ θ c.fn c.jumps).2.1]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- A sum of the first `j + 1` padded right weights is a right partial sum of the flow-line word. -/
theorem sum_range_padFL_right (κ θ : ℝ) (c : BoundaryWord) {j : ℕ} (hj : j < flowLineNR c.fn c.jumps 0) :
    ∑ i ∈ Finset.range (j + 1), (padFL κ θ c.fn c.jumps).2.2 i =
      ∑ l ∈ univ.filter (fun l : Fin (flowLineNR c.fn c.jumps 0) => l ≤ ⟨j, hj⟩),
        flowLineRhoR κ c.fn c.jumps 0 θ l := by
  rw [show (univ.filter fun l : Fin (flowLineNR c.fn c.jumps 0) => l ≤ ⟨j, hj⟩) =
      univ.filter fun l : Fin (flowLineNR c.fn c.jumps 0) => (l : ℕ) ≤ j from
    Finset.filter_congr fun l _ => Fin.le_def]
  rw [Finset.sum_congr rfl fun l _ => (padFL_snd_snd_fin κ θ c.fn c.jumps l).symm,
    sum_fin_filter_eq (flowLineNR c.fn c.jumps 0) (fun l => l ≤ j) (padFL κ θ c.fn c.jumps).2.2]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- **The left side of the stop word stays admissible** (Lemma GW1, (GW1.1); right walk): if the launch word satisfies
`c + θχ < λ` left of the seed, the stop word satisfies it at every negative point, for every record. -/
theorem stopWord_fn_add_lt_of_neg (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ}
    (hL : ∀ y, y < 0 → y ∉ c.jumps → c.fn y + θ * chiC κ < sleLambda κ) (r : RecData) {y : ℝ} (hy : y < 0) :
    (stopWord κ (c, θ, r)).fn y + θ * chiC κ < sleLambda κ := by
  obtain ⟨m, hm, he⟩ := exists_fn_forceWord_of_neg (κ := κ) (nL := flowLineNL c.fn c.jumps 0)
    (nR := flowLineNR c.fn c.jumps 0)
    (pL := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
    (pR := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))
    (ρL := (padFL κ θ c.fn c.jumps).2.1) (ρR := (padFL κ θ c.fn c.jumps).2.2) (s := θ * chiC κ) hy
  have hS : -2 < ∑ i ∈ Finset.range m, (padFL κ θ c.fn c.jumps).2.1 i := by
    rcases m with _ | j
    · simp
    · rw [sum_range_padFL_left κ θ c (by omega)]
      exact neg_two_lt_sum_flowLineRhoL_theta hκ c.isPiecewiseConstantBoundaryData hL _
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  change (forceWord κ _ _ _ _ _ _ _).fn y + _ < _
  rw [he]
  change -sleLambda κ * (1 + ∑ i ∈ Finset.range m, (padFL κ θ c.fn c.jumps).2.1 i) - θ * chiC κ +
    θ * chiC κ < sleLambda κ
  nlinarith

/-- **The right side of the stop word stays admissible** (left walk, the mirror of `stopWord_fn_add_lt_of_neg`). -/
theorem stopWord_fn_add_gt_of_pos (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ}
    (hR : ∀ y, 0 < y → y ∉ c.jumps → -sleLambda κ < c.fn y + θ * chiC κ) (r : RecData) {y : ℝ} (hy : 0 < y) :
    -sleLambda κ < (stopWord κ (c, θ, r)).fn y + θ * chiC κ := by
  obtain ⟨m, hm, he⟩ := exists_fn_forceWord_of_pos (κ := κ) (nL := flowLineNL c.fn c.jumps 0)
    (nR := flowLineNR c.fn c.jumps 0)
    (pL := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
    (pR := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))
    (ρL := (padFL κ θ c.fn c.jumps).2.1) (ρR := (padFL κ θ c.fn c.jumps).2.2) (s := θ * chiC κ)
    (isMarkOrder_stopWord c r).2.1 hy
  have hS : -2 < ∑ i ∈ Finset.range m, (padFL κ θ c.fn c.jumps).2.2 i := by
    rcases m with _ | j
    · simp
    · rw [sum_range_padFL_right κ θ c (by omega)]
      exact neg_two_lt_sum_flowLineRhoR_theta hκ c.isPiecewiseConstantBoundaryData hR _
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  change -sleLambda κ < (forceWord κ _ _ _ _ _ _ _).fn y + _
  rw [he]
  change -sleLambda κ < sleLambda κ * (1 + ∑ i ∈ Finset.range m, (padFL κ θ c.fn c.jumps).2.2 i) -
    θ * chiC κ + θ * chiC κ
  nlinarith

/-- **The untouched right ray keeps its heights** (Lemma GW1, p. 620: "The other side's untouched original right
interval …"): for a real point `y > 0` alive at the stop, the stop word at its image `f_T(y)` is the launch word at
`y` (off the jumps). The right marks `x ≤ y` are exactly those read at positions `markPos ≤ f_T(y)`. -/
theorem stopWord_fn_fwdMap (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {y : ℝ} (hy : 0 < y)
    (hay : ∃ u, IsForwardSol (rdrv r) (y : ℂ) (rtime r) u) (hyJ : y ∉ c.jumps)
    (hzJ : (fwdMap (rdrv r) (rtime r) y).re ∉ (stopWord κ (c, θ, r)).jumps) :
    (stopWord κ (c, θ, r)).fn (fwdMap (rdrv r) (rtime r) y).re = c.fn y := by
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hord := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hz : 0 < (fwdMap (rdrv r) (rtime r) y).re := (isRealHalf_of hw hw0 hT).2.2.2.1 y hy hay
  have h1 := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ)
    (isMarkOrder_stopWord c r) hzJ hz.ne'
  have h2 := forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 θ hy.ne'
    (by rwa [add_zero])
  rw [add_zero] at h2
  change (forceWord κ _ _ _ _ _ _ _).fn _ = _
  rw [h1]
  have key : forceBoundaryData κ (fun i : Fin (flowLineNL c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.1 i)
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.2 j)
      (fun i : Fin (flowLineNL c.fn c.jumps 0) =>
        markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j : Fin (flowLineNR c.fn c.jumps 0) =>
        markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) (fwdMap (rdrv r) (rtime r) y).re =
      forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) y := by
    unfold forceBoundaryData
    simp only [not_lt.2 hz.le, not_lt.2 hy.le, ↓reduceIte]
    congr 2
    refine Finset.sum_congr (Finset.filter_congr fun j _ => ?_) fun j _ => padFL_snd_snd_fin κ θ c.fn c.jumps j
    rw [padFL_fst_snd_fin c.fn c.jumps j]
    exact markPos_le_iff hw hw0 hT (hord.2.2.2 j) hy hay
  rw [key, h2]
  ring

/-- The left marks of a flow-line word are the seed `0` or genuine jumps. -/
theorem flowLineXL_mem (b : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNL b J 0)) :
    flowLineXL b J 0 i = 0 ∨ flowLineXL b J 0 i ∈ J := by
  obtain ⟨m, hm⟩ := i
  cases m with
  | zero => exact Or.inl rfl
  | succ m =>
    right
    have hm' : m < ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < 0)).card := by
      unfold flowLineNL at hm; omega
    change ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < 0)).orderEmbOfFin rfl
      (Fin.rev ⟨m, hm'⟩) - 0 ∈ J
    rw [sub_zero]
    have h := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < 0)) rfl
      (Fin.rev ⟨m, hm'⟩)
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).1

/-- **The untouched left ray keeps its heights** (the mirror of `stopWord_fn_fwdMap`): for a real point `y < 0` alive
at the stop, the stop word at its image `f_T(y)` is the launch word at `y` (off the jumps). -/
theorem stopWord_fn_fwdMap_neg (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {y : ℝ} (hy : y < 0)
    (hay : ∃ u, IsForwardSol (rdrv r) (y : ℂ) (rtime r) u) (hyJ : y ∉ c.jumps)
    (hzJ : (fwdMap (rdrv r) (rtime r) y).re ∉ (stopWord κ (c, θ, r)).jumps) :
    (stopWord κ (c, θ, r)).fn (fwdMap (rdrv r) (rtime r) y).re = c.fn y := by
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hord := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hmo := isMarkOrder_stopWord c r
  have hz : (fwdMap (rdrv r) (rtime r) y).re < 0 := by
    have hH := (isRealFlow_fwd hw hw0 hT).2
    have hal : ∃ u, IsForwardSol (rdrv r) (((-(-y) : ℝ)) : ℂ) (rtime r) u := by rwa [neg_neg]
    have := hH.2.2.2.1 (-y) (by linarith) hal
    simp only [neg_neg] at this
    linarith
  have h1 := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hmo hzJ hz.ne
  have h2 := forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 θ hy.ne (by rwa [add_zero])
  rw [add_zero] at h2
  change (forceWord κ _ _ _ _ _ _ _).fn _ = _
  rw [h1]
  have key : forceBoundaryData κ (fun i : Fin (flowLineNL c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.1 i)
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.2 j)
      (fun i : Fin (flowLineNL c.fn c.jumps 0) =>
        markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j : Fin (flowLineNR c.fn c.jumps 0) =>
        markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) (fwdMap (rdrv r) (rtime r) y).re =
      forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) y := by
    unfold forceBoundaryData
    simp only [hz, hy, ↓reduceIte]
    congr 2
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun i _ => padFL_snd_fst_fin κ θ c.fn c.jumps i
    rw [padFL_fst_fst_fin c.fn c.jumps i]
    -- `f(y)` is not the position of the mark, and `y` is not the mark
    have hne1 : (fwdMap (rdrv r) (rtime r) y).re ≠ markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i) := by
      intro he
      apply hzJ
      refine BoundaryWord.mem_jumps.2 ⟨flowLineNL c.fn c.jumps 0 - 1 - i, by
        change _ < flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0; omega, ?_⟩
      change cumMax (rawPos _ _ _) _ = _
      rw [cumMax_rawPos hmo (by omega), he]
      unfold rawPos
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      beta_reduce
      rw [show flowLineNL c.fn c.jumps 0 - 1 - (flowLineNL c.fn c.jumps 0 - 1 - (i : ℕ)) = i by omega,
        padFL_fst_fst_fin c.fn c.jumps i]
    have hne2 : y ≠ flowLineXL c.fn c.jumps 0 i := by
      intro he
      rcases flowLineXL_mem c.fn c.jumps i with h0 | hJ
      · rw [he] at hy; linarith
      · exact hyJ (he ▸ hJ)
    have hiff := le_markPosL_iff hw hw0 hT (hord.2.1 i) hy hay
    constructor
    · intro hlt
      exact lt_of_le_of_ne (hiff.1 hlt.le) hne2
    · intro hlt
      exact lt_of_le_of_ne (hiff.2 hlt.le) hne1
  rw [key, h2]
  ring

end StopWord

end GW1W

end Theorem14

end InteractingSLE
