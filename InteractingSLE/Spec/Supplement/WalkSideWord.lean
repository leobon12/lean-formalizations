/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSideSpec

/-!
# Theorem 1.4's walk leaves: the stop word on the two sides of a prefix

Packet PROVE-T14-WALKSIDE. Lemma GW3, proof (`source/spec/p625-671.md` L218, p. 636): "On an ordinary selected subarc
the incoming own germ is, respectively, `λ − (π/2)χ = Λ` or `−λ + (π/2)χ = −Λ`." After an angle-`θ` piece stopped at
own time `τ`, the conditional field in the prefix chart has the boundary data of the **stop word**
(`Exist.StagedLaw.stopWord`, PROVE-STAGEDLAW3): the force word of the piece with its marks read from the record,
shifted by `−θχ`. Every left mark of the stop word lies at or left of the images of the alive real points left of the
piece (it is a supremum of such images), so a point `y` of the open left side of the prefix (`WalkBdry.IsLeftSidePt`:
a positive distance right of those images) has no mark between it and the tip: the word there is `−λ − θχ`, and `y`
is not a jump. Mirror on the right side: `λ − θχ`.

* `markPosL_le`: an upper bound of the images of the alive negative points bounds every left mark position;
* `stopWord_fn_left`, `stopWord_fn_right`: the stop word between the marks and the tip;
* **`stopWord_leftSide`**, **`stopWord_rightSide`**: the same at the side points of a recorded prefix, for the record
  of the driver stopped at `τ`.

Deterministic. R48: serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

namespace InteractingSLE.Theorem14.WalkSide

open Exist.StagedLaw Exist.Staged Restart

/-! ### Left marks below the left side -/

section MarkPos

variable {w : ℝ → ℝ} {T : ℝ}

/-- **An upper bound of the images of the alive negative points bounds every left mark position.** -/
theorem markPosL_le (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x c : ℝ} (hx : x ≤ 0)
    (hc : ∀ X : ℝ, X < 0 → (∃ u, IsForwardSol w (X : ℂ) T u) → (fwdMap w T X).re < 0 →
      (fwdMap w T X).re ≤ c) :
    markPosL w T x ≤ c := by
  have hw' : Continuous (-w) := hw.neg
  have hw0' : (-w) 0 = 0 := by simp [hw0]
  have hH := GW1W.isRealHalf_of hw' hw0' hT
  have h := GW1W.le_markPos (w := -w) hw' hw0' hT (x := -x) (c := -c) fun q hxq hq => by
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (neg_nonneg.2 hx) hxq
    have hqa : ∃ u, IsForwardSol w (((-q : ℝ)) : ℂ) T u := (alive_neg_iff w T q).1 hq
    have hr : (fwdMap (-w) T ((q : ℝ) : ℂ)).re = -(fwdMap w T ((-q : ℝ) : ℂ)).re := by
      have e := QuantumZipper.F1.fwdMap_reflect_ofReal w hT (-(q : ℝ))
      rw [neg_neg] at e
      rw [e, Complex.neg_re]
    have hpos := hH.2.2.2.1 q hq0 hq
    have hle := hc (-(q : ℝ)) (by linarith) hqa (by linarith)
    linarith
  unfold markPosL
  change -markPos (-w) T (-x) ≤ c
  linarith

end MarkPos

/-! ### The stop word between the marks and the tip -/

section Word

variable {κ : ℝ}

/-- **Left of the tip and right of every left mark, the stop word is `−λ − θχ`**, and the point is not a jump. -/
theorem stopWord_fn_left (θ : ℝ) (c : BoundaryWord) (r : RecData) {y : ℝ} (hy : y < 0)
    (hL : ∀ i < flowLineNL c.fn c.jumps 0, markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) < y) :
    (stopWord κ (c, θ, r)).fn y = -sleLambda κ - θ * chiC κ ∧ y ∉ (stopWord κ (c, θ, r)).jumps := by
  set nL := flowLineNL c.fn c.jumps 0 with hnL
  set nR := flowLineNR c.fn c.jumps 0 with hnR
  set pL : ℕ → ℝ := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) with hpL
  set pR : ℕ → ℝ := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) with hpR
  have hW : stopWord κ (c, θ, r) = forceWord κ nL nR pL pR (padFL κ θ c.fn c.jumps).2.1
      (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) := rfl
  have hlt : ∀ i < nL, cumMax (rawPos nL pL pR) i < y := by
    intro i
    induction i with
    | zero =>
      intro h0
      change rawPos nL pL pR 0 < y
      simp only [rawPos, h0, ↓reduceIte]
      exact hL _ (by omega)
    | succ i ih =>
      intro hi
      change max (cumMax (rawPos nL pL pR) i) (rawPos nL pL pR (i + 1)) < y
      refine max_lt (ih (by omega)) ?_
      simp only [rawPos, hi, ↓reduceIte]
      exact hL _ (by omega)
  have hge : ∀ i, nL ≤ i → 0 ≤ cumMax (rawPos nL pL pR) i := fun i hi =>
    le_trans (by rw [GW1W.rawPos_nL]) (le_trans (le_cumMax _ nL) (monotone_cumMax _ hi))
  have hidx : (stopWord κ (c, θ, r)).index y = nL := by
    rw [hW]
    unfold BoundaryWord.index
    change ((Finset.range (nL + 1 + nR)).filter fun i => cumMax (rawPos nL pL pR) i < y).card = nL
    have e : ((Finset.range (nL + 1 + nR)).filter fun i => cumMax (rawPos nL pL pR) i < y) = Finset.range nL := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨-, h⟩
        by_contra hni
        exact absurd h (not_lt.2 ((hge i (not_lt.1 hni)).trans' hy.le))
      · intro hi
        exact ⟨by omega, hlt i hi⟩
    rw [e, Finset.card_range]
  refine ⟨?_, fun hj => ?_⟩
  · unfold BoundaryWord.fn
    rw [hidx, hW]
    change wordHeight κ nL _ _ (θ * chiC κ) nL = _
    simp only [wordHeight, le_refl, ↓reduceIte, Nat.sub_self, Finset.range_zero, Finset.sum_empty, add_zero,
      mul_one, sleLambda]
  · rw [hW] at hj
    obtain ⟨i, hi, he⟩ := BoundaryWord.mem_jumps.1 hj
    change cumMax (rawPos nL pL pR) i = y at he
    by_cases hin : i < nL
    · exact absurd he (hlt i hin).ne
    · exact absurd (he ▸ hge i (not_lt.1 hin)) (not_le.2 hy)

/-- **Right of the tip and left of every right mark, the stop word is `λ − θχ`**, and the point is not a jump. -/
theorem stopWord_fn_right (θ : ℝ) (c : BoundaryWord) (r : RecData) {y : ℝ} (hy : 0 < y)
    (hR : ∀ j < flowLineNR c.fn c.jumps 0, y < markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) :
    (stopWord κ (c, θ, r)).fn y = sleLambda κ - θ * chiC κ ∧ y ∉ (stopWord κ (c, θ, r)).jumps := by
  set nL := flowLineNL c.fn c.jumps 0 with hnL
  set nR := flowLineNR c.fn c.jumps 0 with hnR
  set pL : ℕ → ℝ := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) with hpL
  set pR : ℕ → ℝ := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) with hpR
  have hW : stopWord κ (c, θ, r) = forceWord κ nL nR pL pR (padFL κ θ c.fn c.jumps).2.1
      (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) := rfl
  have hord := GW1W.isMarkOrder_stopWord c r
  have hL0 : ∀ i < nL, pL i ≤ 0 := hord.2.1
  have hle : ∀ i, i ≤ nL → cumMax (rawPos nL pL pR) i ≤ 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      change rawPos nL pL pR 0 ≤ 0
      unfold rawPos
      split_ifs with h1 h2
      · exact hL0 _ (by omega)
      · exact le_rfl
      · omega
    | succ i ih =>
      intro hi
      change max (cumMax (rawPos nL pL pR) i) (rawPos nL pL pR (i + 1)) ≤ 0
      refine max_le (ih (by omega)) ?_
      unfold rawPos
      split_ifs with h1 h2
      · exact hL0 _ (by omega)
      · exact le_rfl
      · omega
  have hgt : ∀ i, nL < i → i < nL + 1 + nR → y < cumMax (rawPos nL pL pR) i := by
    intro i hi hi'
    refine lt_of_lt_of_le ?_ (le_cumMax _ i)
    simp only [rawPos, show ¬ i < nL by omega, show i ≠ nL by omega, ↓reduceIte]
    exact hR _ (by omega)
  have hidx : (stopWord κ (c, θ, r)).index y = nL + 1 := by
    rw [hW]
    unfold BoundaryWord.index
    change ((Finset.range (nL + 1 + nR)).filter fun i => cumMax (rawPos nL pL pR) i < y).card = nL + 1
    have e : ((Finset.range (nL + 1 + nR)).filter fun i => cumMax (rawPos nL pL pR) i < y) =
        Finset.range (nL + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hi, h⟩
        by_contra hni
        exact absurd h (not_lt.2 (hgt i (by omega) hi).le)
      · intro hi
        exact ⟨by omega, lt_of_le_of_lt (hle i (by omega)) hy⟩
    rw [e, Finset.card_range]
  refine ⟨?_, fun hj => ?_⟩
  · unfold BoundaryWord.fn
    rw [hidx, hW]
    change wordHeight κ nL _ _ (θ * chiC κ) (nL + 1) = _
    simp only [wordHeight, show ¬ nL + 1 ≤ nL by omega, ↓reduceIte, show nL + 1 - nL - 1 = 0 by omega,
      Finset.range_zero, Finset.sum_empty, add_zero, mul_one, sleLambda]
  · rw [hW] at hj
    obtain ⟨i, hi, he⟩ := BoundaryWord.mem_jumps.1 hj
    change cumMax (rawPos nL pL pR) i = y at he
    by_cases hin : i ≤ nL
    · exact absurd (he ▸ hle i hin) (not_le.2 hy)
    · exact absurd he (hgt i (by omega) hi).ne'

end Word

/-! ### The stop word at the side points of a recorded prefix -/

section Side

open QuantumZipper (fwdMap)

variable {κ : ℝ}

/-- Forward solutions only read the driver up to their time. -/
theorem isForwardSol_congr {W W' : ℝ → ℝ} {T : ℝ} (h : EqOn W W' (Icc 0 T)) (z : ℂ) (u : ℝ → ℂ) :
    IsForwardSol W z T u ↔ IsForwardSol W' z T u := by
  unfold IsForwardSol
  refine and_congr_right fun _ => forall₂_congr fun t ht => ?_
  rw [h ht]

/-- The record driver of a regular driver with a good record is the stopped driver. -/
theorem rdrv_recOf {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (recOf t e))) : rdrv (recOf t e) = stopDrv t e := by
  funext x
  change LocalExt.histDrv (recHist (recOf t e)) x.toNNReal = (retOf t e).1 x.toNNReal
  rw [histDrv_recHist he hg]

/-- The record time of a piece stopped before its lifetime is the stop. -/
theorem rtime_recOf_of_lt {τ : ℝ≥0} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hτ : (τ : ℝ≥0∞) < e.2) :
    rtime (recOf τ e) = τ := by
  change (((min (τ : ℝ≥0∞) e.2).toNNReal : ℝ≥0) : ℝ) = τ
  rw [min_eq_left hτ.le, ENNReal.toNNReal_coe]

/-- The stopped driver and the driver of the recorded piece agree up to `τ`. -/
theorem eqOn_stopDrv_pieceDrv (s : ExplState) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) {t : ℝ≥0∞} {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < min t e.2) :
    EqOn (stopDrv τ e) (WalkBdry.pieceDrv (recPiece s e t)) (Icc 0 (τ : ℝ)) :=
  eqOn_stoppedDrv e (S := min (τ : ℝ≥0∞) e.2) (S' := min t e.2)
    (le_min le_rfl (lt_of_lt_of_le hτ (min_le_right _ _)).le) hτ.le

/-- **On the left side of a recorded prefix the stop word of its record is `−λ − θχ`**, off its jumps. -/
theorem stopWord_leftSide (θ : ℝ) (c : BoundaryWord) (s : ExplState) {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {t : ℝ≥0∞} {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < min t e.2)
    (hg : LocalExt.IsDrvGood (recHist (recOf τ e))) {y : ℝ} (hside : WalkBdry.IsLeftSidePt (recPiece s e t) τ y) :
    (stopWord κ (c, θ, recOf τ e)).fn y = -sleLambda κ - θ * chiC κ ∧
      y ∉ (stopWord κ (c, θ, recOf τ e)).jumps := by
  obtain ⟨hy, ε, hε, hside⟩ := hside
  have hτζ : (τ : ℝ≥0∞) < e.2 := lt_of_lt_of_le hτ (min_le_right _ _)
  have hEq := eqOn_stopDrv_pieceDrv s e hτ
  have hxL := (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0).2.1
  refine stopWord_fn_left θ c _ hy fun i hi => ?_
  refine lt_of_le_of_lt (markPosL_le (c := y - ε) (continuous_rdrv _) (rdrv_zero _) (rtime_nonneg _) ?_
    fun X hX hXa hXi => ?_) (by linarith)
  · rw [padFL_fst_fst_fin c.fn c.jumps ⟨i, hi⟩]
    exact hxL _
  · rw [rdrv_recOf he hg, rtime_recOf_of_lt hτζ] at hXa hXi ⊢
    have hfw : fwdMap (stopDrv τ e) τ X = fwdMap (WalkBdry.pieceDrv (recPiece s e t)) τ X :=
      Ito.fwdMap_congr_of_eqOn_of_le hEq le_rfl
    have hal : WalkBdry.IsAlivePt (recPiece s e t) τ X := by
      obtain ⟨u, hu⟩ := hXa
      exact ⟨u, (isForwardSol_congr hEq _ u).1 hu⟩
    rw [hfw] at hXi ⊢
    linarith [hside X hal hXi]

/-- **On the right side of a recorded prefix the stop word of its record is `λ − θχ`**, off its jumps. -/
theorem stopWord_rightSide (θ : ℝ) (c : BoundaryWord) (s : ExplState) {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {t : ℝ≥0∞} {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < min t e.2)
    (hg : LocalExt.IsDrvGood (recHist (recOf τ e))) {y : ℝ} (hside : WalkBdry.IsRightSidePt (recPiece s e t) τ y) :
    (stopWord κ (c, θ, recOf τ e)).fn y = sleLambda κ - θ * chiC κ ∧
      y ∉ (stopWord κ (c, θ, recOf τ e)).jumps := by
  obtain ⟨hy, ε, hε, hside⟩ := hside
  have hτζ : (τ : ℝ≥0∞) < e.2 := lt_of_lt_of_le hτ (min_le_right _ _)
  have hEq := eqOn_stopDrv_pieceDrv s e hτ
  have hxR := (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0).2.2.2
  refine stopWord_fn_right θ c _ hy fun j hj => ?_
  have hxj : 0 ≤ (padFL 0 0 c.fn c.jumps).1.2 j := by
    rw [padFL_fst_snd_fin c.fn c.jumps ⟨j, hj⟩]
    exact hxR _
  have hw := continuous_rdrv (recOf τ e)
  have hw0 := rdrv_zero (recOf τ e)
  have hT := rtime_nonneg (recOf τ e)
  have hH := GW1W.isRealHalf_of hw hw0 hT
  refine lt_of_lt_of_le (by linarith : y < y + ε) (GW1W.le_markPos hw hw0 hT fun q hxq hq => ?_)
  have hqpos : 0 < (fwdMap (rdrv (recOf τ e)) (rtime (recOf τ e)) ((q : ℝ) : ℂ)).re :=
    hH.2.2.2.1 q (lt_of_le_of_lt hxj hxq) hq
  rw [rdrv_recOf he hg, rtime_recOf_of_lt hτζ] at hq hqpos ⊢
  have hfw : fwdMap (stopDrv τ e) τ ((q : ℝ) : ℂ) = fwdMap (WalkBdry.pieceDrv (recPiece s e t)) τ ((q : ℝ) : ℂ) :=
    Ito.fwdMap_congr_of_eqOn_of_le hEq le_rfl
  have hal : WalkBdry.IsAlivePt (recPiece s e t) τ q := by
    obtain ⟨u, hu⟩ := hq
    exact ⟨u, (isForwardSol_congr hEq _ u).1 hu⟩
  rw [hfw] at hqpos ⊢
  exact (hside q hal hqpos).le

end Side

end InteractingSLE.Theorem14.WalkSide
