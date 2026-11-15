/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkFinishParam
import InteractingSLE.Spec.Supplement.GW1ActiveLawL

/-!
# GW1: deterministic exit classification from swallowed real points

The finite-positive-lifetime hit supplied by the integrated evolution forces an actual
threshold status, excluding the machine's dead branch. At zero lifetime, the threshold
condition of the current word transfers to the original outward boundary height.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC)

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw Restart GW1WalkFinish
open PiecewiseConstantBoundaryData (leftLim rightLim)

theorem launch_thr_true_of_hit {s : ExplState} (hs : GW1W.RProf s)
    (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (hfin : D.2 ≠ ⊤) (hzero : D.2 ≠ 0)
    (hhit : ∃ y : ℝ, 0 < y ∧
      (∀ r < stopTime ⊤ D, ∃ u, IsForwardSol (stopDrv ⊤ D) (y : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol (stopDrv ⊤ D) (y : ℂ) (stopTime ⊤ D) u) :
    stStatus (ExplState.launch s k D θ ⊤) = stThr (some true) := by
  obtain ⟨y, hy, hyb, hyd⟩ := hhit
  obtain ⟨x, hx, hmx⟩ := GW1W.RProf.exists_eq hs hy
  have hhx : ∃ x, stRecR s < x ∧ lHit (stChart s) ⊤ D x := by
    refine ⟨x, hx, (lHit_iff hs.1 ⊤ D x).2 ?_⟩
    rw [hmx]
    exact ⟨hyb, hyd⟩
  obtain ⟨-, -, -, -, hst, -⟩ :=
    launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
  rw [hst]
  simp only [lStatus, not_lt.2 (le_top : D.2 ≤ ⊤), hzero, hhx, ↓reduceIte]

theorem launch_thr_false_of_hit {s : ExplState} (hs : GW1W.LProf s)
    (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (hfin : D.2 ≠ ⊤) (hzero : D.2 ≠ 0)
    (hnoR : stStatus (ExplState.launch s k D θ ⊤) ≠ stThr (some true))
    (hhit : ∃ y : ℝ, y < 0 ∧
      (∀ r < stopTime ⊤ D, ∃ u, IsForwardSol (stopDrv ⊤ D) (y : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol (stopDrv ⊤ D) (y : ℂ) (stopTime ⊤ D) u) :
    stStatus (ExplState.launch s k D θ ⊤) = stThr (some false) := by
  obtain ⟨y, hy, hyb, hyd⟩ := hhit
  obtain ⟨x, hx, hmx⟩ := GW1W.LProf.exists_eq hs (neg_pos.2 hy)
  have hmx' : rProf (stChart s) (-x) = y := by
    rw [GW1W.lProf_eq] at hmx
    linarith only [hmx]
  have hhx : ∃ x, x < stRecL s ∧ lHit (stChart s) ⊤ D x := by
    refine ⟨-x, by linarith only [hx], (lHit_iff hs.1 ⊤ D (-x)).2 ?_⟩
    rw [hmx']
    exact ⟨hyb, hyd⟩
  obtain ⟨-, -, -, -, hst, -⟩ :=
    launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
  rw [hst] at hnoR ⊢
  unfold lStatus at hnoR ⊢
  simp only [not_lt.2 (le_top : D.2 ≤ ⊤), hzero, ↓reduceIte] at hnoR ⊢
  have hn : ¬ ∃ x, stRecR s < x ∧ lHit (stChart s) ⊤ D x := by
    intro hR
    apply hnoR
    rw [ite_eq_left hR]
  rw [ite_eq_right hn, ite_eq_left hhx]

theorem right_height_of_zero_threshold {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {β : BoundaryWord} {s : ExplState} (hI : GW1W.RInv κ θ b jumps β s)
    (hthr : ForceWord.ThresholdCondition
      (flowLineRhoL κ β.fn β.jumps 0 θ) (flowLineRhoR κ β.fn β.jumps 0 θ) 0
      (flowLineXL β.fn β.jumps 0) (flowLineXR β.fn β.jumps 0)) :
    rightLim b (stRecR s) + θ * chiC κ ≤ -sleLambda κ := by
  have hna := (GW1.thresholdCondition_flowLine_zero_iff hκ β.fn β.jumps θ).1 hthr
  obtain ⟨z, -, hz, hzJ, hlim⟩ := Sec5.Aux22ChartE.exists_leftLim_eq
    β.isPiecewiseConstantBoundaryData (z := 0) (lo := -1) (by norm_num)
  have hL : leftLim β.fn 0 + θ * chiC κ < sleLambda κ := by
    rw [hlim]
    exact hI.1 z hz hzJ
  have hR : rightLim β.fn 0 + θ * chiC κ ≤ -sleLambda κ := by
    by_contra hn
    exact hna ⟨hL, lt_of_not_ge hn⟩
  obtain ⟨hi, hhi, hc⟩ :=
    Sec5.Aux22ChartE.exists_forall_Ioo_eq_rightLim β.isPiecewiseConstantBoundaryData 0
  exact GW1W.rightLim_le_of_lowStart hb hI.2.1 hI.2.2 hhi
    (fun z hz => by rw [hc z hz]; exact hR)

theorem left_height_of_zero_threshold {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {β : BoundaryWord} {s : ExplState} (hI : GW1W.LInv κ θ b jumps β s)
    (hthr : ForceWord.ThresholdCondition
      (flowLineRhoL κ β.fn β.jumps 0 θ) (flowLineRhoR κ β.fn β.jumps 0 θ) 0
      (flowLineXL β.fn β.jumps 0) (flowLineXR β.fn β.jumps 0)) :
    sleLambda κ ≤ leftLim b (stRecL s) + θ * chiC κ := by
  have hna := (GW1.thresholdCondition_flowLine_zero_iff hκ β.fn β.jumps θ).1 hthr
  obtain ⟨z, hz, -, hzJ, hlim⟩ := Sec5.Aux22ChartE.exists_rightLim_eq
    β.isPiecewiseConstantBoundaryData (z := 0) (hi := 1) (by norm_num)
  have hR : -sleLambda κ < rightLim β.fn 0 + θ * chiC κ := by
    rw [hlim]
    exact hI.1 z hz hzJ
  have hL : sleLambda κ ≤ leftLim β.fn 0 + θ * chiC κ := by
    by_contra hn
    exact hna ⟨lt_of_not_ge hn, hR⟩
  obtain ⟨lo, hlo, hc⟩ :=
    Sec5.Aux22ChartE.exists_forall_Ioo_eq_leftLim β.isPiecewiseConstantBoundaryData 0
  apply GW1W.leftLim_ge_of_highStart hb hI.2.1 hI.2.2.1 (neg_pos.2 hlo)
  intro z hz
  rw [hc z (by simpa only [neg_neg] using hz)]
  exact hL

theorem recR_le_launch {s : ExplState} (hs : GW1W.RProf s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    stRecR s ≤ stRecR (ExplState.launch s k D θ ⊤) := by
  obtain ⟨-, -, hrec, -, -, -⟩ :=
    launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
  rw [hrec, lRecR_eq_newRec hs.1]
  exact le_newRec hs.2.1 (isRealFlow_stop hreg hgood).1

theorem launch_le_recL {s : ExplState} (hs : GW1W.LProf s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    stRecL (ExplState.launch s k D θ ⊤) ≤ stRecL s := by
  obtain ⟨-, -, -, hrec, -, -⟩ :=
    launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
  rw [hrec, lRecL_eq_newRec hs.1]
  exact neg_le.2 (le_newRec hs.2.1 (isRealFlow_stop hreg hgood).2)

end InteractingSLE.Theorem14.GW1WalkExit
