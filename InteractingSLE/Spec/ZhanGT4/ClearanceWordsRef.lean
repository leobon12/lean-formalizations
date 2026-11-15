/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.WordsRef
import InteractingSLE.Spec.ZhanGT4.ClearanceNoCluster

/-! # Clearance-based consumers of the two-group and reference-word transience results. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

section Groups

variable {κ : ℝ} {nL nR : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Transience for two-group words, `κ > 4`** (B.5): an ordered word with admissible side partial sums, at least one
mark, whose left marks all sit at one point `< 0` and whose right marks all sit at one point `> 0`; given (G5) and clearance,
almost surely every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups_gt_four_of_clearance (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedClearanceStatement.{0} κ)
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hgL : ∀ i j, xL i = xL j) (hgR : ∀ i j, xR i = xR j)
    (hn : 0 < nL + nR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hκ : 0 < κ := by linarith
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE).mono fun ω h => h.1
  cases nL with
  | zero =>
    cases nR with
    | zero => exact absurd hn (lt_irrefl 0)
    | succ n =>
      have hE' := Zhan.IsIntegratedSLEEvolution.mergeRight (fun i => hgR i 0) hE hζ
      exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_oneForce_right hκ4 hG5 (hxR 0)
        (le_sum_right_of_group hadm (hxR 0) fun i => hgR i 0) hE'
  | succ m =>
    have hE₁ := Zhan.IsIntegratedSLEEvolution.mergeLeft (fun i => hgL i 0) hE hζ
    have hρL := le_sum_left_of_group hadm (hxL 0) fun i => hgL i 0
    cases nR with
    | zero => exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_oneForce hκ4 hG5 (hxL 0) hρL hE₁
    | succ n =>
      have hE₂ := Zhan.IsIntegratedSLEEvolution.mergeRight (fun i => hgR i 0) hE₁ hζ
      exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_gt_four_of_clearance hκ4 hG5 hG2 (hxL 0) (hxR 0)
        (hasAdmissiblePartialSums_one hρL (le_sum_right_of_group hadm (hxR 0) fun i => hgR i 0)) hE₂

end Groups

section RefTrans

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- **The reference word is transient** (`κ > 4`, given (G5) and clearance): every evolution of the word with all weights
moved onto the outermost marks has, almost surely, infinite lifetime and the trace event. -/
theorem IsIntegratedSLEEvolution.ae_traceEvent_outerW_gt_four_of_clearance {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedClearanceStatement.{0} κ)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hn : 0 < nL + nR)
    (hE : IsIntegratedSLEEvolution κ xL xR (outerW ρL) (outerW ρR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ TraceEvent (fun t => W t ω) (ζ ω) := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ : 0 < κ := by linarith
  have hζ := IsIntegratedSLEEvolution.ae_lifetime_eq_top_outerW hκ hF hadm hxL hxR hE
  have hE' := Zhan.IsIntegratedSLEEvolution.relabelOuter hE hζ (neg_two_lt_sum_left hκ hF hadm hxL)
    (neg_two_lt_sum_right hκ hF hadm hxR)
  have hFo := isOrderedForceWord_outerPos hF
  have hadmo := hasAdmissiblePartialSums_outerPos hF hadm hxL hxR
  have h23 := hE'.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ hFo hadmo
    (fun i => hxL _) (fun j => hxR _)
  have htr := IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups_gt_four_of_clearance hκ4 hG5 hG2 hFo hadmo
    (fun i => hxL _) (fun j => hxR _) (fun _ _ => rfl) (fun _ _ => rfl) hn hE'
  filter_upwards [h23, htr] with ω h ht
  obtain ⟨hζω, η, hη⟩ := h
  exact ⟨hζω, η, hζω ▸ hη, fun _ => ht η hη⟩

/-- Late returns of the canonical reference trace are rare (`κ > 4`, given (G5) and clearance). -/
theorem codeLaw_outerW_lateSet_tendsto_zero_gt_four_of_clearance (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedClearanceStatement.{0} κ)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hn : 0 < nL + nR) (R : ℝ) :
    Tendsto (fun k => codeLaw κ (outerW ρL) (outerW ρR) (lateSet k R) (xL, xR)) atTop (𝓝 0) := by
  have hκ : 0 < κ := by linarith
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    Sec2.Assembly2.exists_isIntegratedSLEEvolution_of_ordered (ρL := outerW ρL) (ρR := outerW ρR) hκ hF
  exact codeLaw_lateSet_tendsto_zero hκ (fun i j => (hxL i).trans (hxR j)) hE'
    ((IsIntegratedSLEEvolution.ae_traceEvent_outerW_gt_four_of_clearance hκ4 hG5 hG2 hF hadm hxL hxR hn hE').mono
      fun _ h => h.2) R

end RefTrans

end InteractingSLE.ZhanGT4
