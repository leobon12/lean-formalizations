/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartMeas
import InteractingSLE.Spec.Sec5.Lemma56
import InteractingSLE.Spec.ZhanGT4.Words

/-!
# The counterflow restart carrier from the restart law and Zhan's two Part A inputs at `κ′ = 16/κ`

Packet PROVE-SEC5-H. PROVE-SEC5-G reduced SEC5-E's cross-conditioning carrier
`Sec5.CounterflowSegmentRestartStatement` to the restart law `CrossRestart.CounterflowRestartLawStatement` and
Aux. lemma 7 at `κ′ = 16/κ` (`CrossRestart.counterflowSegmentRestartStatement_of_restartLaw`). Aux. lemma 7 is now
proved for every `κ′ > 0` from Zhan's two Part A inputs (G5) `ZhanGT4.StoppingInverseBoundaryStatement` and (G2)
`ZhanGT4.SeparatedTwoForceStatement`, used only when `κ′ > 4` (`ZhanGT4.aux7Statement_of_pos`, PROVE-ZHAN-GT4-B3).
For `0 < κ < 4` the counterflow parameter `κ′ = 16/κ` exceeds `4`, so both inputs are needed at `16/κ`.

* `aux7Statement_sixteen_div_of_partA`: Aux. lemma 7 at `16/κ` for every `0 < κ < 4` from (G5) and (G2) at `16/κ`;
* `counterflowSegmentRestartStatement_of_restartLaw_of_partA`: **the carrier from the restart law and the Part A
  inputs only**;
* `ae_isFirstHitPoint_of_restartLaw_of_partA`, `lemma57_of_restartLaw_of_partA`: SEC5-E's first exit and SEC5-F's
  Lemma 5.7 (one angle) with their inputs replaced by the restart law and the Part A inputs (conditional helpers;
  they replace no source theorem).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u v

namespace InteractingSLE.Sec5

open Sec4 Restart MarkovOther

/-- Zhan's two Part A inputs ((G5) and (G2)) at the counterflow parameter `16/κ`, for every `0 < κ < 4`. -/
def PartAInputsSixteenDiv : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
    ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ) ∧ ZhanGT4.SeparatedTwoForceStatement.{0} (16 / κ)

/-- **Aux. lemma 7 at `κ′ = 16/κ`** for `0 < κ < 4`, from Zhan's Part A inputs at `16/κ`
(`ZhanGT4.aux7Statement_of_pos`). -/
theorem aux7Statement_sixteen_div_of_partA (hA : PartAInputsSixteenDiv) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    Aux7Statement.{v} (16 / κ) :=
  ZhanGT4.aux7Statement_of_pos (by positivity) fun _ => hA κ hκ hκ4

/-- **The counterflow restart carrier from the restart law and Zhan's Part A inputs at `16/κ`**: SEC5-G's reduction
with Aux. lemma 7 for `κ′` discharged. -/
theorem counterflowSegmentRestartStatement_of_restartLaw_of_partA (hA : PartAInputsSixteenDiv)
    (hR : CrossRestart.CounterflowRestartLawStatement.{u}) : CounterflowSegmentRestartStatement.{u} :=
  CrossRestart.counterflowSegmentRestartStatement_of_restartLaw
    (fun _ hκ hκ4 => aux7Statement_sixteen_div_of_partA hA hκ hκ4) hR

variable {κ α x₀ a b a' b' θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}

/-- **The first exit after a flow-line segment** (Lemma 5.7's proof, p. 138) from the restart law and the Part A
inputs (conditional helper). -/
theorem ae_isFirstHitPoint_of_restartLaw_of_partA (hA : PartAInputsSixteenDiv)
    (hR : CrossRestart.CounterflowRestartLawStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2) (hhm : Measurable h)
    (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hη : IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    (σ : ℝ≥0) :
    ∀ᵐ ω ∂P, (σ : ℝ≥0∞) < ζ ω → (∀ t : ℝ≥0, 0 < t → t ≤ σ → η ω t ∈ H) →
      IsFirstHitPoint (stripCounterflowPath (Real.exp (π * x₀)) (γ' ω)) 1
        (lowerLineH ∪ (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (σ : ℝ)) (η ω σ) :=
  ae_isFirstHitPoint_of_counterflowSegmentRestart
    (counterflowSegmentRestartStatement_of_restartLaw_of_partA hA hR)
    (aux7Statement_sixteen_div_of_partA hA hκ hκ4) hκ hκ4 hbd hθ₁ hθ₂ hhm hh hη hcf htr' hci hγ σ

/-- **Lemma 5.7 for one angle** (conditional helper) from the restart law and the Part A inputs: on every positive
horizon `T` before which the flow line is alive and in `ℍ`, the counterflow first hits the explored flow-line segment
at its tip, contains `η([0, T])` and visits its points in reverse chronological order. -/
theorem lemma57_of_restartLaw_of_partA (hA : PartAInputsSixteenDiv)
    (hR : CrossRestart.CounterflowRestartLawStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2) (hhm : Measurable h)
    (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hη : IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {T : Ω → ℝ} (hT0 : ∀ᵐ ω ∂P, 0 < T ω)
    (hT : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < T ω → (t : ℝ≥0∞) < ζ ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T ω → η ω t ∈ H) :
    ∀ᵐ ω ∂P,
      (∀ τ ∈ Icc 0 (T ω), IsFirstHitPoint (stripCounterflowPath (Real.exp (π * x₀)) (γ' ω)) 1
          (lowerLineH ∪ (fun s : ℝ => η ω s.toNNReal) '' Icc 0 τ) (η ω τ.toNNReal)) ∧
      (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (T ω) ⊆
        stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) '' Icc 0 1 ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T ω →
        ∃ v ∈ Icc (0 : ℝ) 1, stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) v = η ω t.toNNReal ∧
          ∀ w ∈ Icc 0 v, stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) w ≠ η ω s.toNNReal :=
  lemma57_of_counterflowSegmentRestart' (counterflowSegmentRestartStatement_of_restartLaw_of_partA hA hR)
    (aux7Statement_sixteen_div_of_partA hA hκ hκ4) hκ hκ4 hbd hθ₁ hθ₂ hhm hh hη hcf htr' hci hγ hT0 hT

end InteractingSLE.Sec5
