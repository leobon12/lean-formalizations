/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetCounterflow
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRouteStrip

/-! # The source counterflow from Part A, without general centered no-return

The Figure 5.1 angle-zero word is admissible by the committed frame adapter.
The barrier-seed route therefore applies directly to its own flow-line driver.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal
universe u

namespace InteractingSLE.Sec5.Prop513Wire
open QuantumZipper Sec4 Prop513Target

/-- No return for the actual Figure 5.1 counterflow, using its barrier seeds. -/
theorem fig51_noReturn_of_partA (hA : PartAInputsSixteenDiv)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ →
      ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 := by
  obtain ⟨_, _, _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  have hk : 4 < 16 / κ := (lt_div_iff₀ hκ).2 (by linarith only [hκ4])
  exact CfNoReturn.Route.ae_trace_ne_zero_of_isFlowLineDriver hk
    (aux7Statement_sixteen_div_of_partA hA hκ hκ4) hfl hadm

/-- Infinite lifetime and strict half-plane membership in the source's
angle-zero frame; Part A is the only theorem-valued no-return input. -/
theorem fig51_trace_mem_H_of_partA (hA : PartAInputsSixteenDiv)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ∈ H := by
  obtain ⟨b₀, J₀, _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  exact ae_lifetime_eq_top_and_trace_mem_H_of_noReturn (div_pos (by norm_num) hκ)
    (Theorem15.isOrderedForceWord_flowLine b₀ J₀ 0) hadm
    ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩ ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩ hC.1
    (fig51_noReturn_of_partA hA hκ hκ4 hb hG hcf)

end InteractingSLE.Sec5.Prop513Wire
