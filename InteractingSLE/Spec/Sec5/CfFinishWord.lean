/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfResumeConditional

/-!
# Reencoding piecewise constant data as a flow-type boundary word

Packet PROVE-CFCHART2, second continuation. Reuse the finite-word representation and
invariance of one-sided limits to classify the original counterflow's force word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfFinish

open Restart Exist.StagedLaw

/-- A given flow driver can be read using a finite boundary word, without changing
the driver, field, lifetime, angle or probability space. -/
theorem exists_flowLineDriver_word {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {κ θ : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hD : IsFlowLineDriver κ b J θ P h W ζ) :
    ∃ c : BoundaryWord, IsFlowLineDriver κ c.fn c.jumps θ P h W ζ := by
  obtain ⟨c, _, he⟩ := BoundaryWord.exists_fn_eq hb
  exact ⟨c, (isFlowLineDriver_congr_of_eqOn hb c.isPiecewiseConstantBoundaryData J he).2 hD⟩

end InteractingSLE.Sec5.CfFinish
