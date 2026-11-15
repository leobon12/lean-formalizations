/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishWord

/-!
# The original counterflow coupling in the zero-prefix image field

Packet PROVE-CFCHART2. Reencode the given boundary datum as a boundary word and use
the time-zero record-field identity. This gives the actual optional hull coupling,
with a word that is already classified by `FCDet.IsFlowType`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfFinish

open CfGiven CfResume Exist Exist.Staged Exist.StagedLaw Restart

/-- At prefix time zero the given counterflow is an optional hull coupling of the
exact image field, with the force coordinates of an actual boundary word. -/
theorem exists_zero_word_coupling {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {κ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∃ (c : BoundaryWord) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling (16 / κ) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
        (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0)
        P 𝓕 W VL VR B ζ (fun ω => imgField κ (recOf 0 (D ω)) (h ω)) := by
  obtain ⟨b, J, g, hb, htr, hD⟩ := hcf
  obtain ⟨c, hc⟩ := exists_flowLineDriver_word hb hD
  obtain ⟨g', 𝓕, VL, VR, B, hshift, hC⟩ := hc
  have he : (fun ω => imgField κ (recOf 0 (D ω)) (h ω)) = g' := by
    funext ω
    rw [imgField_recOf_zero_eq (D ω) (htr ω)]
    exact (Markov.eq_of_isTranslateAddConst_zero
      (by simpa only [zero_mul] using hshift ω)).symm
  rw [← he] at hC
  exact ⟨c, 𝓕, VL, VR, B, hC⟩

end InteractingSLE.Sec5.CfFinish
