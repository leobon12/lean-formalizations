/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfNextMembers

/-!
# Zero-prefix word coupling and physical members with the actual record retained

Packet PROVE-CFCHART2. The original optional coupling supplies its own member
identities. The zero-prefix record adds only null-equivalent information.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfNext

open CfConv CfChart CfGiven Exist Exist.Staged Exist.StagedLaw Restart Restart.DomainMarkov.K2

/-- The zero-prefix image field has an actual word coupling and member locality in
the driving filtration enlarged by the literal stopped record. -/
theorem exists_zero_word_members {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D)
    (hDreg : ∀ ω, IsRegularDriver (D ω)) (hDpos : ∀ᵐ ω ∂P, 0 < (D ω).2) :
    ∃ (c : BoundaryWord) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (hX : IsMeasurableKilledDriving W VL VR ζ),
      IsOptionalHullCoupling (16 / κ) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
        (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0)
        P 𝓕 W VL VR B ζ (fun ω => imgField κ (recOf 0 (D ω)) (h ω)) ∧
      HasSafeMembers P
        (recordFiltration (drivingFiltration P hX) (fun ω => recOf 0 (D ω))
          (measurable_recOf hDm hDreg 0)) univ (fun _ => ⊤) W
        (fun ω => imgField κ (recOf 0 (D ω)) (h ω)) := by
  obtain ⟨c, 𝓕, VL, VR, B, hC⟩ := CfFinish.exists_zero_word_coupling hcf D
  obtain ⟨hX, _⟩ := hC.2.2.2
  refine ⟨c, 𝓕, VL, VR, B, hX, hC, ?_⟩
  apply CfResume.hasSafeMembers_of_le_aeSigma
    (hasSafeMembers_optional_top (div_pos (by norm_num) hκ) hC hX hζ)
  intro t
  exact sup_le (le_aeSigma _ _) (CfResume.recordSigma_zero_le_aeSigma hDreg hDpos _ t)

end InteractingSLE.Sec5.CfNext
