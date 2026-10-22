import HigherDimLQGMetric.Limits.CompareProper

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Tight pure and compared marginals give tight joint laws. -/
theorem l6c_compare_joint_tight {d : ℕ}
    {ι Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ι → Ω → C(Rd d × Rd d, ℝ)) (S : Set ι)
    (hAm : ∀ i ∈ S, AEMeasurable (A i) P)
    (hBm : ∀ i ∈ S, AEMeasurable (B i) P)
    (hAT : IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, ν = P.map (A i)})
    (hBT : IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, ν = P.map (B i)}) :
    IsTightMeasureSet {ν : Measure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)) |
      ∃ i ∈ S, ν = P.map (fun ω => (A i ω, B i ω))} := by
  let T : Set (Measure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ))) :=
    {ν | ∃ i ∈ S, ν = P.map (fun ω => (A i ω, B i ω))}
  change IsTightMeasureSet T
  have h0 : IsTightMeasureSet ((fun ν : Measure
      (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)) => ν.map Prod.fst) '' T) := by
    apply hAT.subset
    rintro ν ⟨μ, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    change (P.map (fun ω => (A i ω, B i ω))).map Prod.fst = P.map (A i)
    simpa only [Function.comp_def] using
      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
        ((hAm i hi).prodMk (hBm i hi))
  have h1 : IsTightMeasureSet ((fun ν : Measure
      (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)) => ν.map Prod.snd) '' T) := by
    apply hBT.subset
    rintro ν ⟨μ, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    change (P.map (fun ω => (A i ω, B i ω))).map Prod.snd = P.map (B i)
    simpa only [Function.comp_def] using
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        ((hAm i hi).prodMk (hBm i hi))
  exact IsTightMeasureSet.prodMk h0 h1

end HigherDimLQGMetric
