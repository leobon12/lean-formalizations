import HigherDimLQGMetric.B3.Interfaces
import Mathlib.MeasureTheory.Measure.Tight

/-! Tightness survives multiplication by a jointly indexed tight scalar family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_tight_random_scale {d : ℕ} {ι Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set ι) (A : ι → Ω → ℝ)
    (D : ι → Ω → C(Rd d × Rd d, ℝ))
    (hAm : ∀ i ∈ S, AEMeasurable (A i) P)
    (hDm : ∀ i ∈ S, AEMeasurable (D i) P)
    (hAt : IsTightMeasureSet {ν : Measure ℝ | ∃ i ∈ S, ν = P.map (A i)})
    (hDt : IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, ν = P.map (D i)}) :
    IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, ν = P.map (fun ω => A i ω • D i ω)} := by
  let T : Set (Measure (ℝ × C(Rd d × Rd d, ℝ))) :=
    {ν | ∃ i ∈ S, ν = P.map (fun ω => (A i ω, D i ω))}
  have hjoint (i : ι) (hi : i ∈ S) :
      AEMeasurable (fun ω => (A i ω, D i ω)) P :=
    (hAm i hi).prodMk (hDm i hi)
  have hT0 : IsTightMeasureSet (Measure.fst '' T) := by
    apply hAt.subset
    rintro ν ⟨μ, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    change (P.map (fun ω => (A i ω, D i ω))).map Prod.fst = P.map (A i)
    simpa only [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
        (hjoint i hi))
  have hT1 : IsTightMeasureSet (Measure.snd '' T) := by
    apply hDt.subset
    rintro ν ⟨μ, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i, hi, ?_⟩
    change (P.map (fun ω => (A i ω, D i ω))).map Prod.snd = P.map (D i)
    simpa only [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        (hjoint i hi))
  have hT : IsTightMeasureSet T := IsTightMeasureSet.prodMk hT0 hT1
  have hmap := hT.map (continuous_smul :
    Continuous fun p : ℝ × C(Rd d × Rd d, ℝ) => p.1 • p.2)
  apply hmap.subset
  rintro ν ⟨i, hi, rfl⟩
  refine ⟨P.map (fun ω => (A i ω, D i ω)), ⟨i, hi, rfl⟩, ?_⟩
  simpa only [Function.comp_def] using
    (AEMeasurable.map_map_of_aemeasurable
      (continuous_smul : Continuous fun p : ℝ × C(Rd d × Rd d, ℝ) =>
        p.1 • p.2).measurable.aemeasurable (hjoint i hi))

end HigherDimLQGMetric
