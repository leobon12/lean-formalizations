import HigherDimLQGMetric.Locality.JointLaw
import HigherDimLQGMetric.DGZ.NondegTight

/-! Tightness of a countable product from tightness of each coordinate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

theorem l7a_tight_countable_coordinates
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    {B : ι → Type*}
    [∀ i, TopologicalSpace (B i)] [∀ i, MeasurableSpace (B i)]
    [∀ i, OpensMeasurableSpace (B i)] [∀ i, BorelSpace (B i)]
    [∀ i, T2Space (B i)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ∀ i, B i)
    (hY : ∀ n i, AEMeasurable (fun ω => Y n ω i) P)
    (hYT : ∀ i, IsTightMeasureSet {ν : Measure (B i) |
      ∃ n, ν = P.map (fun ω => Y n ω i)}) :
    IsTightMeasureSet {ν : Measure (∀ i, B i) |
      ∃ n, ν = P.map (Y n)} := by
  let S : Set (Measure (∀ i, B i)) :=
    {ν | ∃ n, ν = P.map (Y n)}
  change IsTightMeasureSet S
  have hYm (n : ℕ) : AEMeasurable (Y n) P :=
    AEMeasurable.of_eval (hY n)
  apply DGZ.nd_isTightMeasureSet_pi
  intro i
  apply (hYT i).subset
  rintro ν ⟨μ, ⟨n, rfl⟩, rfl⟩
  refine ⟨n, ?_⟩
  simpa only [Function.comp_def] using
    (AEMeasurable.map_map_of_aemeasurable
      (measurable_pi_apply i).aemeasurable (hYm n))

end HigherDimLQGMetric
