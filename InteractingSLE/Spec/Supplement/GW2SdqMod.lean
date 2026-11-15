/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfChartCongr
import InteractingSLE.GFF.LocalSets.GermApprox

/-!
# A measurable version of a function measurable up to null sets

Packet PROVE-GW2-SDE (round 16; the gap family of (N3)). The scaled cover's gap must be measurable for the root's
retained σ-algebra `𝒢` exactly, while the natural readout (the root prefix's junctions, read from a relative
version) is measurable only for its null-completion `LocalSets.aeSigma 𝒢 P`:

* **`exists_measurable_ae_eq_of_aeSigma`**: a bounded real function measurable for the ambient σ-algebra and for
  `aeSigma 𝒢 P` agrees almost surely with a `𝒢`-measurable function (its conditional expectation given `𝒢`; the
  conditional expectation does not see null-equivalent enlargements, `Sec5.CfChart.condExp_ae_eq_of_le_aeSigma`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace InteractingSLE.Theorem14.GW2Sdq

/-- **A measurable version of a function measurable up to null sets** (bounded, real). -/
theorem exists_measurable_ae_eq_of_aeSigma {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {f : Ω → ℝ} (hf : Measurable f)
    (hfa : Measurable[LocalSets.aeSigma 𝒢 P] f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    ∃ g : Ω → ℝ, Measurable[𝒢] g ∧ f =ᵐ[P] g := by
  have h12 : 𝒢 ≤ MeasurableSpace.comap f inferInstance ⊔ 𝒢 := le_sup_right
  have h2 : MeasurableSpace.comap f inferInstance ⊔ 𝒢 ≤ mΩ := sup_le hf.comap_le h𝒢
  have h2a : MeasurableSpace.comap f inferInstance ⊔ 𝒢 ≤ Sec5.CfChart.aeSigma P 𝒢 := by
    refine sup_le ?_ (Sec5.CfChart.le_aeSigma 𝒢 P)
    rintro s ⟨B, hB, rfl⟩
    exact hfa hB
  have hint : Integrable f P :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact hC ω)
  have hm : Measurable[MeasurableSpace.comap f inferInstance ⊔ 𝒢] f :=
    Measurable.mono (comap_measurable f) le_sup_left le_rfl
  have hfm : StronglyMeasurable[MeasurableSpace.comap f inferInstance ⊔ 𝒢] f := hm.stronglyMeasurable
  have hself : P[f | MeasurableSpace.comap f inferInstance ⊔ 𝒢] = f := condExp_of_stronglyMeasurable h2 hfm hint
  have heq := Sec5.CfChart.condExp_ae_eq_of_le_aeSigma h12 h2 h2a hint
  rw [hself] at heq
  exact ⟨P[f | 𝒢], stronglyMeasurable_condExp.measurable, heq⟩

end InteractingSLE.Theorem14.GW2Sdq
