import HigherDimLQGMetric.Locality.MarkovFixed
import LQGMetric.Papers.DFGPS.L2_17CoreA
import LQGMetric.Papers.DFGPS.L2_19CI

/-! Replace raw Markov observations by measurable almost-sure versions in
the finite-stage independence statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric

theorem l7a_indep_of_ae_right_versions
    {Ω : Type} {R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]
    (P : Measure Ω) (A : MeasurableSpace Ω)
    {ι : Type*} (T : Finset ι)
    {B : ι → Type*} [∀ i, MeasurableSpace (B i)]
    (Rraw Rnew : Ω → R)
    (Braw Bnew : ∀ i, i ∈ T → Ω → B i)
    (hRae : Rraw =ᵐ[P] Rnew)
    (hBae : ∀ i, ∀ hi : i ∈ T, Braw i hi =ᵐ[P] Bnew i hi)
    (hind : Indep A
      (MeasurableSpace.comap Rraw inferInstance ⊔
        ⨆ i ∈ T, MeasurableSpace.comap (Braw i ‹i ∈ T›) inferInstance) P) :
    Indep A
      (MeasurableSpace.comap Rnew inferInstance ⊔
        ⨆ i ∈ T, MeasurableSpace.comap (Bnew i ‹i ∈ T›) inferInstance) P := by
  have hR : MeasurableSpace.comap Rnew inferInstance ≤
      aeClosure P (MeasurableSpace.comap Rraw inferInstance) :=
    by
      rintro s ⟨S, hS, rfl⟩
      refine ⟨Rraw ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
      filter_upwards [hRae] with ω hω
      change (Rnew ω ∈ S) = (Rraw ω ∈ S)
      rw [hω]
  have hB (i : ι) (hi : i ∈ T) :
      MeasurableSpace.comap (Bnew i hi) inferInstance ≤
        aeClosure P (MeasurableSpace.comap (Braw i hi) inferInstance) :=
    by
      rintro s ⟨S, hS, rfl⟩
      refine ⟨(Braw i hi) ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
      filter_upwards [hBae i hi] with ω hω
      change (Bnew i hi ω ∈ S) = (Braw i hi ω ∈ S)
      rw [hω]
  apply LQGMetric.DFGPS.L217.indep_of_le_aeClosure hind (le_aeClosure _)
  refine sup_le ?_ (iSup₂_le fun i hi => ?_)
  · exact hR.trans (aeClosure_mono le_sup_left)
  · exact (hB i hi).trans
      (aeClosure_mono (le_sup_of_le_right (le_iSup₂_of_le i hi le_rfl)))

end HigherDimLQGMetric
