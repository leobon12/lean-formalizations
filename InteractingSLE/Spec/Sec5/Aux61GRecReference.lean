/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GRecBoundary
import InteractingSLE.Spec.Sec5.GlueCondPath

/-! # Restore the physical harmonic base in local-set mean pairings -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

namespace InteractingSLE.Sec5.Aux61GRec

/-- A centred mean represented by m becomes the physical mean m + u₀
after adding back the harmonic base distribution. Integrability follows
from harmonicity and compact support of the test, rather than a convention
for a non-integrable Bochner integral. -/
theorem add_base_pairings {O : Set ℂ} {g : DistOn upperHalfPlaneOpens}
    {m u₀ : ℂ → ℝ} (hm : InnerProductSpace.HarmonicOnNhd m O)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hpair : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      g φ = ∫ z, m z * φ z)
    (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ O) :
    (g + smoothDist upperHalfPlaneOpens u₀) φ = ∫ z, (m z + u₀ z) * φ z := by
  have hi := WholeField.integrable_mul_testOn hm.continuousOn φ hφ
  have hi₀ := WholeField.integrable_mul_testOn hu₀.continuousOn φ φ.tsupport_subset
  rw [add_apply, hpair φ hφ, smoothDist_apply hu₀.continuousOn]
  have he : (∫ z, φ z * u₀ z) = ∫ z, u₀ z * φ z :=
    integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  rw [he, ← integral_add hi hi₀]
  exact integral_congr_ae (ae_of_all _ fun z => (add_mul _ _ _).symm)

end InteractingSLE.Sec5.Aux61GRec
