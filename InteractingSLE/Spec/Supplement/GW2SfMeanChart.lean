/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfCentring
import InteractingSLE.Spec.Supplement.GW2JDetR8VersionMean
import InteractingSLE.Spec.Jordan.Transport

/-! # Moving the angle shift between the physical mean and the chart offset -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Filter
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2Sf

/-- Raising the physical harmonic mean by a constant is the same as raising
 the chart offset by that constant. The distribution need only be represented
 on the half plane. -/
theorem chartTransport_add_const_mean {c : Chart} (hc : c.IsConformal)
    (a d k : ℝ) (g : DistOn upperHalfPlaneOpens) {u v : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hv : InnerProductSpace.HarmonicOnNhd v H)
    (he : EqOn v (fun z => u z + d) H) :
    Chart.chartTransport hc 1 (a + d) k
        (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u) =
      Chart.chartTransport hc 1 a k
        (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens v) := by
  ext ψ
  let φ := Chart.pushTest hc ψ
  have hi := WholeField.integrable_mul_testOn hu.continuousOn φ φ.tsupport_subset
  have hid := WholeField.integrable_mul_testOn (f := fun _ : ℂ => d)
    continuousOn_const φ φ.tsupport_subset
  have heI : (∫ z, v z * φ z) = (∫ z, u z * φ z) + d * ∫ z, ψ z := by
    calc
      (∫ z, v z * φ z) = ∫ z, (u z + d) * φ z := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          dsimp only
          by_cases hz : z ∈ tsupport φ
          · rw [he (φ.tsupport_subset hz)]
          · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
      _ = (∫ z, u z * φ z) + d * ∫ z, φ z := by
        simp_rw [add_mul]
        rw [integral_add hi hid, integral_const_mul]
      _ = _ := by rw [Chart.integral_pushTest hc ψ]
  rw [Chart.chartTransport_apply', Chart.chartTransport_apply', add_apply, add_apply,
    Coupling.smoothDist_apply_eq hu.continuousOn, Coupling.smoothDist_apply_eq hv.continuousOn,
    Chart.oneDist_apply]
  change 1 * (g φ + (∫ z, u z * φ z)) + (a + d) * (∫ z, ψ z) + k * _ =
    1 * (g φ + (∫ z, v z * φ z)) + a * (∫ z, ψ z) + k * _
  rw [heI]
  ring

end InteractingSLE.Theorem14.GW2Sf
