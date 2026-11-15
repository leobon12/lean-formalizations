/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVClock

/-! # Translation of the explicit shift and filtration equality under the tilt -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

/-- Adding the chart shift is exactly translating the shifted physical field. -/
theorem isTranslateAddConst_add_chartShift {h h' : DistOn upperHalfPlaneOpens} {y a : ℝ}
    (htr : IsTranslateAddConst y a h h') (F : CMCut) {q : ℂ → ℝ} (hq : ContinuousOn q H) :
    IsTranslateAddConst y a
      (h + smoothDist upperHalfPlaneOpens (fun z => q z - F.f z))
      (h' + chartShift F q y) := by
  intro φ φ' hφ
  have hc : ContinuousOn (fun z => q z - F.f z) H := hq.sub F.smooth.continuous.continuousOn
  have hc' : ContinuousOn (fun z => q (z + y) - (F.shift y).f z) H :=
    (hq.comp (continuousOn_id.add continuousOn_const)
      (fun z hz => (add_real_mem_H_iff y).2 hz)).sub (F.shift y).smooth.continuous.continuousOn
  change h' φ' + chartShift F q y φ' =
    h φ + smoothDist upperHalfPlaneOpens (fun z => q z - F.f z) φ + a * ∫ z, φ' z
  rw [htr φ φ' hφ, chartShift, smoothDist_apply hc', smoothDist_apply hc]
  have hi : (∫ z, φ' z * (q (z + y) - (F.shift y).f z)) =
      ∫ z, φ z * (q z - F.f z) := by
    simp only [hφ, CMCut.shift_f]
    exact integral_add_right_eq_self (fun z => φ z * (q z - F.f z)) (y : ℂ)
  rw [hi]
  ring

namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- Both directions of absolute continuity of the explicit tilt. -/
theorem tilt_equivalent : D.tilt ≪ D.Q₀ ∧ D.Q₀ ≪ D.tilt :=
  ⟨withDensity_absolutelyContinuous _ _, absolutelyContinuous_withDensity_exp D.Λ_measurable D.k_pos⟩

/-- Equivalent laws give the same completed reference driving filtration. -/
theorem driving_tilt_eq {nL nR : ℕ} {W : ℝ≥0 → S → ℝ}
    {VL : Fin nL → ℝ≥0 → S → ℝ} {VR : Fin nR → ℝ≥0 → S → ℝ} {e : S → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR e) :
    drivingFiltration D.tilt hX = drivingFiltration D.Q₀ hX :=
  le_antisymm (RetAux79.drivingFiltration_le_of_absolutelyContinuous hX D.tilt_equivalent.2)
    (RetAux79.drivingFiltration_le_of_absolutelyContinuous hX D.tilt_equivalent.1)

/-- The shifted chart field is measurable. -/
theorem measurable_chartField : Measurable D.chartField :=
  (Coupling.measurable_add_distOnConst (chartShift D.F D.q D.y)).comp D.coupling.2.1

/-- The chart and physical fields satisfy the exact frozen translation predicate. -/
theorem translate_shift : ∀ ω, IsTranslateAddConst D.y (D.θ * QuantumZipper.chiC D.κ)
    (D.shiftedField ω) (D.chartField ω) := fun ω =>
  isTranslateAddConst_add_chartShift (D.translate ω) D.F D.q_extension.1.continuousOn

end CMIVSetting
end InteractingSLE.Restart.FlowStopIdentCMI
