/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafAuxRAssembly
import InteractingSLE.Spec.Coupling.WholeField2Germ

/-!
# Filtrations and closed records of earlier stopped prefixes

Restricting at a stopping time reduces the driving filtration. At an arbitrary
stop of the restricted filtration, the history killed at its minimum with the
prefix lifetime is measurable in the stopped sigma algebra. Aux. 54's left-limit
reader then restores the endpoint without revealing a future sample.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF Restart.Aux54

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V S : Ω → ℝ≥0∞}

/-- Killing at an earlier stopping time reduces the augmented driving filtration. -/
theorem drivingFiltration_le_of_earlier_stop
    (hXV : IsMeasurableKilledDriving W VL VR V)
    (hXS : IsMeasurableKilledDriving W VL VR S)
    (hS : IsStoppingTime (drivingFiltration P hXV) fun ω => (S ω : WithTop ℝ≥0))
    (hle : ∀ ω, S ω ≤ V ω) : drivingFiltration P hXS ≤ drivingFiltration P hXV := by
  have hw := (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_W hXV)).of_le hS hle
  have hl := fun i => (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_VL hXV i)).of_le hS hle
  have hr := fun i => (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_VR hXV i)).of_le hS hle
  have h := Ito.usualAugmentation_mono (Ito.killedDrivingFiltration_le hw hl hr hXS) P
  have hid : usualAugmentation (drivingFiltration P hXV) P = drivingFiltration P hXV := by
    change usualAugmentation (usualAugmentation (killedDrivingFiltration hXV) P) P = _
    rw [Ito.usualAugmentation_eq_rightCont, Ito.nullAugmented_usualAugmentation,
      Filtration.IsRightContinuous.eq]
    rfl
  exact hid ▸ h

/-- The killed record through `τ ∧ S` is measurable at `τ` in the driving
filtration killed at `S`, including when `τ = S`. -/
theorem measurable_killedHistory_min_stopped
    (hXS : IsMeasurableKilledDriving W VL VR S) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hXS) τ) :
    Measurable[hτ.measurableSpace]
      (killedHistory W VL VR fun ω => min (τ ω : ℝ≥0∞) (S ω)) := by
  have hS := isStoppingTime_lifetime_driving (P := P) hXS
  have hθ := hτ.min hS
  have hle : ∀ ω, min (τ ω : ℝ≥0∞) (S ω) ≤ S ω := fun _ => min_le_right _ _
  have hw := (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_W hXS)).of_le hθ hle
  have hl := fun i => (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_VL hXS i)).of_le hθ hle
  have hr := fun i => (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_VR hXS i)).of_le hθ hle
  have hθm : Measurable fun ω => min (τ ω : ℝ≥0∞) (S ω) :=
    hθ.measurable.mono hθ.measurableSpace_le le_rfl
  have hXθ := isMeasurableKilledDriving_of_le hXS hθm hle
  have hraw := Ito.killedDrivingFiltration_le hw hl hr hXθ
  have hrec := measurable_killedHistory_stopped' hθ fun p A hA =>
    hraw (dyadicTime p) _ (Sec4.measurable_killedSample hXθ p hA)
  exact hrec.mono (IsStoppingTime.measurableSpace_mono hθ hτ (fun _ => min_le_left _ _)) le_rfl

/-- A stopped record with its endpoint restored and its later samples set to zero. -/
def closedPrefixHistory {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (γ : HistorySpace nL nR) : HistorySpace nL nR :=
  Sec4.stopHistory (fun δ => δ.1.toNNReal) (recH xL xR γ)

/-- The closed-prefix reader is Borel on every history. -/
theorem measurable_closedPrefixHistory {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    Measurable (closedPrefixHistory xL xR) :=
  (Sec4.measurable_stopHistory (ENNReal.measurable_toNNReal.comp measurable_fst)).comp
    (measurable_recH xL xR)

end InteractingSLE.WFS
