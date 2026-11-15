/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWChart

/-! # Strict-stop locality and the exact terminal locality boundary -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (fwdHull)
variable {S : Type u} [MeasurableSpace S] {D : CMIVSetting S} (C : CMIVClock D)

/-- Before the exit, the old optional coupling supplies locality of the agreeing hull. -/
theorem CMIVClock.isLocalSet_original_of_lt {τ : S → WithTop ℝ≥0}
    (hτ : IsStoppingTime D.driving τ) (hlt : ∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) < C.e ω) :
    IsLocalSet (fun ω => fwdHull (Ito.rpath (C.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.h' D.Q₀ := by
  have hτU : ∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) < D.U ω := by
    filter_upwards [hlt, C.ae_exit] with ω h he
    rw [he] at h
    exact h.trans_le (min_le_left _ _)
  obtain ⟨hX, hker⟩ := D.coupling.2.2.2
  have hloc := (hker τ hτ hτU).1
  apply Coupling.IsLocalSet.congr_set hloc
  filter_upwards [C.pathData τ hτ hlt] with ω h
  obtain ⟨t₂, ht₂, hag⟩ := h.2.2.1
  exact InteractingSLE.fwdHull_eq_of_eqOn (NNReal.coe_nonneg _) ht₂ hag

/-- The tilted locality assertion is fully proved at stops strictly before the exit. -/
theorem CMIVClock.isLocalSet_tilt_of_lt {τ : S → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration D.tilt C.killed) τ)
    (hlt : ∀ᵐ ω ∂D.tilt, (τ ω : ℝ≥0∞) < C.e ω) :
    IsLocalSet (fun ω => fwdHull (Ito.rpath (C.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.chartField D.tilt := by
  have hs : IsStoppingTime D.driving τ := by
    have hr : IsStoppingTime (drivingFiltration D.Q₀ C.killed) τ := by
      rwa [D.driving_tilt_eq C.killed] at hτ
    exact fun t => C.driving_le t _ (hr t)
  exact D.isLocalSet_chartField (C.isLocalSet_original_of_lt hs (D.tilt_equivalent.2.ae_le hlt))

/-- Remaining terminal step: locality of the original field through an exit,
including equality with the original lifetime. No change of measure is involved. -/
def CMIWTerminalHullLocalityStatement : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (D : CMIVSetting S) (C : CMIVClock D)
    (τ : S → WithTop ℝ≥0) (_hτ : IsStoppingTime (drivingFiltration D.Q₀ C.killed) τ),
    (∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) ≤ C.e ω ∧ τ ω ≠ ⊤) →
    IsLocalSet (fun ω => fwdHull (Ito.rpath (C.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.h' D.Q₀

/-- All change-of-measure and chart steps of tilt-locality are discharged. -/
theorem cmiVTiltLocalityStatement_of_terminal (hterminal : CMIWTerminalHullLocalityStatement.{u}) :
    CMIVTiltLocalityStatement.{u} := by
  intro S mS D C τ hτ hτe
  have hr : IsStoppingTime (drivingFiltration D.Q₀ C.killed) τ := by
    rwa [D.driving_tilt_eq C.killed] at hτ
  exact D.isLocalSet_chartField (hterminal D C τ hr (D.tilt_equivalent.2.ae_le hτe))

end InteractingSLE.Restart.FlowStopIdentCMI
