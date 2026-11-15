/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVKernel

/-!
# The positive-exit converse, from the explicit clock and tilt-locality inputs

The kernel, Gaussian clause, integrability, Brownian enlargement, tower,
terminal conditional law, product transfer, and trace are proved here or in
the preceding adapters. Only the named clock construction and tilt-locality
remain inputs; neither is asserted to be proved.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open Sec7.PocketTraversal
variable {S : Type u} [MeasurableSpace S] {D : CMIVSetting S} (C : CMIVClock D)

/-- The reference driving filtration is contained in the original driving filtration. -/
theorem CMIVClock.driving_le : drivingFiltration D.Q₀ C.killed ≤ D.driving := by
  have hraw := Ito.killedDrivingFiltration_le
    (MartChar.adaptedBefore_of_stronglyAdapted C.stopping C.adapted)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted C.stopping
      (stronglyAdapted_geomLW C.adapted C.continuous measurable_const i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted C.stopping
      (stronglyAdapted_geomRW C.adapted C.continuous measurable_const j)) C.killed
  have hid : usualAugmentation D.driving D.Q₀ = D.driving := by
    rw [Ito.usualAugmentation_eq_rightCont]
    have hn : Ito.nullAugmented D.driving D.Q₀ = D.driving :=
      Ito.nullAugmented_usualAugmentation (killedDrivingFiltration D.killed) D.Q₀
    rw [hn]
    exact Filtration.rightCont_self _
  exact (Ito.usualAugmentation_mono hraw D.Q₀).trans hid.le

/-- With a regularized clock, tilt-locality is the sole remaining hull input. -/
theorem CMIVClock.exists_isStoppedFlowLine (hlocal : CMIVTiltLocalityStatement.{u}) :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
      StoppedExtend.IsStoppedFlowLine D.κ D.bR D.JR D.y D.θ (D.tilt.prod ν)
        (fun p => D.shiftedField p.1) (fun p => D.Γ p.1) (fun p => C.e p.1) := by
  let _ := D.Q₀_prob
  let _ : IsProbabilityMeasure D.tilt := D.tilt_prob
  let _ : D.driving.IsRightContinuous := by
    unfold CMIVSetting.driving drivingFiltration usualAugmentation
    infer_instance
  have hF := Theorem15.isOrderedForceWord_flowLine D.bR D.JR D.y
  have hpos : ∀ᵐ ω ∂D.tilt, 0 < C.e ω := D.tilt_equivalent.1.ae_le C.ae_pos
  have hinit : ∀ᵐ ω ∂D.tilt, 0 < C.e ω ∧
      ContinuousOn (C.W · ω) {t | (t : ℝ≥0∞) < C.e ω} ∧ C.W 0 ω = 0 ∧
      (∀ i, geomLW C.W (fun _ => flowLineXL D.bR D.JR D.y) i 0 ω = flowLineXL D.bR D.JR D.y i) ∧
      ∀ j, geomRW C.W (fun _ => flowLineXR D.bR D.JR D.y) j 0 ω = flowLineXR D.bR D.JR D.y j := by
    filter_upwards [hpos] with ω hω
    exact ⟨hω, (C.continuous ω).continuousOn, C.zero ω,
      fun i => geomLW_zero C.continuous C.zero (hF.2.1 i),
      fun j => geomRW_zero C.continuous C.zero (hF.2.2.2 j)⟩
  have hint := fun φ => Coupling.MartMeans2.integrable_apply_of_isCouplingCharFun
    C.isCouplingCharFun hinit φ ((LQGMetric.measurable_distOn_apply φ).comp D.measurable_chartField)
  have hgff := fun (u₀ : ℂ → ℝ) hu₀ => Sec7.Lemma71J.isZBGFFProcess_of_isCouplingCharFun
    (u₀ := u₀) C.isCouplingCharFun D.measurable_chartField hinit hu₀
  have hnull : ∀ A, MeasurableSet A → D.tilt A = 0 → MeasurableSet[D.driving 0] A :=
    fun A hA h0 => Ito.measurableSet_usualAugmentation_of_null hA (D.tilt_equivalent.2 h0) 0
  have hT := RetAux79.isAnnouncingSeq_of_absolutelyContinuous C.announcing le_rfl D.tilt_equivalent.1
  have hle : drivingFiltration D.tilt C.killed ≤ D.driving := by
    rw [D.driving_tilt_eq C.killed]
    exact C.driving_le
  have hσ := fun n => show IsStoppingTime (drivingFiltration D.tilt C.killed) (C.σ n) from by
    rw [D.driving_tilt_eq C.killed]
    exact C.σ_stopping n
  obtain ⟨ν, hν, 𝓕, B, hc⟩ := exists_stoppedHullCoupling_prod_of_clock D.κ_pos hF.2.1 hF.2.2.2
    hF.1 hF.2.2.1 C.zero C.continuous C.adapted C.stopping hnull hT D.measurable_chartField hint hgff
    C.isCouplingCharFun (D.tilt_equivalent.1.ae_le C.threshold) C.killed hle hσ C.σ_monotone
    (D.tilt_equivalent.1.ae_le C.σ_lt) (D.tilt_equivalent.1.ae_le C.σ_limit) (hlocal D C)
  refine ⟨ν, hν, fun p => D.chartField p.1, 𝓕, fun t p => C.W t p.1,
    fun i t p => geomLW C.W (fun _ => flowLineXL D.bR D.JR D.y) i t p.1,
    fun j t p => geomRW C.W (fun _ => flowLineXR D.bR D.JR D.y) j t p.1,
    B, fun p => D.translate_shift p.1, hc, ?_⟩
  exact ConverseBefore.ae_fst_of_ae (P₀ := ν) (D.tilt_equivalent.1.ae_le C.ae_generatingTrace)

end InteractingSLE.Restart.FlowStopIdentCMI
