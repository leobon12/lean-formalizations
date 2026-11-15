/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45ClockDriver
import InteractingSLE.Spec.Coupling.WFSBridge

/-! # Automatic transfer of the clock to the reference driving history -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45
open Restart
namespace ClockSource
variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- The same finite announcing times work in the reference history. Only the
actual driver is retained in the source cutoff history, so no original force
coordinates or finite-word law need to be reconstructed. The reference may
carry any finite family of additional coordinates. -/
theorem announcing_reference {e : S → ℝ≥0∞} {W : ℝ≥0 → S → ℝ}
    (heU : ∀ ω, e ω ≤ D.U ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous (W · ω))
    (hag : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω)
    {nL nR : ℕ} {VL : Fin nL → ℝ≥0 → S → ℝ} {VR : Fin nR → ℝ≥0 → S → ℝ}
    (hX : IsMeasurableKilledDriving W VL VR e)
    {T : ℕ → S → ℝ≥0} (hT : Coupling.IsAnnouncingSeq D.driving D.P e T) :
    Coupling.IsAnnouncingSeq (drivingFiltration D.P hX) D.P e T := by
  classical
  let _ := D.prob
  let 𝓖 := drivingFiltration D.P hX
  have : 𝓖.IsRightContinuous := by unfold 𝓖 drivingFiltration; infer_instance
  have haW : AdaptedBefore 𝓖 e W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _)
    (Coupling.adaptedBefore_killedDriving_W hX)
  obtain ⟨W', -, -, hW'a, hW'ag⟩ := RetAux79.exists_continuous_adapted_stopped hWc hW0 haW
  have hem : Measurable e := FlowStopIdentLift.measurable_lifetime hX
  have hXf : IsMeasurableKilledDriving D.W₀ (fun (_ : Fin 0) _ _ => 0)
      (fun (_ : Fin 0) _ _ => 0) e := by
    intro r A hA
    have hs : {ω | (r : ℝ≥0∞) < e ω ∧
        (D.W₀ r ω, fun _ : Fin 0 => (0 : ℝ), fun _ : Fin 0 => (0 : ℝ)) ∈ A} =
        {ω | (r : ℝ≥0∞) < e ω} ∩ {ω | (r : ℝ≥0∞) < D.U ω ∧
        (D.W₀ r ω, fun _ : Fin 0 => (0 : ℝ), fun _ : Fin 0 => (0 : ℝ)) ∈ A} := by
      ext ω
      exact ⟨fun ⟨ht, hAω⟩ => ⟨ht, ht.trans_le (heU ω), hAω⟩,
        fun ⟨ht, _, hAω⟩ => ⟨ht, hAω⟩⟩
    rw [hs]
    exact (measurableSet_lt measurable_const hem).inter (D.killed r A hA)
  have hes : IsStoppingTime 𝓖 (fun ω => (e ω : WithTop ℝ≥0)) := Ito.isStoppingTime_lifetime haW
  have hXg : IsMeasurableKilledDriving W' (fun (_ : Fin 0) _ _ => 0)
      (fun (_ : Fin 0) _ _ => 0) e := Coupling.isMeasurableKilledDriving_of_adaptedBefore
    (MartChar.adaptedBefore_of_stronglyAdapted hes hW'a)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have hraw := Ito.killedDrivingFiltration_le
    (MartChar.adaptedBefore_of_stronglyAdapted hes hW'a)
    (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) hXg
  have hid : usualAugmentation 𝓖 D.P = 𝓖 := by
    rw [Ito.usualAugmentation_eq_rightCont]
    have hn : Ito.nullAugmented 𝓖 D.P = 𝓖 :=
      Ito.nullAugmented_usualAugmentation (killedDrivingFiltration hX) D.P
    rw [hn]
    exact Filtration.rightCont_self _
  have hle : drivingFiltration D.P hXf ≤ 𝓖 := by
    have hcong : drivingFiltration D.P hXf = drivingFiltration D.P hXg := by
      apply Exist.drivingFiltration_congr_ae
      filter_upwards [hag] with ω hagω
      refine ⟨rfl, fun t ht => ?_⟩
      exact ⟨(hW'ag ω t ht).trans (hagω t ht),
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    rw [hcong]
    exact (Ito.usualAugmentation_mono hraw D.P).trans hid.le
  refine ⟨fun n => ?_, hT.2⟩
  have hs := WFS.isStoppingTime_drivingFiltration_of_lt D.killed hXf heU
    (hT.1 n) (hT.2.2.1 n)
  exact fun t => hle t _ (hs t)

end ClockSource
end InteractingSLE.Sec5.Aux61R45
