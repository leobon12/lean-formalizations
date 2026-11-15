/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXGeom
import InteractingSLE.Spec.Restart.RetPlumbProofDriverAnnounce

/-! # Source announcements lift to the reference killed driving -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open Sec7.PocketTraversal

/-- The reference exit announcement. Restrict the original history at the
exit and apply the landed cutoff stopping-time lift and history congruence. -/
theorem cmiWReferenceAnnounceStatement : CMIWReferenceAnnounceStatement.{u} := by
  intro S mS D e W he hW0 hWc hag hpos hX
  classical
  let _ := D.Q₀_prob
  let 𝓖 := drivingFiltration D.Q₀ hX
  have : 𝓖.IsRightContinuous := by unfold 𝓖 drivingFiltration; infer_instance
  have hseed : ¬ FlowStopIdentG.SeedStop D.κ D.b D.J D.y D.θ D.V := by
    intro hseed
    obtain ⟨ω, hp, hz⟩ := (hpos.and (he.trans (D.ae_exit_zero hseed))).exists
    exact (ne_of_gt hp) hz
  obtain ⟨e₀, -, he₀, -, T, hT⟩ := cmiWSourceAnnounceStatement D hseed
  have he₀e : e₀ =ᵐ[D.Q₀] e := he₀.trans he.symm
  have haW : AdaptedBefore 𝓖 e W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _)
    (Coupling.adaptedBefore_killedDriving_W hX)
  obtain ⟨W', hW'0, hW'c, hW'a, hW'ag⟩ := RetAux79.exists_continuous_adapted_stopped hWc hW0 haW
  have hag' : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W' t ω = D.W₀ t ω := by
    filter_upwards [hag] with ω hω t ht
    exact (hW'ag ω t ht).trans (hω t ht)
  have hgeom := D.ae_original_geom_of_agree he hW'c hag'
  let f : S → ℝ≥0∞ := fun ω => min (e ω) (D.U ω)
  have hem : Measurable e := FlowStopIdentLift.measurable_lifetime hX
  have hfm : Measurable f := hem.min (FlowStopIdentLift.measurable_lifetime D.killed)
  have hfe : f =ᵐ[D.Q₀] e := he.mono fun ω hω =>
    min_eq_left (hω ▸ min_le_left _ _)
  have hXf : IsMeasurableKilledDriving D.W₀ D.VL₀ D.VR₀ f := by
    intro r A hA
    have hs : {ω | (r : ℝ≥0∞) < f ω ∧
        (D.W₀ r ω, fun i => D.VL₀ i r ω, fun j => D.VR₀ j r ω) ∈ A} =
        {ω | (r : ℝ≥0∞) < f ω} ∩ {ω | (r : ℝ≥0∞) < D.U ω ∧
        (D.W₀ r ω, fun i => D.VL₀ i r ω, fun j => D.VR₀ j r ω) ∈ A} := by
      ext ω
      constructor
      · rintro ⟨hr, hAω⟩
        exact ⟨hr, hr.trans_le (min_le_right _ _), hAω⟩
      · rintro ⟨hr, -, hAω⟩
        exact ⟨hr, hAω⟩
    rw [hs]
    exact (measurableSet_lt measurable_const hfm).inter (D.killed r A hA)
  have hes : IsStoppingTime 𝓖 (fun ω => (e ω : WithTop ℝ≥0)) := Ito.isStoppingTime_lifetime haW
  have hWL := fun i => stronglyAdapted_geomLW hW'a hW'c
    (xL := fun _ => flowLineXL D.b D.J D.y) measurable_const i
  have hWR := fun j => stronglyAdapted_geomRW hW'a hW'c
    (xR := fun _ => flowLineXR D.b D.J D.y) measurable_const j
  have hXg := Coupling.isMeasurableKilledDriving_of_adaptedBefore
    (MartChar.adaptedBefore_of_stronglyAdapted hes hW'a)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hes (hWL i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hes (hWR j))
  have hraw := Ito.killedDrivingFiltration_le
    (MartChar.adaptedBefore_of_stronglyAdapted hes hW'a)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hes (hWL i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hes (hWR j)) hXg
  have hid : usualAugmentation 𝓖 D.Q₀ = 𝓖 := by
    rw [Ito.usualAugmentation_eq_rightCont]
    have hn : Ito.nullAugmented 𝓖 D.Q₀ = 𝓖 :=
      Ito.nullAugmented_usualAugmentation (killedDrivingFiltration hX) D.Q₀
    rw [hn]
    exact Filtration.rightCont_self _
  have hle : drivingFiltration D.Q₀ hXf ≤ 𝓖 := by
    have hcong : drivingFiltration D.Q₀ hXf = drivingFiltration D.Q₀ hXg := by
      apply Exist.drivingFiltration_congr_ae
      filter_upwards [hfe, hgeom] with ω hf hg
      refine ⟨hf.symm, fun t ht => ?_⟩
      obtain ⟨hw, hl, hr⟩ := hg t (hf ▸ ht)
      exact ⟨hw.symm, fun i => (hl i).symm, fun j => (hr j).symm⟩
    rw [hcong]
    exact (Ito.usualAugmentation_mono hraw D.Q₀).trans hid.le
  have hTf : ∀ n, ∀ᵐ ω ∂D.Q₀, (T n ω : ℝ≥0∞) < f ω := fun n => by
    filter_upwards [hT.2.2.1 n, he₀e, hfe] with ω ht heq hf
    rwa [hf, ← heq]
  have hTs : ∀ n, IsStoppingTime 𝓖 fun ω => (T n ω : WithTop ℝ≥0) := by
    intro n
    have hs := WFS.isStoppingTime_drivingFiltration_of_lt D.killed hXf
      (fun _ => min_le_right _ _) (hT.1 n) (hTf n)
    exact fun t => hle t _ (hs t)
  refine ⟨fun n ω => (T n ω : WithTop ℝ≥0), hTs,
    fun ω n m hnm => WithTop.coe_le_coe.2 (hT.2.1 ω hnm), ?_, ?_⟩
  · filter_upwards [ae_all_iff.2 hTf, hfe] with ω ht hf n
    exact hf ▸ ht n
  · filter_upwards [RetAux79.ae_tendsto_of_isAnnouncingSeq hT, he₀e] with ω ht heq
    exact heq ▸ ht

end InteractingSLE.Restart.FlowStopIdentCMI
