/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXExit

/-! # The source exit announcement, without a residual input -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI

/-- The source exit is a measurable stopping time and has strict finite
announcements in the original driving filtration. -/
theorem cmiWSourceAnnounceStatement : CMIWSourceAnnounceStatement.{u} := by
  intro S mS D hseed
  classical
  let _ := D.Q₀_prob
  have : D.driving.IsRightContinuous := by
    unfold CMIVSetting.driving drivingFiltration
    infer_instance
  have hstart : (D.y : ℂ) ∈ D.V := not_not.1 fun h => hseed (Or.inl h)
  have hinit : ¬ ForceWord.ThresholdCondition (flowLineRhoL D.κ D.b D.J D.y D.θ)
      (flowLineRhoR D.κ D.b D.J D.y D.θ) 0 (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y) :=
    fun h => hseed (Or.inr h)
  obtain ⟨Z, hZ0, hZc, hZa, hag⟩ := D.exists_continuous_adapted_trace
  have hVc : D.Vᶜ.Nonempty := by
    obtain ⟨R, hR⟩ := D.V_bounded.exists_norm_le
    refine ⟨((|R| + 1 : ℝ) : ℂ), fun hz => ?_⟩
    have h := hR _ hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
    linarith [le_abs_self R]
  obtain ⟨T, hT, -⟩ := D.coupling.1.exists_isAnnouncingSeq_drivingFiltration
    D.κ_pos hinit D.killed
  obtain ⟨A, hA⟩ := exists_isAnnouncingSeq_exitTime (P := D.Q₀) hZa hZc D.V_open hVc
    (fun ω => hZ0 ω ▸ hstart)
  let e : S → ℝ≥0∞ := fun ω => min (D.U ω) (InteractingSLE.exitTime D.V (Z · ω))
  have hem : Measurable e := (FlowStopIdentLift.measurable_lifetime D.killed).min
    (InteractingSLE.measurable_exitTime (fun t => (hZa t).mono (D.driving.le t) le_rfl) hZc D.V_open)
  have haW : AdaptedBefore D.driving D.U D.W₀ := Ito.adaptedBefore_mono
    (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W D.killed)
  refine ⟨e, hem, ?_, (Ito.isStoppingTime_lifetime haW).min
    (InteractingSLE.isStoppingTime_exitTime hZa hZc D.V_open),
    fun n ω => min (T n ω) (A n ω), isAnnouncingSeq_min hT hA⟩
  filter_upwards [hag] with ω hω
  change RLC.exitTime D.V (Z · ω) (D.U ω) = RLC.exitTime D.V (D.Γ ω) (D.U ω)
  have hu : ∀ γ : ℝ≥0 → ℂ, RLC.exitTime univ γ (D.U ω) = D.U ω := fun γ => by
    change min (D.U ω) (InteractingSLE.exitTime univ γ) = D.U ω
    rw [InteractingSLE.exitTime_univ, min_top_right]
  exact (RLC.StoppedAgree.mono (V := D.V) (V' := univ) (subset_univ _)
    ⟨by rw [hu, hu], fun t ht => hω t (by rwa [hu] at ht)⟩).1

end InteractingSLE.Restart.FlowStopIdentCMI
