/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWProof
import InteractingSLE.Spec.Coupling.MartMeans2Announce

/-! # Adaptedness of a measurable version of the available trace -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- A measurable trace version is adapted before the original lifetime.
The reader only uses the driver through the current deterministic time. -/
theorem measurableSet_trace_before {η : S → ℝ≥0 → ℂ}
    (hm : ∀ t, Measurable fun ω => η ω t)
    (hag : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → η ω t = D.Γ ω t)
    (t : ℝ≥0) {A : Set ℂ} (hA : MeasurableSet A) :
    MeasurableSet[D.driving t] {ω | (t : ℝ≥0∞) < D.U ω ∧ η ω t ∈ A} := by
  classical
  have ha : AdaptedBefore D.driving D.U D.W₀ := Ito.adaptedBefore_mono
    (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W D.killed)
  have hlive : MeasurableSet[D.driving t] {ω | (t : ℝ≥0∞) < D.U ω} := by
    simpa only [mem_univ, and_true] using ha t univ MeasurableSet.univ
  let w : S → ℝ≥0 → ℝ := fun ω r => Girsanov.killed D.U D.W₀ (min r t) ω
  have hw : Measurable[D.driving t] w := @Measurable.of_eval S ℝ≥0 (fun _ => ℝ)
    (D.driving t) _ _ fun r =>
    (Girsanov.measurable_killed ha (min r t)).mono (D.driving.mono (min_le_right _ _)) le_rfl
  let R : S → ℂ := fun ω => (D.y : ℂ) + LP.traceAt t (w ω)
  have hR : Measurable[D.driving t] R := measurable_const.add ((LP.measurable_traceAt t).comp hw)
  have he : ∀ᵐ ω ∂D.Q₀, (t : ℝ≥0∞) < D.U ω → R ω = η ω t := by
    filter_upwards [hag, D.trace, D.coupling.1.ae_isIntegratedSLEPath] with ω hω hg hp ht
    have heq : LP.traceAt t (w ω) = LP.traceAt t (D.W₀ · ω) :=
      LP.traceAt_congr fun r hr => by
        simp only [w, min_eq_left hr, Girsanov.killed_of_lt
          ((ENNReal.coe_le_coe.2 hr).trans_lt ht)]
    change (D.y : ℂ) + LP.traceAt t (w ω) = η ω t
    rw [heq, LP.traceAt_eq_of_isGeneratingTrace hg hp.isForcePath.continuousOn_w
      hp.isForcePath.w_zero ht, hω t ht.le]
    exact add_sub_cancel _ _
  apply WholeField.measurableSet_of_ae_eq (D.driving.le t)
    (fun N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t)
    ((measurableSet_lt measurable_const (FlowStopIdentLift.measurable_lifetime D.killed)).inter (hm t hA))
    (hlive.inter (hR hA))
  filter_upwards [he] with ω hω
  apply propext
  constructor
  · rintro ⟨ht, hη⟩
    exact ⟨ht, by change R ω ∈ A; rw [hω ht]; exact hη⟩
  · rintro ⟨ht, hη⟩
    exact ⟨ht, by change η ω t ∈ A; rw [← hω ht]; exact hη⟩

end CMIVSetting
end InteractingSLE.Restart.FlowStopIdentCMI
