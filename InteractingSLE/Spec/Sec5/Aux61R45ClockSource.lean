/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45ClockTrace

/-! # The open-window clock in a general actual driving history -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45
open Restart Restart.FlowStopIdentCMI
namespace ClockSource
variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- Construct the window-exit clock and its strict finite announcements.
The only predictability input concerns the source lifetime, before imposing
any reference force word. The exit itself requires no additional clock input. -/
theorem exists_announced_exit {V : Set ℂ} (hV : IsOpen V)
    (hVc : Vᶜ.Nonempty) (hstart : (D.y : ℂ) ∈ V)
    {R : ℕ → S → ℝ≥0} (hU_announcing : Coupling.IsAnnouncingSeq D.driving D.P D.U R) :
    ∃ e : S → ℝ≥0∞, Measurable e ∧ (∀ ω, e ω ≤ D.U ω) ∧
      (e =ᵐ[D.P] fun ω => RLC.exitTime V (D.Γ ω) (D.U ω)) ∧
      IsStoppingTime D.driving (fun ω => (e ω : WithTop ℝ≥0)) ∧
      ∃ T : ℕ → S → ℝ≥0, Coupling.IsAnnouncingSeq D.driving D.P e T := by
  let _ := D.prob
  obtain ⟨Z, hZ0, hZc, hZa, hag⟩ := D.exists_continuous_adapted_trace
  obtain ⟨A, hA⟩ := exists_isAnnouncingSeq_exitTime (P := D.P) hZa hZc hV hVc
    (fun ω => hZ0 ω ▸ hstart)
  let e : S → ℝ≥0∞ := fun ω => min (D.U ω) (InteractingSLE.exitTime V (Z · ω))
  have hem : Measurable e := (FlowStopIdentLift.measurable_lifetime D.killed).min
    (InteractingSLE.measurable_exitTime (fun t => (hZa t).mono (D.driving.le t) le_rfl) hZc hV)
  refine ⟨e, hem, fun _ => min_le_left _ _, ?_,
    (Ito.isStoppingTime_lifetime D.adaptedBefore).min
      (InteractingSLE.isStoppingTime_exitTime hZa hZc hV),
    fun n ω => min (R n ω) (A n ω), isAnnouncingSeq_min hU_announcing hA⟩
  filter_upwards [hag] with ω hω
  change RLC.exitTime V (Z · ω) (D.U ω) = RLC.exitTime V (D.Γ ω) (D.U ω)
  have hu : ∀ γ : ℝ≥0 → ℂ, RLC.exitTime univ γ (D.U ω) = D.U ω := fun γ => by
    change min (D.U ω) (InteractingSLE.exitTime univ γ) = D.U ω
    rw [InteractingSLE.exitTime_univ, min_top_right]
  exact (RLC.StoppedAgree.mono (V := V) (V' := univ) (subset_univ _)
    ⟨by rw [hu, hu], fun t ht => hω t (by rwa [hu] at ht)⟩).1

end ClockSource
end InteractingSLE.Sec5.Aux61R45
