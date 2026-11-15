/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceInputs
import InteractingSLE.Spec.Sec5.Aux61MarksAlive

/-! # Recording the concrete source code from its contact rule -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW.SourceSetting
open Aux61Marks Aux61ChLoc Aux61ULoc Aux61FibData Aux61GInst LawUnique GlueCond
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)

/-- The physical stop fact applies on the regular restart event as well as
its almost surely equal initial-record event. -/
theorem exit_on_event
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ)
    (i : F.ι) : ∀ᵐ p ∂S.μ, p ∈ F.event i → p ∈ exitEv (F.event i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      (F.path i) (F.contact i) (F.data i).V := by
  filter_upwards [hR.event_version i, hR.physical_stop i] with p he hp hx
  obtain ⟨_, hpos, hstop⟩ := hp (he ▸ hx)
  exact Aux61GCont.mem_exitEv_of_contact_or_exit hx hpos hstop

/-- MARKS' landed record theorem supplies `Inputs.code_marks`. The only
extra input is the record reading of the actual contact rule and path. -/
theorem code_marks_of_record
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ)
    (Ta : F.ι → SourceRecord S.nL S.nR → ℝ≥0∞)
    (hTam : ∀ i, Measurable (Ta i)) (hTaG : ∀ i, IsGalmarinoRule stopRec (Ta i))
    (hrec : ∀ i, ∀ᵐ p ∂S.μ,
      (∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < F.contact i p → F.path i p v =
        Restart.FlowStopIdentG.histTrace 0 (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (F.start i + v)) ∧
      Ta i (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
        (F.start i : ℝ≥0∞) + F.contact i p) (i : F.ι) (q : ℝ≥0) :
    (Aux61FibK.codeFiltration.{u} q).comap (fun p => ULift.up.{u} ((S.marksData F).code i p)) ≤
      (S.marksData F).baseMarks i q := by
  apply codeFiltration_le_nullRuleMarks_of_record (hR.spec i) (hR.open_window i) (hR.zero_window i)
    (hR.landing i) (hR.injective_path i) (hR.chart_measurable i) (hTam i) (hTaG i)
    (hR.continuous_lift i) (S.own.coupling.2.1.comp measurable_fst) (F.data i) rfl (hR.clearance i) q
    (sourceEvent_marks F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hR i q) _
    (S.exit_on_event F hR i)
  filter_upwards [hrec i] with p hp
  exact ⟨rfl, hp⟩

end InteractingSLE.Sec5.Aux61SlitW.SourceSetting
