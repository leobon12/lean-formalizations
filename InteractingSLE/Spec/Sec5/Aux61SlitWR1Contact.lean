/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSelectionFields
import InteractingSLE.Spec.Sec5.Aux61Asm2Build
import InteractingSLE.Spec.Sec5.Aux61GContHistory

/-!
# The start-off input of the actual R1 restart family

R1's separated interior prefix event supplies `R1RestartInputs.start_off`.
The proof reads only the selected initial record. The chart, future contact
time, restart specification and complete `R1RestartInputs` are not inputs.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61FibData Aux61Restart Aux61ULoc LawUnique Restart.FlowStopIdentG
open Aux61Asm2
universe u
variable {S : SourceSetting.{u}} (D : R1Restart S)

/-- R1's selected prefix facts imply the measurable off-obstacle test on
the initial records, after identifying the two record readers. -/
theorem r1_selected_tipOff_of_prefix
    (hq : ∀ i, 0 < (D.q i : ℝ))
    (hY : ∀ i, ∀ y ∈ D.selected i, D.Y i y = y.1)
    (hη : ∀ i, ∀ y ∈ D.selected i,
      D.η i y = fun t : ℝ => histTrace 0 y.2 t.toNNReal)
    (hprefix : ∀ i, D.selected i ⊆ restartPrefixEvent (rationalTime S.s) (D.q i) (D.Y i) (D.η i)) :
    ∀ i, D.selected i ⊆ tipOffRecords (rationalTime S.s) (rationalTime (D.q i)) := by
  intro i y hy
  apply mem_tipOffRecords_of_restartPrefixEvent (hq i)
  have hp := hprefix i hy
  change InjOn (D.η i y) (Icc (0 : ℝ) (D.q i)) ∧
    MapsTo (D.η i y) (Ioc (0 : ℝ) (D.q i)) H ∧
    0 < infDist (D.η i y (D.q i)) (historyHull (rationalTime S.s) (D.Y i) y) at hp
  have hK : historyHull (rationalTime S.s) (D.Y i) y =
      historyHull (rationalTime S.s) Prod.fst y := by
    simp only [historyHull, hY i y hy]
  rw [hη i y hy, hK] at hp
  exact hp

/-- The start-off field for the built family holds at every selected
sample, from the already required R1 prefix configuration. -/
theorem r1_start_off_of_prefix (h : D.HasChart)
    (hq : ∀ i, 0 < (D.q i : ℝ))
    (hY : ∀ i, ∀ y ∈ D.selected i, D.Y i y = y.1)
    (hη : ∀ i, ∀ y ∈ D.selected i,
      D.η i y = fun t : ℝ => histTrace 0 y.2 t.toNNReal)
    (hprefix : ∀ i, D.selected i ⊆ restartPrefixEvent (rationalTime S.s) (D.q i) (D.Y i) (D.η i))
    (i : D.ι) (p : S.Ω × HistorySpace 0 0) (hp : p ∈ D.event i) :
    recordPath S (rationalTime (D.q i)) p 0 ∉
      retObs (rationalTime S.s) (sourceRecord (D.src h)
        (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) :=
  S.start_off_of_selected_tipOff (D.src h) (r1_selected_tipOff_of_prefix D hq hY hη hprefix) i p hp

/-- The obstacle read from the initial records is the physical retained
counterflow obstacle, simultaneously for every restart index. -/
theorem SourceSetting.ae_retObs_sourceRecord (S : SourceSetting.{u})
    (F : SourceRestartData S.Ω S.nL S.nR) : ∀ᵐ p ∂S.μ, ∀ i,
    retObs (rationalTime S.s)
      (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) =
      (H \ GlueCond.cfHullQ (rationalTime S.s) p.2)ᶜ := by
  filter_upwards [ae_mem_goodCfSet S] with p hp i
  change (H \ historyHull (rationalTime S.s) Prod.fst
    (stopRec (rationalTime S.s) p.2,
      stopRec (F.start i) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)))ᶜ = _
  rw [historyHull_stopRec_eq_cfHullQ hp]

/-- The built contact is the positive first physical contact with the
counterflow obstacle on every selected record passing the initial tip
test. This supplies the contact input of the selected-access landing API. -/
theorem r1_contact_fields_of_tipOff (h : D.HasChart)
    (hsel : ∀ i, D.selected i ⊆ tipOffRecords (rationalTime S.s) (rationalTime (D.q i))) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
      D.contact i p = hitTime (recordPath S (rationalTime (D.q i)))
        (fun p => (H \ GlueCond.cfHullQ (rationalTime S.s) p.2)ᶜ) p ∧
      0 < D.contact i p ∧
      recordPath S (rationalTime (D.q i)) p 0 ∈ H \ GlueCond.cfHullQ (rationalTime S.s) p.2 := by
  intro i
  filter_upwards [ae_recordPath S, ae_continuous_ownTrace S, S.ae_retObs_sourceRecord (D.src h)]
    with p hrp hct hobs he
  have h0 := S.start_off_of_selected_tipOff (D.src h) hsel i p he
  have hv := contactRule_eq_add_hitTime (ρ := recordPath S (rationalTime (D.q i)))
    (C := retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (t₀ := rationalTime (D.q i))
    (Y₀ := fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2)
    (R₀ := fun p => killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (x := p) (hrp _).2.1 hct
    (isClosed_retObs _ _) (retObs_nonempty _ _) h0 fun _ _ _ => rfl
  have hT : D.contact i p = hitTime (recordPath S (rationalTime (D.q i)))
      (fun p => retObs (rationalTime S.s) (sourceRecord (D.src h)
        (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) p := by
    change contactRule _ _ _ - (rationalTime (D.q i) : ℝ≥0∞) = _
    rw [hv, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
    rfl
  have hphys : D.contact i p = hitTime (recordPath S (rationalTime (D.q i)))
      (fun p => (H \ GlueCond.cfHullQ (rationalTime S.s) p.2)ᶜ) p := by
    simpa only [hitTime, hobs i] using hT
  have hstart : recordPath S (rationalTime (D.q i)) p 0 ∉
      (H \ GlueCond.cfHullQ (rationalTime S.s) p.2)ᶜ := by
    rwa [hobs i] at h0
  refine ⟨hphys, ?_, not_not.1 hstart⟩
  rw [hT]
  exact Aux61GCont.hitTime_pos_of_notMem (hrp _).2.1 (isClosed_retObs _ _) h0

/-- The exact `R1Inputs.contact_hit` field for the built family, from the
initial record test alone. -/
theorem r1_contact_hit_of_tipOff (h : D.HasChart)
    (hsel : ∀ i, D.selected i ⊆ tipOffRecords (rationalTime S.s) (rationalTime (D.q i))) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
      D.contact i p = hitTime (recordPath S (rationalTime (D.q i)))
        (fun p => retObs (rationalTime S.s) (sourceRecord (D.src h)
          (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) p ∧
      recordPath S (rationalTime (D.q i)) p 0 ∉ retObs (rationalTime S.s)
        (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
  intro i
  filter_upwards [r1_contact_fields_of_tipOff D h hsel i, S.ae_retObs_sourceRecord (D.src h)]
    with p hp hobs he
  refine ⟨?_, S.start_off_of_selected_tipOff (D.src h) hsel i p he⟩
  simpa only [hitTime, hobs i] using (hp he).1

/-- Before the built contact the actual physical continuation stays in
the complement of the retained counterflow obstacle. -/
theorem r1_physical_before_contact (h : D.HasChart)
    (hsel : ∀ i, D.selected i ⊆ tipOffRecords (rationalTime S.s) (rationalTime (D.q i))) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → ∀ v : ℝ≥0, (v : ℝ≥0∞) < D.contact i p →
      S.path p.1 (rationalTime (D.q i) + v) ∈ H \ GlueCond.cfHullQ (rationalTime S.s) p.2 := by
  intro i
  filter_upwards [r1_contact_fields_of_tipOff D h hsel i, ae_recordPath S] with p hp hrp he v hv
  have hn := notMem_of_lt_hitTime (ρ := recordPath S (rationalTime (D.q i)))
    (F := fun p => (H \ GlueCond.cfHullQ (rationalTime S.s) p.2)ᶜ) ((hp he).1 ▸ hv)
  rw [(hrp _).1] at hn
  exact not_not.1 hn

end InteractingSLE.Sec5.Aux61SlitW
