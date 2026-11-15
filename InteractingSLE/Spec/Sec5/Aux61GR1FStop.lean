/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GR1FBuffer
import InteractingSLE.Spec.Sec5.Aux61Asm2Build

/-! # The exact physical-stop field of the built R1 restart family

The recorded path is physically proper almost surely. Its first contact
with the recorded closed obstacle is positive when its seed is off that
obstacle. A bounded physical inverse image of the window then supplies
the finite-contact-or-window-exit alternative of `R1RestartInputs`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GR1F
open Aux61Asm2 Aux61SlitW Aux61SlitW.SourceSetting Aux61FibData
open Aux61ULoc Aux61Marks Aux61GInst LawUnique Restart.FlowStopIdentG
universe u

/-- Every shift of the actual own record path tends to physical infinity. -/
theorem ae_recordPath_proper (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ, ∀ t₀ : ℝ≥0,
    Tendsto (fun v : ℝ≥0 => ‖recordPath S t₀ p v‖) atTop atTop := by
  filter_upwards [S.physical_path, ae_recordPath S] with p hp hr t₀
  have ht : Tendsto (fun v : ℝ≥0 => (t₀ : ℝ) + (v : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_left t₀.coe_nonneg)
      (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hnorm := hp.2.2.tendsto.comp ht
  convert hnorm using 1
  funext v
  rw [(hr t₀).1 v]
  simp only [← NNReal.coe_add, Real.toNNReal_coe, Function.comp_apply]

variable {S : SourceSetting.{u}} (D : R1Restart S) (h : D.HasChart)

/-- The relative contact chosen by the assembler is the actual hitting
time, on the selected event. This reuses MARKS' absolute contact identity. -/
theorem ae_contact_eq_hitTime
    (hstart : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
      recordPath S (rationalTime (D.q i)) p 0 ∉
        retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
          (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (i : D.ι) : ∀ᵐ p ∂S.μ, p ∈ D.event i →
      D.contact i p = hitTime (recordPath S (rationalTime (D.q i)))
        (fun p => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
          (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) p := by
  filter_upwards [hstart i, ae_recordPath S, ae_continuous_ownTrace S] with p h0 hrp hct he
  have hv := contactRule_eq_add_hitTime (ρ := recordPath S (rationalTime (D.q i)))
    (C := retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (t₀ := rationalTime (D.q i))
    (Y₀ := fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2)
    (R₀ := fun p => killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (x := p)
    (hrp _).2.1 hct (isClosed_retObs _ _) (retObs_nonempty _ _) (h0 he) fun _ _ _ => rfl
  change contactRule _ _ _ - ((rationalTime (D.q i) : ℝ≥0) : ℝ≥0∞) = _
  rw [hv, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
  rfl

/-- The exact `physical_stop` field follows from the independently needed
pre-contact domain inclusion and boundedness of the physical window. -/
theorem physical_stop_of_bounded_inverse
    (hstart : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
      recordPath S (rationalTime (D.q i)) p 0 ∉
        retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
          (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (hinside : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → ∀ v : ℝ≥0,
      0 < v → (v : ℝ≥0∞) < D.contact i p → recordPath S (rationalTime (D.q i)) p v ∈
        (sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom)
    (hbounded : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → Bornology.IsBounded
      ((sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.1 ''
        ((D.data i).V ∩ H))) :
    ∀ i, ∀ᵐ p ∂S.μ, sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      D.selected i → p ∈ (D.src h).event i ∧ 0 < (D.src h).contact i p ∧
      ((D.src h).contact i p < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < (D.src h).contact i p ∧
        inPath ((D.src h).event i)
          (sourceChart (withRecordPath S (D.src h)) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
          ((withRecordPath S (D.src h)).path i) ((D.src h).contact i) p v ∉ (D.data i).V) := by
  intro i
  filter_upwards [ae_contact_eq_hitTime D h hstart i, hstart i, ae_recordPath S,
    ae_recordPath_proper S, hinside i, hbounded i] with p hhit h0 hr hp hin hb hsel
  have he : p ∈ D.event i := hsel
  have hpos : 0 < D.contact i p := by
    rw [hhit he]
    exact Aux61GCont.hitTime_pos_of_notMem (hr _).2.1 (isClosed_retObs _ _) (h0 he)
  refine ⟨he, hpos, ?_⟩
  by_cases hfin : D.contact i p < ⊤
  · exact Or.inl hfin
  · right
    have htop : D.contact i p = ⊤ := top_unique (not_lt.1 hfin)
    apply exists_exit_of_contact_top he ((D.chart_spec h i).2.1 _) htop
      (fun v hv => hin he v hv (htop ▸ ENNReal.coe_lt_top)) (hp _) (hb he)

end InteractingSLE.Sec5.Aux61GR1F
