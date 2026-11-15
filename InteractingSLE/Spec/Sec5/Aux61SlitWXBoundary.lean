/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXContinuation

/-!
# The basic restart clauses and the remaining forward-tip theorem

Initial closure and pre-contact component membership are proved. The full
forward-tip limit is the explicit remaining analytic input, stronger than
convergence along a single inverse access. It is transported to R1's chart.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWX
open Aux61SlitW Aux61Asm2 Aux61Restart Aux61FibData Aux61Marks Aux61ULoc LawUnique
open Restart.FlowStopIdentG
universe u

/-- The whole own-domain forward limit at every positive physical tip.
This named analytic input is not asserted proved by an inverse-access limit. -/
def OwnTipForwardLimit (S : SourceSetting.{u}) : Prop :=
  ∀ᵐ p ∂S.μ, ∀ r : ℝ≥0, 0 < r →
    Tendsto (fwdMap (fun t : ℝ => S.own.W t.toNNReal p.1) r)
      (𝓝[H \ fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) r] (S.path p.1 r)) (𝓝[H] 0)

variable {S : SourceSetting.{u}} {D : R1Restart S} (R : ReaderFacts D) (h : D.HasChart)
include R

/-- The quantitative tip clearance in the selected configuration is the
physical clearance; the stopped record reads the terminal tip exactly. -/
theorem ReaderFacts.ae_clearance : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    0 < infDist (S.path p.1 (rationalTime (D.q i))) (GlueCond.cfHullQ (rationalTime S.s) p.2) := by
  intro i
  filter_upwards [ae_trace_eq_and_continuous S, ae_mem_goodCfSet S] with p htr hgood he
  let y : SourceRecord S.nL S.nR := (stopRec (rationalTime S.s) p.2,
    stopRec (rationalTime (D.q i)) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))
  have hy : y ∈ D.selected i := he
  have hK : historyHull (rationalTime S.s) (D.Y i) y = GlueCond.cfHullQ (rationalTime S.s) p.2 := by
    have heq : historyHull (rationalTime S.s) (D.Y i) y =
        historyHull (rationalTime S.s) Prod.fst y := by
      simp only [historyHull, R.counterflow i y hy]
    rw [heq]
    exact historyHull_stopRec_eq_cfHullQ hgood _
  have hc := (R.configuration i hy).1.2.2
  rw [hK, R.path i y hy ⟨(R.q_pos i).le, le_rfl⟩] at hc
  change 0 < infDist (histTrace 0 (stopRec (rationalTime (D.q i))
    (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) (rationalTime (D.q i))) _ at hc
  rwa [histTrace_stopRec_of_le le_rfl, htr.1] at hc

/-- Initial closure follows from the whole current collar and the actual
Loewner inverse-tip limit. -/
theorem ReaderFacts.ae_start_mem : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    recordPath S (rationalTime (D.q i)) p 0 ∈ closure
      ((sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) := by
  intro i
  filter_upwards [R.ae_geometry h i, S.physical_path, ae_recordPath S] with p hg hp hrp he
  have : (𝓝[H] (0 : ℂ)).NeBot := PrimeEnd.approachH_neBot (0 : ℝ)
  have hlim := hp.2.1.tendsto_fwdMapInv_tip hp.1.continuous_rpath
    (by simpa only [Ito.rpath, Real.toNNReal_zero] using hp.1.2.1) (rationalTime (D.q i)).coe_nonneg
  have hm := mem_closure_of_tendsto hlim (eventually_mem_of_collar (hg he).collar)
  simpa only [(hrp (rationalTime (D.q i))).1 0, add_zero, Real.toNNReal_coe] using hm

/-- The actual continuation stays in R1's selected component before the
first counterflow contact, without assuming an assembled restart spec. -/
theorem ReaderFacts.ae_inside : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < D.contact i p →
      recordPath S (rationalTime (D.q i)) p v ∈
        (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom := by
  intro i
  filter_upwards [R.ae_geometry h i, R.ae_domain h i, R.ae_clearance i, S.physical_path,
    S.counterflow_retained_geometry, ae_recordPath S, r1_contact_fields_of_tipOff D h R.tipOff i]
    with p hg hd hcl hp hcf hrp hct he v hv hvT
  obtain ⟨b, hb⟩ := hd he
  have hT : D.contact i p = hitTime (fun _ : Unit => recordPath S (rationalTime (D.q i)) p)
      (fun _ => (H \ GlueCond.cfHullQ (rationalTime S.s) p.2)ᶜ) () := by
    simpa only [hitTime] using (hct he).1
  apply continuation_mem_component (hg he) hp.1.continuous_rpath
    (by simpa only [Ito.rpath, Real.toNNReal_zero] using hp.1.2.1) hp.2.1 hp.2.2
    (hcf (rationalTime S.s)).2.1 _ hb (hrp _).2.1 (fun v => ?_) hT hv hvT
  · simpa only [Real.toNNReal_coe] using hcl he
  · simpa only [← NNReal.coe_add, Real.toNNReal_coe] using (hrp (rationalTime (D.q i))).1 v

/-- Transport the explicit whole-domain forward-tip theorem to the
normalized retained chart by the own forward/inverse identities. -/
theorem ReaderFacts.ae_start_lim (hTip : OwnTipForwardLimit S) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → Tendsto
      (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).1
      (𝓝[((sourceChart (source D h) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ)]
        (recordPath S (rationalTime (D.q i)) p 0)) (𝓝 0) := by
  intro i
  filter_upwards [hTip, R.ae_geometry h i, S.physical_path, ae_recordPath S] with p ht hg hp hrp he
  have hW := hp.1.continuous_rpath
  have hW0 : (fun t : ℝ => S.own.W t.toNNReal p.1) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hp.1.2.1
  have hsub : ((sourceChart (source D h) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) ⊆
      H \ fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime (D.q i)) := by
    rw [WangWu.fwdHull_eq_image_Ioc hp.2.1 hp.2.2 (rationalTime (D.q i)).coe_nonneg]
    intro z hz
    exact ⟨((hg he).retained hz).1, fun hP => ((hg he).retained hz).2
      (Or.inr (image_mono Ioc_subset_Icc_self hP))⟩
  have hforward := (ht (rationalTime (D.q i)) (hg he).start_pos).mono_left (nhdsWithin_mono _ hsub)
  have hcomp := (hg he).current.comp hforward
  have heq : (fun z =>
      (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).1
        (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime (D.q i))
          (fwdMap (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime (D.q i)) z))) =ᶠ[
      𝓝[((sourceChart (source D h) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ)] (S.path p.1 (rationalTime (D.q i)))]
      (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).1 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact congrArg
      (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).1
      (QuantumZipper.RS.fwdMapInv_fwdMap (W := fun t : ℝ => S.own.W t.toNNReal p.1)
        hW hW0 (rationalTime (D.q i)).coe_nonneg (hsub hz))
  simpa only [(hrp (rationalTime (D.q i))).1 0, add_zero] using hcomp.congr' heq

end InteractingSLE.Sec5.Aux61SlitWX
