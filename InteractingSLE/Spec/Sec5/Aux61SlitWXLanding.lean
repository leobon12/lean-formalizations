/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXBoundary
import InteractingSLE.Spec.Sec5.Aux61SlitWPointFields

/-! # Selected landing from the proved per-sample restart clauses -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWX
open Aux61SlitW Aux61Asm2 Aux61Restart Aux61FibData Aux61GInst Aux61Marks Aux61ULoc LawUnique
open WangWu (negInv histLine)

/-- The basic restart clauses at one sample, before any full-measure cut. -/
structure RestartPoint (c : Chart) (ρ : ℝ≥0 → ℂ) (T : ℝ≥0∞) : Prop where
  continuous : Continuous ρ
  conformal : c.IsConformal
  start_mem : ρ 0 ∈ closure (c.dom : Set ℂ)
  start_lim : Tendsto c.1 (𝓝[(c.dom : Set ℂ)] (ρ 0)) (𝓝 0)
  inside : ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < T → ρ v ∈ c.dom

/-- Constant data realize the per-sample clauses on a measurable unit space. -/
theorem RestartPoint.unitSpec {c : Chart} {ρ : ℝ≥0 → ℂ} {T : ℝ≥0∞} (B : RestartPoint c ρ T) :
    IsRestartSpec (univ : Set Unit) (fun _ => c) (fun _ => ρ) (fun _ => T) where
  measurableSet := MeasurableSet.univ
  measT := measurable_const
  measρ := fun _ => measurable_const
  contρ := fun _ _ => B.continuous
  chart := ⟨fun _ => MeasurableSet.const _,
    fun _ => measurable_const.indicator (MeasurableSet.const _),
    fun _ => measurable_const.indicator (MeasurableSet.const _)⟩
  conf := fun _ _ => B.conformal
  start_mem := fun _ _ => B.start_mem
  start_lim := fun _ _ => B.start_lim
  inside := fun _ _ => B.inside

/-- Apply the landed geometric landing theorem to pointwise good data,
without a pointwise restart assertion on the whole raw event. -/
theorem landing_of_restartPoint {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {x : X} (hx : x ∈ E)
    (B : RestartPoint (c x) (ρ x) (T x))
    {Wcf : ℝ → ℝ} {β η : ℝ → ℂ} {s r : ℝ} (hs0 : 0 ≤ s)
    (hβ : IsLoewnerTrace Wcf β) (hη : ContinuousOn η (Icc 0 r))
    (hηH : MapsTo η (Icc 0 r) Hbar) {b : ℂ}
    (hb : b ∈ retainedDomain (negInv '' fwdHull Wcf s) η r)
    (hdom : ((c x).dom : Set ℂ) = restartComponent (negInv '' fwdHull Wcf s) η r b)
    (hT : T x = hitTime ρ (fun _ => (H \ negInv '' fwdHull Wcf s)ᶜ) x)
    {U V : Set ℂ} (hUb : Bornology.IsBounded U) {δ : ℝ} (hwindow : V ⊆ seedExitWindow U δ)
    (hseed : ∀ a : ℝ, |a| < δ → boundedInverse (c x) (a : ℂ) ∉ oldModelBoundary (counterflowRecord β s))
    (hpos : 0 < T x) (heq : Aux61FibData.exitTime E c ρ T V x = T x) (hfin : T x < ⊤) :
    ∃ L : ℂ, L ∉ V ∧ Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 L) := by
  have hp : inPath (univ : Set Unit) (fun _ => c x) (fun _ => ρ x) (fun _ => T x) () =
      inPath E c ρ T x := by
    funext v
    simp only [inPath, mem_univ, hx, true_and]
  have ht : Aux61FibData.exitTime (univ : Set Unit) (fun _ => c x) (fun _ => ρ x)
      (fun _ => T x) V () = Aux61FibData.exitTime E c ρ T V x := by
    unfold Aux61FibData.exitTime
    congr 1
    funext a
    have hm : () ∈ winEv (univ : Set Unit) (fun _ => c x) (fun _ => ρ x) (fun _ => T x) V a ↔
        x ∈ winEv E c ρ T V a := by
      simp only [winEv, mem_ofPred_eq, mem_univ, hx, true_and, hp]
    rw [hm]
  have hT' : T x = hitTime (fun _ : Unit => ρ x) (fun _ => (H \ negInv '' fwdHull Wcf s)ᶜ) () := by
    simpa only [hitTime] using hT
  obtain ⟨L, hLV, hlim⟩ := selected_landing_at_of_retained B.unitSpec (mem_univ ())
    hs0 hβ hη hηH hb hdom hT' hUb hwindow hseed hpos (ht.trans heq) hfin
  exact ⟨L, hLV, by rwa [hp] at hlim⟩

universe u
variable {S : SourceSetting.{u}} {D : R1Restart S} (R : ReaderFacts D) (h : D.HasChart)
include R

/-- The basic restart data are proved almost surely from the selected
record model, with only the explicit whole-domain forward-tip input. -/
theorem ReaderFacts.ae_restartPoint (hTip : OwnTipForwardLimit S) : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    RestartPoint (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
      (recordPath S (rationalTime (D.q i)) p) (D.contact i p) := by
  intro i
  filter_upwards [R.ae_start_mem h i, R.ae_start_lim h hTip i, R.ae_inside h i, ae_recordPath S]
    with p hm hl hi hrp he
  exact ⟨(hrp _).2.1, (chart_spec D h i).conformal _, hm he, hl he, hi he⟩

/-- The selected landing clause now needs no basic restart specification
or chart-geometry hypothesis; both have been derived from R1. -/
theorem ReaderFacts.ae_landing (hTip : OwnTipForwardLimit S)
    (U : D.ι → Set ℂ) (δ : D.ι → ℝ) (hUb : ∀ i, Bornology.IsBounded (U i))
    (hwindow : ∀ i, (D.data i).V ⊆ seedExitWindow (U i) (δ i))
    (hseed : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → ∀ a : ℝ, |a| < δ i →
      boundedInverse (sourceChart (source D h)
        (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) (a : ℂ) ∉
        oldModelBoundary (counterflowRecord (histLine p.2) (rationalTime S.s))) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
      Aux61FibData.exitTime (D.event i)
        (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (recordPath S (rationalTime (D.q i))) (D.contact i) (D.data i).V p = D.contact i p →
      D.contact i p < ⊤ → ∃ L : ℂ, L ∉ (D.data i).V ∧ Tendsto
        (inPath (D.event i)
          (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
          (recordPath S (rationalTime (D.q i))) (D.contact i) p)
        (𝓝[<] (D.contact i p).toNNReal) (𝓝 L) := by
  intro i
  filter_upwards [R.ae_restartPoint h hTip i, R.ae_domain h i, S.physical_path,
    S.counterflow_good, r1_contact_fields_of_tipOff D h R.tipOff i, hseed i]
    with p hB hd hp hcf hct hgap he heq hfin
  have B := hB he
  obtain ⟨b, hbdom⟩ := hd he
  have hK := GlueCond.cfHullQ_eq_of_mem_goodCfSet hcf.1 (rationalTime S.s)
  rw [hK] at hbdom
  have hb : b ∈ retainedDomain (negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (D.q i)) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ b).Nonempty
    rw [← hbdom]
    exact ⟨_, B.conformal.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hT : D.contact i p = hitTime (recordPath S (rationalTime (D.q i)))
      (fun _ => (H \ negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))ᶜ) p := by
    simpa only [hitTime, hK] using (hct he).1
  apply landing_of_restartPoint he B (rationalTime S.s).coe_nonneg
    (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.2.2 (hp.2.2.cont.mono Icc_subset_Ici_self) _ hb hbdom hT
    (hUb i) (hwindow i) (hgap he) (hct he).2.1 heq hfin
  intro t ht
  rcases ht.1.eq_or_lt with he0 | ht0
  · rw [← he0]
    change S.path p.1 (0 : ℝ).toNNReal ∈ Hbar
    rw [hp.2.2.zero]
    exact zero_mem_Hbar
  · exact H_subset_Hbar (hp.2.2.mem_H t ht0)

end InteractingSLE.Sec5.Aux61SlitWX
