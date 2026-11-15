/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWYTip
import InteractingSLE.Spec.Sec5.Aux61SlitWXLanding
import InteractingSLE.Spec.Sec5.Aux61SlitWCaptureFields

/-!
# The actual normalized selected endpoint with no forward-tip premise

At a finite physical first contact, the fully certified R1 chart has a
nonzero real selected endpoint. The per-sample restart facts suffice for
the existing deterministic endpoint theorem, through its unit-space form.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWY
open Aux61SlitW Aux61SlitWX Aux61Asm2 Aux61Restart Aux61FibData Aux61ULoc LawUnique
open GlueCond WangWu
universe u
variable {S : SourceSetting.{u}} {D : R1Restart S} (R : ReaderFacts D) (h : D.HasChart)
include R

/-- Every selected sample has the basic restart clauses almost surely.
The whole-domain tip theorem is now discharged by the actual source law. -/
theorem ae_restartPoint : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    RestartPoint (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
      (recordPath S (rationalTime (D.q i)) p) (D.contact i p) :=
  R.ae_restartPoint h (ownTipForwardLimit S)

/-- Finite physical contact has a nonzero real selected chart endpoint.
No window, exit, capture, comparison or additional analytic input is used. -/
theorem ae_real_accessEndpoint : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → D.contact i p < ⊤ →
    ∃ y : ℝ, y ≠ 0 ∧ Tendsto
      (inPath (D.event i)
        (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (recordPath S (rationalTime (D.q i))) (D.contact i) p)
      (𝓝[<] (D.contact i p).toNNReal) (𝓝 (y : ℂ)) := by
  intro i
  filter_upwards [ae_restartPoint R h i, R.ae_domain h i, R.ae_geometry h i, S.physical_path,
    S.counterflow_good, ae_recordPath S, r1_contact_fields_of_tipOff D h R.tipOff i]
    with p hB hd hg hp hcf hrp hct he hfin
  obtain ⟨b, hbdom⟩ := hd he
  have hK := cfHullQ_eq_of_mem_goodCfSet hcf.1 (rationalTime S.s)
  rw [hK] at hbdom
  have B := hB he
  have hb : b ∈ retainedDomain (negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (D.q i)) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ b).Nonempty
    rw [← hbdom]
    exact ⟨_, B.conformal.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hT : D.contact i p = hitTime (fun _ : Unit => recordPath S (rationalTime (D.q i)) p)
      (fun _ => (H \ negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))ᶜ) () := by
    simpa only [hitTime, hK] using (hct he).1
  have hgeom := hg he
  rw [hK] at hgeom
  obtain ⟨y, hy, hlim⟩ := exists_real_source_accessEndpoint B.unitSpec (mem_univ ())
    (hct he).2.1 hfin hp.1.continuous_rpath
    (by simpa only [Ito.rpath, Real.toNNReal_zero] using hp.1.2.1) hp.2.1 hp.2.2
    (rationalTime S.s).coe_nonneg (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.2.2 hb hbdom hgeom hT
    (fun v _ _ => by
      simpa only [← NNReal.coe_add, Real.toNNReal_coe] using (hrp (rationalTime (D.q i))).1 v)
  refine ⟨y, hy, ?_⟩
  have hpath : inPath (univ : Set Unit)
      (fun _ => sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
      (fun _ => recordPath S (rationalTime (D.q i)) p) (fun _ => D.contact i p) () =
      inPath (D.event i)
        (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (recordPath S (rationalTime (D.q i))) (D.contact i) p := by
    funext v
    simp only [inPath, mem_univ, he, true_and]
  rwa [hpath] at hlim

end InteractingSLE.Sec5.Aux61SlitWY
