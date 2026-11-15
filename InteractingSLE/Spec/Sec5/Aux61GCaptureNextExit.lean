/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextRestart
import InteractingSLE.Spec.Sec5.Aux61GR1FStop

/-! # Physical exit for the fully normalized source chart

The actual proper continuation leaves a window with bounded physical
inverse image if contact is infinite. The existing compact buffer of the
fibre data gives that boundedness when its bounded inverse avoids the pole.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GCaptureNext
open Aux61SlitW Aux61Asm2 Aux61SlitWX Aux61FibData Aux61GInst Aux61ULoc LawUnique
universe u
variable {S : SourceSetting.{u}} (D : R1Restart S) (h : D.HasChart) (R : ReaderFacts D)
include R

/-- The normalized source's exit input follows from the already proved
pre-contact inclusion and actual physical properness. -/
theorem physicalExit_of_bounded_inverse
    (hbounded : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → Bornology.IsBounded
      ((sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.1 ''
        ((D.data i).V ∩ H))) : PhysicalExit D h := by
  intro i
  filter_upwards [hbounded i, R.ae_inside h i, Aux61GR1F.ae_recordPath_proper S]
    with p hb hi hp he
  by_cases hfin : D.contact i p < ⊤
  · exact Or.inl hfin
  · right
    have htop : D.contact i p = ⊤ := top_unique (not_lt.1 hfin)
    exact Aux61GR1F.exists_exit_of_contact_top he ((chart_spec D h i).conformal _) htop
      (fun v hv => hi he v hv (htop ▸ ENNReal.coe_lt_top)) (hp _) (hb he)

/-- The source traces supply the continuous bounded inverse extension for
the actual normalized chart; no new analytic extension input is needed. -/
theorem normalized_boundedInverse_continuous :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → ContinuousOn
      (boundedInverse (sourceChart (source D h)
        (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) Hbar := by
  intro i
  filter_upwards [R.ae_domain h i, S.physical_path, S.counterflow_good]
    with p hd hp hcf he
  obtain ⟨b, hbdom⟩ := hd he
  have hK := GlueCond.cfHullQ_eq_of_mem_goodCfSet hcf.1 (rationalTime S.s)
  rw [hK] at hbdom
  have hc := (chart_spec D h i).conformal
    (sourceRecord (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  have hb : b ∈ Aux61Restart.retainedDomain
      (WangWu.negInv '' QuantumZipper.fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (D.q i)) := by
    apply connectedComponentIn_nonempty_iff.1
    change (Aux61Restart.restartComponent _ _ _ b).Nonempty
    rw [← hbdom]
    exact ⟨_, hc.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hηH : MapsTo (fun t : ℝ => S.path p.1 t.toNNReal)
      (Icc 0 (rationalTime (D.q i) : ℝ)) Hbar := by
    intro t ht
    rcases ht.1.eq_or_lt with hzero | hpos
    · rw [← hzero]
      change S.path p.1 (0 : ℝ).toNNReal ∈ Hbar
      rw [hp.2.2.zero]
      exact InteractingSLE.zero_mem_Hbar
    · exact QuantumZipper.H_subset_Hbar (hp.2.2.mem_H t hpos)
  exact (boundedInverse_spec_of_traces (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.2.2
    (rationalTime S.s).coe_nonneg (hp.2.2.cont.mono Icc_subset_Ici_self) hηH hb hc hbdom).2.1

/-- Use the existing compact buffer and the proved continuous extension.
Avoidance of physical infinity on that buffer is the remaining input. -/
theorem physicalExit_of_finite_buffer
    (hfinite : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
      ∀ z ∈ closure (D.data i).buffer ∩ Hbar,
        boundedInverse (sourceChart (source D h)
          (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) z ≠ 1) :
    PhysicalExit D h := by
  apply physicalExit_of_bounded_inverse D h R
  intro i
  filter_upwards [normalized_boundedInverse_continuous D h R i, hfinite i]
    with p hf hfin he
  exact Aux61GR1F.isBounded_inverse_window ((chart_spec D h i).conformal _)
    (D.data i).V_sub (D.data i).buffer_compact (hf he) (hfin he)

end InteractingSLE.Sec5.Aux61GCaptureNext
