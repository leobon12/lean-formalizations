/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoMeet

/-!
# R.6: common current-domain points for seed-opening outer pockets

PROVE-R6-TWO. The same fresh-future and inner-tip argument at infinity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Two

open Sec6 PocketTraversal PocketStopMarked Lemma71C
open PocketStopMarked.Outer

/-- A fresh outer-traversal point near an interior visit is an actual
later original visit in the same chosen open pocket and in the old
relative outer domain. -/
theorem exists_later_visit_in_outer_domainInf {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsOuterPocketInf W η C y₀ τ ψ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travInf η C τ ψ)) (hVo : IsOpen V) (hVC : V ⊆ C)
    (htip : η (pocketFibreInf η C τ
      (clockOf (clockEnd η C τ) (capInv (travInf η C τ ψ) q))) ∈ V) :
    ∃ t : ℝ, pocketFibreInf η C τ
        (clockOf (clockEnd η C τ) (capInv (travInf η C τ ψ) q)) < t ∧
      η t ∈ V ∧ η t ∈ C ∩ ψ ⁻¹'
        (H \ fwdHull (fun s : ℝ => segDriver (travInf η C τ ψ) s.toNNReal) q) := by
  let γ := travInf η C τ ψ
  let L := clockEnd η C τ
  let a := capInv γ q
  let T := pocketFibreInf η C τ (clockOf L a)
  let ζ : ℝ → ℂ := fun u => erasedPathInf η C τ (clockOf L u)
  have hL : 0 < L := hP.erase.clockEnd_pos
  have ha0 : 0 ≤ a := capInv_nonneg γ q
  have hζc : ContinuousOn ζ (Ici 0) := hP.erase.continuousOn_erasedPath.comp
    (continuousOn_clockOf L) fun u hu =>
      clockOf_mem_Ico hL hu
  have hζa : ζ a ∈ V := htip
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hVo (ζ a) hζa
  obtain ⟨d, hd, hclose⟩ := Metric.continuousWithinAt_iff.1 (hζc a ha0) ε hε
  obtain ⟨u, hu, hz⟩ := exists_trace_mem_domain hP.driven ha0
    (show a < a + d / 2 by linarith only [hd])
  have hu0 : 0 ≤ u := ha0.trans hu.1.le
  have hdu : dist u a < d := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.2 hu.1)]
    linarith only [hu.2, hd]
  have hzuV : ζ u ∈ V := hεV (hclose hu0 hdu)
  let t := pocketFibreInf η C τ (clockOf L u)
  have hclku := hP.erase.clock_fibre
    (show clockOf L u ∈ Ico 0 L from clockOf_mem_Ico hL hu0)
  have hclka := hP.erase.clock_fibre
    (show clockOf L a ∈ Ico 0 L from clockOf_mem_Ico hL ha0)
  have hTt : T < t := by
    by_contra h
    have hm := hP.erase.monotone_clock (not_lt.1 h)
    change pocketClockInf η C τ t ≤ pocketClockInf η C τ T at hm
    rw [hclku, hclka] at hm
    exact (not_le_of_gt (strictMonoOn_clockOf hL ha0 hu0 hu.1)) hm
  refine ⟨t, hTt, hzuV, hVC hzuV, ?_⟩
  rw [hP.driven.fwdHull_segDriver q.coe_nonneg
    (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)]
  exact hz

/-- Choose a rational inner level after an original visit `T`. A later
physical visit in the open outer current domain supplies a common point
through the inner tip limit and monotonicity of inner current domains. -/
theorem exists_rat_meetInf_of_later_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {V : Set ℂ}
    {y₀ : ℂ} {τ T t : ℝ} {φ : ℂ → ℂ} {B outer : Chart}
    (hP : IsOuterPocketInf W η V y₀ τ φ) (hB : B.IsConformal)
    (hBdom : (B.dom : Set ℂ) = V) (hBfwd : EqOn B.1 φ V)
    (hT0 : 0 ≤ T) (hTip : η T ∈ V) (hTt : T < t) (htV : η t ∈ V)
    (htO : η t ∈ (outer.dom : Set ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q' : ℚ, relCapInf η V τ φ T < q' ∧
      (q' : ℝ) < relCapInf η V τ φ T + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travInf η V τ φ) ∧
      T < PocketStopWallsFin.ambTime0Inf η V τ φ (StripSys.rt q') ∧
      (((B.loewner (fun s : ℝ => segDriver (travInf η V τ φ) s.toNNReal)
        (StripSys.rt q')).dom : Set ℂ) ∩ (outer.dom : Set ℂ)).Nonempty := by
  have hTV := hP.erase.mem_visitSet hT0 hTip
  have ht0 := hT0.trans hTt.le
  have htv := hP.erase.mem_visitSet ht0 htV
  have hinc := relCapInf_outer_lt_of_visit hP hTV hTt
  have hc0 : 0 ≤ relCapInf η V τ φ T :=
    hP.driven.capClock_nonneg (Outer.relTimeInf_nonneg hP hTV.1.le)
  have hct0 : 0 ≤ relCapInf η V τ φ t :=
    hP.driven.capClock_nonneg (Outer.relTimeInf_nonneg hP htv.1.le)
  obtain ⟨q', hqlo, hqhi⟩ := exists_rat_btwn
    (lt_min hinc (lt_add_of_pos_right (relCapInf η V τ φ T) hε))
  have hq0 : (0 : ℝ) < q' := hc0.trans_lt hqlo
  have hrt : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ hq0.le
  have hqt : (q' : ℝ) < relCapInf η V τ φ t := hqhi.trans_le (min_le_left _ _)
  have htLive := Outer.relCapInf_lt_capLife hP htv.1.le
  have hqLive : ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travInf η V τ φ) := by
    rw [← ENNReal.ofReal_coe_nnreal, hrt]
    exact (ENNReal.ofReal_le_ofReal hqt.le).trans_lt htLive
  have hstop : T < PocketStopWallsFin.ambTime0Inf η V τ φ (StripSys.rt q') := by
    by_contra h
    have hcap := (Outer.ambTime0Inf_le_iff hP (StripSys.rt q').coe_nonneg
      (by rwa [ENNReal.ofReal_coe_nnreal]) hTV.1.le).1 (not_lt.1 h)
    rw [hrt] at hcap
    exact (not_le_of_gt hqlo) hcap
  let qt := (relCapInf η V τ φ t).toNNReal
  have hqtLive : (qt : ℝ≥0∞) < capLife (travInf η V τ φ) := by
    simpa only [qt, ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hct0] using htLive
  have hTrace : capTrace (travInf η V τ φ) qt = B.1 (η t) := by
    rw [hBfwd htV]
    exact capTrace_relCapInf_outer_of_visit hP htv
  have hpcl := tip_mem_closure_relChart_dom hB hP.driven hqtLive (by rwa [hBdom]) hTrace
  have hqle : StripSys.rt q' ≤ qt := by
    rw [← NNReal.coe_le_coe, hrt, Real.coe_toNNReal _ hct0]
    exact hqt.le
  have hdom := relChart_dom_antitone (c := fun _ : Unit => B)
    (γ := fun _ : Unit => travInf η V τ φ) (ω := ()) hB hP.driven hqtLive hqle
  have hpcl' := closure_mono hdom hpcl
  obtain ⟨z, hzO, hzI⟩ := mem_closure_iff.1 hpcl' _ outer.dom.isOpen htO
  exact ⟨q', hqlo, hqhi.trans_le (min_le_right _ _), hqLive, hstop, z, hzI, hzO⟩

/-- The common-point and rational-time obligations for a seed-opening outer
pocket and a bounded inner outer pocket, from their actual erasure and driven-traversal data alone. -/
theorem exists_rat_meet_outerInf {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {yC xV yV : ℂ} {τC τV σV : ℝ} {ψ φ : ℂ → ℂ} {B outer : Chart}
    (hC : IsOuterPocketInf W η C yC τC ψ)
    (hV : IsOuterPocket W η V xV yV τV σV φ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travInf η C τC ψ))
    (hVC : V ⊆ C) (hB : B.IsConformal) (hBdom : (B.dom : Set ℂ) = V)
    (hBfwd : EqOn B.1 φ V)
    (hOuter : (outer.dom : Set ℂ) = C ∩ ψ ⁻¹'
      (H \ fwdHull (fun s : ℝ => segDriver (travInf η C τC ψ) s.toNNReal) q))
    (htip : η (pocketFibreInf η C τC
      (clockOf (clockEnd η C τC) (capInv (travInf η C τC ψ) q))) ∈ V)
    {ε : ℝ} (hε : 0 < ε) :
    let T := pocketFibreInf η C τC
      (clockOf (clockEnd η C τC) (capInv (travInf η C τC ψ) q))
    ∃ q' : ℚ, relCap η V τV σV φ T < q' ∧
      (q' : ℝ) < relCap η V τV σV φ T + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (trav η V τV σV φ) ∧
      T < PocketStopWallsFin.ambTime0 η V τV σV φ (StripSys.rt q') ∧
      (((B.loewner (fun s : ℝ => segDriver (trav η V τV σV φ) s.toNNReal)
        (StripSys.rt q')).dom : Set ℂ) ∩ (outer.dom : Set ℂ)).Nonempty := by
  obtain ⟨t, hTt, htV, htC⟩ := exists_later_visit_in_outer_domainInf hC hq hV.erase.isOpen hVC htip
  have hT0 := hC.erase.fibre_nonneg (clockOf_mem_Ico hC.erase.clockEnd_pos
    (capInv_nonneg (travInf η C τC ψ) q))
  exact exists_rat_meet_of_later_visit hV hB hBdom hBfwd hT0 htip hTt htV
    (hOuter.symm ▸ htC) hε

/-- The common-point and rational-time obligations for two seed-opening outer
pockets, from their actual erasure and driven-traversal data alone. -/
theorem exists_rat_meet_outerInfInf {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {yC yV : ℂ} {τC τV : ℝ} {ψ φ : ℂ → ℂ} {B outer : Chart}
    (hC : IsOuterPocketInf W η C yC τC ψ)
    (hV : IsOuterPocketInf W η V yV τV φ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travInf η C τC ψ))
    (hVC : V ⊆ C) (hB : B.IsConformal) (hBdom : (B.dom : Set ℂ) = V)
    (hBfwd : EqOn B.1 φ V)
    (hOuter : (outer.dom : Set ℂ) = C ∩ ψ ⁻¹'
      (H \ fwdHull (fun s : ℝ => segDriver (travInf η C τC ψ) s.toNNReal) q))
    (htip : η (pocketFibreInf η C τC
      (clockOf (clockEnd η C τC) (capInv (travInf η C τC ψ) q))) ∈ V)
    {ε : ℝ} (hε : 0 < ε) :
    let T := pocketFibreInf η C τC
      (clockOf (clockEnd η C τC) (capInv (travInf η C τC ψ) q))
    ∃ q' : ℚ, relCapInf η V τV φ T < q' ∧
      (q' : ℝ) < relCapInf η V τV φ T + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travInf η V τV φ) ∧
      T < PocketStopWallsFin.ambTime0Inf η V τV φ (StripSys.rt q') ∧
      (((B.loewner (fun s : ℝ => segDriver (travInf η V τV φ) s.toNNReal)
        (StripSys.rt q')).dom : Set ℂ) ∩ (outer.dom : Set ℂ)).Nonempty := by
  obtain ⟨t, hTt, htV, htC⟩ := exists_later_visit_in_outer_domainInf hC hq hV.erase.isOpen hVC htip
  have hT0 := hC.erase.fibre_nonneg (clockOf_mem_Ico hC.erase.clockEnd_pos
    (capInv_nonneg (travInf η C τC ψ) q))
  exact exists_rat_meetInf_of_later_visit hV hB hBdom hBfwd hT0 htip hTt htV
    (hOuter.symm ▸ htC) hε

end InteractingSLE.Sec7.R6Two
