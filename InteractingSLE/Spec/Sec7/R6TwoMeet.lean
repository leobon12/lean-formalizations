/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoClock

/-!
# R.6: common points of two outer current domains

PROVE-R6-TWO. A fresh point of the outer traversal in a nested open pocket
is an original future visit in the old outer current domain. At that visit
the inner current tip is adherent to the inner domain. Its nearby active
points therefore meet the old outer domain.
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
theorem exists_later_visit_in_outer_domain {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (trav η C τ σ ψ)) (hVo : IsOpen V) (hVC : V ⊆ C)
    (htip : η (pocketFibre η C τ σ
      (clockOf (pocketClock η C τ σ σ) (capInv (trav η C τ σ ψ) q))) ∈ V) :
    ∃ t : ℝ, pocketFibre η C τ σ
        (clockOf (pocketClock η C τ σ σ) (capInv (trav η C τ σ ψ) q)) < t ∧
      η t ∈ V ∧ η t ∈ C ∩ ψ ⁻¹'
        (H \ fwdHull (fun s : ℝ => segDriver (trav η C τ σ ψ) s.toNNReal) q) := by
  let γ := trav η C τ σ ψ
  let L := pocketClock η C τ σ σ
  let a := capInv γ q
  let T := pocketFibre η C τ σ (clockOf L a)
  let ζ : ℝ → ℂ := fun u => erasedPath η C τ σ (clockOf L u)
  have hL : 0 < L := hP.erase.clock_σ_pos
  have ha0 : 0 ≤ a := capInv_nonneg γ q
  have hζc : ContinuousOn ζ (Ici 0) := hP.erase.continuousOn_erasedPath.comp
    (continuousOn_clockOf L) fun u hu =>
      ⟨(clockOf_mem_Ico hL hu).1, (clockOf_mem_Ico hL hu).2.le⟩
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
  let t := pocketFibre η C τ σ (clockOf L u)
  have hclku := hP.erase.clock_fibre
    (show clockOf L u ∈ Icc 0 L from
      ⟨(clockOf_mem_Ico hL hu0).1, (clockOf_mem_Ico hL hu0).2.le⟩)
  have hclka := hP.erase.clock_fibre
    (show clockOf L a ∈ Icc 0 L from
      ⟨(clockOf_mem_Ico hL ha0).1, (clockOf_mem_Ico hL ha0).2.le⟩)
  have hTt : T < t := by
    by_contra h
    have hm := hP.erase.monotone_clock (not_lt.1 h)
    change pocketClock η C τ σ t ≤ pocketClock η C τ σ T at hm
    rw [hclku, hclka] at hm
    exact (not_le_of_gt (strictMonoOn_clockOf hL ha0 hu0 hu.1)) hm
  refine ⟨t, hTt, hzuV, hVC hzuV, ?_⟩
  rw [hP.driven.fwdHull_segDriver q.coe_nonneg
    (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)]
  exact hz

/-- Choose a rational inner level after an original visit `T`. A later
physical visit in the open outer current domain supplies a common point
through the inner tip limit and monotonicity of inner current domains. -/
theorem exists_rat_meet_of_later_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {V : Set ℂ}
    {x₀ y₀ : ℂ} {τ σ T t : ℝ} {φ : ℂ → ℂ} {B outer : Chart}
    (hP : IsOuterPocket W η V x₀ y₀ τ σ φ) (hB : B.IsConformal)
    (hBdom : (B.dom : Set ℂ) = V) (hBfwd : EqOn B.1 φ V)
    (hT0 : 0 ≤ T) (hTip : η T ∈ V) (hTt : T < t) (htV : η t ∈ V)
    (htO : η t ∈ (outer.dom : Set ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q' : ℚ, relCap η V τ σ φ T < q' ∧
      (q' : ℝ) < relCap η V τ σ φ T + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (trav η V τ σ φ) ∧
      T < PocketStopWallsFin.ambTime0 η V τ σ φ (StripSys.rt q') ∧
      (((B.loewner (fun s : ℝ => segDriver (trav η V τ σ φ) s.toNNReal)
        (StripSys.rt q')).dom : Set ℂ) ∩ (outer.dom : Set ℂ)).Nonempty := by
  have hTV := hP.erase.mem_visitSet hT0 hTip
  have ht0 := hT0.trans hTt.le
  have htv := hP.erase.mem_visitSet ht0 htV
  have htI : t ∈ Ico τ σ := ⟨htv.1.1.le, htv.1.2⟩
  have hTI : T ∈ Ico τ σ := ⟨hTV.1.1.le, hTV.1.2⟩
  have hinc := relCap_outer_lt_of_visit hP hTV htI hTt
  have hc0 : 0 ≤ relCap η V τ σ φ T :=
    hP.driven.capClock_nonneg (Outer.relTime_nonneg hP hTI)
  have hct0 : 0 ≤ relCap η V τ σ φ t :=
    hP.driven.capClock_nonneg (Outer.relTime_nonneg hP htI)
  obtain ⟨q', hqlo, hqhi⟩ := exists_rat_btwn
    (lt_min hinc (lt_add_of_pos_right (relCap η V τ σ φ T) hε))
  have hq0 : (0 : ℝ) < q' := hc0.trans_lt hqlo
  have hrt : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ hq0.le
  have hqt : (q' : ℝ) < relCap η V τ σ φ t := hqhi.trans_le (min_le_left _ _)
  have htLive := Outer.relCap_lt_capLife hP htI
  have hqLive : ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (trav η V τ σ φ) := by
    rw [← ENNReal.ofReal_coe_nnreal, hrt]
    exact (ENNReal.ofReal_le_ofReal hqt.le).trans_lt htLive
  have hstop : T < PocketStopWallsFin.ambTime0 η V τ σ φ (StripSys.rt q') := by
    by_contra h
    have hcap := (Outer.ambTime0_le_iff hP (StripSys.rt q').coe_nonneg
      (by rwa [ENNReal.ofReal_coe_nnreal]) hTI).1 (not_lt.1 h)
    rw [hrt] at hcap
    exact (not_le_of_gt hqlo) hcap
  let qt := (relCap η V τ σ φ t).toNNReal
  have hqtLive : (qt : ℝ≥0∞) < capLife (trav η V τ σ φ) := by
    simpa only [qt, ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hct0] using htLive
  have hTrace : capTrace (trav η V τ σ φ) qt = B.1 (η t) := by
    rw [hBfwd htV]
    exact capTrace_relCap_outer_of_visit hP htv
  have hpcl := tip_mem_closure_relChart_dom hB hP.driven hqtLive (by rwa [hBdom]) hTrace
  have hqle : StripSys.rt q' ≤ qt := by
    rw [← NNReal.coe_le_coe, hrt, Real.coe_toNNReal _ hct0]
    exact hqt.le
  have hdom := relChart_dom_antitone (c := fun _ : Unit => B)
    (γ := fun _ : Unit => trav η V τ σ φ) (ω := ()) hB hP.driven hqtLive hqle
  have hpcl' := closure_mono hdom hpcl
  obtain ⟨z, hzO, hzI⟩ := mem_closure_iff.1 hpcl' _ outer.dom.isOpen htO
  exact ⟨q', hqlo, hqhi.trans_le (min_le_right _ _), hqLive, hstop, z, hzI, hzO⟩

/-- The common-point and rational-time obligations for two bounded outer
pockets, from their actual erasure and driven-traversal data alone. -/
theorem exists_rat_meet_outer {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {xC yC xV yV : ℂ} {τC σC τV σV : ℝ} {ψ φ : ℂ → ℂ} {B outer : Chart}
    (hC : IsOuterPocket W η C xC yC τC σC ψ)
    (hV : IsOuterPocket W η V xV yV τV σV φ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (trav η C τC σC ψ))
    (hVC : V ⊆ C) (hB : B.IsConformal) (hBdom : (B.dom : Set ℂ) = V)
    (hBfwd : EqOn B.1 φ V)
    (hOuter : (outer.dom : Set ℂ) = C ∩ ψ ⁻¹'
      (H \ fwdHull (fun s : ℝ => segDriver (trav η C τC σC ψ) s.toNNReal) q))
    (htip : η (pocketFibre η C τC σC
      (clockOf (pocketClock η C τC σC σC) (capInv (trav η C τC σC ψ) q))) ∈ V)
    {ε : ℝ} (hε : 0 < ε) :
    let T := pocketFibre η C τC σC
      (clockOf (pocketClock η C τC σC σC) (capInv (trav η C τC σC ψ) q))
    ∃ q' : ℚ, relCap η V τV σV φ T < q' ∧
      (q' : ℝ) < relCap η V τV σV φ T + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (trav η V τV σV φ) ∧
      T < PocketStopWallsFin.ambTime0 η V τV σV φ (StripSys.rt q') ∧
      (((B.loewner (fun s : ℝ => segDriver (trav η V τV σV φ) s.toNNReal)
        (StripSys.rt q')).dom : Set ℂ) ∩ (outer.dom : Set ℂ)).Nonempty := by
  obtain ⟨t, hTt, htV, htC⟩ := exists_later_visit_in_outer_domain hC hq hV.erase.isOpen hVC htip
  have hT0 := hC.erase.nonneg.trans (hC.erase.fibre_mem
    (clockOf (pocketClock η C τC σC σC) (capInv (trav η C τC σC ψ) q))).1
  exact exists_rat_meet_of_later_visit hV hB hBdom hBfwd hT0 htip hTt htV
    (hOuter.symm ▸ htC) hε

end InteractingSLE.Sec7.R6Two
