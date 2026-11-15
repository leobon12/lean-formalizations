/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoPoints

/-!
# R.6: accessibility of the inner target in the selected current component

PROVE-R6-TWO. A bounded outer pocket's target remains adherent to every
live current relative domain. This is obtained from its erased traversal
at completion, not from reverse visit order of an outer wall.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Two

open Sec6 PocketTraversal PocketStopMarked Lemma71C
open PocketStopMarked.Outer R7Aux131

/-- The physical target of a finite outer pocket is adherent to every
live relative current domain, even when that domain is only the selected
incident component of the ambient complement. -/
theorem target_mem_closure_relChart_dom {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ} {B : Chart}
    (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) (hB : B.IsConformal)
    (hBdom : (B.dom : Set ℂ) = C) (hBfwd : EqOn B.1 ψ C) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (trav η C τ σ ψ)) :
    x₀ ∈ closure ((B.loewner (fun s : ℝ => segDriver (trav η C τ σ ψ) s.toNNReal) q).dom : Set ℂ) := by
  let γ := trav η C τ σ ψ
  let L := pocketClock η C τ σ σ
  let ζ : ℝ → ℂ := fun u => erasedPath η C τ σ (clockOf L u)
  have hL : 0 < L := hP.erase.clock_σ_pos
  have hζend : Tendsto ζ atTop (𝓝 x₀) := by
    have hmem : Icc 0 L ∈ 𝓝[<] L := mem_of_superset (Ioo_mem_nhdsLT hL) Ioo_subset_Icc_self
    have hcont := (hP.erase.continuousOn_erasedPath L ⟨hL.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem
    have hlim := hcont.tendsto.comp (tendsto_clockOf hL)
    rwa [hP.erase.erasedPath_clock_σ] at hlim
  have hγend : Tendsto (fun u => ‖γ u‖) atTop atTop :=
    hP.erase.tendsto_norm_relTrav hP.jordan.2.2.2.2.2.2
  have hAc : IsCompact (γ '' Icc 0 (capInv γ q)) :=
    isCompact_Icc.image_of_continuousOn (hP.driven.continuousOn.mono fun _ hu => hu.1)
  obtain ⟨R, hR, hAR⟩ := exists_closure_subset_ball hAc.isBounded
  rw [Metric.mem_closure_iff]
  intro ε hε
  have he := (hζend.eventually (ball_mem_nhds x₀ hε)).and (hγend.eventually (eventually_gt_atTop R))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  let a : ℝ := max N 0
  obtain ⟨u, hu, huH⟩ := PocketStopMarked.exists_mem_H_of_lt hP.driven
    (le_max_right N 0) (show a < a + 1 by linarith only)
  have hu0 : 0 ≤ u := (le_max_right N 0).trans hu.1.le
  have huN : N ≤ u := (le_max_left N 0).trans hu.1.le
  have hzC : ζ u ∈ C := (Outer.jordan_mem_H_iff hP.jordan
    (hP.erase.erasedPath_mem (clockOf_mem_Ico hL hu0)) hP.erase.isOpen).1 huH
  refine ⟨ζ u, ?_, ?_⟩
  · rw [loewner_dom_eq_inter hB hBdom hBfwd hP.subset_H hP.jordan.2.2.2.1 hP.driven hq,
      hP.driven.fwdHull_segDriver q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)]
    refine ⟨hzC, huH, fun hfill => ?_⟩
    have hnorm := mem_ball_zero_iff.1 (fillH_subset_ball hR hAR hfill)
    exact (not_lt_of_ge (hN u huN).2.le) hnorm
  · exact (dist_comm x₀ (ζ u)).trans_lt (mem_ball.1 (hN u huN).1)

/-- An accessible point off a closed trace is free, by the existing
free/trapped dichotomy. -/
theorem isFreeAt_of_mem_closure_domain {F : Set ℂ} (hF : IsClosed F) {z : ℂ}
    (hzF : z ∉ F) (hz : z ∈ closure (H \ fillH F)) : HalfPlaneSep.IsFreeAt F z := by
  rcases HalfPlaneSep.isFreeAt_or_isTrappedAt hF hzF with h | ⟨ε, hε, hd⟩
  · exact h
  · obtain ⟨w, hwD, hwB⟩ := Metric.mem_closure_iff.1 hz ε hε
    exact False.elim (Set.disjoint_left.1 hd
      (mem_ball.2 ((dist_comm w z).trans_lt hwB)) hwD)

/-- The target of the inner pocket has an unfilled collar in the outer
initial coordinate when the selected inner current domain lies in the
outer one. Freshness excludes the outer traced prefix; accessibility
excludes the trapped alternative. This covers the case of distinct
finite targets without reverse visitation of their shared outer wall. -/
theorem isFreeAt_outer_inner_target {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {xC yC xV yV : ℂ} {τC σC τV σV : ℝ} {ψ φ : ℂ → ℂ} {BV : Chart}
    (hC : IsOuterPocket W η C xC yC τC σC ψ)
    (hV : IsOuterPocket W η V xV yV τV σV φ)
    (hBV : BV.IsConformal) (hBVdom : (BV.dom : Set ℂ) = V) (hBVfwd : EqOn BV.1 φ V)
    {q qV : ℝ≥0} (hqV : (qV : ℝ≥0∞) < capLife (trav η V τV σV φ))
    (hPole : xV ≠ xC)
    (hT : pocketFibre η C τC σC
      (clockOf (pocketClock η C τC σC σC) (capInv (trav η C τC σC ψ) q)) < σV)
    (hIncl : ((BV.loewner (fun s : ℝ => segDriver (trav η V τV σV φ) s.toNNReal) qV).dom : Set ℂ) ⊆
      C ∩ ψ ⁻¹' (H \ fillH (trav η C τC σC ψ '' Icc 0 (capInv (trav η C τC σC ψ) q)))) :
    HalfPlaneSep.IsFreeAt (trav η C τC σC ψ '' Icc 0 (capInv (trav η C τC σC ψ) q)) (ψ xV) := by
  let γ := trav η C τC σC ψ
  let a := capInv γ q
  let L := pocketClock η C τC σC σC
  let D := C ∩ ψ ⁻¹' (H \ fillH (γ '' Icc 0 a))
  have ha0 : 0 ≤ a := capInv_nonneg γ q
  have hL : 0 < L := hC.erase.clock_σ_pos
  have hxD : xV ∈ closure D := closure_mono hIncl
    (target_mem_closure_relChart_dom hV hBV hBVdom hBVfwd hqV)
  have hxC : xV ∈ closure C := closure_mono inter_subset_left hxD
  have hcont : ContinuousWithinAt ψ D xV := (hC.jordan.1 xV ⟨hxC, hPole⟩).mono
    (fun z hz => ⟨subset_closure hz.1, fun h => hC.erase.notMem_x (h ▸ hz.1)⟩)
  have hxψ : ψ xV ∈ closure (H \ fillH (γ '' Icc 0 a)) :=
    closure_mono (by rintro z ⟨p, hp, rfl⟩; exact hp.2) (hcont.mem_closure_image hxD)
  have hAc : IsCompact (γ '' Icc 0 a) :=
    isCompact_Icc.image_of_continuousOn (hC.driven.continuousOn.mono fun _ hu => hu.1)
  refine isFreeAt_of_mem_closure_domain hAc.isClosed ?_ hxψ
  rintro ⟨u, hu, heq⟩
  have huc := clockOf_mem_Ico hL hu.1
  have hac := clockOf_mem_Ico hL ha0
  have hpcl := hC.erase.erasedPath_mem huc
  have hpEq : erasedPath η C τC σC (clockOf L u) = xV :=
    hC.jordan.2.1 hpcl ⟨hxC, hPole⟩ heq
  have htime := hC.erase.monotone_fibre ((strictMonoOn_clockOf hL).monotoneOn hu.1 ha0 hu.2)
  have htime0 := hC.erase.nonneg.trans (hC.erase.fibre_mem (clockOf L u)).1
  exact hV.erase.fresh_x ⟨pocketFibre η C τC σC (clockOf L u),
    ⟨htime0, htime.trans_lt hT⟩, hpEq⟩

/-- The seed-opening outer-pocket version of the inner-target collar.
The outer Jordan coordinate is continuous on its entire finite closure. -/
theorem isFreeAt_outerInf_inner_target {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {yC xV yV : ℂ} {τC τV σV : ℝ} {ψ φ : ℂ → ℂ} {BV : Chart}
    (hC : IsOuterPocketInf W η C yC τC ψ)
    (hV : IsOuterPocket W η V xV yV τV σV φ)
    (hBV : BV.IsConformal) (hBVdom : (BV.dom : Set ℂ) = V) (hBVfwd : EqOn BV.1 φ V)
    {q qV : ℝ≥0} (hqV : (qV : ℝ≥0∞) < capLife (trav η V τV σV φ))
    (hT : pocketFibreInf η C τC
      (clockOf (clockEnd η C τC) (capInv (travInf η C τC ψ) q)) < σV)
    (hIncl : ((BV.loewner (fun s : ℝ => segDriver (trav η V τV σV φ) s.toNNReal) qV).dom : Set ℂ) ⊆
      C ∩ ψ ⁻¹' (H \ fillH (travInf η C τC ψ '' Icc 0 (capInv (travInf η C τC ψ) q)))) :
    HalfPlaneSep.IsFreeAt (travInf η C τC ψ '' Icc 0 (capInv (travInf η C τC ψ) q)) (ψ xV) := by
  let γ := travInf η C τC ψ
  let a := capInv γ q
  let L := clockEnd η C τC
  let D := C ∩ ψ ⁻¹' (H \ fillH (γ '' Icc 0 a))
  have ha0 : 0 ≤ a := capInv_nonneg γ q
  have hL : 0 < L := hC.erase.clockEnd_pos
  have hxD : xV ∈ closure D := closure_mono hIncl
    (target_mem_closure_relChart_dom hV hBV hBVdom hBVfwd hqV)
  have hxC : xV ∈ closure C := closure_mono inter_subset_left hxD
  have hcont : ContinuousWithinAt ψ D xV := (hC.jordan.1 xV hxC).mono
    (fun _ hz => subset_closure hz.1)
  have hxψ : ψ xV ∈ closure (H \ fillH (γ '' Icc 0 a)) :=
    closure_mono (by rintro z ⟨p, hp, rfl⟩; exact hp.2) (hcont.mem_closure_image hxD)
  have hAc : IsCompact (γ '' Icc 0 a) :=
    isCompact_Icc.image_of_continuousOn (hC.driven.continuousOn.mono fun _ hu => hu.1)
  refine isFreeAt_of_mem_closure_domain hAc.isClosed ?_ hxψ
  rintro ⟨u, hu, heq⟩
  have huc := clockOf_mem_Ico hL hu.1
  have hac := clockOf_mem_Ico hL ha0
  have hpcl := hC.erase.erasedPath_mem huc
  have hpEq : erasedPathInf η C τC (clockOf L u) = xV :=
    hC.jordan.2.1 hpcl hxC heq
  have htime := hC.erase.monotoneOn_fibre huc hac
    ((strictMonoOn_clockOf hL).monotoneOn hu.1 ha0 hu.2)
  exact hV.erase.fresh_x ⟨pocketFibreInf η C τC (clockOf L u),
    ⟨hC.erase.fibre_nonneg huc, htime.trans_lt hT⟩, hpEq⟩

end InteractingSLE.Sec7.R6Two
