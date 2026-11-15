/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxDil5
import InteractingSLE.Spec.Supplement.GW2ShrFill
import InteractingSLE.Spec.Supplement.Q3RelGB6Chart

/-!
# GW2's open lines: the kernel relative chart is a dilation of the stage chart at the stage start

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start dilation). Deterministic: for the launch chart `cL` and a
stage chart `cs` with the same domain as `ρ = relMap Uk t₀ ∘ cL.1` (the kernel's relative chart read through
`cL`), if `cs` sends the `cL`-preimages of the current piece's small hulls near `0` and of the conditional
counterflow's continuation far away, then `ρ = λ · cs.1` on the domain:

* `exists_ball_disjoint_invHull`: a retained (inverted) hull stays away from `0`;
* **`kernel_dilation`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

open Supp8.GB6 (relMap)
open Supp8.Q3Rel (invHull)

/-- **A retained hull stays away from `0`.** -/
theorem exists_ball_disjoint_invHull {U : ℝ → ℝ} (hU : Continuous U) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ ρ > 0, ∀ w ∈ invHull U σ, ρ ≤ ‖w‖ := by
  rcases hσ.lt_or_eq with hσ' | rfl
  · obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := σ)).exists_bound_of_continuousOn hU.continuousOn
    have hsub := QuantumZipper.CaraR.fwdHull_subset_closedBall hU hσ' (M := M) fun r hr => by
      simpa [Real.norm_eq_abs] using hM r hr
    set R := M + 3 * Real.sqrt σ with hR
    have hRpos : 0 < R := by
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hσ'.le⟩)
      have : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ'
      linarith
    refine ⟨R⁻¹, inv_pos.2 hRpos, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxR : ‖x‖ ≤ R := by simpa [dist_zero_right] using hsub hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 fun h => by
      have h1 : x.im > 0 := hx.1
      rw [h] at h1
      simp at h1
    rw [norm_neg, norm_inv]
    exact inv_anti₀ hx0 hxR
  · refine ⟨1, one_pos, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty hU] at hx
    exact absurd hx (notMem_empty x)

/-- **The kernel relative chart is a dilation of the stage chart at the stage start.** -/
theorem kernel_dilation {cL cs : Chart} (hcL : cL.IsConformal) (hcs : cs.IsConformal) {Uk : ℝ → ℝ}
    (hUk : Continuous Uk) (hUk0 : Uk 0 = 0) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {V : ℝ → ℝ} (hV : Continuous V)
    (hV0 : V 0 = 0) (hdom : (cs.dom : Set ℂ) = (cL.trans (GW2JointKernel.jointChart Uk t₀)).dom)
    {u v : ℕ → ℝ} (hu : ∀ n, 0 < u n) (hu0 : Tendsto u atTop (𝓝 0)) (hv : ∀ n, 0 < v n)
    (hv0 : Tendsto v atTop (𝓝 0))
    (hc₀ : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ cL.2.1 '' fwdHull V (u n) ∩ (cs.dom : Set ℂ), ‖cs.1 z‖ < ε)
    (hc₁ : ∀ M : ℝ, ∀ᶠ n in atTop,
      ∀ z ∈ cL.2.1 '' (invHull Uk (t₀ + v n) \ invHull Uk t₀) ∩ (cs.dom : Set ℂ), M < ‖cs.1 z‖) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ (cs.dom : Set ℂ), relMap Uk t₀ (cL.1 x) = (lam : ℂ) * cs.1 x := by
  set d := cL.trans (GW2JointKernel.jointChart Uk t₀) with hd
  have hj := Supp8.Q3Rel.isDomainChart_rel hUk hUk0 ht₀
  have hjc : (GW2JointKernel.jointChart Uk t₀).IsConformal := hj.isConformal
  have hjdom : ((GW2JointKernel.jointChart Uk t₀).dom : Set ℂ) = H \ invHull Uk t₀ := by
    rw [hjc.coe_dom, hj.image_eq]
  have hdc : d.IsConformal := hcL.trans hjc
  have hmemd : ∀ w ∈ H \ invHull Uk t₀, cL.2.1 w ∈ (d.dom : Set ℂ) := by
    intro w hw
    rw [SetLike.mem_coe, WalkInf.mem_dom_trans_iff hcL hjc]
    refine ⟨hcL.inv_mem_dom hw.1, ?_⟩
    rw [hcL.2.2 w hw.1, ← SetLike.mem_coe, hjdom]
    exact hw
  have hfwdd : ∀ z ∈ (d.dom : Set ℂ), cL.1 z ∈ H \ invHull Uk t₀ := by
    intro z hz
    rw [SetLike.mem_coe, WalkInf.mem_dom_trans_iff hcL hjc] at hz
    rw [← hjdom]
    exact hz.2
  obtain ⟨ρ, hρ, hρw⟩ := exists_ball_disjoint_invHull hUk ht₀
  have hsmall : ∀ ε > 0, ∀ᶠ n in atTop, fwdHull V (u n) ⊆ closedBall 0 ε := by
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := GW4Ident.eventually_fwdHull_subset_closedBall hV hV0 hε
    filter_upwards [(tendsto_order.1 hu0).2 δ hδ] with n hn
    exact hball (u n) (hu n) hn.le
  have hS₀ : ∀ᶠ n in atTop, ((fun n => cL.2.1 '' fwdHull V (u n)) n ∩ (cs.dom : Set ℂ)).Nonempty := by
    filter_upwards [hsmall (ρ / 2) (half_pos hρ)] with n hn
    obtain ⟨w, hw⟩ := Set.nonempty_of_ssubset (QuantumZipper.RS.fwdHull_ssubset hV hV0 le_rfl (hu n))
    have hwH : w ∈ H := hw.1.1
    have hwinv : w ∉ invHull Uk t₀ := fun h => by
      have h1 := hρw w h
      have h2 : ‖w‖ ≤ ρ / 2 := by simpa [dist_zero_right] using hn hw.1
      linarith
    refine ⟨cL.2.1 w, ⟨w, hw.1, rfl⟩, ?_⟩
    rw [hdom]
    exact hmemd w ⟨hwH, hwinv⟩
  have hS₁ : ∀ᶠ n in atTop,
      ((fun n => cL.2.1 '' (invHull Uk (t₀ + v n) \ invHull Uk t₀)) n ∩ (cs.dom : Set ℂ)).Nonempty := by
    refine Eventually.of_forall fun n => ?_
    obtain ⟨x, hx⟩ := Set.nonempty_of_ssubset (QuantumZipper.RS.fwdHull_ssubset hUk hUk0 ht₀
      (lt_add_of_pos_right t₀ (hv n)))
    have hw1 : -x⁻¹ ∈ invHull Uk (t₀ + v n) := ⟨x, hx.1, rfl⟩
    have hw2 : -x⁻¹ ∉ invHull Uk t₀ := by
      rintro ⟨y, hy, hyx⟩
      have : y = x := by
        have h := congrArg (fun z : ℂ => -z⁻¹) hyx
        simpa using h
      exact hx.2 (this ▸ hy)
    have hwH : -x⁻¹ ∈ H := GW2Shr.invHull_subset_H hUk (by linarith [hv n]) hw1
    refine ⟨cL.2.1 (-x⁻¹), ⟨-x⁻¹, ⟨hw1, hw2⟩, rfl⟩, ?_⟩
    rw [hdom]
    exact hmemd _ ⟨hwH, hw2⟩
  have hd₀ : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ (fun n => cL.2.1 '' fwdHull V (u n)) n ∩ (cs.dom : Set ℂ), ‖d.1 z‖ < ε := by
    intro ε hε
    obtain ⟨η, hη, hrel⟩ := relMap_small_near_zero hUk hUk0 ht₀ hε
    filter_upwards [hsmall (η / 2) (half_pos hη)] with n hn
    rintro z ⟨⟨w, hw, rfl⟩, hzd⟩
    rw [hdom] at hzd
    have hwH : w ∈ H := hw.1
    have h1 := hfwdd _ hzd
    rw [hcL.2.2 w hwH] at h1
    change ‖relMap Uk t₀ (cL.1 (cL.2.1 w))‖ < ε
    rw [hcL.2.2 w hwH]
    refine hrel w h1 ?_
    have h2 : ‖w‖ ≤ η / 2 := by simpa [dist_zero_right] using hn hw
    linarith
  have hd₁ : ∀ M : ℝ, ∀ᶠ n in atTop,
      ∀ z ∈ (fun n => cL.2.1 '' (invHull Uk (t₀ + v n) \ invHull Uk t₀)) n ∩ (cs.dom : Set ℂ), M < ‖d.1 z‖ := by
    intro M
    obtain ⟨δ, hδ, hfar⟩ := relMap_continuation_far hUk hUk0 ht₀ (M := max 1 M)
      (lt_of_lt_of_le one_pos (le_max_left _ _))
    filter_upwards [(tendsto_order.1 hv0).2 δ hδ] with n hn
    rintro z ⟨⟨w, hw, rfl⟩, -⟩
    have hwH : w ∈ H := GW2Shr.invHull_subset_H hUk (by linarith [hv n]) hw.1
    change M < ‖relMap Uk t₀ (cL.1 (cL.2.1 w))‖
    rw [hcL.2.2 w hwH]
    have := hfar (v n) (hv n) hn.le w hw
    linarith [le_max_right 1 M]
  obtain ⟨lam, hlam, hdil⟩ := dilation_of_shrinking hcs hdc hdom hS₀ hS₁ hc₀ hd₀ hc₁ hd₁
  exact ⟨lam, hlam, fun x hx => hdil x hx⟩

end InteractingSLE.Theorem14.GW2Omx
