/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7FaceSelectSides

/-!
# An untouched unbounded exterior stays outside a bounded chart face

PROVE-R7-GAPEQ. Domain membership is the landed no-entry theorem. Bounded displacement
preserves unboundedness under the chart. Jordan separation then excludes the exterior and
its physical closure from the inner face, even at surviving points of an outer suffix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7FaceSelect

open Sec6 WangWu

/-- Inversion sends a set accumulating at zero, but omitting zero, to an unbounded set. -/
theorem not_isBounded_image_negInv_of_zero_closure {E : Set ℂ}
    (h0 : (0 : ℂ) ∈ closure E) (hE0 : (0 : ℂ) ∉ E) :
    ¬ IsBounded (negInv '' E) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hδ : 0 < (|M| + 1)⁻¹ := by positivity
  obtain ⟨z, hzE, hzδ⟩ := Metric.mem_closure_iff.1 h0 _ hδ
  have hz0 : z ≠ 0 := fun he => hE0 (he ▸ hzE)
  have hzδ' : ‖z‖ < (|M| + 1)⁻¹ := by simpa [dist_zero_left] using hzδ
  have hlarge : |M| + 1 < ‖negInv z‖ := by
    rw [norm_negInv]
    exact (lt_inv_comm₀ (by positivity) (norm_pos_iff.2 hz0)).2 hzδ'
  have hsmall := hM _ ⟨z, hzE, rfl⟩
  linarith [le_abs_self M]

/-- The forward chart preserves unboundedness on any subset of its actual domain. -/
theorem not_isBounded_lift {W : ℝ → ℝ} {r : ℝ} {E : Set ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hr : 0 ≤ r)
    (hED : E ⊆ H \ fwdHull W r) (hEb : ¬ IsBounded E) :
    ¬ IsBounded (fwdMap W r '' E) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  obtain ⟨K, hK⟩ := exists_norm_trMap_zero_sub_le hW hW0 hr
  apply hEb
  refine isBounded_iff_forall_norm_le.2 ⟨M + K, fun z hz => ?_⟩
  have hgH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr (hED hz)
  have hk := hK (fwdMap W r z) hgH
  rw [trMap_zero_fwdMap hW hW0 hr (hED hz)] at hk
  exact (norm_le_norm_sub_add z (fwdMap W r z)).trans
    (add_le_add hk (hM _ ⟨z, hz, rfl⟩)) |>.trans (by linarith)

/-- A preconnected unbounded set missing a Jordan curve lies on its outer side. -/
theorem subset_outerSide_of_unbounded {Γ E : Set ℂ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hE : IsPreconnected E) (hEb : ¬ IsBounded E) (hEΓ : Disjoint E Γ) :
    E ⊆ outerSide Γ := by
  obtain ⟨-, hb, -, -, hi, ho, -, -, -⟩ := jordan_sides hΓ hΓH
  have hsub : E ⊆ innerSide Γ ∪ outerSide Γ := by
    rw [← compl_eq_innerSide_union_outerSide]
    exact fun _ hz => Set.disjoint_left.1 hEΓ hz
  exact (hE.subset_or_subset hi ho disjoint_innerSide_outerSide hsub).resolve_left
    (fun h => hEb (hb.subset h))

/-- An unbounded connected exterior avoided by the trace lifts to the outer Jordan side.
The curve's half-plane boundary is required to map outside that exterior. -/
theorem lift_exterior_subset_outerSide {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    {Γ E : Set ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hr : 0 ≤ r) (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hE : IsPreconnected E) (hEH : E ⊆ H) (hEb : ¬ IsBounded E)
    (havoid : Disjoint E (η '' Icc 0 r))
    (hbd : ∀ w ∈ Γ, w ∈ H → trMap W 0 r w ∉ E) :
    E ⊆ H \ fwdHull W r ∧ fwdMap W r '' E ⊆ outerSide Γ := by
  have hED := subset_domain_of_not_isBounded hη hr hE hEH havoid hEb
  refine ⟨hED, subset_outerSide_of_unbounded hΓ hΓH
    (hE.image _ ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr).continuousOn.mono hED))
    (not_isBounded_lift hW hW0 hr hED hEb) ?_⟩
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨z, hz, rfl⟩ hzΓ
  have hn := hbd _ hzΓ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr (hED hz))
  rw [trMap_zero_fwdMap hW hW0 hr (hED hz)] at hn
  exact hn hz

/-- Physical closure points of an untouched exterior cannot map to the inner face.
The argument is local at a surviving point, so does not identify different prime ends. -/
theorem trMap_inner_not_mem_closure_exterior {W : ℝ → ℝ} {r : ℝ} {Γ E : Set ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hr : 0 ≤ r)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hEO : fwdMap W r '' E ⊆ outerSide Γ) :
    ∀ w ∈ innerSide Γ, trMap W 0 r w ∉ closure E := by
  intro w hw hcl
  have hwH := innerSide_subset_H hΓ hΓH hw
  have hzD := trMap_zero_mem_domain hW hW0 hr hwH
  have hg : ContinuousAt (fwdMap W r) (trMap W 0 r w) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr).continuousOn.continuousAt
      (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hr |>.mem_nhds hzD)
  have hcl' := hg.continuousWithinAt.mem_closure_image (s := E) hcl
  rw [fwdMap_trMap_zero hW hW0 hr hwH] at hcl'
  have hdisj := (disjoint_innerSide_outerSide (J := Γ)).closure_right
    (jordan_sides hΓ hΓH).2.2.2.2.1
  exact Set.disjoint_left.1 hdisj hw (closure_mono hEO hcl')

end InteractingSLE.Sec7.R7FaceSelect
