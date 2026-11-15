/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBoundCutPocket

/-!
# A common closing contact beyond every finite component landing

The closing parameters are supplied by the existing shaped-pocket
coordinate. They are strict bounds on both walks, uniformly over all
finite real boundary coordinates, including zero and real connectors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntBoundCut

open GW4Reg GB11Chart

/-- Every finite chart landing precedes the same finite common closing
contact on both complete proper walks. No cutoff selection is assumed. -/
theorem exists_closing_contact {α β : ℝ≥0 → ℂ}
    (hα : GB11.IsCompleteSimpleFlow α) (hβ : GB11.IsCompleteSimpleFlow β)
    (horder : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t'))
    (hno : ∀ a b : ℝ≥0, a < b → ¬ α '' Icc a b ⊆ range β)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range α) (range β))
    {c : Chart} (hc : IsComponentChart (range α) (range β) C c)
    (hb : Bornology.IsBounded C) :
    ∃ U V : ℝ≥0, 0 < U ∧ 0 < V ∧ α U = β V ∧ α U ∈ closure C ∧
      ∀ x : ℝ,
        (∀ r, α r = GW4Traverse.invExt c (x : ℂ) → r < U) ∧
        (∀ r, β r = GW4Traverse.invExt c (x : ℂ) → r < V) := by
  obtain ⟨s, t, u, v, hs⟩ := exists_shape_of_component_chart hα hβ horder hno hC hc
  have hu : u ≠ ⊤ := fun hu => hs.unbounded hu hb
  obtain ⟨hv, hsu, htv⟩ := PocketShapeDet.finite_parameters horder hs hu
  have hentry := hs.entry hu
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hα) (isClosed_range_of_isCompleteSimpleFlow hβ) hC
  obtain ⟨p₀, hp₀, _, _⟩ := hc.2.2.2.2.1 0
  have hp₀' : Tendsto c.2.1 (𝓝[H] (0 : ℂ)) (𝓝 p₀) := by
    simpa only [Complex.ofReal_zero] using hp₀
  have hzero : Tendsto c.2.1 (𝓝[H] (0 : ℂ)) (𝓝 (α s)) :=
    (PocketCompass.chart_zero_eq_exit hα hβ horder hC hs hc hp₀') ▸ hp₀'
  obtain ⟨ψ, G, k, hcoord, _, _⟩ := exists_isPocketCoord_of_bounded hα hβ horder hC hs hu hc hzero
  refine ⟨u.toNNReal, v.toNNReal, zero_le.trans_lt hsu, zero_le.trans_lt htv,
    hentry.1, hentry.2.1, fun x => ?_⟩
  have hland := GW4Traverse.tendsto_invExt hc hCo
    (show (x : ℂ) ∈ Hbar by change 0 ≤ (x : ℂ).im; simp only [Complex.ofReal_im, le_refl])
  have hmem := landing_mem_of_pocketCoord hcoord hland
  constructor
  · intro r he
    have hle := PocketShapeFin.right_parameter_le_entry hα hβ horder hC hs hu (he.symm ▸ hmem.1)
    apply lt_of_not_ge
    intro hge
    have hre : r = u.toNNReal := le_antisymm hle hge
    apply hmem.2
    change GW4Traverse.invExt c (x : ℂ) = α u.toNNReal
    exact he.symm.trans (congrArg α hre)
  · intro r he
    have hrfr : β r ∈ frontier C := by
      rw [hCo.frontier_eq]
      exact ⟨he.symm ▸ hmem.1, fun hz =>
        (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).2 (Or.inr ⟨r, rfl⟩)⟩
    have hle : r ≤ v.toNNReal := by
      rcases hs.frontier_subset hrfr with ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
      · have hqu : q ≤ u.toNNReal := ENNReal.coe_le_coe.1 (by
          simpa only [ENNReal.coe_toNNReal hu] using hq.2)
        exact le_of_not_gt fun hvr =>
          (not_lt_of_ge hqu) ((horder u.toNNReal q v.toNNReal r hentry.1 heq).2 hvr)
      · have hqr : q = r := hβ.2.1 heq
        subst q
        exact ENNReal.coe_le_coe.1 (by simpa only [ENNReal.coe_toNNReal hv] using hq.2)
    apply lt_of_not_ge
    intro hge
    have hre : r = v.toNNReal := le_antisymm hle hge
    apply hmem.2
    change GW4Traverse.invExt c (x : ℂ) = α u.toNNReal
    exact he.symm.trans ((congrArg β hre).trans hentry.1.symm)

end InteractingSLE.Theorem14.WalkIntBoundCut
