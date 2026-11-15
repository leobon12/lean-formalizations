/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Instances.Rat

/-! # A uniform criterion for zero limits on compact boundary patches

Compactness upgrades pointwise boundary limits to uniform smallness on a
thickening. Rational tolerances and radii suffice for this criterion.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric

namespace InteractingSLE.Sec5.Aux61GVan

/-- Vanishing at every point of a compact patch is equivalent to uniform
smallness near that patch, with only rational tolerances and radii. -/
theorem tendsto_zero_on_compact_iff {K U : Set ℂ} (hK : IsCompact K) {f : ℂ → ℝ} :
    (∀ a ∈ K, Tendsto f (𝓝[U] a) (𝓝 0)) ↔
      ∀ ε : ℚ, 0 < ε → ∃ δ : ℚ, 0 < δ ∧
        ∀ z ∈ U, z ∈ thickening (δ : ℝ) K → |f z| ≤ ε := by
  constructor
  · intro h ε hε
    have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
    have hA : {z | z ∈ U → |f z| ≤ (ε : ℝ)} ∈ 𝓝ˢ K := by
      apply mem_nhdsSet_iff_forall.2
      intro a ha
      apply eventually_nhdsWithin_iff.1
      filter_upwards [(h a ha).eventually (ball_mem_nhds (0 : ℝ) hεR)] with z hz
      exact (by simpa only [mem_ball, Real.dist_eq, sub_zero] using hz : |f z| < ε).le
    obtain ⟨r, hr, hrA⟩ := (hasBasis_nhdsSet_thickening hK).mem_iff.1 hA
    obtain ⟨δ, hδ0, hδr⟩ := exists_rat_btwn hr
    refine ⟨δ, by exact_mod_cast hδ0, fun z hzU hz => ?_⟩
    exact hrA ((thickening_mono hδr.le K) hz) hzU
  · intro h a ha
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨r, hr0, hrε⟩ := exists_rat_btwn hε
    obtain ⟨δ, hδ0, hδ⟩ := h r (by exact_mod_cast hr0)
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ0
    have hn : thickening (δ : ℝ) K ∈ 𝓝 a :=
      mem_nhdsSet_iff_forall.1 (thickening_mem_nhdsSet K hδR) a ha
    filter_upwards [nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with z hz hzU
    simpa only [Real.dist_eq, sub_zero] using (hδ z hzU hz).trans_lt hrε

end InteractingSLE.Sec5.Aux61GVan
