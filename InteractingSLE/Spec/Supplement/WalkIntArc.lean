/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkContinuum
import InteractingSLE.Spec.Sec7.Lemma613Geom

/-!
# Local coincidence of the two proper walk ranges

Packet PROVE-T14-WALKINT. A common continuum contains a nondegenerate common arc
(`WalkCont.exists_Icc_image_subset_of_isPreconnected`). At every interior point of
that arc the complete walk ranges coincide in a ball. This strengthens the stopped
range collar in `Sec7.Lemma613.exists_sameArc` to a prescribed point and complete
ranges. It does not identify the incident sides of the prefix charts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkInt

/-- At an interior point of an arc common to two proper curves, their complete
ranges agree locally. -/
theorem exists_ball_range_eq_of_common_arc {α β : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    {a b c : ℝ≥0} (hac : a < c) (hcb : c < b)
    (hsub : α '' Icc a b ⊆ range β) :
    ∃ r > 0, range α ∩ ball (α c) r = range β ∩ ball (α c) r := by
  classical
  let g : ℝ≥0 → ℝ≥0 := fun u => Function.invFun β (α u)
  have hgeq : ∀ u ∈ Icc a b, β (g u) = α u := fun u hu =>
    Function.invFun_eq (hsub (mem_image_of_mem α hu))
  obtain ⟨R, hR⟩ := (isCompact_Icc.image hα.1).isBounded.exists_norm_le
  obtain ⟨T, hT⟩ := eventually_atTop.1 (tendsto_atTop.1 hβ.2.2.2 (R + 1))
  have hgT : ∀ u ∈ Icc a b, g u ∈ Icc 0 T := by
    intro u hu
    refine ⟨zero_le, ?_⟩
    by_contra hno
    have hlarge := hT (g u) (not_le.1 hno).le
    have hsmall := hR (α u) (mem_image_of_mem α hu)
    rw [hgeq u hu] at hlarge
    linarith only [hlarge, hsmall]
  have hgc : ContinuousOn g (Icc a b) :=
    Sec7.Lemma613.continuousOn_of_comp_eq hα.1.continuousOn
      hβ.1.continuousOn hβ.2.1.injOn hgT hgeq
  have hgi : InjOn g (Icc a b) := by
    intro u hu v hv huv
    apply hα.2.1
    rw [← hgeq u hu, ← hgeq v hv, huv]
  obtain ⟨lo, hi, hlo, hhi, hI⟩ :=
    Sec7.Lemma613.exists_Ioo_subset_image hac hcb hgc hgi
  have hc : c ∈ Ioo a b := ⟨hac, hcb⟩
  have hβc : β (g c) = α c := hgeq c (Ioo_subset_Icc_self hc)
  have hαcl : IsClosed (α '' (Ioo a b)ᶜ) :=
    (WalkCont.isClosedEmbedding_of_isProperCurve hα).isClosedMap _ isOpen_Ioo.isClosed_compl
  have hβcl : IsClosed (β '' (Ioo lo hi)ᶜ) :=
    (WalkCont.isClosedEmbedding_of_isProperCurve hβ).isClosedMap _ isOpen_Ioo.isClosed_compl
  have hpα : α c ∉ α '' (Ioo a b)ᶜ := by
    rintro ⟨u, hu, he⟩
    exact hu (hα.2.1 he ▸ hc)
  have hpβ : α c ∉ β '' (Ioo lo hi)ᶜ := by
    rintro ⟨u, hu, he⟩
    rw [← hβc] at he
    exact hu (hβ.2.1 he ▸ ⟨hlo, hhi⟩)
  obtain ⟨rα, hrα, hballα⟩ := Metric.isOpen_iff.1 hαcl.isOpen_compl _ hpα
  obtain ⟨rβ, hrβ, hballβ⟩ := Metric.isOpen_iff.1 hβcl.isOpen_compl _ hpβ
  refine ⟨min rα rβ, lt_min hrα hrβ, ?_⟩
  ext z
  constructor
  · rintro ⟨⟨u, rfl⟩, hub⟩
    have hu : u ∈ Ioo a b := by
      by_contra hno
      exact hballα (ball_subset_ball (min_le_left _ _) hub) ⟨u, hno, rfl⟩
    exact ⟨hsub (mem_image_of_mem α (Ioo_subset_Icc_self hu)), hub⟩
  · rintro ⟨⟨v, rfl⟩, hvb⟩
    have hv : v ∈ Ioo lo hi := by
      by_contra hno
      exact hballβ (ball_subset_ball (min_le_right _ _) hvb) ⟨v, hno, rfl⟩
    obtain ⟨u, hu, huv⟩ := hI hv
    exact ⟨⟨u, (hgeq u hu).symm.trans (congrArg β huv)⟩, hvb⟩

/-- A common continuum of two proper curves contains a common interior arc with
local equality of the complete ranges at every interior parameter. -/
theorem exists_common_arc_local_eq {α β : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    {S : Set ℂ} (hS : S ⊆ range α ∩ range β) (hSc : IsPreconnected S)
    (hSn : ¬ S.Subsingleton) :
    ∃ a b : ℝ≥0, a < b ∧ α '' Icc a b ⊆ S ∧ ∀ c ∈ Ioo a b,
      ∃ r > 0, range α ∩ ball (α c) r = range β ∩ ball (α c) r := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.1 hSn
  obtain ⟨a, b, hab, hsub⟩ := WalkCont.exists_Icc_image_subset_of_isPreconnected
    (WalkCont.isClosedEmbedding_of_isProperCurve hα).isEmbedding
    (fun z hz => (hS hz).1) hSc hx hy hxy
  exact ⟨a, b, hab, hsub, fun c hc =>
    exists_ball_range_eq_of_common_arc hα hβ hc.1 hc.2
      (fun z hz => (hS (hsub hz)).2)⟩

/-- A nondegenerate common continuum in the closed half-plane, with no real
subcontinuum, has an interior half-plane point where the complete curves agree
locally. The real-subcontinuum premise is supplied for ordinary walk pieces by
`WalkPiece.pieces_real_subsingleton_of_range`. -/
theorem exists_common_point_mem_H {α β : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    {S : Set ℂ} (hS : S ⊆ range α ∩ range β) (hSc : IsPreconnected S)
    (hSn : ¬ S.Subsingleton) (hSH : S ⊆ QuantumZipper.Hbar)
    (hreal : ∀ T ⊆ S ∩ {z : ℂ | z.im = 0}, IsPreconnected T → T.Subsingleton) :
    ∃ p ∈ S ∩ QuantumZipper.H, ∃ r > 0,
      range α ∩ ball p r = range β ∩ ball p r := by
  obtain ⟨a, b, hab, hsub, hloc⟩ := exists_common_arc_local_eq hα hβ hS hSc hSn
  have hne : ∃ c ∈ Ioo a b, (α c).im ≠ 0 := by
    by_contra hno
    have hall : ∀ c ∈ Ioo a b, (α c).im = 0 := by
      simpa only [not_exists, not_and, not_not] using hno
    have hTsub : α '' Ioo a b ⊆ S ∩ {z : ℂ | z.im = 0} := by
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨hsub (mem_image_of_mem α (Ioo_subset_Icc_self hc)), hall c hc⟩
    have hT := hreal _ hTsub (isPreconnected_Ioo.image α hα.1.continuousOn)
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    obtain ⟨d, hcd, hdb⟩ := exists_between hcb
    exact hcd.ne (hα.2.1 (hT (mem_image_of_mem α ⟨hac, hcb⟩)
      (mem_image_of_mem α ⟨hac.trans hcd, hdb⟩)))
  obtain ⟨c, hc, hci⟩ := hne
  have hcS : α c ∈ S := hsub (mem_image_of_mem α (Ioo_subset_Icc_self hc))
  have hcH : α c ∈ QuantumZipper.H :=
    lt_of_le_of_ne (show 0 ≤ (α c).im from hSH hcS) hci.symm
  obtain ⟨r, hr, heq⟩ := hloc c hc
  exact ⟨α c, ⟨hcS, hcH⟩, r, hr, heq⟩

end InteractingSLE.Theorem14.WalkInt
