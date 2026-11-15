/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFiberPrefix
import InteractingSLE.Spec.Supplement.GW4TraverseTrace

/-!
# Physical component collars give real transition intervals

The component inverse is continuous up to the real line. A physical collar
avoiding a reference domain therefore supplies real transition limits on
a smaller interval. No finiteness of real trace contacts is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntFiber

/-- A physical collar on the two component walls supplies the entire real
transition interval needed for reflection. The component entry 0 is excluded. -/
theorem exists_realLimits_of_component_collar {R L C : Set ℂ} {c d : Chart}
    (hchart : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    (hd : d.IsConformal) (hproper : GW1P.HasProperBdryExt d)
    {x r ρ : ℝ} (hx : x ≠ 0) (hr : 0 < r) (hρ : 0 < ρ) {p : ℂ}
    (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p))
    (havoid : Disjoint (d.dom : Set ℂ) (((R ∪ L) ∩ H) ∩ ball p r))
    (hdom : ∀ z ∈ H ∩ ball (x : ℂ) ρ, c.2.1 z ∈ d.dom) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      (∀ z ∈ H ∩ ball (x : ℂ) δ, c.2.1 z ∈ d.dom) ∧
      ∀ z ∈ ball (x : ℂ) δ, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
        Tendsto (fun w => d.1 (c.2.1 w)) (𝓝[H] z) (𝓝 v) := by
  have hc := GW3Law.isConformal_of_isComponentChart hchart hCo hCH
  have hxbar : (x : ℂ) ∈ Hbar := by simp [QuantumZipper.Hbar]
  have hEx : GW4Traverse.invExt c (x : ℂ) = p := by
    let _ := GW1P.neBot_nhdsWithin_H hxbar
    exact tendsto_nhds_unique (GW4Traverse.tendsto_invExt hchart hCo hxbar) hland
  have hnear : ∀ᶠ z in 𝓝[Hbar] (x : ℂ),
      GW4Traverse.invExt c z ∈ ball p r ∧ z ≠ 0 := by
    have hE := (GW4Traverse.continuousOn_invExt hchart hCo _ hxbar).tendsto
    rw [hEx] at hE
    have hEb : ∀ᶠ z in 𝓝[Hbar] (x : ℂ), GW4Traverse.invExt c z ∈ ball p r :=
      hE (ball_mem_nhds p hr)
    exact hEb.and
      (nhdsWithin_le_nhds (eventually_ne_nhds (by exact_mod_cast hx)))
  obtain ⟨a, ha, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hnear
  refine ⟨min a ρ, lt_min ha hρ, min_le_right _ _, ?_, ?_⟩
  · intro z hz
    exact hdom z ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩
  · intro z hz hz0
    have hzρ := ball_subset_ball (min_le_right a ρ) hz
    have hza := ball_subset_ball (min_le_left a ρ) hz
    have hzbar : z ∈ Hbar := mem_Hbar_of_im_eq_zero hz0
    obtain ⟨hEb, hzne⟩ := hsub ⟨hza, hzbar⟩
    have he : (z.re : ℂ) = z := (eq_ofReal_re_of_im_eq_zero hz0).symm
    have hzr : z.re ≠ 0 := by
      intro h
      apply hzne
      rw [← he, h, ofReal_zero]
    obtain ⟨q, hq, hR, hL⟩ := hchart.2.2.2.2.1 z.re
    have hEq : GW4Traverse.invExt c z = q := by
      let _ := GW1P.neBot_nhdsWithin_H hzbar
      exact tendsto_nhds_unique (GW4Traverse.tendsto_invExt hchart hCo hzbar)
        (by simpa only [he] using hq)
    have hnot : GW4Traverse.invExt c z ∉ d.dom := by
      intro hp
      have hH : GW4Traverse.invExt c z ∈ H := hd.dom_subset hp
      have hwall : GW4Traverse.invExt c z ∈ R ∪ L := by
        rw [hEq]
        rcases lt_or_gt_of_ne hzr with hn | hp
        · exact Or.inr (hL hn)
        · exact Or.inl (hR hp)
      exact Set.disjoint_left.1 havoid hp ⟨⟨hwall, hH⟩, hEb⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 isOpen_ball z hzρ
    have hlim := exists_real_transition_limit_of_landing hc hd hproper hε
      (x := z.re) (fun w hw => hdom w ⟨hw.1, hεsub (by simpa [he] using hw.2)⟩)
      hnot (by simpa only [he] using GW4Traverse.tendsto_invExt hchart hCo hzbar)
    simpa only [he] using hlim

open WalkBdry WalkMean

/-- Real roots and connectors add no point in H to the ordinary walk set. -/
theorem physOf_inter_H (w : ExplSpec) (s : ExplState) :
    physOf w s ∩ H = wsetOf s := by
  ext z
  simp only [physOf, wsetOf, ordOf, mem_inter_iff, mem_union, mem_singleton_iff,
    mem_iUnion, mem_image, exists_prop]
  constructor
  · rintro ⟨(⟨rfl | h⟩ | ⟨a, -, t, -, rfl⟩), hzH⟩
    · exact absurd hzH (by simp [QuantumZipper.H])
    · exact ⟨h, hzH⟩
    · exact absurd hzH (by simp [QuantumZipper.H])
  · rintro ⟨h, hzH⟩
    exact ⟨Or.inl (Or.inr h), hzH⟩

/-- The original local walk-containment conjuncts imply the physical
reference-domain gap used above. -/
theorem disjoint_component_wall_collar {wR wL : ExplSpec} {s s' : ExplState}
    {d : Chart} {A : Set ℂ} {p : ℂ} {r : ℝ}
    (hA : Disjoint (d.dom : Set ℂ) A)
    (hown : wsetOf s ∩ ball p r ⊆ A)
    (hother : wsetOf s' ∩ ball p r ⊆ wsetOf s) :
    Disjoint (d.dom : Set ℂ)
      (((physOf wR s ∪ physOf wL s') ∩ H) ∩ ball p r) := by
  refine Set.disjoint_left.2 fun z hz ⟨⟨hwall, hzH⟩, hball⟩ => ?_
  have hwalk : z ∈ wsetOf s := by
    rcases hwall with hR | hL
    · exact (Set.ext_iff.1 (physOf_inter_H wR s) z).1 ⟨hR, hzH⟩
    · exact hother ⟨(Set.ext_iff.1 (physOf_inter_H wL s') z).1 ⟨hL, hzH⟩, hball⟩
  exact Set.disjoint_left.1 hA hz (hown ⟨hwalk, hball⟩)

end InteractingSLE.Theorem14.WalkIntFiber
