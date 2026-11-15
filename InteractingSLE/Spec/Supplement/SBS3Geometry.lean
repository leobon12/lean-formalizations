/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Interval.Set.Infinite
import InteractingSLE.Spec.Supplement.SBLemmaS2Lift

/-!
# Lemma S3: selecting an interval in the old boundary

Packet PROVE-T14-S3, specification pp. 579–580. These deterministic lemmas use
the continuous injective lift supplied by S2. They do not assume a relative
Loewner driver, whose construction uses S3.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- A point of the lifted retained range lies on the real boundary of the chart. -/
theorem im_eq_zero_of_landing_mem {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}
    (hc : IsDomainChart (H \ fillH A) c) (hgi : EqOn g c.2.1 H)
    {z : ℂ} (hz : 0 ≤ z.im) (hA : g z ∈ A) : z.im = 0 := by
  refine le_antisymm (le_of_not_gt fun hpos => ?_) hz
  have hD := hc.inv_mem hpos
  rw [← hgi hpos] at hD
  exact hD.2 ⟨hD.1, Or.inl (subset_closure hA)⟩

/-- A nontrivial lifted common arc contains a nontrivial closed real interval.
Only the lift is required to be injective; the old physical history may pinch. -/
theorem exists_real_interval_of_lift {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}
    (hc : IsDomainChart (H \ fillH A) c) (hgi : EqOn g c.2.1 H)
    {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) {s₁ s₂ : ℝ≥0}
    (hs : s₁ < s₂) (hA : (g ∘ γ) '' Ioo s₁ s₂ ⊆ A) :
    ∃ a b : ℝ, a < b ∧
      ((↑) : ℝ → ℂ) '' Icc a b ⊆ γ '' Ioo s₁ s₂ ∧
      (∀ x ∈ Icc a b, g (x : ℂ) ∈ A) := by
  obtain ⟨t₁, ht₁, ht₁s₂⟩ := exists_between hs
  obtain ⟨t₂, ht₁t₂, ht₂⟩ := exists_between ht₁s₂
  have him : ∀ t ∈ Ioo s₁ s₂, (γ t).im = 0 := fun t ht =>
    im_eq_zero_of_landing_mem hc hgi (hγ.2.2.1 t) (hA ⟨t, ht, rfl⟩)
  have hsub : Icc t₁ t₂ ⊆ Ioo s₁ s₂ := fun t ht =>
    ⟨ht₁.trans_le ht.1, ht.2.trans_lt ht₂⟩
  have hne : (γ t₁).re ≠ (γ t₂).re := by
    intro he
    have h₁ := him t₁ (hsub (left_mem_Icc.2 ht₁t₂.le))
    have h₂ := him t₂ (hsub (right_mem_Icc.2 ht₁t₂.le))
    exact ht₁t₂.ne (hγ.2.1 (Complex.ext he (h₁.trans h₂.symm)))
  have hconn : IsPreconnected ((fun t => (γ t).re) '' Icc t₁ t₂) :=
    isPreconnected_Icc.image _ (Complex.continuous_re.comp hγ.1).continuousOn
  have h₁ : (γ t₁).re ∈ (fun t => (γ t).re) '' Icc t₁ t₂ :=
    ⟨t₁, left_mem_Icc.2 ht₁t₂.le, rfl⟩
  have h₂ : (γ t₂).re ∈ (fun t => (γ t).re) '' Icc t₁ t₂ :=
    ⟨t₂, right_mem_Icc.2 ht₁t₂.le, rfl⟩
  have hmin := hconn.Icc_subset (min_rec' (fun x => x ∈ (fun t => (γ t).re) '' Icc t₁ t₂) h₁ h₂)
    (max_rec' (fun x => x ∈ (fun t => (γ t).re) '' Icc t₁ t₂) h₁ h₂)
  have hreal : ((↑) : ℝ → ℂ) ''
      Icc (min (γ t₁).re (γ t₂).re) (max (γ t₁).re (γ t₂).re) ⊆
      γ '' Ioo s₁ s₂ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, he⟩ := hmin hx
    refine ⟨t, hsub ht, Complex.ext he ?_⟩
    simpa only [Complex.ofReal_im] using him t (hsub ht)
  refine ⟨_, _, min_lt_max.2 hne, hreal, fun x hx => ?_⟩
  obtain ⟨t, ht, he⟩ := hreal ⟨x, hx, rfl⟩
  rw [← he]
  exact hA ⟨t, ht, rfl⟩

/-- Shrink a real interval to a compact interval avoiding every transition mark,
on which a piecewise constant boundary word has one value. -/
theorem exists_const_interval {B : ℝ → ℝ} {J : Finset ℝ}
    (hB : IsPiecewiseConstantBoundaryData B J) {a b : ℝ} (hab : a < b) :
    ∃ x c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧
      (∀ y ∈ Icc c d, y ∉ J ∧ B y = B x) ∧ x ∈ Ioo c d := by
  obtain ⟨x, hx, hxJ⟩ := (Ioo_infinite hab).exists_notMem_finset J
  have hloc : ∀ᶠ y in 𝓝 x, y ∈ Ioo a b ∧ y ∉ J ∧ B y = B x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2,
      J.finite_toSet.isClosed.isOpen_compl.mem_nhds hxJ, hB x hxJ]
      with y hy hyJ hyB using ⟨hy, hyJ, hyB⟩
  obtain ⟨u, v, hxuv, huv⟩ := hloc.exists_Ioo_subset
  obtain ⟨c, huc, hcx⟩ := exists_between hxuv.1
  obtain ⟨d, hxd, hdv⟩ := exists_between hxuv.2
  have hcd : Icc c d ⊆ Ioo u v := fun y hy =>
    ⟨huc.trans_le hy.1, hy.2.trans_lt hdv⟩
  exact ⟨x, c, d, hcx.trans hxd, fun y hy => (huv (hcd hy)).1,
    fun y hy => (huv (hcd hy)).2, hcx, hxd⟩

/-- The old-boundary interval selected from S2 can be selected inside one
constancy interval of the current canonical word, away from all its marks. -/
theorem exists_const_real_interval_of_lift {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}
    (hc : IsDomainChart (H \ fillH A) c) (hgi : EqOn g c.2.1 H)
    {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) {s₁ s₂ : ℝ≥0}
    (hs : s₁ < s₂) (hA : (g ∘ γ) '' Ioo s₁ s₂ ⊆ A)
    {B : ℝ → ℝ} {J : Finset ℝ} (hB : IsPiecewiseConstantBoundaryData B J) :
    ∃ x a b : ℝ, a < b ∧ x ∈ Ioo a b ∧
      ((↑) : ℝ → ℂ) '' Icc a b ⊆ γ '' Ioo s₁ s₂ ∧
      (∀ y ∈ Icc a b, g (y : ℂ) ∈ A ∧ y ∉ J ∧ B y = B x) := by
  obtain ⟨a₀, b₀, hab₀, hsub, hland⟩ := exists_real_interval_of_lift hc hgi hγ hs hA
  obtain ⟨x, a, b, hab, hI, hword, hx⟩ := exists_const_interval hB hab₀
  refine ⟨x, a, b, hab, hx,
    (image_mono fun y hy => Ioo_subset_Icc_self (hI hy)).trans hsub,
    fun y hy => ⟨hland y (Ioo_subset_Icc_self (hI hy)), hword y hy⟩⟩

/-- S2 supplies the lift used in S3's finite-word selection, directly from a
proper one-sided witness and a common physical arc after its visit to `L`. -/
theorem exists_const_real_interval_of_s2 {p : ℝ → ℂ} {β : ℝ≥0 → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (p t).im) (hβ : Supp9B.IsProperCurve β)
    (hβ0 : β 0 = 0) (hA : p '' Icc 0 1 ⊆ Supp9B.closedRightSide β)
    {c : Chart} {g : ℂ → ℂ}
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) {tL : ℝ≥0}
    (htL : β tL = realMin (p '' Icc 0 1)) {s₁ s₂ : ℝ≥0} (hs : s₁ < s₂)
    (harc : β '' Ioo (tL + s₁) (tL + s₂) ⊆ p '' Icc 0 1)
    {B : ℝ → ℝ} {J : Finset ℝ} (hB : IsPiecewiseConstantBoundaryData B J) :
    ∃ (γ : ℝ≥0 → ℂ) (x a b : ℝ), Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧
      (∀ t, g (γ t) = β (tL + t)) ∧ a < b ∧ x ∈ Ioo a b ∧
      ((↑) : ℝ → ℂ) '' Icc a b ⊆ γ '' Ioo s₁ s₂ ∧
      (∀ y ∈ Icc a b, g (y : ℂ) ∈ p '' Icc 0 1 ∧ y ∉ J ∧ B y = B x) := by
  obtain ⟨γ, hγ, hγ0, hγg⟩ := s2LiftStatement p β hp hp0 hpH hβ hβ0 hA c g
    hc hgc hgi hgf tL htL
  have harc' : (g ∘ γ) '' Ioo s₁ s₂ ⊆ p '' Icc 0 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Function.comp_apply, hγg]
    exact harc ⟨tL + t, ⟨by simpa only [add_comm] using add_lt_add_left ht.1 tL,
      by simpa only [add_comm] using add_lt_add_left ht.2 tL⟩, rfl⟩
  obtain ⟨x, a, b, hab, hx, hI, hword⟩ :=
    exists_const_real_interval_of_lift hc.1 hgi hγ hs harc' hB
  exact ⟨γ, x, a, b, hγ, hγ0, hγg, hab, hx, hI, hword⟩

end InteractingSLE.Theorem14.SB.S3
