/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3Geometry
import InteractingSLE.Spec.Supplement.SBS3CollarRecords
import InteractingSLE.Spec.Supplement.SBLemmaS5Main

/-!
# Lemma S3: old-range lift coordinates are positive after the seed

Packet PROVE-T14-S3, specification pp. 579–580. The left-entry chart's
already proved boundary orientation sends every negative chart coordinate
to an untouched original real point left of the old base. Hence a lifted
old-range contact is nonnegative, and injectivity makes it positive after
time zero.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- Negative left-entry coordinates land strictly left of the entire old
real base, so they cannot land in the old history. -/
theorem g_ofReal_notMem_old_of_neg {p : ℝ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) {c : Chart} {g : ℂ → ℂ}
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {x : ℝ} (hx : x < 0) : g (x : ℂ) ∉ p '' Icc 0 1 := by
  obtain ⟨e, -, -, hge, hsurj⟩ := hc.exists_boundary_orient hp hp0 hgc hgi
  obtain ⟨y, hy, hey⟩ := hsurj x hx
  have hgx : g (x : ℂ) = (y : ℂ) := by rw [← hey]; exact (hge y hy).2
  rw [hgx]
  intro hyA
  exact (not_le.2 hy) ((realBase_facts hp hp0).2.2.1 y hyA).1

/-- Every lifted old-range contact is real and nonnegative in a left-entry
chart. No simplicity of the physical old history is required. -/
theorem re_nonneg_of_landing_mem_old {p : ℝ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) {c : Chart} {g : ℂ → ℂ}
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {z : ℂ} (hz : 0 ≤ z.im) (hzA : g z ∈ p '' Icc 0 1) : 0 ≤ z.re := by
  have him := im_eq_zero_of_landing_mem hc.1 hgi hz hzA
  have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp only [Complex.ofReal_im, him])
  by_contra hneg
  exact g_ofReal_notMem_old_of_neg hp hp0 hc hgc hgi (not_le.1 hneg) (hzr ▸ hzA)

/-- A proper lift from zero has strictly positive coordinate at every
old-range contact after time zero. -/
theorem re_pos_of_lift_landing_mem_old {p : ℝ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) {c : Chart} {g : ℂ → ℂ}
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0)
    {t : ℝ≥0} (ht : 0 < t) (htA : g (γ t) ∈ p '' Icc 0 1) : 0 < (γ t).re := by
  have him := im_eq_zero_of_landing_mem hc.1 hgi (hγ.2.2.1 t) htA
  refine lt_of_le_of_ne (re_nonneg_of_landing_mem_old hp hp0 hc hgc hgi (hγ.2.2.1 t) htA) ?_
  intro hre
  have hzero : γ t = γ 0 := by
    rw [hγ0]
    exact Complex.ext hre.symm him
  exact ht.ne' (hγ.2.1 hzero)

/-- A lifted common arc is traversed in increasing real coordinates. -/
theorem strictMonoOn_re_of_lifted_common_arc {p : ℝ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) {c : Chart} {g : ℂ → ℂ}
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0)
    {s₁ s₂ : ℝ≥0} (harc : (g ∘ γ) '' Ioo s₁ s₂ ⊆ p '' Icc 0 1) :
    StrictMonoOn (fun t => (γ t).re) (Ioo s₁ s₂) := by
  intro s hs t ht hst
  have hsA := harc ⟨s, hs, rfl⟩
  have htA := harc ⟨t, ht, rfl⟩
  have hsim := im_eq_zero_of_landing_mem hc.1 hgi (hγ.2.2.1 s) hsA
  have htim := im_eq_zero_of_landing_mem hc.1 hgi (hγ.2.2.1 t) htA
  have htnn := re_nonneg_of_landing_mem_old hp hp0 hc hgc hgi (hγ.2.2.1 t) htA
  exact re_lt_of_real_before_nonneg_contact hγ hγ0 htnn hst hsim
    (Complex.ext rfl (by simp only [Complex.ofReal_im, htim]))

/-- The finite-word interval selected from a lifted common arc lies
strictly to the right of the left-entry seed. -/
theorem exists_positive_const_interval_of_lift {p : ℝ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) {c : Chart} {g : ℂ → ℂ}
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0)
    {s₁ s₂ : ℝ≥0} (hs : s₁ < s₂)
    (harc : (g ∘ γ) '' Ioo s₁ s₂ ⊆ p '' Icc 0 1)
    {B : ℝ → ℝ} {J : Finset ℝ} (hB : IsPiecewiseConstantBoundaryData B J) :
    ∃ x a b : ℝ, 0 < a ∧ a < b ∧ x ∈ Ioo a b ∧
      ((↑) : ℝ → ℂ) '' Icc a b ⊆ γ '' Ioo s₁ s₂ ∧
      (∀ y ∈ Icc a b, g (y : ℂ) ∈ p '' Icc 0 1 ∧ y ∉ J ∧ B y = B x) := by
  obtain ⟨x, a, b, hab, hx, hI, hword⟩ :=
    exists_const_real_interval_of_lift hc.1 hgi hγ hs harc hB
  obtain ⟨t, ht, hta⟩ := hI ⟨a, left_mem_Icc.2 hab.le, rfl⟩
  have htA : g (γ t) ∈ p '' Icc 0 1 := by
    rw [hta]
    exact (hword a (left_mem_Icc.2 hab.le)).1
  have hpos := re_pos_of_lift_landing_mem_old hp hp0 hc hgc hgi hγ hγ0
    (lt_of_le_of_lt zero_le ht.1) htA
  rw [hta, Complex.ofReal_re] at hpos
  exact ⟨x, a, b, hpos, hab, hx, hI, hword⟩

end InteractingSLE.Theorem14.SB.S3
