/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkChain
import InteractingSLE.Spec.Supplement.SBLvPinchUse

/-!
# S5's stage path: a simple path through a walk prefix

Packet PROVE-T14-SBLEAVES2, item (2)(a) of `planning/handoffs/PROVE-T14-SBLEAVES.md` §7.4. Lemma S5's relative step
(`Lv.erasureStep_relative_of_finite`) parametrizes the retained set by a continuous path `p` on `[0, 1]` with finite
fibres. The walk's prefixes are chronological arc histories (`GW1WalkChain.ArcHistory`, from
`WalkIntRunChron.stateRepresented_run`): a root followed by arcs each meeting the past only at its start. Such a set is
the image of a *simple* path (`exists_path_of_arcHistory`), and the retained prefix `A ∪ [u, 0]` of SB2(1) is the image
of the real bridge followed by that path, a path with finite fibres (`exists_bridge_path`).

* `concatPath`: the concatenation of two paths on `[0, 1]`, with continuity, image, finite fibres and injectivity;
* `exists_path_of_arcHistory`;
* `exists_bridge_path`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lw

/-- The concatenation of two paths parametrized by `[0, 1]`: `p₁` on `[0, 1/2]`, then `p₂` on `[1/2, 1]`. -/
def concatPath (p₁ p₂ : ℝ → ℂ) (s : ℝ) : ℂ := if s ≤ 1 / 2 then p₁ (2 * s) else p₂ (2 * s - 1)

theorem concatPath_zero (p₁ p₂ : ℝ → ℂ) : concatPath p₁ p₂ 0 = p₁ 0 := by
  simp [concatPath]

theorem concatPath_one (p₁ p₂ : ℝ → ℂ) : concatPath p₁ p₂ 1 = p₂ 1 := by
  norm_num [concatPath]

theorem concatPath_eqOn_left (p₁ p₂ : ℝ → ℂ) :
    EqOn (concatPath p₁ p₂) (fun s => p₁ (2 * s)) (Icc 0 (1 / 2)) := fun s hs => by
  simp only [concatPath, hs.2, ↓reduceIte]

theorem concatPath_eqOn_right {p₁ p₂ : ℝ → ℂ} (hj : p₁ 1 = p₂ 0) :
    EqOn (concatPath p₁ p₂) (fun s => p₂ (2 * s - 1)) (Icc (1 / 2) 1) := fun s hs => by
  rcases hs.1.lt_or_eq with hlt | heq
  · simp only [concatPath, not_le.2 hlt, ↓reduceIte]
  · subst heq; norm_num [concatPath, hj]

theorem continuousOn_concatPath {p₁ p₂ : ℝ → ℂ} (h₁ : ContinuousOn p₁ (Icc 0 1)) (h₂ : ContinuousOn p₂ (Icc 0 1))
    (hj : p₁ 1 = p₂ 0) : ContinuousOn (concatPath p₁ p₂) (Icc 0 1) := by
  have hsplit : Icc (0 : ℝ) 1 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 1 := (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
  rw [hsplit]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · refine ContinuousOn.congr ?_ (concatPath_eqOn_left p₁ p₂)
    exact h₁.comp (continuous_const.mul continuous_id).continuousOn fun s hs =>
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · refine ContinuousOn.congr ?_ (concatPath_eqOn_right hj)
    exact h₂.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn fun s hs =>
      ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem image_concatPath {p₁ p₂ : ℝ → ℂ} (hj : p₁ 1 = p₂ 0) :
    concatPath p₁ p₂ '' Icc 0 1 = p₁ '' Icc 0 1 ∪ p₂ '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    by_cases hs2 : s ≤ 1 / 2
    · exact Or.inl ⟨2 * s, ⟨by linarith [hs.1], by linarith⟩, (concatPath_eqOn_left p₁ p₂ ⟨hs.1, hs2⟩).symm⟩
    · push Not at hs2
      exact Or.inr ⟨2 * s - 1, ⟨by linarith, by linarith [hs.2]⟩,
        (concatPath_eqOn_right hj ⟨hs2.le, hs.2⟩).symm⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · refine ⟨r / 2, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
      rw [concatPath_eqOn_left p₁ p₂ ⟨by linarith [hr.1], by linarith [hr.2]⟩]
      simp only; congr 1; ring
    · refine ⟨(r + 1) / 2, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
      rw [concatPath_eqOn_right hj ⟨by linarith [hr.1], by linarith [hr.2]⟩]
      simp only; congr 1; ring

/-- Finite fibres of a concatenation. -/
theorem finite_fibre_concatPath {p₁ p₂ : ℝ → ℂ} (hj : p₁ 1 = p₂ 0)
    (h₁ : ∀ z, (p₁ ⁻¹' {z} ∩ Icc 0 1).Finite) (h₂ : ∀ z, (p₂ ⁻¹' {z} ∩ Icc 0 1).Finite) (z : ℂ) :
    (concatPath p₁ p₂ ⁻¹' {z} ∩ Icc 0 1).Finite := by
  refine (((h₁ z).image fun r => r / 2).union ((h₂ z).image fun r => (r + 1) / 2)).subset ?_
  rintro s ⟨hsz, hs⟩
  by_cases hs2 : s ≤ 1 / 2
  · refine Or.inl ⟨2 * s, ⟨?_, by linarith [hs.1], by linarith⟩, by ring⟩
    have := concatPath_eqOn_left p₁ p₂ ⟨hs.1, hs2⟩
    simp only [mem_preimage, mem_singleton_iff] at hsz ⊢
    rw [← hsz, this]
  · push Not at hs2
    refine Or.inr ⟨2 * s - 1, ⟨?_, by linarith, by linarith [hs.2]⟩, by ring⟩
    have := concatPath_eqOn_right hj ⟨hs2.le, hs.2⟩
    simp only [mem_preimage, mem_singleton_iff] at hsz ⊢
    rw [← hsz, this]

/-- **Injectivity of a concatenation** of two simple paths, the second meeting the first only at its start. -/
theorem injOn_concatPath {p₁ p₂ : ℝ → ℂ} (hj : p₁ 1 = p₂ 0) (h₁ : InjOn p₁ (Icc 0 1)) (h₂ : InjOn p₂ (Icc 0 1))
    (hmeet : ∀ r ∈ Icc (0 : ℝ) 1, p₂ r ∈ p₁ '' Icc 0 1 → r = 0) : InjOn (concatPath p₁ p₂) (Icc 0 1) := by
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ 1 / 2 →
      concatPath p₁ p₂ s = concatPath p₁ p₂ t → s = t := by
    intro s hs t ht hs2 hst
    rw [concatPath_eqOn_left p₁ p₂ ⟨hs.1, hs2⟩] at hst
    by_cases ht2 : t ≤ 1 / 2
    · rw [concatPath_eqOn_left p₁ p₂ ⟨ht.1, ht2⟩] at hst
      beta_reduce at hst
      have := h₁ ⟨by linarith [hs.1], by linarith⟩ ⟨by linarith [ht.1], by linarith⟩ hst
      linarith
    · push Not at ht2
      rw [concatPath_eqOn_right hj ⟨ht2.le, ht.2⟩] at hst
      beta_reduce at hst
      have h0 := hmeet (2 * t - 1) ⟨by linarith, by linarith [ht.2]⟩
        ⟨2 * s, ⟨by linarith [hs.1], by linarith⟩, hst⟩
      linarith
  intro s hs t ht hst
  by_cases hs2 : s ≤ 1 / 2
  · exact key s hs t ht hs2 hst
  by_cases ht2 : t ≤ 1 / 2
  · exact (key t ht s hs ht2 hst.symm).symm
  push Not at hs2 ht2
  rw [concatPath_eqOn_right hj ⟨hs2.le, hs.2⟩, concatPath_eqOn_right hj ⟨ht2.le, ht.2⟩] at hst
  beta_reduce at hst
  have := h₂ ⟨by linarith, by linarith [hs.2]⟩ ⟨by linarith, by linarith [ht.2]⟩ hst
  linarith

/-- An injective path has finite fibres. -/
theorem finite_fibre_of_injOn {p : ℝ → ℂ} (h : InjOn p (Icc 0 1)) (z : ℂ) : (p ⁻¹' {z} ∩ Icc 0 1).Finite :=
  Set.Subsingleton.finite fun _ ha _ hb => h ha.2 hb.2 (ha.1.trans hb.1.symm)

open GW1WalkChain GW1X in
/-- **A chronological arc history is the image of a simple path** from its root to its endpoint (or is the root
alone). -/
theorem exists_path_of_arcHistory {x : ℂ} {A : Set ℂ} {q : ℂ} (h : ArcHistory x A q) :
    (A = {x} ∧ q = x) ∨ ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ InjOn p (Icc 0 1) ∧ p 0 = x ∧ p 1 = q ∧
      p '' Icc 0 1 = A ∧ ∀ s ∈ Icc (0 : ℝ) 1, p s ≠ x → 0 ≤ (p s).im := by
  induction h with
  | root => exact Or.inl ⟨rfl, rfl⟩
  | @append A q past α arc upper start meet ih =>
    set a : ℝ → ℂ := fun s => α s.toNNReal with ha
    have hmem : ∀ s ∈ Icc (0 : ℝ) 1, s.toNNReal ∈ Iic (1 : ℝ≥0) := fun s hs =>
      show s.toNNReal ≤ 1 from Real.toNNReal_le_one.2 hs.2
    have hac : ContinuousOn a (Icc 0 1) := arc.1.comp continuous_real_toNNReal.continuousOn hmem
    have hainj : InjOn a (Icc 0 1) := fun s hs t ht hst =>
      (Real.toNNReal_eq_toNNReal_iff hs.1 ht.1).1 (arc.2 (hmem s hs) (hmem t ht) hst)
    have haimg : a '' Icc 0 1 = α '' Iic 1 := by
      ext z
      constructor
      · rintro ⟨s, hs, rfl⟩; exact ⟨_, hmem s hs, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨(t : ℝ), ⟨t.2, by exact_mod_cast (show t ≤ 1 from ht)⟩, by simp [ha]⟩
    have ha0 : a 0 = q := by simp [ha, start]
    have ha1 : a 1 = α 1 := by simp [ha]
    have haH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (a s).im := fun s hs => upper _ (hmem s hs)
    right
    rcases ih with ⟨rfl, rfl⟩ | ⟨p₀, hc, hinj, h0, h1, himg, hH⟩
    · refine ⟨a, hac, hainj, ha0, ha1, ?_, fun s hs _ => haH s hs⟩
      rw [haimg, ← start, union_eq_right.2 (singleton_subset_iff.2
        (mem_image_of_mem α (mem_Iic.2 (zero_le : (0 : ℝ≥0) ≤ 1))))]
    · have hj : p₀ 1 = a 0 := by rw [h1, ha0]
      refine ⟨concatPath p₀ a, continuousOn_concatPath hc hac hj, injOn_concatPath hj hinj hainj ?_,
        by rw [concatPath_zero, h0], by rw [concatPath_one, ha1], by rw [image_concatPath hj, himg, haimg], ?_⟩
      · intro r hr hrA
        rw [himg] at hrA
        have h0r := meet r.toNNReal (hmem r hr) hrA
        rw [Real.toNNReal_eq_zero] at h0r
        exact le_antisymm h0r hr.1
      · intro s hs hsx
        by_cases hs2 : s ≤ 1 / 2
        · have he := concatPath_eqOn_left p₀ a ⟨hs.1, hs2⟩
          rw [he] at hsx ⊢
          exact hH (2 * s) ⟨by linarith [hs.1], by linarith⟩ hsx
        · push Not at hs2
          rw [concatPath_eqOn_right hj ⟨hs2.le, hs.2⟩]
          exact haH _ ⟨by linarith, by linarith [hs.2]⟩

/-- **The retained prefix with its real bridge** `A ∪ [u, 0]` (`u < 0`) is the image of a path from `u` with finite
fibres, when `A` is the image of a simple path from `0`. -/
theorem exists_bridge_path {A : Set ℂ} {u : ℝ} (hu : u < 0) {p₀ : ℝ → ℂ} (hc : ContinuousOn p₀ (Icc 0 1))
    (hinj : InjOn p₀ (Icc 0 1)) (h0 : p₀ 0 = 0) (himg : p₀ '' Icc 0 1 = A)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p₀ s).im) :
    ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = u ∧ (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧
      p '' Icc 0 1 = ((↑) : ℝ → ℂ) '' Icc u 0 ∪ A ∧ ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im := by
  set seg : ℝ → ℂ := fun s => ((u * (1 - s) : ℝ) : ℂ) with hseg
  have hsc : ContinuousOn seg (Icc 0 1) := by fun_prop
  have hsj : seg 1 = p₀ 0 := by simp [hseg, h0]
  have hsinj : InjOn seg (Icc 0 1) := fun s _ t _ hst => by
    have h := Complex.ofReal_injective hst
    have := mul_left_cancel₀ hu.ne h
    linarith
  have hsimg : seg '' Icc 0 1 = ((↑) : ℝ → ℂ) '' Icc u 0 := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨u * (1 - s), ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨1 - y / u, ⟨?_, ?_⟩, ?_⟩
      · rw [sub_nonneg, div_le_one_of_neg hu]; exact hy.1
      · have : 0 ≤ y / u := div_nonneg_of_nonpos hy.2 hu.le
        linarith
      · simp only [hseg, sub_sub_cancel]
        rw [mul_div_cancel₀ _ hu.ne]
  refine ⟨concatPath seg p₀, continuousOn_concatPath hsc hc hsj, by rw [concatPath_zero]; simp [hseg],
    finite_fibre_concatPath hsj (finite_fibre_of_injOn hsinj) (finite_fibre_of_injOn hinj), ?_, ?_⟩
  · rw [image_concatPath hsj, hsimg, himg]
  · intro s hs
    by_cases hs2 : s ≤ 1 / 2
    · rw [concatPath_eqOn_left seg p₀ ⟨hs.1, hs2⟩]
      simp [hseg]
    · push Not at hs2
      rw [concatPath_eqOn_right hsj ⟨hs2.le, hs.2⟩]
      exact hH _ ⟨by linarith, by linarith [hs.2]⟩

end InteractingSLE.Theorem14.SB.Lw
