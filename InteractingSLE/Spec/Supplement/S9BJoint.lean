/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BAccess

/-!
# Supplement §9: the joint domain of two prefixes and its accessible points

Packet PROVE-SUPP9-C.

For two prefixes `γ₁([0, T₁])`, `γ₂([0, T₂])` of curves from real seeds, `jointDomain γ₁ T₁ γ₂ T₂` is the
complement in `ℍ` of the filling of their union: the joint unbounded component of Lemma W4's proof and of Lemma G13
(supplement pp. 506, 532). The union is traversed by one path started on `ℝ` (up and down the second prefix, along
the real segment between the seeds, up the first prefix; `exists_path_union`), so every point of the closure of the
joint domain is the start of a proper injective tail inside it (`exists_tail_of_mem_closure_jointDomain`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp9B

/-! ### Paths along prefixes -/

/-- The path `u ↦ γ(T u)`, `u ∈ [0, 1]`, along the prefix `γ([0, T])`. -/
def prefixPath (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (hγ : ContinuousOn γ (Icc 0 T)) : Path (γ 0) (γ T) where
  toFun u := γ ⟨(T : ℝ) * u, mul_nonneg T.2 u.2.1⟩
  continuous_toFun := by
    refine hγ.comp_continuous ((continuous_const.mul continuous_subtype_val).subtype_mk _) fun u => ?_
    exact ⟨zero_le, NNReal.coe_le_coe.1 (mul_le_of_le_one_right T.2 u.2.2)⟩
  source' := by
    have : (⟨(T : ℝ) * ((0 : unitInterval) : ℝ), mul_nonneg T.2 (0 : unitInterval).2.1⟩ : ℝ≥0) = 0 :=
      NNReal.eq (by show (T : ℝ) * ((0 : unitInterval) : ℝ) = ((0 : ℝ≥0) : ℝ); simp)
    exact congrArg γ this
  target' := by
    have : (⟨(T : ℝ) * ((1 : unitInterval) : ℝ), mul_nonneg T.2 (1 : unitInterval).2.1⟩ : ℝ≥0) = T :=
      NNReal.eq (by show (T : ℝ) * ((1 : unitInterval) : ℝ) = T; simp)
    exact congrArg γ this

theorem range_prefixPath (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (hγ : ContinuousOn γ (Icc 0 T)) :
    range (prefixPath γ T hγ) = γ '' Icc 0 T := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨⟨(T : ℝ) * u, mul_nonneg T.2 u.2.1⟩,
      ⟨zero_le, NNReal.coe_le_coe.1 (mul_le_of_le_one_right T.2 u.2.2)⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    rcases eq_or_ne T 0 with hT | hT
    · have ht0 : t = 0 := le_antisymm (hT ▸ ht.2) zero_le
      exact ⟨0, by rw [ht0]; exact (prefixPath γ T hγ).source⟩
    · have hT' : (0 : ℝ) < T := by positivity
      have hu0 : (0 : ℝ) ≤ t / T := by positivity
      have hu1 : (t : ℝ) / T ≤ 1 := (div_le_one hT').2 (by exact_mod_cast ht.2)
      refine ⟨⟨(t : ℝ) / T, hu0, hu1⟩, ?_⟩
      have : (⟨(T : ℝ) * ((t : ℝ) / T), mul_nonneg T.2 hu0⟩ : ℝ≥0) = t :=
        NNReal.eq (by show (T : ℝ) * ((t : ℝ) / T) = t; field_simp)
      exact congrArg γ this

/-- **One path along two prefixes.** The union of two prefixes from real seeds, together with the real segment
between the seeds, is the image of `[0, 1]` under one continuous path started on `ℝ`. -/
theorem exists_path_union {γ₁ γ₂ : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0} (h₁ : ContinuousOn γ₁ (Icc 0 T₁))
    (h₂ : ContinuousOn γ₂ (Icc 0 T₂)) (hH₁ : MapsTo γ₁ (Icc 0 T₁) Hbar)
    (hH₂ : MapsTo γ₂ (Icc 0 T₂) Hbar) (h₁0 : (γ₁ 0).im = 0) (h₂0 : (γ₂ 0).im = 0) :
    ∃ ζ : ℝ → ℂ, ContinuousOn ζ (Icc 0 1) ∧ MapsTo ζ (Icc 0 1) Hbar ∧ (ζ 0).im = 0 ∧
      γ₁ '' Icc 0 T₁ ∪ γ₂ '' Icc 0 T₂ ⊆ ζ '' Icc 0 1 ∧
      ζ '' Icc 0 1 ⊆ γ₁ '' Icc 0 T₁ ∪ γ₂ '' Icc 0 T₂ ∪ {z | z.im = 0} := by
  set p₁ := prefixPath γ₁ T₁ h₁
  set p₂ := prefixPath γ₂ T₂ h₂
  set P := p₂.trans (p₂.symm.trans ((Path.segment (γ₂ 0) (γ₁ 0)).trans p₁)) with hP
  have hrange : range P = γ₂ '' Icc 0 T₂ ∪ (γ₂ '' Icc 0 T₂ ∪ (segment ℝ (γ₂ 0) (γ₁ 0) ∪ γ₁ '' Icc 0 T₁)) := by
    rw [hP, Path.trans_range, Path.trans_range, Path.trans_range, Path.symm_range, Path.range_segment,
      range_prefixPath, range_prefixPath]
  have himg : P.extend '' Icc 0 1 = range P := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, (P.extend_extends' ⟨t, ht⟩).symm⟩
    · rintro ⟨t, rfl⟩; exact ⟨t, t.2, P.extend_extends' t⟩
  have hseg : segment ℝ (γ₂ 0) (γ₁ 0) ⊆ {z : ℂ | z.im = 0} := by
    have hc : Convex ℝ {z : ℂ | z.im = 0} := by
      intro x hx y hy u v _ _ huv
      show (u • x + v • y).im = 0
      simp only [add_im, Complex.real_smul, mul_im, ofReal_re, ofReal_im, zero_mul,
        add_zero]
      rw [hx, hy]; ring
    exact hc.segment_subset h₂0 h₁0
  refine ⟨P.extend, P.continuous_extend.continuousOn, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have : P.extend t ∈ range P := himg ▸ mem_image_of_mem _ ht
    rw [hrange] at this
    rcases this with h | (h | (h | h))
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hH₂ hu
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hH₂ hu
    · show 0 ≤ (P.extend t).im
      rw [hseg h]
    · obtain ⟨u, hu, hue⟩ := h; rw [← hue]; exact hH₁ hu
  · rw [P.extend_zero]; exact h₂0
  · rw [himg, hrange]
    rintro z (h | h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h
  · rw [himg, hrange]
    rintro z (h | (h | (h | h)))
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (hseg h)
    · exact Or.inl (Or.inl h)

/-! ### The joint domain -/

/-- Adding real points does not change the filling in `ℍ`. -/
theorem fillH_eq_of_subset_union_real {K L : Set ℂ} (hKL : K ⊆ L) (hLK : L ⊆ K ∪ {z | z.im = 0}) :
    fillH L = fillH K := by
  have hR : IsClosed {z : ℂ | z.im = 0} := isClosed_eq continuous_im continuous_const
  have hcl : ∀ z ∈ H, z ∈ closure L ↔ z ∈ closure K := by
    intro z hz
    refine ⟨fun h => ?_, fun h => closure_mono hKL h⟩
    have h' := closure_mono hLK h
    rw [closure_union, hR.closure_eq] at h'
    rcases h' with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hz)
  have hdiff : H \ closure L = H \ closure K := by
    ext z
    exact ⟨fun ⟨hz, hzL⟩ => ⟨hz, fun h => hzL ((hcl z hz).2 h)⟩,
      fun ⟨hz, hzK⟩ => ⟨hz, fun h => hzK ((hcl z hz).1 h)⟩⟩
  ext z
  simp only [fillH, mem_ofPred_eq, hdiff]
  exact ⟨fun ⟨hz, h⟩ => ⟨hz, h.imp_left (hcl z hz).1⟩, fun ⟨hz, h⟩ => ⟨hz, h.imp_left (hcl z hz).2⟩⟩

/-- The joint unbounded domain of two prefixes: the complement in `ℍ` of the filling of their union. -/
def jointDomain (γ₁ : ℝ≥0 → ℂ) (T₁ : ℝ≥0) (γ₂ : ℝ≥0 → ℂ) (T₂ : ℝ≥0) : Set ℂ :=
  H \ fillH (γ₁ '' Icc 0 T₁ ∪ γ₂ '' Icc 0 T₂)

theorem jointDomain_subset_H {γ₁ γ₂ : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0} : jointDomain γ₁ T₁ γ₂ T₂ ⊆ H :=
  sdiff_subset

theorem notMem_jointDomain_left {γ₁ γ₂ : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0} {t : ℝ≥0} (ht : t ≤ T₁) :
    γ₁ t ∉ jointDomain γ₁ T₁ γ₂ T₂ := fun h =>
  h.2 ⟨h.1, Or.inl (subset_closure (Or.inl ⟨t, ⟨zero_le, ht⟩, rfl⟩))⟩

theorem notMem_jointDomain_right {γ₁ γ₂ : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0} {t : ℝ≥0} (ht : t ≤ T₂) :
    γ₂ t ∉ jointDomain γ₁ T₁ γ₂ T₂ := fun h =>
  h.2 ⟨h.1, Or.inl (subset_closure (Or.inr ⟨t, ⟨zero_le, ht⟩, rfl⟩))⟩

/-- **Accessibility in the joint domain.** Every point of the closure of the joint domain of two prefixes from
real seeds starts a continuous injective curve tending to `∞` whose later points lie in the joint domain. -/
theorem exists_tail_of_mem_closure_jointDomain {γ₁ γ₂ : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0}
    (h₁ : ContinuousOn γ₁ (Icc 0 T₁)) (h₂ : ContinuousOn γ₂ (Icc 0 T₂)) (hH₁ : MapsTo γ₁ (Icc 0 T₁) Hbar)
    (hH₂ : MapsTo γ₂ (Icc 0 T₂) Hbar) (h₁0 : (γ₁ 0).im = 0) (h₂0 : (γ₂ 0).im = 0) {p : ℂ}
    (hp : p ∈ closure (jointDomain γ₁ T₁ γ₂ T₂)) :
    ∃ T : ℝ≥0 → ℂ, Continuous T ∧ Function.Injective T ∧ T 0 = p ∧
      (∀ t, 0 < t → T t ∈ jointDomain γ₁ T₁ γ₂ T₂) ∧ Tendsto (fun t => ‖T t‖) atTop atTop := by
  obtain ⟨ζ, hζc, hζH, hζ0, hsub, hsup⟩ := exists_path_union h₁ h₂ hH₁ hH₂ h₁0 h₂0
  have hfill := fillH_eq_of_subset_union_real hsub hsup
  have hJ : jointDomain γ₁ T₁ γ₂ T₂ = H \ fillH (ζ '' Icc 0 1) := by rw [jointDomain, hfill]
  rw [hJ] at hp ⊢
  exact exists_tail_of_mem_closure zero_le_one hζc hζH hζ0 hp

end Supp9B

end InteractingSLE
