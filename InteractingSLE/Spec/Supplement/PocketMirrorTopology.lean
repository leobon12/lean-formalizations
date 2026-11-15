/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketCompassGap

/-!
# Reflection of a disc pocket and its boundary coordinate

PROVE-POCKETSHAPE. Conjugation swaps the two sides of a disc crosscut.
Reflecting both the source and target of a two-point uniformizer preserves
holomorphicity and reverses its real boundary values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology Metric Function
open QuantumZipper (H Hbar)
open scoped ComplexConjugate

namespace InteractingSLE.Theorem14.PocketMirror

open WangWu Sec7.PocketJordan

/-- Conjugation preserves boundedness. -/
theorem isBounded_conj_image_iff {S : Set ℂ} : IsBounded (conj '' S) ↔ IsBounded S := by
  refine ⟨fun h => ?_, fun h => isometry_conj.lipschitzWith.isBounded_image h⟩
  have h' := isometry_conj.lipschitzWith.isBounded_image h
  simpa only [image_image, conj_conj, image_id'] using h'

/-- The closure identity for conjugation, with its function coercion explicit. -/
theorem conj_image_closure (S : Set ℂ) : conj '' closure S = closure (conj '' S) :=
  conjCLE.toHomeomorph.image_closure S

/-- Bounded complementary components, hence Jordan interiors, commute with conjugation. -/
theorem mem_jordanIn_conj_image {J : Set ℂ} {z : ℂ} :
    conj z ∈ jordanIn (conj '' J) ↔ z ∈ jordanIn J := by
  have hcomp : ∀ (U : Set ℂ) (w : ℂ),
      IsBounded (connectedComponentIn (conj '' U) (conj w)) ↔ IsBounded (connectedComponentIn U w) := by
    intro U w
    by_cases hw : w ∈ U
    · have he := conjCLE.toHomeomorph.image_connectedComponentIn hw
      change conj '' connectedComponentIn U w = connectedComponentIn (conj '' U) (conj w) at he
      rw [← he, isBounded_conj_image_iff]
    · have hw' : conj w ∉ conj '' U := fun ⟨v, hv, he⟩ => hw (conjCLE.injective he ▸ hv)
      rw [connectedComponentIn_eq_empty hw, connectedComponentIn_eq_empty hw']
  have hcompl : conj '' Jᶜ = (conj '' J)ᶜ := conjCLE.toHomeomorph.toEquiv.image_compl J
  have hi : Injective (conj : ℂ → ℂ) := conjCLE.injective
  simp only [jordanIn, mem_ofPred_eq, ← hcompl, hcomp, hi.mem_set_image]

/-- Reflect a disc crosscut across the real diameter. -/
theorem isDiscCrosscut_conj {α : ℝ → ℂ} (hα : IsDiscCrosscut α) : IsDiscCrosscut (conj ∘ α) := by
  refine ⟨continuous_conj.comp_continuousOn hα.cont, conjCLE.injective.injOn.comp hα.inj (mapsTo_univ _ _),
    ?_, ?_, ?_⟩
  · simp only [comp_apply, hα.zero, map_neg, map_one]
  · simp only [comp_apply, hα.one, map_one]
  · intro t ht
    simpa only [comp_apply, mem_ball, dist_zero_right, norm_conj] using hα.mem_disc t ht

/-- The lower semicircle reflects to the upper semicircle. -/
theorem conj_image_semiArc_neg : conj '' semiArc (-1) = semiArc 1 := by
  apply Subset.antisymm
  · rintro _ ⟨w, hw, rfl⟩
    simpa only [semiArc, mem_ofPred_eq, norm_conj, conj_im, one_mul, neg_one_mul] using hw
  · intro w hw
    refine ⟨conj w, ?_, conj_conj w⟩
    simpa only [semiArc, mem_ofPred_eq, norm_conj, conj_im, one_mul, neg_one_mul, neg_neg] using hw

/-- Conjugation exchanges the lower and upper sides of the reflected crosscut. -/
theorem mem_crossSide_conj_upper {α : ℝ → ℂ} {z : ℂ} :
    conj z ∈ crossSide (conj ∘ α) 1 ↔ z ∈ crossSide α (-1) := by
  change conj z ∈ jordanIn ((conj ∘ α) '' Icc 0 1 ∪ semiArc 1) ↔ _
  rw [image_comp, ← conj_image_semiArc_neg, ← image_union, mem_jordanIn_conj_image]
  rfl

/-- Reflect a half-plane-valued coordinate with the same two marked parameters. -/
def mirrorUniformizer (Ψ : ℂ → ℂ) (z : ℂ) : ℂ := -conj (Ψ (conj z))

/-- A two-point boundary uniformizer reflects holomorphically with negative real boundary values. -/
theorem isBdryUniformizer_mirror {D : Set ℂ} (hDo : IsOpen D) {p q : ℂ} {Ψ : ℂ → ℂ}
    (hU : IsBdryUniformizer D p q Ψ) :
    IsBdryUniformizer (conj '' D) (conj p) (conj q) (mirrorUniformizer Ψ) := by
  have hmem : ∀ {S : Set ℂ} {z : ℂ}, z ∈ conj '' S ↔ conj z ∈ S := by
    intro S z
    constructor
    · rintro ⟨w, hw, rfl⟩; simpa only [conj_conj] using hw
    · intro hz; exact ⟨conj z, hz, conj_conj z⟩
  have hE : ∀ {z : ℂ}, z ∈ closure (conj '' D) \ {conj q} → conj z ∈ closure D \ {q} := by
    intro z hz
    rw [← conj_image_closure] at hz
    exact ⟨hmem.1 hz.1, fun he => hz.2 (by rw [← conj_conj z, he]; exact mem_singleton _)⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hd := (hU.conf.1.differentiableAt (hDo.mem_nhds (hmem.1 hz))).conj_conj
    rw [conj_conj] at hd
    exact hd.neg.differentiableWithinAt
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      change 0 < (-conj (Ψ (conj z))).im
      simpa only [neg_im, conj_im, neg_neg] using (show 0 < (Ψ (conj z)).im from hU.conf.2.mapsTo (hmem.1 hz))
    · intro z hz w hw he
      exact conjCLE.injective (hU.conf.2.injOn (hmem.1 hz) (hmem.1 hw)
        (conjCLE.injective (neg_injective he)))
    · intro w hw
      have hwH : -conj w ∈ H := by
        change 0 < (-conj w).im
        simpa only [neg_im, conj_im, neg_neg] using (show 0 < w.im from hw)
      obtain ⟨z, hz, he⟩ := hU.conf.2.surjOn hwH
      refine ⟨conj z, ⟨z, hz, rfl⟩, ?_⟩
      simp only [mirrorUniformizer, conj_conj, he, map_neg, neg_neg]
  · exact (continuous_conj.comp_continuousOn (hU.cont.comp continuous_conj.continuousOn (fun _ hz => hE hz))).neg
  · intro z hz w hw he
    exact conjCLE.injective (hU.inj (hE hz) (hE hw) (conjCLE.injective (neg_injective he)))
  · intro z hz
    change 0 ≤ (-conj (Ψ (conj z))).im
    simpa only [neg_im, conj_im, neg_neg] using (show 0 ≤ (Ψ (conj z)).im from hU.mapsTo (hE hz))
  · simp only [mirrorUniformizer, conj_conj, hU.zero, map_zero, neg_zero]
  · have ht : Tendsto conj (𝓝[closure (conj '' D) \ {conj q}] (conj q))
        (𝓝[closure D \ {q}] q) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun _ hz => hE hz⟩
      simpa only [conj_conj] using continuous_conj.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[closure (conj '' D) \ {conj q}] (conj q) ≤ 𝓝 (conj q))
    have he : (fun w => ‖mirrorUniformizer Ψ w‖) = fun w => ‖Ψ (conj w)‖ := by
      funext w
      rw [mirrorUniformizer, norm_neg, norm_conj]
    rw [he]
    exact hU.tendsto.comp ht

end InteractingSLE.Theorem14.PocketMirror
