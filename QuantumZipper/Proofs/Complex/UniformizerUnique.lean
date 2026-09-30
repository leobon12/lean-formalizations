/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (CA-H4U, EXT-CA node U6)
-/
import QuantumZipper.Proofs.Complex.UniformizerRight
import QuantumZipper.Proofs.Complex.BasicsAutomorphisms

/-!
# Uniqueness of the normalized uniformizer up to scaling (EXT-CA node U6)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "U", node U6.

* `normalizedUniformizer_unique`: for an open `D` which accumulates at `0` and at `∞`
  (`(𝓝[D] 0).NeBot`, `(cobounded ℂ ⊓ 𝓟 D).NeBot`), two normalized uniformizers of `D` differ by a
  positive factor: `φ₂ = a φ₁` on `D`, `a > 0`.
* `normalizedUniformizer_unique_leftComponent`, `normalizedUniformizer_unique_rightComponent`:
  the case of the two components of a simple chord.

The two accumulation hypotheses are necessary: if, e.g., `0 ∉ closure D`, the condition
`φ → 0` at `0` is vacuous and `φ` can be composed with any automorphism of `ℍ` fixing `∞`.

## Sources

`χ = φ₂ ∘ φ₁⁻¹` is a holomorphic bijection of `ℍ` (A2 for the inverse), hence a real Möbius map
`(a w + b)/(c w + d)` (A6, `exists_realMobius_of_bijOn_H`; Burckel, *Classical Analysis in the
Complex Plane*, Thm 6.2(ii)).  The normalizations force `b = 0` (limit at `0`: the numerator
`a w + b = χ(w)(c w + d) → 0`) and `c = 0` (limit at `∞`: otherwise `χ(w) → a/c`).  Own elementary
argument for these two limits (the blueprint applies A6's `exists_mul_of_bijOn_H_of_tendsto`,
which would need the limits of `χ` along all of `ℍ`, not only along `φ₁(D)`-sequences).
-/

noncomputable section

open Set Metric Filter Bornology
open scoped Topology

namespace QuantumZipper.CA.Uniformizer

/-- **U6.** Two normalized uniformizers of an open `D` accumulating at `0` and `∞` differ by a
positive factor. -/
theorem normalizedUniformizer_unique {D : Set ℂ} (hDo : IsOpen D) (hD0 : (𝓝[D] 0).NeBot)
    (hDinf : (cobounded ℂ ⊓ 𝓟 D).NeBot) {φ₁ φ₂ : ℂ → ℂ}
    (h₁ : IsNormalizedUniformizer D φ₁) (h₂ : IsNormalizedUniformizer D φ₂) :
    ∃ a : ℝ, 0 < a ∧ EqOn φ₂ (fun z => (a : ℂ) * φ₁ z) D := by
  obtain ⟨hb₁, hd₁, h0₁, hi₁⟩ := h₁
  obtain ⟨hb₂, hd₂, h0₂, hi₂⟩ := h₂
  set e := univalentOPH hDo hd₁ hb₁.injOn with he
  have himg : φ₁ '' D = H := hb₁.image_eq
  have hinvOn : InvOn e.symm φ₁ D H :=
    ⟨fun z hz => univalentOPH_symm_apply_apply hDo hd₁ hb₁.injOn hz,
      fun w hw => univalentOPH_apply_symm_apply hDo hd₁ hb₁.injOn (himg ▸ hw)⟩
  have hsymm : BijOn e.symm H D := hb₁.symm hinvOn.symm
  have hχd : DifferentiableOn ℂ (fun w => φ₂ (e.symm w)) H :=
    hd₂.comp (himg ▸ differentiableOn_univalentOPH_symm hDo hd₁ hb₁.injOn) hsymm.mapsTo
  have hχb : BijOn (fun w => φ₂ (e.symm w)) H H := hb₂.comp hsymm
  obtain ⟨a, b, c, d, hdet, hEq⟩ := exists_realMobius_of_bijOn_H hχd hχb
  have hkey : ∀ z ∈ D, φ₂ z = realMobius a b c d (φ₁ z) := fun z hz => by
    rw [← hEq (hb₁.mapsTo hz)]
    simp only [hinvOn.1 hz]
  have hden : ∀ z ∈ D, (c : ℂ) * φ₁ z + d ≠ 0 := fun z hz =>
    realMobius_denom_ne_zero hdet (hb₁.mapsTo hz)
  have hevD0 : ∀ᶠ z in 𝓝[D] 0, z ∈ D := self_mem_nhdsWithin
  have hevDi : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 D, z ∈ D := mem_inf_of_right (mem_principal_self D)
  -- `b = 0`: the numerator `a φ₁ + b = φ₂ · (c φ₁ + d) → 0 · d = 0`
  have hb : b = 0 := by
    have hnum : Tendsto (fun z => (a : ℂ) * φ₁ z + b) (𝓝[D] 0) (𝓝 ((a : ℂ) * 0 + b)) :=
      (h0₁.const_mul _).add_const _
    have hprod : Tendsto (fun z => φ₂ z * ((c : ℂ) * φ₁ z + d)) (𝓝[D] 0)
        (𝓝 (0 * ((c : ℂ) * 0 + d))) := h0₂.mul ((h0₁.const_mul _).add_const _)
    have hnum' : Tendsto (fun z => (a : ℂ) * φ₁ z + b) (𝓝[D] 0) (𝓝 (0 * ((c : ℂ) * 0 + d))) := by
      refine hprod.congr' (hevD0.mono fun z hz => ?_)
      rw [hkey z hz, realMobius, div_mul_cancel₀ _ (hden z hz)]
    have := tendsto_nhds_unique hnum hnum'
    simpa using this
  subst hb
  -- `c = 0`: otherwise `φ₂ = a / (c + d / φ₁) → a / c` at `∞`
  have hc : c = 0 := by
    by_contra hc
    have hφ₁inf : Tendsto φ₁ (cobounded ℂ ⊓ 𝓟 D) (cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]; exact hi₁
    have hq : Tendsto (fun z => (c : ℂ) + d / φ₁ z) (cobounded ℂ ⊓ 𝓟 D) (𝓝 ((c : ℂ) + d * 0)) :=
      ((tendsto_inv₀_cobounded.comp hφ₁inf).const_mul (d : ℂ)).const_add _ |>.congr
        fun z => by simp [div_eq_mul_inv]
    rw [mul_zero, add_zero] at hq
    have hlim : Tendsto φ₂ (cobounded ℂ ⊓ 𝓟 D) (𝓝 ((a : ℂ) / c)) := by
      refine ((tendsto_const_nhds (x := (a : ℂ))).div hq (by exact_mod_cast hc)).congr'
        (hevDi.mono fun z hz => ?_)
      have hne : φ₁ z ≠ 0 := fun h0 => by
        have := hb₁.mapsTo hz
        rw [h0] at this
        exact lt_irrefl 0 (show (0 : ℝ) < (0 : ℂ).im from this)
      rw [hkey z hz, realMobius]
      simp only [Pi.div_apply, Complex.ofReal_zero, add_zero]
      rw [show (c : ℂ) + d / φ₁ z = ((c : ℂ) * φ₁ z + d) / φ₁ z by field_simp,
        div_div_eq_mul_div]
    exact not_tendsto_atTop_of_tendsto_nhds hlim.norm hi₂
  subst hc
  have hdet' : 0 < a * d := by simpa using hdet
  have hd : d ≠ 0 := by rintro rfl; simp at hdet'
  refine ⟨a / d, div_pos hdet' (mul_self_pos.2 hd) |>.trans_eq (by field_simp), fun z hz => ?_⟩
  rw [hkey z hz, realMobius]
  push_cast
  ring

theorem normalizedUniformizer_unique_leftComponent {η : ℝ → ℂ} (hη : IsSimpleChord η)
    {φ₁ φ₂ : ℂ → ℂ} (h₁ : IsNormalizedUniformizer (leftComponent η) φ₁)
    (h₂ : IsNormalizedUniformizer (leftComponent η) φ₂) :
    ∃ a : ℝ, 0 < a ∧ EqOn φ₂ (fun z => (a : ℂ) * φ₁ z) (leftComponent η) :=
  normalizedUniformizer_unique (isOpen_leftComponent hη)
    (mem_closure_iff_nhdsWithin_neBot.1 (zero_mem_closure_leftComponent hη))
    (neBot_cobounded_inf_leftComponent hη) h₁ h₂

theorem normalizedUniformizer_unique_rightComponent {η : ℝ → ℂ} (hη : IsSimpleChord η)
    {φ₁ φ₂ : ℂ → ℂ} (h₁ : IsNormalizedUniformizer (rightComponent η) φ₁)
    (h₂ : IsNormalizedUniformizer (rightComponent η) φ₂) :
    ∃ a : ℝ, 0 < a ∧ EqOn φ₂ (fun z => (a : ℂ) * φ₁ z) (rightComponent η) := by
  have hη' := isSimpleChord_refl_comp hη
  have hpre : rightComponent η = refl ⁻¹' leftComponent (refl ∘ η) := by
    ext z; exact mem_rightComponent_iff
  have hsub : refl '' leftComponent (refl ∘ η) ⊆ rightComponent η := by
    rintro _ ⟨w, hw, rfl⟩; exact refl_mem_right_of_mem_left hw
  refine normalizedUniformizer_unique ?_ ?_ ?_ h₁ h₂
  · rw [hpre]; exact (isOpen_leftComponent hη').preimage continuous_refl
  · refine mem_closure_iff_nhdsWithin_neBot.1 (closure_mono hsub ?_)
    have := mem_closure_image continuous_refl.continuousAt (zero_mem_closure_leftComponent hη')
    simpa [refl] using this
  · have hL := neBot_cobounded_inf_leftComponent hη'
    rw [inf_principal_neBot_iff] at hL ⊢
    intro U hU
    have hrefl : Tendsto refl (cobounded ℂ) (cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa using tendsto_norm_cobounded_atTop
    obtain ⟨z, hzU, hzL⟩ := hL _ (hrefl hU)
    exact ⟨refl z, hzU, hsub ⟨z, hzL, rfl⟩⟩

end QuantumZipper.CA.Uniformizer
