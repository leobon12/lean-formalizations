/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (CA-H4U, EXT-CA node U5)
-/
import QuantumZipper.Proofs.Complex.UniformizerNormalize
import QuantumZipper.Blueprint.External
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The right component by reflection; `RiemannMappingCaratheodory` (EXT-CA node U5)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "U", node U5.  With the reflection
`refl z = -conj z` of `ℍ` in the imaginary axis:

* `isSimpleChord_refl_comp`: `refl ∘ η` is again a simple chord;
* `mem_rightComponent_iff`: `z ∈ rightComponent η ↔ refl z ∈ leftComponent (refl ∘ η)`;
* `exists_normalizedUniformizer_rightComponent`: `refl ∘ φ ∘ refl` is a normalized uniformizer of
  `rightComponent η` when `φ` is one of `leftComponent (refl ∘ η)` (U4);
* `riemannMappingCaratheodory : Blueprint.RiemannMappingCaratheodory` (Theorem 1.8 input).

## Sources

The blueprint's U5 sketch; elementary (own proof).  The holomorphy of `conj ∘ f ∘ conj` is
mathlib's `DifferentiableAt.conj_conj`.
-/

noncomputable section

open Set Metric Filter Bornology
open scoped Topology ComplexConjugate

namespace QuantumZipper.CA.Uniformizer

/-- The reflection `z ↦ -conj z` in the imaginary axis. -/
def refl (z : ℂ) : ℂ := -conj z

@[simp] theorem refl_refl (z : ℂ) : refl (refl z) = z := by simp [refl]

@[simp] theorem refl_im (z : ℂ) : (refl z).im = z.im := by simp [refl]

@[simp] theorem norm_refl (z : ℂ) : ‖refl z‖ = ‖z‖ := by simp [refl]

theorem refl_ofReal (x : ℝ) : refl (x : ℂ) = ((-x : ℝ) : ℂ) := by simp [refl]

theorem refl_injective : Function.Injective refl := fun z w h => by
  rw [← refl_refl z, h, refl_refl]

theorem continuous_refl : Continuous refl := (Complex.continuous_conj).neg

theorem refl_mem_H_iff {z : ℂ} : refl z ∈ H ↔ z ∈ H := by
  show 0 < (refl z).im ↔ 0 < z.im
  rw [refl_im]

theorem isSimpleChord_refl_comp {η : ℝ → ℂ} (hη : IsSimpleChord η) : IsSimpleChord (refl ∘ η) :=
  ⟨by simp [refl, hη.1], continuous_refl.comp_continuousOn hη.2.1,
    refl_injective.comp_injOn hη.2.2.1, fun t ht => refl_mem_H_iff.2 (hη.2.2.2.1 t ht),
    by simpa [Function.comp_def] using hη.2.2.2.2⟩

theorem refl_mem_slit_iff {η : ℝ → ℂ} {w : ℂ} :
    refl w ∈ H \ (refl ∘ η) '' Ici (0 : ℝ) ↔ w ∈ H \ η '' Ici (0 : ℝ) := by
  have himg : refl w ∈ (refl ∘ η) '' Ici (0 : ℝ) ↔ w ∈ η '' Ici (0 : ℝ) := by
    rw [image_comp]
    exact refl_injective.mem_set_image
  simp only [mem_diff, refl_mem_H_iff, himg]

/-- Transport of the defining paths by the reflection (one direction). -/
theorem refl_mem_left_of_mem_right {η : ℝ → ℂ} {z : ℂ} (hz : z ∈ rightComponent η) :
    refl z ∈ leftComponent (refl ∘ η) := by
  obtain ⟨hzΩ, x, hx, p, hp⟩ := hz
  refine ⟨refl_mem_slit_iff.2 hzΩ, -x, by linarith,
    (p.map continuous_refl).cast rfl (refl_ofReal x).symm, fun t ht => ?_⟩
  exact refl_mem_slit_iff.2 (hp t ht)

/-- Transport of the defining paths by the reflection (other direction). -/
theorem refl_mem_right_of_mem_left {η : ℝ → ℂ} {z : ℂ} (hz : z ∈ leftComponent (refl ∘ η)) :
    refl z ∈ rightComponent η := by
  obtain ⟨hzΩ, x, hx, p, hp⟩ := hz
  have hΩ : ∀ w, w ∈ H \ (refl ∘ η) '' Ici (0 : ℝ) → refl w ∈ H \ η '' Ici (0 : ℝ) :=
    fun w hw => refl_mem_slit_iff.1 (by rwa [refl_refl])
  refine ⟨hΩ z hzΩ, -x, by linarith,
    (p.map continuous_refl).cast rfl (refl_ofReal x).symm, fun t ht => ?_⟩
  exact hΩ _ (hp t ht)

theorem mem_rightComponent_iff {η : ℝ → ℂ} {z : ℂ} :
    z ∈ rightComponent η ↔ refl z ∈ leftComponent (refl ∘ η) :=
  ⟨refl_mem_left_of_mem_right, fun h => by simpa using refl_mem_right_of_mem_left h⟩

theorem bijOn_refl_right (η : ℝ → ℂ) :
    BijOn refl (rightComponent η) (leftComponent (refl ∘ η)) :=
  ⟨fun _ hz => refl_mem_left_of_mem_right hz, refl_injective.injOn,
    fun w hw => ⟨refl w, refl_mem_right_of_mem_left hw, refl_refl w⟩⟩

theorem bijOn_refl_H : BijOn refl H H :=
  ⟨fun _ hz => refl_mem_H_iff.2 hz, refl_injective.injOn,
    fun w hw => ⟨refl w, refl_mem_H_iff.2 hw, refl_refl w⟩⟩

theorem differentiableAt_refl_comp_refl {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (refl z)) : DifferentiableAt ℂ (fun w => refl (f (refl w))) z := by
  have hg : DifferentiableAt ℂ (fun u => f (-u)) (conj z) := by
    have : DifferentiableAt ℂ (fun u : ℂ => -u) (conj z) := differentiableAt_id.neg
    exact hf.comp (conj z) this
  have h := hg.conj_conj
  rw [Complex.conj_conj] at h
  have heq : (fun w => refl (f (refl w)))
      = fun w => -((conj ∘ (fun u => f (-u)) ∘ conj) w) := by
    funext w
    simp [refl]
  rw [heq]
  exact h.neg

/-- **U5 (right component).** -/
theorem exists_normalizedUniformizer_rightComponent {η : ℝ → ℂ} (hη : IsSimpleChord η) :
    ∃ φ, IsNormalizedUniformizer (rightComponent η) φ := by
  have hη' := isSimpleChord_refl_comp hη
  obtain ⟨φ, hφb, hφd, hφ0, hφinf⟩ := exists_normalizedUniformizer_leftComponent hη'
  have hDo := isOpen_leftComponent hη'
  refine ⟨fun z => refl (φ (refl z)), bijOn_refl_H.comp (hφb.comp (bijOn_refl_right η)),
    fun z hz => ?_, ?_, ?_⟩
  · have hz' := refl_mem_left_of_mem_right hz
    exact (differentiableAt_refl_comp_refl
      (hφd.differentiableAt (hDo.mem_nhds hz'))).differentiableWithinAt
  · have h1 : Tendsto refl (𝓝[rightComponent η] 0) (𝓝[leftComponent (refl ∘ η)] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun z hz =>
        refl_mem_left_of_mem_right hz⟩
      have := (continuous_refl.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := rightComponent η))
      simpa [refl] using this
    have h2 := (continuous_refl.tendsto 0).comp (hφ0.comp h1)
    simpa [refl, Function.comp_def] using h2
  · have h1 : Tendsto refl (cobounded ℂ ⊓ 𝓟 (rightComponent η))
        (cobounded ℂ ⊓ 𝓟 (leftComponent (refl ∘ η))) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_inf_principal.2
        (Eventually.of_forall fun z hz => refl_mem_left_of_mem_right hz))⟩
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa using tendsto_norm_cobounded_atTop.mono_left
        (inf_le_left : cobounded ℂ ⊓ 𝓟 (rightComponent η) ≤ cobounded ℂ)
    simpa [Function.comp_def] using hφinf.comp h1

/-- **U5 / Theorem 1.8 input.** The Riemann mapping theorem with Carathéodory's boundary
normalization for both complementary components of a simple chord. -/
theorem riemannMappingCaratheodory : Blueprint.RiemannMappingCaratheodory := fun _η hη =>
  ⟨exists_normalizedUniformizer_leftComponent hη, exists_normalizedUniformizer_rightComponent hη⟩

end QuantumZipper.CA.Uniformizer
