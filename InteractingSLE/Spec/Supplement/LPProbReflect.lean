/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPAmalgamate
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Reflection of Loewner chains, generating traces and complete force words

Packet PROVE-R17 (supplement §§5–6, `source/spec/p433-480.md` L921 ff. and `p481-528.md` L1–L215). The
large-parameter reductions repeatedly "reflect" a configuration (LP1: "Reflection gives the
corresponding left-seed assertion"; LP6: "Reflect so that the positions are `0 ≤ x₁ < x₂`"; LP8:
"Reflection proves the other orientation"; LP10: "Reflect to make it the right side"). This file
proves the reflection principle in the form these steps use.

* `reflectC z = −z̄`, an involutive isometry of `ℂ` preserving `ℍ` (`reflectHomeo`).
* `isForwardSol_neg`, `swallowTime_neg`, `fwdHull_neg`: the forward Loewner flow driven by `−W`
  is the reflection of the flow driven by `W`; in particular `K_t(−W) = −\overline{K_t(W)}`.
* `isFilling_reflectC`: the frozen `IsFilling` relation is reflection invariant.
* `isGeneratingTrace_reflect`: if `η` generates the chain of `w` on `[0, T]`, then `−η̄` generates the
  chain of `−w`.
* `IsCompleteForceWord.reflect`, `isCompleteForceWord_reflect_iff`: completeness (continuity up to the
  continuation threshold and transience) of a force word is equivalent to completeness of the
  reflected word `(−xR, −xL, ρR, ρL)`; the evolution-level reflection is
  `IsIntegratedSLEEvolution.reflect` (`Spec/Sec4/RepulsionNoncollision.lean`, reused).
* `IsDistinctForceWord.reflect`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate

universe u

namespace InteractingSLE.LP

/-- The reflection `z ↦ −z̄` of the plane across the imaginary axis. -/
def reflectC (z : ℂ) : ℂ := -conj z

@[simp] theorem reflectC_reflectC (z : ℂ) : reflectC (reflectC z) = z := by
  simp [reflectC]

@[simp] theorem im_reflectC (z : ℂ) : (reflectC z).im = z.im := by simp [reflectC]

@[simp] theorem norm_reflectC (z : ℂ) : ‖reflectC z‖ = ‖z‖ := by simp [reflectC]

theorem continuous_reflectC : Continuous reflectC := Complex.continuous_conj.neg

/-- The reflection as an involutive homeomorphism. -/
def reflectHomeo : ℂ ≃ₜ ℂ where
  toFun := reflectC
  invFun := reflectC
  left_inv := reflectC_reflectC
  right_inv := reflectC_reflectC
  continuous_toFun := continuous_reflectC
  continuous_invFun := continuous_reflectC

theorem coe_reflectHomeo : ⇑reflectHomeo = reflectC := rfl

/-- The reflection of a solution of the centered forward flow driven by `W` started at `z` solves
the flow driven by `−W` started at `−z̄`. -/
theorem isForwardSol_neg {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (h : QuantumZipper.IsForwardSol W z T u) :
    QuantumZipper.IsForwardSol (-W) (reflectC z) T (fun t => reflectC (u t)) := by
  refine ⟨continuous_reflectC.comp_continuousOn h.1, fun t ht => ⟨?_, ?_⟩⟩
  · simpa [reflectC] using (h.2 t ht).1
  · have he := (h.2 t ht).2
    have hi : (∫ s in (0 : ℝ)..t, 2 / reflectC (u s)) = -conj (∫ s in (0 : ℝ)..t, 2 / u s) := by
      rw [← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_neg]
      congr 1; ext s
      have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
      simp only [reflectC, div_neg, map_div₀, h2]
    show reflectC (u t) = _
    rw [hi, he]
    simp only [reflectC, Pi.neg_apply, map_add, map_sub, Complex.conj_ofReal,
      Complex.ofReal_neg]
    ring

/-- Swallowing times are reflection invariant. -/
theorem swallowTime_neg (W : ℝ → ℝ) (z : ℂ) :
    QuantumZipper.swallowTime (-W) (reflectC z) = QuantumZipper.swallowTime W z := by
  have key : ∀ (W : ℝ → ℝ) (z : ℂ), QuantumZipper.swallowTime W z ≤
      QuantumZipper.swallowTime (-W) (reflectC z) := by
    intro W z
    unfold QuantumZipper.swallowTime
    apply sSup_le_sSup
    rintro _ ⟨T, ⟨hT, u, hu⟩, rfl⟩
    exact ⟨T, ⟨hT, _, isForwardSol_neg hu⟩, rfl⟩
  refine le_antisymm ?_ (key W z)
  simpa using key (-W) (reflectC z)

/-- The hull of `−W` is the reflection of the hull of `W`. -/
theorem fwdHull_neg (W : ℝ → ℝ) (T : ℝ) :
    QuantumZipper.fwdHull (-W) T = reflectC '' QuantumZipper.fwdHull W T := by
  ext z
  simp only [QuantumZipper.fwdHull, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨hz, hs⟩
    refine ⟨reflectC z, ⟨?_, ?_⟩, reflectC_reflectC z⟩
    · simpa [QuantumZipper.H] using hz
    · rw [← swallowTime_neg, reflectC_reflectC]; exact hs
  · rintro ⟨y, ⟨hy, hs⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [QuantumZipper.H] using hy
    · rw [swallowTime_neg]; exact hs


theorem isometry_reflectC : Isometry reflectC := isometry_neg.comp Complex.isometry_conj

theorem reflectC_mem_H_iff {z : ℂ} : reflectC z ∈ QuantumZipper.H ↔ z ∈ QuantumZipper.H := by
  simp [QuantumZipper.H]

theorem reflectC_image_eq_preimage (S : Set ℂ) : reflectC '' S = reflectC ⁻¹' S := by
  ext z; constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hz; exact ⟨reflectC z, hz, reflectC_reflectC z⟩

theorem H_diff_reflectC_image (S : Set ℂ) :
    QuantumZipper.H \ reflectC '' S = reflectC '' (QuantumZipper.H \ S) := by
  rw [reflectC_image_eq_preimage, reflectC_image_eq_preimage]
  ext z; simp [reflectC_mem_H_iff]

theorem isBounded_reflectC_image_iff {S : Set ℂ} :
    Bornology.IsBounded (reflectC '' S) ↔ Bornology.IsBounded S := by
  constructor
  · intro h
    have := isometry_reflectC.lipschitzWith.isBounded_image h
    rwa [← image_comp, show reflectC ∘ reflectC = id from funext reflectC_reflectC,
      image_id] at this
  · exact isometry_reflectC.lipschitzWith.isBounded_image

/-- A filling pair reflects to a filling pair. -/
theorem isFilling_reflectC {K A : Set ℂ} (h : IsFilling K A) :
    IsFilling (reflectC '' K) (reflectC '' A) := by
  obtain ⟨⟨z, hz, hcc⟩, hub⟩ := h
  have hzA : z ∈ QuantumZipper.H \ A := by
    have : z ∈ connectedComponentIn (QuantumZipper.H \ A) z := hcc ▸ hz
    exact connectedComponentIn_subset _ _ this
  refine ⟨⟨reflectC z, ?_, ?_⟩, ?_⟩
  · rw [H_diff_reflectC_image]; exact mem_image_of_mem _ hz
  · rw [H_diff_reflectC_image, H_diff_reflectC_image]
    have := reflectHomeo.image_connectedComponentIn hzA
    rw [coe_reflectHomeo] at this
    rw [← this, hcc]
  · rw [H_diff_reflectC_image, isBounded_reflectC_image_iff]; exact hub

/-- **Reflection of a generating trace**: if `η` generates the Loewner chain of `w` on `[0, T]`,
then `−η̄` generates the chain of `−w`. -/
theorem isGeneratingTrace_reflect {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (h : IsGeneratingTrace w T η) : IsGeneratingTrace (-w) T (fun t => reflectC (η t)) := by
  obtain ⟨h0, hc, hf⟩ := h
  refine ⟨by simp [h0, reflectC], continuous_reflectC.comp_continuousOn hc, fun t ht => ?_⟩
  have e : (fun s : ℝ => (-w) s.toNNReal) = -(fun s : ℝ => w s.toNNReal) := rfl
  rw [e, fwdHull_neg, show (fun t => reflectC (η t)) = reflectC ∘ η from rfl, image_comp]
  exact isFilling_reflectC (hf t ht)



/-- **Reflection of a complete force word**: if every evolution of `(xL, xR, ρL, ρR)` has a
transient generating trace, so does every evolution of the reflected word
`(−xR, −xL, ρR, ρL)` ("Reflection gives the corresponding left-seed assertion", LP1; "Reflection
proves the other orientation", LP8). -/
theorem IsCompleteForceWord.reflect {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h : IsCompleteForceWord.{u} a xL xR ρL ρR) :
    IsCompleteForceWord.{u} a (-xR) (-xL) ρR ρL := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hE' := hE.reflect
  rw [neg_neg, neg_neg] at hE'
  filter_upwards [h P 𝓕 (-W) _ _ (-B) ζ hE'] with ω ⟨η, hη, htr⟩
  refine ⟨fun t => reflectC (η t), ?_, fun hz => ?_⟩
  · have := isGeneratingTrace_reflect hη
    have e : (-fun t => (-W) t ω) = fun t => W t ω := by ext t; simp
    rwa [e] at this
  · simpa only [norm_reflectC] using htr hz

/-- `IsCompleteForceWord` is invariant under reflection. -/
theorem isCompleteForceWord_reflect_iff {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} :
    IsCompleteForceWord.{u} a (-xR) (-xL) ρR ρL ↔ IsCompleteForceWord.{u} a xL xR ρL ρR := by
  refine ⟨fun h => ?_, fun h => IsCompleteForceWord.reflect h⟩
  have h' : IsCompleteForceWord.{u} a (-(-xL)) (-(-xR)) ρL ρR := IsCompleteForceWord.reflect h
  rwa [neg_neg, neg_neg] at h'

/-- The reflected word of a word with distinct positions has distinct positions. -/
theorem IsDistinctForceWord.reflect {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (h : IsDistinctForceWord xL xR) : IsDistinctForceWord (-xR) (-xL) := by
  obtain ⟨⟨hL, hL0, hR, hR0⟩, hanti, hmono⟩ := h
  refine ⟨⟨fun i i' hii => neg_le_neg (hR hii), fun i => neg_nonpos.2 (hR0 i),
    fun i i' hii => neg_le_neg (hL hii), fun i => neg_nonneg.2 (hL0 i)⟩,
    fun i i' hii => neg_lt_neg (hmono hii), fun i i' hii => neg_lt_neg (hanti hii)⟩

end InteractingSLE.LP
