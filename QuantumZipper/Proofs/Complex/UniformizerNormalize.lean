/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (CA-H4U, EXT-CA node U4, normalization)
-/
import QuantumZipper.Proofs.Complex.UniformizerLimits

/-!
# The normalized uniformizer of the left component (EXT-CA node U4)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "U", node U4.

`exists_normalizedUniformizer_leftComponent`: for a simple chord `η`, `leftComponent η` has a
normalized conformal uniformizer onto `ℍ` (`IsNormalizedUniformizer`).

Construction: `φ₀ : D → ℍ` is the inverse of the conformal map of U3; by
`exists_boundary_limits`, `cayley ∘ φ₀` tends to distinct points `ζ₀` (at `0`) and `ζ∞` (at `∞`)
of the unit circle.  With `c = conj ζ∞` (so `c ζ∞ = 1`) and `ζ' = c ζ₀ ≠ 1`, the real number
`x' = cayleyInv ζ'` and the automorphism `z ↦ cayleyInv (c · cayley z) - x'` of `ℍ` (a rotation of
the disk conjugated by the Cayley map, followed by a real translation) send the two limits to `0`
and `∞`, so `φ z = cayleyInv (c · cayley (φ₀ z)) - x'` is normalized.

## Sources

The blueprint's U4 sketch ("precompose with the automorphism of `ℍ` sending `0 ↦ ζ₀`,
`∞ ↦ ζ∞`"); the automorphism is written explicitly (own elementary construction).
-/

noncomputable section

open Set Metric Filter Bornology
open scoped Topology ComplexConjugate

namespace QuantumZipper.CA.Uniformizer

variable {η : ℝ → ℂ}

theorem bijOn_cayleyInv_ball : BijOn cayleyInv (ball (0 : ℂ) 1) H :=
  bijOn_cayley_H.symm ⟨fun w hw => cayley_cayleyInv (ne_one_of_mem_unitBall hw),
    fun z hz => cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hz))⟩

theorem bijOn_mul_ball {c : ℂ} (hc : ‖c‖ = 1) :
    BijOn (fun w => c * w) (ball (0 : ℂ) 1) (ball 0 1) := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  refine ⟨fun w hw => ?_, fun w _ v _ h => mul_left_cancel₀ hc0 h, fun w hw => ⟨c⁻¹ * w, ?_, ?_⟩⟩
  · rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_mul, hc, one_mul]
    exact hw
  · rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_mul, norm_inv, hc, inv_one, one_mul]
    exact hw
  · show c * (c⁻¹ * w) = w
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

theorem bijOn_sub_real (x : ℝ) : BijOn (fun z : ℂ => z - x) H H := by
  refine ⟨fun z hz => ?_, fun z _ w _ h => sub_left_inj.1 h, fun z hz => ⟨z + x, ?_, by simp⟩⟩
  · have : 0 < z.im := hz
    show 0 < (z - x).im
    simpa using this
  · have : 0 < z.im := hz
    show 0 < (z + x).im
    simpa using this

/-- **U4.** The left component of a simple chord has a normalized conformal uniformizer. -/
theorem exists_normalizedUniformizer_leftComponent (hη : IsSimpleChord η) :
    ∃ φ, IsNormalizedUniformizer (leftComponent η) φ := by
  obtain ⟨ψ, hψb, hψd, φ₀, hφb, hφd, -, hinv⟩ := exists_conformal_H_leftComponent hη
  obtain ⟨ζ₀, ζi, h0n, hin, hne, hl0, hli⟩ :=
    exists_boundary_limits hη hψb hψd hφb.mapsTo hinv
  set c : ℂ := conj ζi with hcdef
  have hc : ‖c‖ = 1 := by rw [hcdef, Complex.norm_conj, hin]
  have hci : c * ζi = 1 := by
    rw [hcdef, Complex.conj_mul', hin]
    simp
  set ζ' : ℂ := c * ζ₀ with hζ'def
  have hζ'1 : ζ' ≠ 1 := by
    intro h
    apply hne
    have : ζi * ζ' = ζi := by rw [h, mul_one]
    rw [hζ'def, show ζi * (c * ζ₀) = (c * ζi) * ζ₀ by ring, hci, one_mul] at this
    exact this
  have hζ'n : ‖ζ'‖ = 1 := by rw [hζ'def, norm_mul, hc, h0n, one_mul]
  set x' : ℝ := (cayleyInv ζ').re with hx'def
  have hx' : ((x' : ℝ) : ℂ) = cayleyInv ζ' := cayleyInv_real_of_norm_eq_one hζ'n
  have hDo := isOpen_leftComponent hη
  have hmemb : ∀ z ∈ leftComponent η, c * cayley (φ₀ z) ∈ ball (0 : ℂ) 1 := fun z hz =>
    (bijOn_mul_ball hc).mapsTo (cayley_mem_ball (hφb.mapsTo hz))
  refine ⟨fun z => cayleyInv (c * cayley (φ₀ z)) - x', ?_, ?_, ?_, ?_⟩
  · exact (bijOn_sub_real x').comp (bijOn_cayleyInv_ball.comp
      ((bijOn_mul_ball hc).comp (bijOn_cayley_H.comp hφb)))
  · intro z hz
    have hH := hφb.mapsTo hz
    have h1 : DifferentiableAt ℂ (fun z => c * cayley (φ₀ z)) z :=
      ((differentiableAt_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hH))).comp z
        (hφd.differentiableAt (hDo.mem_nhds hz))).const_mul c
    exact (((differentiableAt_cayleyInv (ne_one_of_mem_unitBall (hmemb z hz))).comp z
      h1).sub_const _).differentiableWithinAt
  · have h1 : Tendsto (fun z => c * cayley (φ₀ z)) (𝓝[leftComponent η] 0) (𝓝 ζ') :=
      hl0.const_mul c
    have h2 := (((continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hζ'1)).tendsto).comp
      h1).sub_const (x' : ℂ)
    have h0 : cayleyInv ζ' - (x' : ℂ) = 0 := by rw [hx', sub_self]
    rw [h0] at h2
    exact h2
  · have h1 : Tendsto (fun z => c * cayley (φ₀ z)) (cobounded ℂ ⊓ 𝓟 (leftComponent η))
        (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨by rw [← hci]; exact hli.const_mul c, ?_⟩
      exact eventually_inf_principal.2 (Eventually.of_forall fun z hz =>
        ne_one_of_mem_unitBall (hmemb z hz))
    have h2 : Tendsto (fun z => ‖cayleyInv (c * cayley (φ₀ z))‖)
        (cobounded ℂ ⊓ 𝓟 (leftComponent η)) atTop :=
      tendsto_norm_cobounded_atTop.comp (tendsto_cayleyInv_nhdsNE_one.comp h1)
    refine tendsto_atTop_mono (fun z => ?_) (tendsto_atTop_add_const_right _ (-‖(x' : ℂ)‖) h2)
    have := norm_sub_norm_le (cayleyInv (c * cayley (φ₀ z))) (x' : ℂ)
    linarith

end QuantumZipper.CA.Uniformizer
