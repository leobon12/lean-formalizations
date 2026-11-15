/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.HullKernel
import InteractingSLE.Foundations.Complex.RiemannMap
import InteractingSLE.Spec.Sec7.Lemma71EMobius

/-!
# Pathwise facts for the two-point normalized pocket chart

Packet PROVE-LEMMA71E. Deterministic inputs of the measurable pocket chart (`Lemma71EChart.lean`), for a simply
connected domain `D` with a conformal map `ψ₁ : D → ℍ` that tends to `0` along a sequence `z m` and to `∞` along a
sequence `w m` of points of `D` (the two marked boundary points `x₀`, `y₀` of the pocket, Specification §7.1,
"`ψ : C → ℍ` … sends `x₀` to `0` and `y₀` to `∞`").

* **Uniqueness up to scaling** (`exists_pos_eqOn_mul_of_tendsto`): two such maps differ by a positive factor
  (the argument of QuantumZipper's `normalizedUniformizer_unique`, with sequences in place of the filters at `0` and
  `∞`: `ψ₂ ∘ ψ₁⁻¹` is a real Möbius map `(aw + b)/(cw + d)`; the limit along `z m` forces `b = 0`, the limit along
  `w m` forces `c = 0`).
* **Boundary values of a disc chart** (`exists_tendsto_disc_of_tendsto`): any conformal `Φ : D → 𝔻` has limits
  `p ≠ q` on the unit circle along the two sequences (`Φ ∘ ψ₁⁻¹ ∘ cayleyInv` is a disc automorphism
  `u · (ζ − b)/(1 − b̄ζ)`, continuous on the closed disc, injective on the circle).
* `IsDerivLog.congr_of_eqOn`: derivative lifts transfer along maps that agree on an open set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function
open scoped ComplexConjugate
open QuantumZipper (H)
open QuantumZipper.CA (cayley cayleyInv diskMobius realMobius)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.Lemma71E

/-- Derivative lifts transfer along maps and logarithms that agree on an open set. -/
theorem IsDerivLog.congr_of_eqOn {ψ ψ' L L' : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D) (h : IsDerivLog ψ L D)
    (hψ : EqOn ψ ψ' D) (hL : EqOn L L' D) : IsDerivLog ψ' L' D := by
  refine ⟨h.1.congr hL.symm, fun z hz => ?_⟩
  have hev : ψ =ᶠ[𝓝 z] ψ' := Filter.eventuallyEq_of_mem (hDo.mem_nhds hz) hψ
  rw [← hev.deriv_eq, ← hL hz]
  exact h.2 z hz

/-- **Two conformal maps of `D` onto `ℍ` with the same two-sequence normalization differ by a positive factor.** -/
theorem exists_pos_eqOn_mul_of_tendsto {D : Set ℂ} (hDo : IsOpen D) {φ₁ φ₂ : ℂ → ℂ}
    (h₁ : IsConformalBijection φ₁ D H) (h₂ : IsConformalBijection φ₂ D H) {z w : ℕ → ℂ}
    (hz : ∀ m, z m ∈ D) (hw : ∀ m, w m ∈ D) (h0₁ : Tendsto (fun m => φ₁ (z m)) atTop (𝓝 0))
    (h0₂ : Tendsto (fun m => φ₂ (z m)) atTop (𝓝 0)) (hi₁ : Tendsto (fun m => ‖φ₁ (w m)‖) atTop atTop)
    (hi₂ : Tendsto (fun m => ‖φ₂ (w m)‖) atTop atTop) :
    ∃ a : ℝ, 0 < a ∧ EqOn φ₂ (fun x => (a : ℂ) * φ₁ x) D := by
  have hinv := isConformalBijection_invFunOn hDo h₁
  have hχ := isConformalBijection_comp h₂ hinv
  obtain ⟨a, b, c, d, hdet, hEq⟩ := QuantumZipper.CA.exists_realMobius_of_bijOn_H hχ.1 hχ.2
  have hkey : ∀ x ∈ D, φ₂ x = realMobius a b c d (φ₁ x) := fun x hx => by
    rw [← hEq (h₁.2.mapsTo hx)]
    simp only [Function.comp_apply, h₁.2.injOn.leftInvOn_invFunOn hx]
  have hden : ∀ x ∈ D, (c : ℂ) * φ₁ x + d ≠ 0 := fun x hx =>
    QuantumZipper.CA.realMobius_denom_ne_zero hdet (h₁.2.mapsTo hx)
  -- `b = 0`
  have hb : b = 0 := by
    have hnum : Tendsto (fun m => (a : ℂ) * φ₁ (z m) + b) atTop (𝓝 ((a : ℂ) * 0 + b)) :=
      (h0₁.const_mul _).add_const _
    have hprod : Tendsto (fun m => φ₂ (z m) * ((c : ℂ) * φ₁ (z m) + d)) atTop
        (𝓝 (0 * ((c : ℂ) * 0 + d))) := h0₂.mul ((h0₁.const_mul _).add_const _)
    have hnum' : Tendsto (fun m => (a : ℂ) * φ₁ (z m) + b) atTop (𝓝 (0 * ((c : ℂ) * 0 + d))) := by
      refine hprod.congr fun m => ?_
      rw [hkey _ (hz m), realMobius, div_mul_cancel₀ _ (hden _ (hz m))]
    have := tendsto_nhds_unique hnum hnum'
    simpa using this
  subst hb
  -- `c = 0`
  have hc : c = 0 := by
    by_contra hc
    have hφ₁inf : Tendsto (fun m => φ₁ (w m)) atTop (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]; exact hi₁
    have hq : Tendsto (fun m => (c : ℂ) + d / φ₁ (w m)) atTop (𝓝 ((c : ℂ) + d * 0)) :=
      ((tendsto_inv₀_cobounded.comp hφ₁inf).const_mul (d : ℂ)).const_add _ |>.congr
        fun m => by simp [div_eq_mul_inv]
    rw [mul_zero, add_zero] at hq
    have hlim : Tendsto (fun m => φ₂ (w m)) atTop (𝓝 ((a : ℂ) / c)) := by
      refine ((tendsto_const_nhds (x := (a : ℂ))).div hq (by exact_mod_cast hc)).congr fun m => ?_
      have hne : φ₁ (w m) ≠ 0 := fun h0 => by
        have := h₁.2.mapsTo (hw m)
        rw [h0] at this
        exact lt_irrefl 0 (show (0 : ℝ) < (0 : ℂ).im from this)
      rw [hkey _ (hw m), realMobius]
      simp only [Complex.ofReal_zero, add_zero, Pi.div_apply]
      rw [show (c : ℂ) + d / φ₁ (w m) = ((c : ℂ) * φ₁ (w m) + d) / φ₁ (w m) by field_simp,
        div_div_eq_mul_div]
    exact not_tendsto_atTop_of_tendsto_nhds hlim.norm hi₂
  subst hc
  have hdet' : 0 < a * d := by simpa using hdet
  have hd : d ≠ 0 := by rintro rfl; simp at hdet'
  refine ⟨a / d, ?_, fun x hx => ?_⟩
  · have : 0 < a * d / (d * d) := div_pos hdet' (mul_self_pos.2 hd)
    rwa [mul_div_mul_right _ _ hd] at this
  · rw [hkey x hx, realMobius]
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    push_cast
    rw [zero_mul, zero_add, add_zero, div_mul_eq_mul_div, mul_comm]

/-- The disc Möbius map is continuous at every point of the closed disc. -/
theorem continuousAt_diskMobius {b ζ : ℂ} (hb : ‖b‖ < 1) (hζ : ‖ζ‖ ≤ 1) : ContinuousAt (diskMobius b) ζ := by
  have : DifferentiableAt ℂ (fun x : ℂ => (x - b) / (1 - conj b * x)) ζ :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) (QuantumZipper.CA.diskMobius_denom_ne_zero hb hζ)
  exact this.continuousAt

theorem norm_diskMobius_of_norm_eq_one {b ζ : ℂ} (hb : ‖b‖ < 1) (hζ : ‖ζ‖ = 1) : ‖diskMobius b ζ‖ = 1 := by
  have h := QuantumZipper.CA.one_sub_sq_norm_diskMobius hb hζ.le
  rw [hζ, one_pow, sub_self, mul_zero, zero_div] at h
  have h2 : ‖diskMobius b ζ‖ ^ 2 = 1 := by linarith
  have h3 := norm_nonneg (diskMobius b ζ)
  nlinarith

theorem cayley_zero : cayley 0 = -1 := by
  simp [cayley]

/-- **Boundary values of a disc chart along the two sequences**: if `ψ₁ : D → ℍ` tends to `0` along `z m` and to
`∞` along `w m`, then any conformal `Φ : D → 𝔻` tends to distinct points `p`, `q` of the unit circle along them. -/
theorem exists_tendsto_disc_of_tendsto {D : Set ℂ} (hDo : IsOpen D) {Φ ψ₁ : ℂ → ℂ}
    (hΦ : IsConformalBijection Φ D (ball 0 1)) (hψ₁ : IsConformalBijection ψ₁ D H) {z w : ℕ → ℂ}
    (hz : ∀ m, z m ∈ D) (hw : ∀ m, w m ∈ D) (h0 : Tendsto (fun m => ψ₁ (z m)) atTop (𝓝 0))
    (hi : Tendsto (fun m => ‖ψ₁ (w m)‖) atTop atTop) :
    ∃ p q : ℂ, ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ p ≠ q ∧ Tendsto (fun m => Φ (z m)) atTop (𝓝 p) ∧
      Tendsto (fun m => Φ (w m)) atTop (𝓝 q) := by
  have hinv := isConformalBijection_invFunOn hDo hψ₁
  have hA := isConformalBijection_comp hΦ (isConformalBijection_comp hinv
    InteractingSLE.isConformalBijection_cayleyInv)
  obtain ⟨u, b, hu, hb, hAeq⟩ := exists_eqOn_mul_diskMobius_of_isConformalBijection hA
  have hb' : ‖b‖ < 1 := mem_ball_zero_iff.1 hb
  -- `Φ = u · diskMobius b ∘ cayley ∘ ψ₁` on `D`
  have hrep : ∀ x ∈ D, Φ x = u * diskMobius b (cayley (ψ₁ x)) := by
    intro x hx
    have hxH : ψ₁ x ∈ H := hψ₁.2.mapsTo hx
    have hc := QuantumZipper.CA.cayley_mem_ball hxH
    have e := hAeq hc
    simp only [Function.comp_apply] at e
    rw [← e]
    rw [QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hxH)),
      hψ₁.2.injOn.leftInvOn_invFunOn hx]
  have hm1 : ‖(-1 : ℂ)‖ = 1 := by simp
  refine ⟨u * diskMobius b (-1), u * diskMobius b 1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_mul, hu, one_mul, norm_diskMobius_of_norm_eq_one hb' hm1]
  · rw [norm_mul, hu, one_mul, norm_diskMobius_of_norm_eq_one hb' norm_one]
  · intro h
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    have h' := mul_left_cancel₀ hu0 h
    have e1 := QuantumZipper.CA.diskMobius_neg_diskMobius hb' hm1.le
    have e2 := QuantumZipper.CA.diskMobius_neg_diskMobius hb' norm_one.le
    rw [h', e2] at e1
    norm_num at e1
  · have hc : Tendsto (fun m => cayley (ψ₁ (z m))) atTop (𝓝 (-1)) := by
      rw [← cayley_zero]
      exact ((QuantumZipper.CA.differentiableAt_cayley (by simp)).continuousAt.tendsto).comp h0
    refine (((continuousAt_diskMobius hb' hm1.le).tendsto.comp hc).const_mul u).congr fun m => ?_
    exact (hrep _ (hz m)).symm
  · have hc : Tendsto (fun m => cayley (ψ₁ (w m))) atTop (𝓝 1) :=
      QuantumZipper.CA.tendsto_cayley_cobounded.comp (tendsto_norm_atTop_iff_cobounded.1 hi)
    refine (((continuousAt_diskMobius hb' norm_one.le).tendsto.comp hc).const_mul u).congr fun m => ?_
    exact (hrep _ (hw m)).symm

end InteractingSLE.Sec7.Lemma71E
