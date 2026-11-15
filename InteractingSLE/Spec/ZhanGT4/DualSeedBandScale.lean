/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandIntegral

/-!
# Logarithmic fields in the Brownian spatial coordinate

Packet PROVE-ZHAN-GT4-A22. Rescale the actual logarithm, retaining the
first, second and third chain-rule factors explicitly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE.ZhanGT4

/-- Spatial rescaling of a regular logarithm. This is a statement about
the logarithm itself, independently of the existing exponential cutoff. -/
theorem IsLogField.seed_scale
    {ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ} {a b y ρ K σ : ℝ}
    (h : IsLogField ℓ ℓx ℓxx ℓxxx ℓt a b (σ * y) ρ K) (hσ : 0 < σ) :
    IsLogField (fun u x => ℓ u (σ * x)) (fun u x => σ * ℓx u (σ * x))
      (fun u x => σ ^ 2 * ℓxx u (σ * x)) (fun u x => σ ^ 3 * ℓxxx u (σ * x))
      (fun u x => ℓt u (σ * x)) a b y (ρ / σ) ((1 + σ + σ ^ 2 + σ ^ 3) * K) := by
  have hm (x : ℝ) (hx : |x - y| < 3 * (ρ / σ)) : |σ * x - σ * y| < 3 * ρ := by
    rw [← mul_sub, abs_mul, abs_of_pos hσ]
    have hh := mul_lt_mul_of_pos_left hx hσ
    have he : σ * (3 * (ρ / σ)) = 3 * ρ := by field_simp
    exact hh.trans_eq he
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.1, σ * p.2))
      (Icc a b ×ˢ {x | |x - y| < 3 * (ρ / σ)})
      (Icc a b ×ˢ {x | |x - σ * y| < 3 * ρ}) := fun p hp => ⟨hp.1, hm _ hp.2⟩
  have hc : Continuous (fun p : ℝ × ℝ => (p.1, σ * p.2)) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => σ * x) σ x := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id x).const_mul σ
  have h0 : 0 ≤ K := h.Knonneg
  have h1 : 0 ≤ σ * K := mul_nonneg hσ.le h0
  have h2 : 0 ≤ σ ^ 2 * K := mul_nonneg (sq_nonneg _) h0
  have h3 : 0 ≤ σ ^ 3 * K := by positivity
  refine ⟨div_pos h.pos hσ, by positivity, ?_, ?_, ?_, ?_,
    h.cont.comp hc.continuousOn hmap,
    continuousOn_const.mul (h.contX.comp hc.continuousOn hmap),
    continuousOn_const.mul (h.contXX.comp hc.continuousOn hmap),
    h.contT.comp hc.continuousOn hmap, ?_⟩
  · intro u hu x hx
    exact ((h.dx u hu (σ * x) (hm x hx)).comp x (hd x)).congr_deriv (mul_comm _ _)
  · intro u hu x hx
    exact (((h.dxx u hu (σ * x) (hm x hx)).comp x (hd x)).const_mul σ).congr_deriv (by ring)
  · intro u hu x hx
    exact (((h.dxxx u hu (σ * x) (hm x hx)).comp x (hd x)).const_mul (σ ^ 2)).congr_deriv (by ring)
  · intro u hu x hx
    exact h.dt u hu (σ * x) (hm x hx)
  · intro u hu x hx
    obtain ⟨hb₀, hb₁, hb₂, hb₃, hbT⟩ := h.bound u hu (σ * x) (hm x hx)
    have h₁ : |σ * ℓx u (σ * x)| ≤ σ * K := by
      simpa only [abs_mul, abs_of_pos hσ] using mul_le_mul_of_nonneg_left hb₁ hσ.le
    have h₂ : |σ ^ 2 * ℓxx u (σ * x)| ≤ σ ^ 2 * K := by
      simpa only [abs_mul, abs_pow, abs_of_pos hσ] using
        mul_le_mul_of_nonneg_left hb₂ (sq_nonneg σ)
    have h₃ : |σ ^ 3 * ℓxxx u (σ * x)| ≤ σ ^ 3 * K := by
      simpa only [abs_mul, abs_pow, abs_of_pos hσ] using
        mul_le_mul_of_nonneg_left hb₃ (show 0 ≤ σ ^ 3 by positivity)
    exact ⟨hb₀.trans (by nlinarith only [h1, h2, h3]),
      h₁.trans (by nlinarith only [h0, h2, h3]), h₂.trans (by nlinarith only [h0, h1, h3]),
      h₃.trans (by nlinarith only [h0, h1, h2]), hbT.trans (by nlinarith only [h1, h2, h3])⟩

end InteractingSLE.ZhanGT4
