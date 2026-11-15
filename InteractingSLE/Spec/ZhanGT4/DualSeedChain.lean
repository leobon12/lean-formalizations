/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# A one-sided chain rule along a moving point from partial derivatives

Packet PROVE-ZHAN-GT4-A19 (Zhan's A.1.6). The seeded density of §A.1.6 is a field `ℓ(t, x)` evaluated at moving points
(the driver `W_t` after removing the drift, the own-chart marks `V^m_t`), so its time derivative at a fixed space point
is that of `t ↦ f(t, v(t))`. Mathlib's `hasStrictFDerivAt_uncurry_coprod` needs partial derivatives on an open
neighbourhood (and its little-o lemma `isLittleO_sub_sub_fderiv` is not exported); here the time derivative is
one-sided (within `[b, c]`), so we prove the estimate from the mean value theorem:

* `isLittleO_sub_sub_of_partial`: the space increment along a moving point;

* **`hasDerivWithinAt_comp_of_partial`**: if `τ ↦ f(τ, v(t))` has derivative `f_t` within `s` at `t`, `v` has
  derivative `v'` within `s` at `t`, `f(τ, ·)` has derivative `f_x(τ, z)` near `(t, v(t))` (along `𝓝[s] t ×ˢ 𝓝 (v t)`),
  and `f_x` is continuous there, then `τ ↦ f(τ, v(τ))` has derivative `f_t + f_x(t, v(t)) v'` within `s` at `t`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Asymptotics Set

namespace InteractingSLE.ZhanGT4

/-- **The space increment along a moving point**: if `f(τ, ·)` has derivative `f_x(τ, z)` near `(t, z₀)` and `f_x` is
continuous there, then `f(τ, v(τ)) − f(τ, z₀) − f_x(t, z₀)(v(τ) − z₀) = o(v(τ) − z₀)` for `v(τ) → z₀`. -/
theorem isLittleO_sub_sub_of_partial {f fx : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {l : Filter ℝ} {t z₀ : ℝ}
    (hv : Tendsto v l (𝓝 z₀)) (hfx : ∀ᶠ p in l ×ˢ 𝓝 z₀, HasDerivAt (f p.1) (fx p.1 p.2) p.2)
    (hcx : Tendsto (fun p : ℝ × ℝ => fx p.1 p.2) (l ×ˢ 𝓝 z₀) (𝓝 (fx t z₀))) :
    (fun τ => f τ (v τ) - f τ z₀ - fx t z₀ * (v τ - z₀)) =o[l] fun τ => v τ - z₀ := by
  refine isLittleO_iff.2 fun c hc => ?_
  have hev : ∀ᶠ p in l ×ˢ 𝓝 z₀, HasDerivAt (f p.1) (fx p.1 p.2) p.2 ∧ |fx p.1 p.2 - fx t z₀| < c := by
    filter_upwards [hfx, hcx (Metric.ball_mem_nhds _ hc)] with p hp hp'
    exact ⟨hp, by rw [mem_preimage, Metric.mem_ball, Real.dist_eq] at hp'; exact hp'⟩
  obtain ⟨U, hU, Z, hZ, hUZ⟩ := mem_prod_iff.1 hev
  obtain ⟨δ, hδ, hδZ⟩ := Metric.mem_nhds_iff.1 hZ
  filter_upwards [hU, hv (Metric.ball_mem_nhds _ hδ)] with τ hτ hvτ
  rw [mem_preimage, Metric.mem_ball] at hvτ
  have hseg : uIcc z₀ (v τ) ⊆ Metric.ball z₀ δ := by
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq]
    rw [Real.dist_eq] at hvτ
    rcases le_total z₀ (v τ) with h | h
    · rw [uIcc_of_le h] at hz
      rw [abs_lt]; constructor <;> [linarith [hz.1]; linarith [hz.2, (abs_lt.1 hvτ).2]]
    · rw [uIcc_of_ge h] at hz
      rw [abs_lt]; constructor <;> [linarith [hz.1, (abs_lt.1 hvτ).1]; linarith [hz.2]]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun z => f τ z - fx t z₀ * z)
    (f' := fun z => fx τ z - fx t z₀) (C := c) (s := uIcc z₀ (v τ)) (fun z hz => ?_) (fun z hz => ?_)
    (convex_uIcc z₀ (v τ)) left_mem_uIcc right_mem_uIcc
  · have e : f τ (v τ) - f τ z₀ - fx t z₀ * (v τ - z₀) =
        (f τ (v τ) - fx t z₀ * v τ) - (f τ z₀ - fx t z₀ * z₀) := by ring
    rw [e]
    exact hmvt
  · have hp := (hUZ (show (τ, z) ∈ U ×ˢ Z from ⟨hτ, hδZ (hseg hz)⟩)).1
    exact (hp.sub ((hasDerivAt_id z).const_mul (fx t z₀)) |>.congr_deriv (by simp)).hasDerivWithinAt
  · have hp := (hUZ (show (τ, z) ∈ U ×ˢ Z from ⟨hτ, hδZ (hseg hz)⟩)).2
    rw [Real.norm_eq_abs]
    exact hp.le

/-- **The chain rule along a moving point** (one-sided in time). -/
theorem hasDerivWithinAt_comp_of_partial {f fx : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {s : Set ℝ} {t ft v' : ℝ}
    (hft : HasDerivWithinAt (fun τ => f τ (v t)) ft s t) (hv : HasDerivWithinAt v v' s t)
    (hfx : ∀ᶠ p in 𝓝[s] t ×ˢ 𝓝 (v t), HasDerivAt (f p.1) (fx p.1 p.2) p.2)
    (hcx : Tendsto (fun p : ℝ × ℝ => fx p.1 p.2) (𝓝[s] t ×ˢ 𝓝 (v t)) (𝓝 (fx t (v t)))) :
    HasDerivWithinAt (fun τ => f τ (v τ)) (ft + fx t (v t) * v') s t := by
  have hsp := isLittleO_sub_sub_of_partial hv.continuousWithinAt.tendsto hfx hcx
  have hvO : (fun τ => v τ - v t) =O[𝓝[s] t] fun τ => τ - t := hv.hasFDerivWithinAt.isBigO_sub
  have h1 : (fun τ => f τ (v τ) - f τ (v t) - fx t (v t) * (v τ - v t)) =o[𝓝[s] t] fun τ => τ - t :=
    hsp.trans_isBigO hvO
  have h2 : (fun τ => v τ - v t - (τ - t) • v') =o[𝓝[s] t] fun τ => τ - t := hv.isLittleO
  have h3 : (fun τ => f τ (v t) - f t (v t) - (τ - t) • ft) =o[𝓝[s] t] fun τ => τ - t := hft.isLittleO
  have hsum := (h1.add (h2.const_mul_left (fx t (v t)))).add h3
  refine HasDerivWithinAt.of_isLittleO (hsum.congr_left fun τ => ?_)
  simp only [smul_eq_mul]
  ring

end InteractingSLE.ZhanGT4
