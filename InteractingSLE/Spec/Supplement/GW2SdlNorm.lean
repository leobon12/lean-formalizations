/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdlScale

/-!
# GW2's stage mean, clause (G2): the dilation from two boundary normalizations

Packet PROVE-GW2-STAGEMEAN, dilation round. The chart clause of `GW2Sdl.StageDilationAt` asks that the kernel-route
chart `ca` be the instance's stage chart `cs` dilated by some `λ > 0`. Two conformal charts with the same domain
differ by a real Möbius map of `ℍ` (`GW2Spm.exists_realMobius_of_same_dom`); this file shows that the Möbius map is a
positive dilation as soon as it fixes the two marked boundary points in the analytic sense:

* **`realMobius_b_eq_zero`**: a real Möbius map of positive determinant tending to `0` at `0` (within `ℍ`) has `b = 0`;
* **`realMobius_e_eq_zero`**: if moreover `‖M(iy)‖ → ∞` as `y → ∞`, then `e = 0`;
* **`exists_dilation_of_realMobius`**: such a Möbius map is `w ↦ λ w` with `λ = a / f > 0`;
* **`exists_dilation_of_same_dom`**: two conformal charts `c, d` with the same domain such that `d.1 ∘ c.2.1` tends to
  `0` at `0` and is unbounded along `iy`, `y → ∞`, satisfy `d.1 = λ · c.1` on the common domain for some `λ > 0`;
* `dilationFactor c d = ‖d.1 (c.2.1 i)‖` and **`eq_dilationFactor`**: the factor is canonical (no choice needed).

For the stage (`c = cs`, `d = ca`): `0` is the explored tip (both charts are centred there) and `∞` the counterflow
tip (both relative maps send it to `∞`); the two limits are the tip correspondences of the two charts. Deterministic.
Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Theorem14.GW2Sdl

/-- For `z ∈ ℍ` the denominator of a real Möbius map of nonzero determinant does not vanish. -/
theorem realMobius_den_ne_zero {a b e f : ℝ} (hdet : 0 < a * f - b * e) {z : ℂ} (hz : z ∈ H) :
    (e : ℂ) * z + f ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im, mul_re, sub_zero, add_re,
    zero_re] at him hre
  have hzi : 0 < z.im := hz
  have he : e = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact h1
    · exact absurd h1 hzi.ne'
  rw [he, zero_mul, zero_add] at hre
  rw [he, hre] at hdet
  simp at hdet

/-- **A real Möbius map tending to `0` at `0` within `ℍ` has `b = 0`.** -/
theorem realMobius_b_eq_zero {a b e f : ℝ} (hdet : 0 < a * f - b * e)
    (h0 : Tendsto (realMobius a b e f) (𝓝[H] 0) (𝓝 0)) : b = 0 := by
  have hid : ∀ z ∈ H, realMobius a b e f z * ((e : ℂ) * z + f) = (a : ℂ) * z + b := fun z hz => by
    unfold realMobius
    exact div_mul_cancel₀ _ (realMobius_den_ne_zero hdet hz)
  have hcont : ∀ (p q : ℂ), Tendsto (fun z : ℂ => p * z + q) (𝓝[H] 0) (𝓝 (p * 0 + q)) := fun p q =>
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hL := h0.mul (hcont e f)
  have hne : (𝓝[H] (0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    show (0 : ℝ) ≤ (0 : ℂ).im
    simp
  have heq := tendsto_nhds_unique (hL.congr' (eventually_nhdsWithin_of_forall hid)) (hcont a b)
  simp only [zero_mul, mul_zero, zero_add] at heq
  exact_mod_cast heq.symm

/-- **A real Möbius map with `b = 0`, unbounded along the imaginary axis, has `e = 0`.** -/
theorem realMobius_e_eq_zero {a e f : ℝ}
    (hinf : Tendsto (fun y : ℝ => ‖realMobius a 0 e f ((y : ℂ) * I)‖) atTop atTop) : e = 0 := by
  by_contra he
  have heabs : 0 < |e| := abs_pos.2 he
  obtain ⟨y, hy, hpos⟩ := ((hinf.eventually_gt_atTop (|a| / |e|)).and (eventually_gt_atTop (0 : ℝ))).exists
  have hnum : ‖(a : ℂ) * ((y : ℂ) * I) + ((0 : ℝ) : ℂ)‖ = |a| * y := by
    simp only [ofReal_zero, add_zero, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
  have hden : |e| * y ≤ ‖(e : ℂ) * ((y : ℂ) * I) + f‖ := by
    have h1 := Complex.abs_im_le_norm ((e : ℂ) * ((y : ℂ) * I) + f)
    have h2 : ((e : ℂ) * ((y : ℂ) * I) + f).im = e * y := by simp
    rw [h2, abs_mul, abs_of_pos hpos] at h1
    exact h1
  have hdpos : 0 < |e| * y := mul_pos heabs hpos
  have hle : ‖realMobius a 0 e f ((y : ℂ) * I)‖ ≤ |a| / |e| := by
    unfold realMobius
    rw [norm_div, hnum]
    calc |a| * y / ‖(e : ℂ) * ((y : ℂ) * I) + f‖ ≤ |a| * y / (|e| * y) :=
          div_le_div_of_nonneg_left (by positivity) hdpos hden
      _ = |a| / |e| := by field_simp
  exact absurd hy (not_lt.2 hle)

/-- **A real Möbius map fixing `0` and `∞` (analytically) is a positive dilation.** -/
theorem exists_dilation_of_realMobius {a b e f : ℝ} (hdet : 0 < a * f - b * e)
    (h0 : Tendsto (realMobius a b e f) (𝓝[H] 0) (𝓝 0))
    (hinf : Tendsto (fun y : ℝ => ‖realMobius a b e f ((y : ℂ) * I)‖) atTop atTop) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ w, realMobius a b e f w = (lam : ℂ) * w := by
  have hb := realMobius_b_eq_zero hdet h0
  subst hb
  have he := realMobius_e_eq_zero hinf
  subst he
  have haf : 0 < a * f := by simpa using hdet
  have hf : f ≠ 0 := fun h => by rw [h, mul_zero] at haf; exact lt_irrefl 0 haf
  have hlam : 0 < a / f := by
    have hf2 : 0 < f ^ 2 := by positivity
    have e : a / f = a * f / f ^ 2 := by field_simp
    rw [e]
    exact div_pos haf hf2
  exact ⟨a / f, hlam, fun w => realMobius_eq_dilation hf w⟩

/-- **Two conformal charts with the same domain whose transition fixes `0` and `∞` differ by a positive dilation.** -/
theorem exists_dilation_of_same_dom {c d : Chart} (hc : c.IsConformal) (hd : d.IsConformal)
    (hdom : (c.dom : Set ℂ) = d.dom) (h0 : Tendsto (fun w => d.1 (c.2.1 w)) (𝓝[H] 0) (𝓝 0))
    (hinf : Tendsto (fun y : ℝ => ‖d.1 (c.2.1 ((y : ℂ) * I))‖) atTop atTop) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ (c.dom : Set ℂ), d.1 x = (lam : ℂ) * c.1 x := by
  obtain ⟨a, b, e, f, hdet, hM⟩ := GW2Spm.exists_realMobius_of_same_dom hc hd hdom
  have h0' : Tendsto (realMobius a b e f) (𝓝[H] 0) (𝓝 0) :=
    h0.congr' (eventually_nhdsWithin_of_forall fun w hw => hM hw)
  have hinf' : Tendsto (fun y : ℝ => ‖realMobius a b e f ((y : ℂ) * I)‖) atTop atTop := by
    refine hinf.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hyH : (y : ℂ) * I ∈ H := by
      show 0 < ((y : ℂ) * I).im
      simpa using hy
    have h := hM hyH
    simp only at h
    rw [h]
  obtain ⟨lam, hlam, hdil⟩ := exists_dilation_of_realMobius hdet h0' hinf'
  refine ⟨lam, hlam, fun x hx => ?_⟩
  have h := hM (hc.fwd_mem hx)
  simp only at h
  rw [hc.inv_fwd hx] at h
  rw [h, hdil]

/-- **The canonical dilation factor of two charts**: `‖d.1 (c.2.1 i)‖`. -/
def dilationFactor (c d : Chart) : ℝ := ‖d.1 (c.2.1 I)‖

/-- **Under the two normalizations the dilation factor is canonical**: `d.1 = dilationFactor c d · c.1` on the common
domain, with `dilationFactor c d > 0`. -/
theorem eq_dilationFactor {c d : Chart} (hc : c.IsConformal) (hd : d.IsConformal)
    (hdom : (c.dom : Set ℂ) = d.dom) (h0 : Tendsto (fun w => d.1 (c.2.1 w)) (𝓝[H] 0) (𝓝 0))
    (hinf : Tendsto (fun y : ℝ => ‖d.1 (c.2.1 ((y : ℂ) * I))‖) atTop atTop) :
    0 < dilationFactor c d ∧ ∀ x ∈ (c.dom : Set ℂ), d.1 x = (dilationFactor c d : ℂ) * c.1 x := by
  obtain ⟨lam, hlam, hdil⟩ := exists_dilation_of_same_dom hc hd hdom h0 hinf
  have hIH : I ∈ H := by
    show (0 : ℝ) < I.im
    simp
  have hI := hdil _ (hc.inv_mem_dom hIH)
  rw [hc.2.2 I hIH] at hI
  have hfac : dilationFactor c d = lam := by
    unfold dilationFactor
    rw [hI, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hlam]
  rw [hfac]
  exact ⟨hlam, hdil⟩

end InteractingSLE.Theorem14.GW2Sdl
