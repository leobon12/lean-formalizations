/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# Continuous logarithms as limits of chain sums; measurable derivatives of random holomorphic maps

Packet PROVE-LEMMA71E (item (3) of PROVE-LEMMA71D's "What remains" C (v): the pocket chart's derivative lift must be
measurable in `ω`). Two elementary tools.

* **Chain sums.** If `L` is a continuous logarithm of `g` along the segment `[0, u]`, then for every fine enough
  partition the principal logarithms of the ratios of consecutive values of `g` add up to `L u − L 0`
  (`eventually_chainLogSum_eq`): consecutive increments of `L` are smaller than `π`, so the principal logarithm of
  `exp` of each increment is the increment, and the sum telescopes. The chain sums only evaluate `g`, so they turn a
  continuous logarithm of a random function into a limit of measurable functions.
* **Derivatives.** The derivative of a random function that is holomorphic at a point and measurable in `ω` near it is
  measurable in `ω` (`measurable_deriv_of_measurable`): it is the limit of difference quotients along a real sequence.

## Main results

* `chainLogSum`, **`eventually_chainLogSum_eq`**, `tendsto_chainLogSum`;
* **`measurable_deriv_of_measurable`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.Sec7.Lemma71E

/-! ### Chain sums of principal logarithms -/

/-- The chain sum of principal logarithms of the ratios of `g` at the points `(j/N) u`, `j = 0, …, N`. -/
def chainLogSum (g : ℂ → ℂ) (u : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, log (g ((((j + 1 : ℕ) : ℝ) / N : ℝ) * u) / g ((((j : ℕ) : ℝ) / N : ℝ) * u))

/-- **Chain sums compute continuous logarithms.** If `L` is continuous along the segment `[0, u]` and
`exp ∘ L = g` there, then the chain sums of `g` are eventually `L u − L 0`. -/
theorem eventually_chainLogSum_eq {g L : ℂ → ℂ} {u : ℂ}
    (hL : ContinuousOn (fun t : ℝ => L ((t : ℂ) * u)) (Icc 0 1))
    (hexp : ∀ t ∈ Icc (0 : ℝ) 1, exp (L ((t : ℂ) * u)) = g ((t : ℂ) * u)) :
    ∀ᶠ N : ℕ in atTop, chainLogSum g u N = L u - L 0 := by
  set f : ℝ → ℂ := fun t => L ((t : ℂ) * u) with hf
  have huc : UniformContinuousOn f (Icc 0 1) := isCompact_Icc.uniformContinuousOn_of_continuous hL
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc Real.pi Real.pi_pos
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / δ)
  filter_upwards [eventually_gt_atTop N₀, eventually_gt_atTop 0] with N hN hN0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hmem : ∀ j : ℕ, j ≤ N → ((j : ℝ) / N) ∈ Icc (0 : ℝ) 1 := fun j hj =>
    ⟨by positivity, (div_le_one hNpos).2 (by exact_mod_cast hj)⟩
  have hstep : ∀ j ∈ Finset.range N,
      log (g ((((j + 1 : ℕ) : ℝ) / N : ℝ) * u) / g ((((j : ℕ) : ℝ) / N : ℝ) * u)) =
        f (((j + 1 : ℕ) : ℝ) / N) - f ((j : ℝ) / N) := by
    intro j hj
    have hj' : j < N := Finset.mem_range.1 hj
    have h1 := hmem (j + 1) hj'
    have h0 := hmem j hj'.le
    rw [← hexp _ h1, ← hexp _ h0, ← exp_sub]
    have hd : dist (((j + 1 : ℕ) : ℝ) / N) ((j : ℝ) / N) < δ := by
      rw [Real.dist_eq, ← sub_div, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, abs_of_pos (by positivity)]
      have : 1 / δ < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN.le)
      rw [div_lt_iff₀ hδ] at this
      rw [div_lt_iff₀ hNpos]
      linarith
    have hlt := hδf _ h1 _ h0 hd
    rw [Complex.dist_eq] at hlt
    have him := abs_lt.1 (lt_of_le_of_lt (Complex.abs_im_le_norm _) hlt)
    exact log_exp (by linarith [him.1]) (by linarith [him.2])
  rw [chainLogSum, Finset.sum_congr rfl hstep]
  have htel := Finset.sum_range_sub (fun j : ℕ => f ((j : ℝ) / N)) N
  simp only [Nat.cast_add, Nat.cast_one] at htel ⊢
  rw [htel, div_self hNpos.ne', Nat.cast_zero, zero_div]
  simp only [hf, ofReal_one, one_mul, ofReal_zero, zero_mul]

/-- The chain sums converge to `L u − L 0`. -/
theorem tendsto_chainLogSum {g L : ℂ → ℂ} {u : ℂ}
    (hL : ContinuousOn (fun t : ℝ => L ((t : ℂ) * u)) (Icc 0 1))
    (hexp : ∀ t ∈ Icc (0 : ℝ) 1, exp (L ((t : ℂ) * u)) = g ((t : ℂ) * u)) :
    Tendsto (chainLogSum g u) atTop (𝓝 (L u - L 0)) :=
  tendsto_const_nhds.congr' (EventuallyEq.symm (eventually_chainLogSum_eq hL hexp))

/-- The chain sums of a continuous logarithm on a convex set containing `0` and `u`. -/
theorem tendsto_chainLogSum_of_convex {g L : ℂ → ℂ} {S : Set ℂ} (hS : Convex ℝ S) (h0 : (0 : ℂ) ∈ S)
    {u : ℂ} (hu : u ∈ S) (hL : ContinuousOn L S) (hexp : ∀ z ∈ S, exp (L z) = g z) :
    Tendsto (chainLogSum g u) atTop (𝓝 (L u - L 0)) := by
  have hmaps : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * u ∈ S := by
    intro t ht
    have := hS h0 hu (sub_nonneg.2 ht.2) ht.1 (by ring)
    simpa [Complex.real_smul] using this
  refine tendsto_chainLogSum ?_ fun t ht => hexp _ (hmaps t ht)
  exact hL.comp (Continuous.continuousOn (by fun_prop)) hmaps

/-! ### Measurable derivatives -/

/-- **The derivative of a random holomorphic function is measurable**: if `F ω` is differentiable at `w` for every
`ω`, and `ω ↦ F ω z` is measurable for every `z` in a neighbourhood `U` of `w`, then `ω ↦ (F ω)′(w)` is
measurable (the limit of the difference quotients along `h_n = r/(n+2)`, `B(w, r) ⊆ U`). -/
theorem measurable_deriv_of_measurable {Ω : Type*} [MeasurableSpace Ω] {F : Ω → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) {w : ℂ} (hw : w ∈ U) (hF : ∀ z ∈ U, Measurable fun ω => F ω z)
    (hd : ∀ ω, DifferentiableAt ℂ (F ω) w) : Measurable fun ω => deriv (F ω) w := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU w hw
  set h : ℕ → ℂ := fun n => ((r / ((n : ℝ) + 2) : ℝ) : ℂ) with hh
  have hpos : ∀ n : ℕ, (0 : ℝ) < r / ((n : ℝ) + 2) := fun n => by positivity
  have hmem : ∀ n, w + h n ∈ U := by
    intro n
    refine hrU (mem_ball.2 ?_)
    rw [dist_eq_norm, add_sub_cancel_left, hh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlim : Tendsto h atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
          tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        simpa using h2.const_div_atTop r
      have h3 := (continuous_ofReal.tendsto 0).comp this
      rw [ofReal_zero] at h3
      rw [hh]
      exact h3
    · show h n ≠ 0
      rw [hh]
      exact Complex.ofReal_ne_zero.2 (hpos n).ne'
  refine measurable_of_tendsto_metrizable (f := fun n ω => (h n)⁻¹ • (F ω (w + h n) - F ω w))
    (fun n => ?_) (tendsto_pi_nhds.2 fun ω => ((hd ω).hasDerivAt.tendsto_slope_zero).comp hlim)
  exact Measurable.const_smul (g := fun ω => F ω (w + h n) - F ω w) ((hF _ (hmem n)).sub (hF w hw)) (h n)⁻¹

end InteractingSLE.Sec7.Lemma71E
