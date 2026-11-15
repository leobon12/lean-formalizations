/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.FiniteExceptionUniqueness
import Mathlib.Analysis.Complex.Harmonic.Poisson

/-!
# Wang–Wu §4.2: removing the exceptional endpoint singularities (Lemmas 4.7, 4.9, Corollary 4.8)

Packet PROVE-WW-B. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31),
§4.2, pp. 18–20 (text dump lines 1058–1184).

## Main results

* `eqOn_zero_of_log_growth` — **Lemma 4.7** (finite exceptional prime ends): a harmonic function
  on the unit disc with `sup_{|z| = r} |u| ≤ C (1 + log (1/(1 − r)))` and continuous boundary value
  `0` off a finite set vanishes. It is a corollary of the disk step of Aux. lemma 28
  (`InteractingSLE.Sec6.eqOn_zero_of_growth`, power growth `(1 − r)^{−α}`, `α < 1/2`), since
  `log (1/(1 − r)) ≤ 4 (1 − r)^{−1/4}`.
* `eqOn_of_log_growth_of_tendsto` — **Corollary 4.8**, deterministic core: on a simply connected
  domain `C = f(𝔻)`, a harmonic `H` with `|H(z)| ≤ K (1 + log (1 + 1/dist(z, ∂C)))` and a bounded
  harmonic candidate `v` whose difference has boundary limit `0` at every prime end (point of the
  circle, read through `f`) except finitely many are equal (Koebe's distance estimate turns the
  bound into logarithmic radial growth of `(H − v) ∘ f`; then Lemma 4.7).
* `eqOn_zero_of_bounded_of_ae_tendsto_radial`, `eqOn_of_bounded_of_ae_tendsto_radial` —
  **Lemma 4.9** (bounded harmonic uniqueness): two bounded harmonic functions on a simply
  connected domain whose difference has radial limit `0` at almost every point of the circle
  (harmonic measure of the disk chart) are equal; the source's argument: the Poisson formula on
  concentric circles (Mathlib `HarmonicOnNhd.circleAverage_poissonKernel_smul`) and bounded
  convergence. `eqOn_of_bounded_of_tendsto_off_finite` is the finite-exception case.
-/

set_option autoImplicit false

noncomputable section

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

namespace InteractingSLE.WangWu

open InteractingSLE.Sec6 QuantumZipper.CA.Koebe SupercriticalConformalCovariance

/-! ### Lemma 4.7 -/

/-- `log (1/(1 − r)) ≤ 4 (1 − r)^{−1/4}` for `0 ≤ r < 1`. -/
lemma log_one_div_le_four_mul_rpow {x : ℝ} (hx : 0 < x) :
    Real.log (1 / x) ≤ 4 * x ^ (-(1 / 4 : ℝ)) := by
  rw [one_div, Real.log_inv]
  exact neg_log_le_four_mul_rpow hx

/-- `0 ≤ log (1/(1 − r))` for `0 < 1 − r ≤ 1`. -/
lemma log_one_div_nonneg {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 0 ≤ Real.log (1 / x) :=
  Real.log_nonneg (by rw [le_div_iff₀ hx]; linarith)

/-- **Wang–Wu, Lemma 4.7** (finite exceptional prime ends). Let `u` be harmonic in the unit disc
with `sup_{|z| = r} |u(z)| ≤ C (1 + log (1/(1 − r)))` for `0 < r < 1`, and suppose `u` extends
continuously with value zero to every boundary point outside a finite set `E`. Then `u = 0`. -/
theorem eqOn_zero_of_log_growth {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1))
    {E : Set ℂ} (hE : E.Finite) {C : ℝ}
    (hgrowth : ∀ z ∈ ball (0 : ℂ) 1, 0 < ‖z‖ → |u z| ≤ C * (1 + Real.log (1 / (1 - ‖z‖))))
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → Tendsto u (𝓝[ball 0 1] q) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, u z = 0 := by
  -- a bound on the closed disc of radius `1/2`
  have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have hcont : ContinuousOn u (closedBall (0 : ℂ) (1 / 2)) := fun z hz =>
    (hu z (hsub hz)).1.continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn hcont
  -- power growth
  have hgrowth' : ∀ z ∈ ball (0 : ℂ) 1,
      |u z| ≤ (|M| + 5 * |C|) * (1 - ‖z‖) ^ (-(1 / 4 : ℝ)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hr : 0 < 1 - ‖z‖ := by linarith
    have hr1 : 1 - ‖z‖ ≤ 1 := by linarith [norm_nonneg z]
    have hP : 1 ≤ (1 - ‖z‖) ^ (-(1 / 4 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
    have hP0 : 0 ≤ (1 - ‖z‖) ^ (-(1 / 4 : ℝ)) := by linarith
    by_cases hz2 : ‖z‖ ≤ 1 / 2
    · have h1 : |u z| ≤ M := by
        have := hM z (mem_closedBall_zero_iff.2 hz2)
        rwa [Real.norm_eq_abs] at this
      calc |u z| ≤ |M| := h1.trans (le_abs_self M)
        _ ≤ |M| * (1 - ‖z‖) ^ (-(1 / 4 : ℝ)) := le_mul_of_one_le_right (abs_nonneg _) hP
        _ ≤ (|M| + 5 * |C|) * (1 - ‖z‖) ^ (-(1 / 4 : ℝ)) := by
          gcongr
          linarith [abs_nonneg C]
    · have hpos : 0 < ‖z‖ := by linarith
      have hL := log_one_div_le_four_mul_rpow hr
      have hL0 := log_one_div_nonneg hr hr1
      calc |u z| ≤ C * (1 + Real.log (1 / (1 - ‖z‖))) := hgrowth z hz hpos
        _ ≤ |C| * (1 + Real.log (1 / (1 - ‖z‖))) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
        _ ≤ |C| * (5 * (1 - ‖z‖) ^ (-(1 / 4 : ℝ))) := by
          gcongr
          linarith
        _ ≤ (|M| + 5 * |C|) * (1 - ‖z‖) ^ (-(1 / 4 : ℝ)) := by
          nlinarith [abs_nonneg M, abs_nonneg C]
  set E' : Finset ℂ := hE.toFinset.filter (fun p => ‖p‖ = 1)
  have hE' : ∀ p ∈ E', ‖p‖ = 1 := fun p hp => (Finset.mem_filter.1 hp).2
  have hbd' : ∀ q : ℂ, ‖q‖ = 1 → q ∉ E' → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0) := by
    intro q hq hqE
    refine hbd q (mem_sphere_zero_iff_norm.2 hq) fun hqE' => hqE ?_
    exact Finset.mem_filter.2 ⟨hE.mem_toFinset.2 hqE', hq⟩
  exact eqOn_zero_of_growth hu hE' (by norm_num) (by norm_num) hgrowth' hbd'

/-! ### Lemma 4.9 -/

/-- The Poisson kernel `P(0, w, z)` is at most `4/(1 − |w|)²` for `(1 + |w|)/2 ≤ |z| ≤ 1`. -/
lemma abs_poissonKernel_le {w z : ℂ} (hw : ‖w‖ < 1) (hz1 : ‖z‖ ≤ 1)
    (hz : (1 + ‖w‖) / 2 ≤ ‖z‖) : |poissonKernel 0 w z| ≤ 4 / (1 - ‖w‖) ^ 2 := by
  simp only [poissonKernel, sub_zero]
  have hd : (1 - ‖w‖) / 2 ≤ ‖z - w‖ := by
    have := norm_sub_norm_le z w
    linarith
  have hd0 : 0 < (1 - ‖w‖) / 2 := by linarith
  have hnum0 : 0 ≤ ‖z‖ ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hnum1 : ‖z‖ ^ 2 - ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w, norm_nonneg z]
  have hden : ((1 - ‖w‖) / 2) ^ 2 ≤ ‖z - w‖ ^ 2 := pow_le_pow_left₀ hd0.le hd 2
  rw [abs_of_nonneg (div_nonneg hnum0 (sq_nonneg _))]
  calc (‖z‖ ^ 2 - ‖w‖ ^ 2) / ‖z - w‖ ^ 2 ≤ 1 / ((1 - ‖w‖) / 2) ^ 2 :=
        div_le_div₀ zero_le_one hnum1 (by positivity) hden
    _ = 4 / (1 - ‖w‖) ^ 2 := by
        have : (1 - ‖w‖) ≠ 0 := by linarith
        field_simp
        ring

/-- **Wang–Wu, Lemma 4.9** (bounded harmonic uniqueness), disc form. A bounded harmonic function
on the unit disc whose radial limit is `0` at almost every point of the circle vanishes. (Harmonic
measure on the circle is equivalent to arc length.) Proof as in the source: the Poisson formula on
the concentric circles of radius `r < 1` and bounded convergence as `r ↑ 1`. -/
theorem eqOn_zero_of_bounded_of_ae_tendsto_radial {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ ball (0 : ℂ) 1, |u z| ≤ M)
    (hrad : ∀ᵐ θ : ℝ, Tendsto (fun r : ℝ => u (circleMap 0 r θ)) (𝓝[<] 1) (𝓝 0)) :
    ∀ w ∈ ball (0 : ℂ) 1, u w = 0 := by
  intro w hw
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have hpos : 0 < 1 - ‖w‖ := by linarith
  set ρ : ℕ → ℝ := fun n => 1 - (1 - ‖w‖) / (2 * ((n : ℝ) + 1)) with hρ
  have hρlt : ∀ n, ρ n < 1 := fun n => by
    have : 0 < (1 - ‖w‖) / (2 * ((n : ℝ) + 1)) := by positivity
    simp only [hρ]; linarith
  have hρge : ∀ n, (1 + ‖w‖) / 2 ≤ ρ n := fun n => by
    have h1 : (1 - ‖w‖) / (2 * ((n : ℝ) + 1)) ≤ (1 - ‖w‖) / 2 :=
      div_le_div_of_nonneg_left hpos.le (by norm_num)
        (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    simp only [hρ]; linarith
  have hρ0 : ∀ n, 0 < ρ n := fun n =>
    lt_of_lt_of_le (by linarith [norm_nonneg w]) (hρge n)
  have hρt : Tendsto ρ atTop (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hρlt⟩
    have h0 : Tendsto (fun n : ℕ => (1 - ‖w‖) / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((1 - ‖w‖) / 2)
      rw [mul_zero] at h
      refine h.congr fun n => ?_
      field_simp
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  have hnorm : ∀ n θ, ‖circleMap 0 (ρ n) θ‖ = ρ n := fun n θ => by
    rw [norm_circleMap_zero, abs_of_pos (hρ0 n)]
  have hcm : ∀ n θ, circleMap 0 (ρ n) θ ∈ ball (0 : ℂ) 1 := fun n θ => by
    rw [mem_ball_zero_iff, hnorm]; exact hρlt n
  have hucont : ContinuousOn u (ball (0 : ℂ) 1) := fun z hz =>
    (hu z hz).1.continuousAt.continuousWithinAt
  -- the Poisson formula on each circle
  set F : ℕ → ℝ → ℝ := fun n θ =>
    poissonKernel 0 w (circleMap 0 (ρ n) θ) * u (circleMap 0 (ρ n) θ) with hF
  have hPoisson : ∀ n, u w = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, F n θ := by
    intro n
    have hharm : InnerProductSpace.HarmonicOnNhd u (closedBall 0 (ρ n)) := fun z hz =>
      hu z (closedBall_subset_ball (hρlt n) hz)
    have hwr : w ∈ ball (0 : ℂ) (ρ n) := mem_ball_zero_iff.2 (by linarith [hρge n])
    have := hharm.circleAverage_poissonKernel_smul hwr
    rw [Real.circleAverage_def, smul_eq_mul] at this
    rw [← this]
    rfl
  -- bounded convergence
  set B : ℝ := 4 / (1 - ‖w‖) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hPk : ∀ n θ, |poissonKernel 0 w (circleMap 0 (ρ n) θ)| ≤ B := fun n θ =>
    abs_poissonKernel_le hw1 (by rw [hnorm]; exact (hρlt n).le) (by rw [hnorm]; exact hρge n)
  have hlim : Tendsto (fun n => ∫ θ in (0 : ℝ)..2 * π, F n θ) atTop
      (𝓝 (∫ _ in (0 : ℝ)..2 * π, (0 : ℝ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B * M)
      ?_ ?_ intervalIntegrable_const ?_
    · refine Eventually.of_forall fun n => ?_
      have hden : ∀ θ, ‖circleMap 0 (ρ n) θ - 0 - (w - 0)‖ ^ 2 ≠ 0 := fun θ => by
        have h1 := norm_sub_norm_le (circleMap 0 (ρ n) θ) w
        rw [hnorm] at h1
        have : 0 < ‖circleMap 0 (ρ n) θ - 0 - (w - 0)‖ := by
          simp only [sub_zero]; linarith [hρge n]
        positivity
      have hc1 : Continuous fun θ => poissonKernel 0 w (circleMap 0 (ρ n) θ) := by
        simp only [poissonKernel]
        exact Continuous.div (by fun_prop) (by fun_prop) hden
      have hc2 : Continuous fun θ => u (circleMap 0 (ρ n) θ) :=
        hucont.comp_continuous (continuous_circleMap 0 (ρ n)) (hcm n)
      exact (hc1.mul hc2).aestronglyMeasurable
    · refine Eventually.of_forall fun n => Eventually.of_forall fun θ _ => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hPk n θ) (hM _ (hcm n θ)) (abs_nonneg _) hB0
    · filter_upwards [hrad] with θ hθ _
      have h1 : Tendsto (fun n => u (circleMap 0 (ρ n) θ)) atTop (𝓝 0) := hθ.comp hρt
      have h2 : Tendsto (fun n => B * ‖u (circleMap 0 (ρ n) θ)‖) atTop (𝓝 0) := by
        simpa using h1.norm.const_mul B
      refine squeeze_zero_norm (fun n => ?_) h2
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hPk n θ) (abs_nonneg _)
  have hconst : Tendsto (fun n => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, F n θ) atTop
      (𝓝 ((2 * π)⁻¹ * 0)) := by
    simpa using hlim.const_mul (2 * π)⁻¹
  have e : (fun n => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, F n θ) = fun _ => u w :=
    funext fun n => (hPoisson n).symm
  rw [e, mul_zero] at hconst
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-- The difference of two harmonic functions on `C`, pulled back by a conformal map of the disc
onto `C`, is harmonic on the disc. -/
lemma harmonicOnNhd_comp_sub {C : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalBijection f (ball 0 1) C)
    {H₁ H₂ : ℂ → ℝ} (h₁ : InnerProductSpace.HarmonicOnNhd H₁ C)
    (h₂ : InnerProductSpace.HarmonicOnNhd H₂ C) :
    InnerProductSpace.HarmonicOnNhd (fun ζ => H₁ (f ζ) - H₂ (f ζ)) (ball 0 1) := by
  intro ζ hζ
  have hfa : AnalyticAt ℂ f ζ := hf.1.analyticAt (isOpen_ball.mem_nhds hζ)
  have hfz : f ζ ∈ C := hf.2.mapsTo hζ
  exact (QuantumZipper.FieldLawler.fl_harmonicAt_comp hfa (h₁ _ hfz)).sub
    (QuantumZipper.FieldLawler.fl_harmonicAt_comp hfa (h₂ _ hfz))

/-- **Wang–Wu, Lemma 4.9** (bounded harmonic uniqueness). Two bounded harmonic functions on a simply
connected domain `C = f(𝔻)` (`f` conformal) that have the same prime-end boundary limits almost
everywhere for harmonic measure are equal: here the boundary condition is read in the disc chart,
as radial limits of the difference at almost every point of the circle. -/
theorem eqOn_of_bounded_of_ae_tendsto_radial {C : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) {H₁ H₂ : ℂ → ℝ}
    (h₁ : InnerProductSpace.HarmonicOnNhd H₁ C) (h₂ : InnerProductSpace.HarmonicOnNhd H₂ C)
    {M₁ M₂ : ℝ} (hb₁ : ∀ z ∈ C, |H₁ z| ≤ M₁) (hb₂ : ∀ z ∈ C, |H₂ z| ≤ M₂)
    (hrad : ∀ᵐ θ : ℝ, Tendsto (fun r : ℝ => H₁ (f (circleMap 0 r θ)) - H₂ (f (circleMap 0 r θ)))
      (𝓝[<] 1) (𝓝 0)) :
    EqOn H₁ H₂ C := by
  have hu := harmonicOnNhd_comp_sub hf h₁ h₂
  have hM : ∀ ζ ∈ ball (0 : ℂ) 1, |H₁ (f ζ) - H₂ (f ζ)| ≤ M₁ + M₂ := fun ζ hζ =>
    (abs_sub _ _).trans (add_le_add (hb₁ _ (hf.2.mapsTo hζ)) (hb₂ _ (hf.2.mapsTo hζ)))
  have h0 := eqOn_zero_of_bounded_of_ae_tendsto_radial hu hM hrad
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hf.2.surjOn hz
  have := h0 ζ hζ
  linarith

/-- **Wang–Wu, Lemma 4.9**, "in particular": the exceptions are finitely many prime ends (points of
the circle of the disc chart), and the difference has unrestricted boundary limit `0` elsewhere. -/
theorem eqOn_of_bounded_of_tendsto_off_finite {C : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) {H₁ H₂ : ℂ → ℝ}
    (h₁ : InnerProductSpace.HarmonicOnNhd H₁ C) (h₂ : InnerProductSpace.HarmonicOnNhd H₂ C)
    {M₁ M₂ : ℝ} (hb₁ : ∀ z ∈ C, |H₁ z| ≤ M₁) (hb₂ : ∀ z ∈ C, |H₂ z| ≤ M₂)
    {E : Set ℂ} (hE : E.Finite)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      Tendsto (fun ζ => H₁ (f ζ) - H₂ (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) :
    EqOn H₁ H₂ C := by
  have hu := harmonicOnNhd_comp_sub hf h₁ h₂
  have hgrowth : ∀ ζ ∈ ball (0 : ℂ) 1, 0 < ‖ζ‖ →
      |H₁ (f ζ) - H₂ (f ζ)| ≤ (M₁ + M₂) * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
    intro ζ hζ _
    have hz1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    have hL0 := log_one_div_nonneg (x := 1 - ‖ζ‖) (by linarith) (by linarith [norm_nonneg ζ])
    have e1 := hb₁ _ (hf.2.mapsTo hζ)
    have e2 := hb₂ _ (hf.2.mapsTo hζ)
    have hM0 : 0 ≤ M₁ + M₂ := by linarith [abs_nonneg (H₁ (f ζ)), abs_nonneg (H₂ (f ζ))]
    calc |H₁ (f ζ) - H₂ (f ζ)| ≤ M₁ + M₂ := (abs_sub _ _).trans (add_le_add e1 e2)
      _ ≤ (M₁ + M₂) * (1 + Real.log (1 / (1 - ‖ζ‖))) := le_mul_of_one_le_right hM0 (by linarith)
  have h0 := eqOn_zero_of_log_growth hu hE hgrowth hbd
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hf.2.surjOn hz
  have := h0 ζ hζ
  linarith

/-! ### Corollary 4.8, deterministic core -/

/-- **Wang–Wu, Corollary 4.8**, deterministic core (identification of a component mean). Let
`C = f(𝔻)` be simply connected (`f` conformal), `H` harmonic on `C` with the logarithmic bound
`|H(z)| ≤ K (1 + log (1 + 1/dist(z, ∂C)))` (Lemma 4.6's conclusion, valid on all of `C` after the
bounded part far from the boundary is absorbed into `K`), and `v` a bounded harmonic candidate.
If `H − v` has boundary limit `0` at every prime end of `C` (point of the circle, read through
`f`) except finitely many, then `H = v` on `C`. Proof as in the source: Koebe's distance estimate
`dist(f(w), ∂C) ≥ c (1 − |w|)^p` gives logarithmic radial growth of `(H − v) ∘ f`; Lemma 4.7. -/
theorem eqOn_of_log_growth_of_tendsto {C : Set ℂ} (hCo : IsOpen C) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) {H v : ℂ → ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd H C) (hv : InnerProductSpace.HarmonicOnNhd v C)
    {M : ℝ} (hvb : ∀ z ∈ C, |v z| ≤ M) {K : ℝ}
    (hgrowth : ∀ z ∈ C, |H z| ≤ K * (1 + Real.log (1 + (infDist z (frontier C))⁻¹)))
    {E : Set ℂ} (hE : E.Finite)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      Tendsto (fun ζ => H (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) :
    EqOn H v C := by
  obtain ⟨hfd, hfb⟩ := hf
  have hfinj := hfb.injOn
  have hfim : f '' ball 0 1 = C := hfb.image_eq
  have hball0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hCne : C.Nonempty := ⟨f 0, hfb.mapsTo hball0⟩
  have hCuniv : C ≠ univ := hfim ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos hfd hfinj
  set κ := koebeCovConst * ‖deriv f 0‖
  have hκ : 0 < κ := mul_pos koebeCovConst_pos
    (norm_pos_iff.2 (QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd hfinj hball0))
  set p : ℝ := 1 + koebeDistExp
  have hp : 0 < p := by have := koebeDistExp_pos; simp only [p]; linarith
  have hdist : ∀ ζ ∈ ball (0 : ℂ) 1, κ * (1 - ‖ζ‖) ^ p ≤ infDist (f ζ) (frontier C) := by
    intro ζ hζ
    have := koebe_mul_pow_le_infDist hfd hfinj hζ
    rw [hfim] at this
    exact this.trans (infDist_compl_le_infDist_frontier hCo hCne hCuniv _)
  -- logarithmic radial growth of `H ∘ f`
  set K' : ℝ := |K| * (1 + Real.log (1 + κ⁻¹) + p) + |M|
  have hgrowth' : ∀ ζ ∈ ball (0 : ℂ) 1, 0 < ‖ζ‖ →
      |H (f ζ) - v (f ζ)| ≤ K' * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
    intro ζ hζ _
    have hz1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    have hr : 0 < 1 - ‖ζ‖ := by linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hL0 := log_one_div_nonneg hr hr1
    have hy : 0 < (1 - ‖ζ‖) ^ p := Real.rpow_pos_of_pos hr p
    have hy1 : (1 - ‖ζ‖) ^ p ≤ 1 := Real.rpow_le_one hr.le hr1 hp.le
    have hd := hdist ζ hζ
    have hd0 : 0 < κ * (1 - ‖ζ‖) ^ p := mul_pos hκ hy
    -- `1 + 1/d ≤ (1 + κ⁻¹) (1 − r)^{−p}`
    have h1 : 1 + (infDist (f ζ) (frontier C))⁻¹ ≤ (1 + κ⁻¹) * ((1 - ‖ζ‖) ^ p)⁻¹ := by
      have hinv : (infDist (f ζ) (frontier C))⁻¹ ≤ κ⁻¹ * ((1 - ‖ζ‖) ^ p)⁻¹ := by
        rw [← mul_inv]
        exact inv_anti₀ hd0 hd
      have hge : 1 ≤ ((1 - ‖ζ‖) ^ p)⁻¹ := one_le_inv₀ hy |>.2 hy1
      nlinarith [inv_pos.2 hκ]
    have hpos1 : 0 < 1 + (infDist (f ζ) (frontier C))⁻¹ := by
      have := inv_nonneg.2 (infDist_nonneg (x := f ζ) (s := frontier C)); linarith
    have h2 : Real.log (1 + (infDist (f ζ) (frontier C))⁻¹) ≤
        Real.log (1 + κ⁻¹) + p * Real.log (1 / (1 - ‖ζ‖)) := by
      have hκ1 : 0 < 1 + κ⁻¹ := by have := inv_pos.2 hκ; linarith
      calc Real.log (1 + (infDist (f ζ) (frontier C))⁻¹)
          ≤ Real.log ((1 + κ⁻¹) * ((1 - ‖ζ‖) ^ p)⁻¹) := Real.log_le_log hpos1 h1
        _ = Real.log (1 + κ⁻¹) + p * Real.log (1 / (1 - ‖ζ‖)) := by
          rw [Real.log_mul hκ1.ne' (inv_pos.2 hy).ne', Real.log_inv, Real.log_rpow hr, one_div,
            Real.log_inv]
          ring
    have hlog0 : 0 ≤ Real.log (1 + (infDist (f ζ) (frontier C))⁻¹) := by
      have := inv_nonneg.2 (infDist_nonneg (x := f ζ) (s := frontier C))
      exact Real.log_nonneg (by linarith)
    have hHz : |H (f ζ)| ≤ |K| * (1 + Real.log (1 + κ⁻¹) + p) * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
      have hκlog : 0 ≤ Real.log (1 + κ⁻¹) := Real.log_nonneg (by have := inv_pos.2 hκ; linarith)
      calc |H (f ζ)| ≤ K * (1 + Real.log (1 + (infDist (f ζ) (frontier C))⁻¹)) :=
            hgrowth _ (hfb.mapsTo hζ)
        _ ≤ |K| * (1 + Real.log (1 + (infDist (f ζ) (frontier C))⁻¹)) :=
            mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
        _ ≤ |K| * (1 + (Real.log (1 + κ⁻¹) + p * Real.log (1 / (1 - ‖ζ‖)))) := by gcongr
        _ ≤ |K| * (1 + Real.log (1 + κ⁻¹) + p) * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
            rw [mul_assoc]
            gcongr
            nlinarith
    have hvz : |v (f ζ)| ≤ |M| * (1 + Real.log (1 / (1 - ‖ζ‖))) :=
      ((hvb _ (hfb.mapsTo hζ)).trans (le_abs_self M)).trans
        (le_mul_of_one_le_right (abs_nonneg _) (by linarith))
    calc |H (f ζ) - v (f ζ)| ≤ |H (f ζ)| + |v (f ζ)| := abs_sub _ _
      _ ≤ _ := add_le_add hHz hvz
      _ = K' * (1 + Real.log (1 / (1 - ‖ζ‖))) := by simp only [K']; ring
  have hu := harmonicOnNhd_comp_sub ⟨hfd, hfb⟩ hH hv
  have h0 := eqOn_zero_of_log_growth hu hE hgrowth' hbd
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hfb.surjOn hz
  have := h0 ζ hζ
  linarith

/-- **Wang–Wu, Corollary 4.8**, deterministic core, under the weaker subpower bound
`|H(z)| ≤ C_ε (1 + dist(z, ∂C)^{−ε})` for every `ε > 0` (implied by the logarithmic bound of
Lemma 4.6; it is the growth hypothesis of the specification's Aux. lemma 28). Same conclusion as
`eqOn_of_log_growth_of_tendsto`; the disc step is `eqOn_zero_of_growth` with exponent `1/4`. -/
theorem eqOn_of_subpower_growth_of_tendsto {C : Set ℂ} (hCo : IsOpen C) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) {H v : ℂ → ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd H C) (hv : InnerProductSpace.HarmonicOnNhd v C)
    {M : ℝ} (hvb : ∀ z ∈ C, |v z| ≤ M)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ z ∈ C,
      |H z| ≤ Cε * (1 + infDist z (frontier C) ^ (-ε)))
    {E : Set ℂ} (hE : E.Finite)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      Tendsto (fun ζ => H (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) :
    EqOn H v C := by
  obtain ⟨hfd, hfb⟩ := hf
  have hfinj := hfb.injOn
  have hfim : f '' ball 0 1 = C := hfb.image_eq
  have hball0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hCne : C.Nonempty := ⟨f 0, hfb.mapsTo hball0⟩
  have hCuniv : C ≠ univ := hfim ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos hfd hfinj
  set κ := koebeCovConst * ‖deriv f 0‖
  have hκ : 0 < κ := mul_pos koebeCovConst_pos
    (norm_pos_iff.2 (QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd hfinj hball0))
  have hdist : ∀ ζ ∈ ball (0 : ℂ) 1,
      κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp) ≤ infDist (f ζ) (frontier C) := by
    intro ζ hζ
    have := koebe_mul_pow_le_infDist hfd hfinj hζ
    rw [hfim] at this
    exact this.trans (infDist_compl_le_infDist_frontier hCo hCne hCuniv _)
  set ε₀ : ℝ := 1 / (4 * (1 + koebeDistExp))
  have hε₀ : 0 < ε₀ := by have := koebeDistExp_pos; positivity
  obtain ⟨Cε, hCε⟩ := hgrowth ε₀ hε₀
  have hHgrowth : ∀ ζ ∈ ball (0 : ℂ) 1,
      |H (f ζ)| ≤ |Cε| * (1 + κ ^ (-ε₀)) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
    intro ζ hζ
    have hr : 0 < 1 - ‖ζ‖ := by have := mem_ball_zero_iff.1 hζ; linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hpow0 : 0 < κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp) := by positivity
    have h1 : infDist (f ζ) (frontier C) ^ (-ε₀) ≤
        (κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp)) ^ (-ε₀) :=
      Real.rpow_le_rpow_of_nonpos hpow0 (hdist ζ hζ) (by linarith)
    have h2 : (κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp)) ^ (-ε₀) =
        κ ^ (-ε₀) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.mul_rpow hκ.le (by positivity), ← Real.rpow_mul hr.le]
      congr 2
      simp only [ε₀]
      have := koebeDistExp_pos
      field_simp
    have h3 : 1 ≤ (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
    have h4 := hCε (f ζ) (hfb.mapsTo hζ)
    have hκp : 0 ≤ κ ^ (-ε₀) := by positivity
    have hnn : 0 ≤ 1 + infDist (f ζ) (frontier C) ^ (-ε₀) := by
      have := Real.rpow_nonneg (infDist_nonneg (x := f ζ) (s := frontier C)) (-ε₀)
      linarith
    calc |H (f ζ)| ≤ Cε * (1 + infDist (f ζ) (frontier C) ^ (-ε₀)) := h4
      _ ≤ |Cε| * (1 + infDist (f ζ) (frontier C) ^ (-ε₀)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hnn
      _ ≤ |Cε| * (1 + κ ^ (-ε₀) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ))) := by
          gcongr; rw [← h2]; exact h1
      _ ≤ |Cε| * ((1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) + κ ^ (-ε₀) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ))) := by
          gcongr
      _ = |Cε| * (1 + κ ^ (-ε₀)) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by ring
  set C' := |Cε| * (1 + κ ^ (-ε₀)) + |M|
  have hugrowth : ∀ ζ ∈ ball (0 : ℂ) 1,
      |H (f ζ) - v (f ζ)| ≤ C' * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
    intro ζ hζ
    have hr : 0 < 1 - ‖ζ‖ := by have := mem_ball_zero_iff.1 hζ; linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hP : 1 ≤ (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
    have hvz : |v (f ζ)| ≤ |M| * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) :=
      ((hvb _ (hfb.mapsTo hζ)).trans (le_abs_self M)).trans
        (le_mul_of_one_le_right (abs_nonneg _) hP)
    calc |H (f ζ) - v (f ζ)| ≤ |H (f ζ)| + |v (f ζ)| := abs_sub _ _
      _ ≤ _ := add_le_add (hHgrowth ζ hζ) hvz
      _ = C' * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by simp only [C']; ring
  have hu := harmonicOnNhd_comp_sub ⟨hfd, hfb⟩ hH hv
  set E' : Finset ℂ := hE.toFinset.filter (fun p => ‖p‖ = 1)
  have hE' : ∀ p ∈ E', ‖p‖ = 1 := fun p hp => (Finset.mem_filter.1 hp).2
  have hbd' : ∀ q : ℂ, ‖q‖ = 1 → q ∉ E' →
      Tendsto (fun ζ => H (f ζ) - v (f ζ)) (𝓝[ball (0 : ℂ) 1] q) (𝓝 0) := by
    intro q hq hqE
    refine hbd q (mem_sphere_zero_iff_norm.2 hq) fun hqE' => hqE ?_
    exact Finset.mem_filter.2 ⟨hE.mem_toFinset.2 hqE', hq⟩
  have h0 := eqOn_zero_of_growth hu hE' (by norm_num) (by norm_num) hugrowth hbd'
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hfb.surjOn hz
  have := h0 ζ hζ
  linarith

end InteractingSLE.WangWu
