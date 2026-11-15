/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.GrowthMaximal
import InteractingSLE.Frozen.Spec.IsHarmonicDistOn
import InteractingSLE.WangWu.Singular

/-!
# Lemma 4.6: logarithmic growth of local-set means (Wang–Wu, §4.2)

Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.2, Lemma 4.6
(text dump lines 1060–1124): "Let `F = h_D + F₀` be a GFF in a bounded planar domain, with bounded
harmonic mean. Let `A` be any local set and let `H_A` be its conditional mean distribution, harmonic
off `A`. There is an almost surely finite random constant `C_A` such that
`|H_A(z)| ≤ C_A (1 + log(1/dist(z, A ∪ ∂D)))` whenever `z ∈ D \ A` and its distance from `A ∪ ∂D`
is at most a fixed small constant. A bounded-window version holds in `ℍ`."

This file proves the bounded-window version in `ℍ` for the zero-boundary GFF `h` (the setting of
the frozen local sets, ruling R19 (5)). The hypotheses are exactly the two properties of `H_A` that
the source's proof uses: `H_A(ψ) = E[h(ψ) | 𝒜]` for every test function `ψ` (the conditional mean;
`𝒜` is any sub-σ-algebra, e.g. that of the local set), and that `H_A` is given on `ℍ \ A` by a
harmonic function `v`; locality of `A` is not needed beyond these. The conclusion holds for every
harmonic representative `v` and with `dist(z, A ∪ ∂ℍ) = infDist z (ℍ \ A)ᶜ ≤ 1`.

## Proof (as in the source)

* (*) `|F_n(z)| ≤ S (n + 1)` for all admissible rational centres, `S` integrable
  (`InteractingSLE.WangWu.lintegral_windowSup_lt_top`);
* on `B̄(z, 2^{-n}) ⊂ ℍ \ A`, radial averaging gives `H_A(z) = h₁(bump)/(4^{-n} m) = E[F_n(z) | 𝒜]`,
  and conditional Jensen gives `|H_A(z)| ≤ (n + 1) E[S | 𝒜]`, simultaneously for all rational
  centres and scales off one null set;
* continuity of `v` extends this to every centre; choosing `2^{-n} ≍ dist(z, A ∪ ∂ℍ)/8` gives the
  logarithm.

## Main results

* `ae_abs_condExp_le_of_abs_le`: conditional Jensen in the form `|E[X|𝒜]| ≤ E[Y|𝒜]` for `|X| ≤ Y`;
* `abs_le_log_of_window_bound`: the deterministic last step (bumps at rational centres → all
  centres → the logarithm);
* `ae_window_bound_of_condMean`, `ae_window_bound_of_condMean_add`: the simultaneous conditional
  bound `|h₁(φ_{n,z})| ≤ (n + 1) E[S | 𝒜] (+ M_F)`;
* `ae_abs_le_log_of_condMean` (**Lemma 4.6**, bounded window in `ℍ`), its bounded-mean version
  `ae_abs_le_log_of_condMean_add` (`F = h + F₀`, `|F₀| ≤ M_F`), and
  `ae_exists_abs_le_log_of_condMean` (with the harmonic representative);
* `eqOn_of_window_log_bound`, `ae_eqOn_of_condMean`, `ae_eqOn_of_condMean_add`
  (**Corollary 4.8** for bounded components `C ⊆ ℍ \ A` with a Riemann map, from the
  deterministic core `eqOn_of_log_growth_of_tendsto` of `Singular.lean`).

Unbounded components are not covered: the window version controls `H_A` only on bounded sets,
and the source's reduction ("after mapping the ambient domain to a bounded one") needs the
conformal transport of the conditional-mean statement.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Real

namespace InteractingSLE.WangWu

open GFF (bumpFun bumpMass bumpMass_pos integral_mul_bumpFun_of_harmonic tsupport_bumpFun_subset)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Conditional Jensen for the absolute value**: if `|X| ≤ Y` a.s. with `Y` integrable and `X`
a.e. strongly measurable, then `|E[X | 𝒜]| ≤ E[Y | 𝒜]` a.s. -/
theorem ae_abs_condExp_le_of_abs_le {𝒜 : MeasurableSpace Ω} {X Y : Ω → ℝ} (hY : Integrable Y P)
    (hX : AEStronglyMeasurable[mΩ] X P) (hXY : ∀ᵐ ω ∂P, |X ω| ≤ Y ω) :
    ∀ᵐ ω ∂P, |P[X | 𝒜] ω| ≤ P[Y | 𝒜] ω := by
  have hXi : Integrable X P := hY.mono' hX (hXY.mono fun ω h => by rwa [Real.norm_eq_abs])
  have h1 : P[X | 𝒜] ≤ᵐ[P] P[Y | 𝒜] :=
    condExp_mono hXi hY (hXY.mono fun ω h => (le_abs_self _).trans h)
  have h2 : P[-X | 𝒜] ≤ᵐ[P] P[Y | 𝒜] :=
    condExp_mono hXi.neg hY (hXY.mono fun ω h => (neg_le_abs _).trans h)
  filter_upwards [h1, h2, condExp_neg X 𝒜] with ω h1 h2 h3
  rw [h3, Pi.neg_apply] at h2
  exact abs_le.2 ⟨by linarith, h1⟩

/-! ### Deterministic lemmas -/

lemma tsupport_windowTest_subset {R : ℝ} {s : Bool} {n : ℕ} {a b : ℚ}
    (hi : IsWindowIdx R n a b) :
    tsupport (windowTest R (s, n, a, b)) ⊆ closedBall (ratPt a b) (dyScale n) := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra hyc
  apply hy
  rw [windowTest_apply_of_isWindowIdx (i := (s, n, a, b)) hi,
    normBump_eq_zero (dyScale_pos n) (fun hb => hyc (ball_subset_closedBall hb)), mul_zero]

/-- The mean value of a harmonic function against the window test function. -/
lemma integral_mul_windowTest_of_harmonic {R : ℝ} {n : ℕ} {a b : ℚ} (hi : IsWindowIdx R n a b)
    {V : Set ℂ} (hV : IsOpen V) {v : ℂ → ℝ} (hv : InnerProductSpace.HarmonicOnNhd v V)
    (hB : closedBall (ratPt a b) (dyScale n) ⊆ V) :
    ∫ y, v y * windowTest R (true, n, a, b) y = v (ratPt a b) := by
  have hm := bumpMass_pos
  have hδ := dyScale_pos n
  have e : ∀ y, v y * windowTest R (true, n, a, b) y =
      (v y * bumpFun (ratPt a b) (dyScale n) y) / (dyScale n ^ 2 * bumpMass) := by
    intro y
    rw [windowTest_apply_of_isWindowIdx (i := (true, n, a, b)) hi, normBump]
    simp only [winSign, ite_true, one_mul]
    ring
  simp_rw [e]
  rw [integral_div, integral_mul_bumpFun_of_harmonic hV hv hδ hB]
  field_simp

lemma infDist_compl_le_im {U : Set ℂ} (hU : U ⊆ QuantumZipper.H) {z : ℂ} (hz : z ∈ QuantumZipper.H) :
    infDist z Uᶜ ≤ z.im := by
  have hre : ((z.re : ℝ) : ℂ) ∈ Uᶜ := fun h => by
    have := hU h
    simp [QuantumZipper.H] at this
  refine (infDist_le_dist_of_mem hre).trans ?_
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  have h0 : (0 : ℝ) < z.im := hz
  simp [abs_of_pos h0]

lemma mem_of_dist_lt_infDist {U : Set ℂ} {z w : ℂ} (h : dist w z < infDist z Uᶜ) : w ∈ U := by
  by_contra hw
  have := infDist_le_dist_of_mem (x := z) (show w ∈ Uᶜ from hw)
  rw [dist_comm] at this
  linarith

lemma exists_ratPt_near (z : ℂ) {r : ℝ} (hr : 0 < r) : ∃ a b : ℚ, ‖ratPt a b - z‖ < r := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - r / 2 < z.re + r / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - r / 2 < z.im + r / 2 by linarith)
  refine ⟨a, b, (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_⟩
  have e1 : (ratPt a b - z).re = a - z.re := rfl
  have e2 : (ratPt a b - z).im = b - z.im := rfl
  rw [e1, e2]
  have h1 : |(a : ℝ) - z.re| < r / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  have h2 : |(b : ℝ) - z.im| < r / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  linarith

/-- **The scale choice**: for `0 < d ≤ 1` there is `n` with `2^{-n} < d/4` and
`n + 1 ≤ 4 (1 + log(1/d))`. -/
lemma exists_scale {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ n : ℕ, dyScale n < d / 4 ∧ (n : ℝ) + 1 ≤ 4 * (1 + Real.log (1 / d)) := by
  classical
  have hex : ∃ m : ℕ, 4 / d < (2 : ℝ) ^ m := by
    obtain ⟨m, hm⟩ := exists_nat_gt (4 / d)
    exact ⟨m, hm.trans (by exact_mod_cast Nat.lt_two_pow_self)⟩
  set N := Nat.find hex with hN
  have hNspec : 4 / d < (2 : ℝ) ^ N := Nat.find_spec hex
  have h4d : 4 ≤ 4 / d := by rw [le_div_iff₀ hd]; linarith
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hNspec
    linarith
  have hprev : (2 : ℝ) ^ (N - 1) ≤ 4 / d :=
    not_lt.1 (Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos))
  have hpow : (2 : ℝ) ^ N ≤ 8 / d := by
    have : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)]
    rw [this]
    calc (2 : ℝ) * 2 ^ (N - 1) ≤ 2 * (4 / d) := by gcongr
      _ = 8 / d := by ring
  refine ⟨N, ?_, ?_⟩
  · have h2 : dyScale N = 1 / 2 ^ N := by rw [dyScale, inv_pow, one_div]
    rw [h2, div_lt_div_iff₀ (by positivity) (by norm_num)]
    rw [div_lt_iff₀ hd] at hNspec
    linarith
  · have hL : 0 ≤ Real.log (1 / d) := Real.log_nonneg (by rw [le_div_iff₀ hd]; linarith)
    have hlog := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_div (by norm_num) hd.ne',
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at hlog
    rw [one_div, Real.log_inv] at hL ⊢
    have hl2 := Real.log_two_gt_d9
    push_cast at hlog
    nlinarith

/-! ### Lemma 4.6: the deterministic last step -/

/-- **Deterministic last step of Lemma 4.6.** Let `U ⊆ ℍ` be open and `T` a functional on test
functions whose values at the window bumps of radius `|R| + 1` satisfy
`|T(φ_{n,z})| ≤ (n + 1) K + K'`. Then every harmonic `v` on `U` representing `T` on `U` satisfies
`|v(z)| ≤ 4 (|K| + |K'|) (1 + log(1/d(z)))` for `z ∈ U`, `|z| ≤ R`, `d(z) = dist(z, Uᶜ) ≤ 1`. -/
theorem abs_le_log_of_window_bound {R : ℝ} {U : Set ℂ} (hUo : IsOpen U)
    (hUH : U ⊆ QuantumZipper.H) {T : LQGMetric.TestOn upperHalfPlaneOpens → ℝ} {K K' : ℝ}
    (hT : ∀ (n : ℕ) (a b : ℚ), IsWindowIdx (|R| + 1) n a b →
      |T (windowTest (|R| + 1) (true, n, a, b))| ≤ ((n : ℝ) + 1) * K + K')
    {v : ℂ → ℝ} (hv : InnerProductSpace.HarmonicOnNhd v U)
    (hrep : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ U → T φ = ∫ z, v z * φ z)
    {z : ℂ} (hz : z ∈ U) (hzR : ‖z‖ ≤ R) (hd1 : infDist z Uᶜ ≤ 1) :
    |v z| ≤ 4 * (|K| + |K'|) * (1 + Real.log (1 / infDist z Uᶜ)) := by
  set R' : ℝ := |R| + 1 with hR'
  set d := infDist z Uᶜ with hd
  have hUc : Uᶜ.Nonempty := ⟨0, fun h0 => by
    have := hUH h0; simp [QuantumZipper.H] at this⟩
  have hd0 : 0 < d := (hUo.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h => h hz)
  obtain ⟨n, hnδ, hnlog⟩ := exists_scale hd0 hd1
  have hdim : d ≤ z.im := infDist_compl_le_im hUH (hUH hz)
  -- the bound at rational centres near `z`
  have hrat : ∀ a b : ℚ, ‖ratPt a b - z‖ < d / 4 → |v (ratPt a b)| ≤ ((n : ℝ) + 1) * K + K' := by
    intro a b hab
    have him : |(b : ℝ) - z.im| ≤ ‖ratPt a b - z‖ := Complex.abs_im_le_norm (ratPt a b - z)
    have hwin : IsWindowIdx R' n a b := by
      refine ⟨?_, ?_⟩
      · have := (abs_lt.1 (him.trans_lt hab)).1
        linarith
      · have := norm_le_norm_add_norm_sub' (ratPt a b) z
        linarith [le_abs_self R]
    have hball : closedBall (ratPt a b) (dyScale n) ⊆ U := by
      intro w hw
      refine mem_of_dist_lt_infDist (z := z) ?_
      rw [mem_closedBall] at hw
      have := dist_triangle w (ratPt a b) z
      rw [dist_eq_norm (ratPt a b) z] at this
      linarith
    have hval := hrep (windowTest R' (true, n, a, b))
      ((tsupport_windowTest_subset hwin).trans hball)
    rw [integral_mul_windowTest_of_harmonic hwin hUo hv hball] at hval
    rw [← hval]
    exact hT n a b hwin
  -- continuity of `v` at `z`
  have hcont : ContinuousAt v z := (hv z hz).1.continuousAt
  have hvz : |v z| ≤ ((n : ℝ) + 1) * K + K' := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨η, hη, hηv⟩ := Metric.continuousAt_iff.1 hcont ε hε
    obtain ⟨a, b, hab⟩ := exists_ratPt_near z (lt_min hη (by positivity : 0 < d / 4))
    have h1 := hηv (by rw [dist_eq_norm]; exact hab.trans_le (min_le_left _ _))
    have h2 := hrat a b (hab.trans_le (min_le_right _ _))
    rw [Real.dist_eq] at h1
    have h3 : |v z| ≤ |v (ratPt a b)| + |v (ratPt a b) - v z| := by
      have := abs_sub_abs_le_abs_sub (v z) (v (ratPt a b))
      rw [abs_sub_comm] at this
      linarith
    linarith
  have hL : 0 ≤ Real.log (1 / d) := Real.log_nonneg (by rw [le_div_iff₀ hd0]; linarith)
  have hn1 : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  calc |v z| ≤ ((n : ℝ) + 1) * K + K' := hvz
    _ ≤ ((n : ℝ) + 1) * (|K| + |K'|) := by
        nlinarith [le_abs_self K, le_abs_self K', abs_nonneg K, abs_nonneg K']
    _ ≤ (4 * (1 + Real.log (1 / d))) * (|K| + |K'|) :=
        mul_le_mul_of_nonneg_right hnlog (by positivity)
    _ = 4 * (|K| + |K'|) * (1 + Real.log (1 / d)) := by ring

/-! ### Lemma 4.6: the probabilistic step -/

/-- **The simultaneous conditional bound.** If `h₁(ψ) = E[h(ψ) | 𝒜]` for every test function,
then a.s., for every admissible rational window index, `|h₁(φ_{n,z})| ≤ (n + 1) E[S | 𝒜]`. -/
theorem ae_window_bound_of_condMean [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) {𝒜 : MeasurableSpace Ω}
    {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | 𝒜]) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (a b : ℚ), IsWindowIdx R n a b →
      |h₁ ω (windowTest R (true, n, a, b))| ≤
        ((n : ℝ) + 1) * P[fun ω => (windowSup h R ω).toReal | 𝒜] ω + 0 := by
  let _ : MeasurableSpace Ω := mΩ
  set S : Ω → ℝ := fun ω => (windowSup h R ω).toReal with hSdef
  have hS : Integrable S P := integrable_windowSup_toReal hh hR
  have hJ : ∀ᵐ ω ∂P, ∀ j : ℕ × ℚ × ℚ, IsWindowIdx R j.1 j.2.1 j.2.2 →
      |h₁ ω (windowTest R (true, j.1, j.2.1, j.2.2))| ≤ ((j.1 : ℝ) + 1) * P[S | 𝒜] ω := by
    rw [ae_all_iff]
    rintro ⟨n, a, b⟩
    by_cases hj : IsWindowIdx R n a b
    · have hX : ∀ᵐ ω ∂P, |h ω (windowTest R (true, n, a, b))| ≤ (((n : ℝ) + 1) • S) ω :=
        (ae_windowSup_lt_top hh hR).mono fun ω hω => by
          rw [Pi.smul_apply, smul_eq_mul]
          exact abs_windowField_le hω hj
      have hjen := ae_abs_condExp_le_of_abs_le (𝒜 := 𝒜) (hS.smul ((n : ℝ) + 1))
        (hh.process.measurable (windowTest R (true, n, a, b))).aestronglyMeasurable hX
      filter_upwards [hmean (windowTest R (true, n, a, b)), hjen,
        condExp_smul ((n : ℝ) + 1) S 𝒜] with ω h1 h2 h3
      intro _
      rw [h1]
      rw [h3, Pi.smul_apply, smul_eq_mul] at h2
      exact h2
    · exact ae_of_all _ fun ω hω => absurd hω hj
  filter_upwards [hJ] with ω hω n a b hi
  rw [add_zero]
  exact hω (n, a, b) hi

/-- The window bumps are probability densities: `|∫ F₀ φ_{n,z}| ≤ M` if `|F₀| ≤ M` on `ℍ`. -/
lemma abs_integral_mul_windowTest_le {R : ℝ} {n : ℕ} {a b : ℚ} (hi : IsWindowIdx R n a b)
    {F₀ : ℂ → ℝ} {M : ℝ} (hF₀ : ∀ z ∈ QuantumZipper.H, |F₀ z| ≤ M) :
    |∫ z, F₀ z * windowTest R (true, n, a, b) z| ≤ M := by
  have hm := bumpMass_pos
  have hδ := dyScale_pos n
  set φ := windowTest R (true, n, a, b)
  have hφ : ∀ y, φ y = bumpFun (ratPt a b) (dyScale n) y / (dyScale n ^ 2 * bumpMass) := by
    intro y
    rw [windowTest_apply_of_isWindowIdx (i := (true, n, a, b)) hi, normBump]
    simp only [winSign, ite_true, one_mul]
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => by
    rw [hφ]; exact div_nonneg (GFF.bumpFun_nonneg _ _ _) (by positivity)
  have hφi : Integrable (fun y => M * φ y) :=
    ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul M)
  have hint1 : ∫ y, φ y = 1 := by
    simp_rw [hφ]
    rw [integral_div, GFF.integral_bumpFun hδ]
    field_simp
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hφi (ae_of_all _ fun y => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ0 y)]
    by_cases hy : y ∈ QuantumZipper.H
    · exact mul_le_mul_of_nonneg_right (hF₀ y hy) (hφ0 y)
    · rw [φ.zero_on_compl hy, Pi.zero_apply, mul_zero, mul_zero]
  · rw [integral_const_mul, hint1, mul_one]

/-- **The simultaneous conditional bound with a bounded mean.** If the field is `h + F₀` with `h`
the zero-boundary GFF and `F₀` bounded by `M_F` on `ℍ`, and `h₁(ψ) = E[h(ψ) + ∫ F₀ ψ | 𝒜]`, then
a.s., for every admissible rational window index, `|h₁(φ_{n,z})| ≤ (n + 1) E[S | 𝒜] + M_F`. -/
theorem ae_window_bound_of_condMean_add [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) {𝒜 : MeasurableSpace Ω}
    (h𝒜 : 𝒜 ≤ mΩ) {F₀ : ℂ → ℝ} {MF : ℝ} (hF₀ : ∀ z ∈ QuantumZipper.H, |F₀ z| ≤ MF)
    {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ + ∫ z, F₀ z * φ z | 𝒜]) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (a b : ℚ), IsWindowIdx R n a b →
      |h₁ ω (windowTest R (true, n, a, b))| ≤
        ((n : ℝ) + 1) * P[fun ω => (windowSup h R ω).toReal | 𝒜] ω + MF := by
  let _ : MeasurableSpace Ω := mΩ
  -- the centred conditional mean
  have hc : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ - ∫ z, F₀ z * φ z) =ᵐ[P] P[fun ω => h ω φ | 𝒜] := by
    intro φ
    set c : ℝ := ∫ z, F₀ z * φ z
    have hXi : Integrable (fun ω => h ω φ) P :=
      (hh.process.gaussian.hasGaussianLaw_eval φ).integrable
    have hadd := condExp_add (m := 𝒜) hXi (integrable_const c)
    have hconst : P[fun _ : Ω => c | 𝒜] = fun _ => c := condExp_const h𝒜 c
    filter_upwards [hmean φ, hadd] with ω h1 h2
    rw [h1]
    change P[(fun ω => h ω φ) + fun _ => c | 𝒜] ω - c = _
    rw [h2, Pi.add_apply, hconst]
    ring
  -- apply the centred bound to `h₁ − F₀` evaluated on the window bumps
  set S : Ω → ℝ := fun ω => (windowSup h R ω).toReal with hSdef
  have hS : Integrable S P := integrable_windowSup_toReal hh hR
  have hJ : ∀ᵐ ω ∂P, ∀ j : ℕ × ℚ × ℚ, IsWindowIdx R j.1 j.2.1 j.2.2 →
      |h₁ ω (windowTest R (true, j.1, j.2.1, j.2.2))| ≤ ((j.1 : ℝ) + 1) * P[S | 𝒜] ω + MF := by
    rw [ae_all_iff]
    rintro ⟨n, a, b⟩
    by_cases hj : IsWindowIdx R n a b
    · have hX : ∀ᵐ ω ∂P, |h ω (windowTest R (true, n, a, b))| ≤ (((n : ℝ) + 1) • S) ω :=
        (ae_windowSup_lt_top hh hR).mono fun ω hω => by
          rw [Pi.smul_apply, smul_eq_mul]
          exact abs_windowField_le hω hj
      have hjen := ae_abs_condExp_le_of_abs_le (𝒜 := 𝒜) (hS.smul ((n : ℝ) + 1))
        (hh.process.measurable (windowTest R (true, n, a, b))).aestronglyMeasurable hX
      filter_upwards [hc (windowTest R (true, n, a, b)), hjen,
        condExp_smul ((n : ℝ) + 1) S 𝒜] with ω h1 h2 h3
      intro _
      rw [h3, Pi.smul_apply, smul_eq_mul, ← h1] at h2
      have h4 := abs_integral_mul_windowTest_le hj hF₀
      have h5 := abs_sub_abs_le_abs_sub (h₁ ω (windowTest R (true, n, a, b)))
        (∫ z, F₀ z * windowTest R (true, n, a, b) z)
      linarith
    · exact ae_of_all _ fun ω hω => absurd hω hj
  filter_upwards [hJ] with ω hω n a b hi
  exact hω (n, a, b) hi

/-! ### Lemma 4.6 -/

/-- **Lemma 4.6 (logarithmic growth of local-set means), bounded-window version in `ℍ`.** Let `h`
be the zero-boundary GFF on `ℍ`, `𝒜` a σ-algebra, `A` a random set with `ℍ \ A` a.s. open, and
`h₁` the conditional mean field: `h₁(ψ) = E[h(ψ) | 𝒜]` a.s. for every test function `ψ`. Then for
every window radius `R`, almost surely there is a finite constant `C` such that for every harmonic
function `v` on `ℍ \ A` representing `h₁` there, and every `z ∈ ℍ \ A` with `|z| ≤ R` and
`d(z) = dist(z, A ∪ ∂ℍ) ≤ 1`, `|v(z)| ≤ C (1 + log(1/d(z)))`. -/
theorem ae_abs_le_log_of_condMean [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (QuantumZipper.H \ A ω)) (R : ℝ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (QuantumZipper.H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ QuantumZipper.H \ A ω →
        h₁ ω φ = ∫ z, v z * φ z) →
      ∀ z ∈ QuantumZipper.H \ A ω, ‖z‖ ≤ R → infDist z (QuantumZipper.H \ A ω)ᶜ ≤ 1 →
        |v z| ≤ C * (1 + Real.log (1 / infDist z (QuantumZipper.H \ A ω)ᶜ)) := by
  filter_upwards [ae_window_bound_of_condMean hh hmean (R := |R| + 1) (by positivity), hopen]
    with ω hω hUo
  exact ⟨_, fun v hv hrep z hz hzR hd1 =>
    abs_le_log_of_window_bound hUo sdiff_subset hω hv hrep hz hzR hd1⟩

/-- **Lemma 4.6 for a field with bounded harmonic mean** (`F = h + F₀`, `|F₀| ≤ M_F` on `ℍ`):
if `h₁(ψ) = E[h(ψ) + ∫ F₀ ψ | 𝒜]` (the conditional mean of `F`), the same logarithmic bound
holds ("the bounded deterministic mean can be absorbed into the constants"). -/
theorem ae_abs_le_log_of_condMean_add [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) {F₀ : ℂ → ℝ} {MF : ℝ}
    (hF₀ : ∀ z ∈ QuantumZipper.H, |F₀ z| ≤ MF)
    {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ + ∫ z, F₀ z * φ z | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (QuantumZipper.H \ A ω)) (R : ℝ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (QuantumZipper.H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ QuantumZipper.H \ A ω →
        h₁ ω φ = ∫ z, v z * φ z) →
      ∀ z ∈ QuantumZipper.H \ A ω, ‖z‖ ≤ R → infDist z (QuantumZipper.H \ A ω)ᶜ ≤ 1 →
        |v z| ≤ C * (1 + Real.log (1 / infDist z (QuantumZipper.H \ A ω)ᶜ)) := by
  filter_upwards [ae_window_bound_of_condMean_add hh h𝒜 hF₀ hmean (R := |R| + 1) (by positivity),
    hopen] with ω hω hUo
  exact ⟨_, fun v hv hrep z hz hzR hd1 =>
    abs_le_log_of_window_bound hUo sdiff_subset hω hv hrep hz hzR hd1⟩

/-- **Lemma 4.6, with the representative.** If moreover `h₁` is a.s. harmonic on `ℍ \ A`
(`IsHarmonicDistOn`), then a.s. there are a harmonic representative `v` of `h₁` on `ℍ \ A` and a
finite constant `C` with `|v(z)| ≤ C (1 + log(1/d(z)))` for `|z| ≤ R`, `d(z) ≤ 1`. -/
theorem ae_exists_abs_le_log_of_condMean [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (QuantumZipper.H \ A ω))
    (hharm : ∀ᵐ ω ∂P, IsHarmonicDistOn (h₁ ω) (QuantumZipper.H \ A ω)) (R : ℝ) :
    ∀ᵐ ω ∂P, ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (QuantumZipper.H \ A ω) ∧
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ QuantumZipper.H \ A ω →
        h₁ ω φ = ∫ z, v z * φ z) ∧
      ∃ C : ℝ, ∀ z ∈ QuantumZipper.H \ A ω, ‖z‖ ≤ R → infDist z (QuantumZipper.H \ A ω)ᶜ ≤ 1 →
        |v z| ≤ C * (1 + Real.log (1 / infDist z (QuantumZipper.H \ A ω)ᶜ)) := by
  filter_upwards [ae_abs_le_log_of_condMean hh hmean hopen R, hharm] with ω hω hH
  obtain ⟨C, hC⟩ := hω
  obtain ⟨v, hv, hrep⟩ := hH
  exact ⟨v, hv, hrep, C, hC v hv hrep⟩

/-! ### Corollary 4.8 (identification of a component mean) -/

/-- For `z` in an open set `C`, the distance to the frontier is at most the distance to the
complement (a segment from `z` to a point of `Cᶜ` crosses the frontier). -/
lemma infDist_frontier_le_infDist_compl {C : Set ℂ} (hCo : IsOpen C) {z : ℂ} (hz : z ∈ C)
    (hne : Cᶜ.Nonempty) : infDist z (frontier C) ≤ infDist z Cᶜ := by
  refine (le_infDist hne).2 fun w hw => ?_
  by_contra hlt
  push Not at hlt
  have hseg : ∀ p ∈ segment ℝ z w, dist z p ≤ dist z w := by
    intro p hp
    have := (convex_closedBall z (dist z w)).segment_subset (mem_closedBall_self dist_nonneg)
      (by rw [mem_closedBall, dist_comm]) hp
    rw [mem_closedBall, dist_comm] at this
    exact this
  have hdisj : ∀ p ∈ segment ℝ z w, p ∉ frontier C := fun p hp hpf => by
    have h2 := infDist_le_dist_of_mem hpf (x := z)
    linarith [hseg p hp]
  have hcov : segment ℝ z w ⊆ C ∪ (closure C)ᶜ := by
    intro p hp
    by_cases hpC : p ∈ C
    · exact Or.inl hpC
    · refine Or.inr fun hcl => hdisj p hp ⟨hcl, ?_⟩
      rwa [hCo.interior_eq]
  have hwC : w ∈ (closure C)ᶜ := fun hcl => hdisj w (right_mem_segment ℝ z w) ⟨hcl, by
    rw [hCo.interior_eq]; exact hw⟩
  obtain ⟨p, -, hpC, hpC'⟩ := (convex_segment z w).isPreconnected C (closure C)ᶜ hCo
    isClosed_closure.isOpen_compl hcov ⟨z, left_mem_segment ℝ z w, hz⟩
    ⟨w, right_mem_segment ℝ z w, hwC⟩
  exact hpC' (subset_closure hpC)

/-- **Corollary 4.8, deterministic form.** Let `U ⊆ ℍ` be open and `H'` harmonic on `U` with the
logarithmic growth of Lemma 4.6 in every window. If `C ⊆ U` is a bounded open set with a Riemann
map `f : 𝔻 → C` and `v` is a bounded harmonic function on `C` with `H' ∘ f − v ∘ f → 0` at every
circle point outside a finite set, then `H' = v` on `C`. -/
theorem eqOn_of_window_log_bound {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ QuantumZipper.H)
    {H' : ℂ → ℝ} (hH' : InnerProductSpace.HarmonicOnNhd H' U)
    (hlog : ∀ R : ℕ, ∃ C₀ : ℝ, ∀ z ∈ U, ‖z‖ ≤ R → infDist z Uᶜ ≤ 1 →
      |H' z| ≤ C₀ * (1 + Real.log (1 / infDist z Uᶜ)))
    {C : Set ℂ} (hCo : IsOpen C) (hCU : C ⊆ U) (hCb : Bornology.IsBounded C) {f : ℂ → ℂ}
    (hf : SupercriticalConformalCovariance.IsConformalBijection f (ball 0 1) C) {v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v C) (hvb : ∃ M, ∀ z ∈ C, |v z| ≤ M) {E : Set ℂ}
    (hE : E.Finite)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      Tendsto (fun ζ => H' (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) :
    EqOn H' v C := by
  obtain ⟨M, hM⟩ := hvb
  obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hCb
  obtain ⟨R, hR⟩ := exists_nat_ge R₀
  obtain ⟨C₀, hC₀⟩ := hlog R
  have hUc : Uᶜ.Nonempty := ⟨0, fun h0 => by
    have := hUH h0; simp [QuantumZipper.H] at this⟩
  -- boundedness of `H'` away from `Uᶜ` inside the window
  set K : Set ℂ := closedBall 0 R ∩ {z | 1 ≤ infDist z Uᶜ} with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 (R : ℝ)).inter_right
    (isClosed_le continuous_const (continuous_infDist_pt _))
  have hKU : K ⊆ U := fun z hz => by
    by_contra hzU
    have := infDist_zero_of_mem (show z ∈ Uᶜ from hzU)
    linarith [hz.2.out]
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn
    (fun z hz => (hH' z (hKU hz)).1.continuousAt.continuousWithinAt)
  refine eqOn_of_log_growth_of_tendsto hCo hf (fun z hz => hH' z (hCU hz)) hv hM
    (K := |C₀| + |B|) ?_ hE hbd
  intro z hz
  have hzU := hCU hz
  have hzR : ‖z‖ ≤ R := by
    have := hR₀ hz
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hCc : Cᶜ.Nonempty := hUc.mono (compl_subset_compl.2 hCU)
  have hd0 : 0 < infDist z Uᶜ :=
    (hUo.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h => h hzU)
  have hfr0 : 0 < infDist z (frontier C) := by
    have hfrne : (frontier C).Nonempty := by
      refine nonempty_frontier_iff.2 ⟨⟨z, hz⟩, fun huniv => ?_⟩
      obtain ⟨w, hw⟩ := hCc
      exact hw (huniv ▸ mem_univ w)
    exact (isClosed_frontier.notMem_iff_infDist_pos hfrne).1
      (fun hf' => (hCo.inter_frontier_eq.subset ⟨hz, hf'⟩ : z ∈ (∅ : Set ℂ)))
  have hdle : infDist z (frontier C) ≤ infDist z Uᶜ :=
    (infDist_frontier_le_infDist_compl hCo hz hCc).trans
      (infDist_le_infDist_of_subset (compl_subset_compl.2 hCU) hUc)
  have hlog1 : 0 ≤ Real.log (1 + (infDist z (frontier C))⁻¹) :=
    Real.log_nonneg (by linarith [inv_pos.2 hfr0])
  by_cases hd1 : infDist z Uᶜ ≤ 1
  · have h1 := hC₀ z hzU hzR hd1
    have h2 : Real.log (1 / infDist z Uᶜ) ≤ Real.log (1 + (infDist z (frontier C))⁻¹) := by
      refine Real.log_le_log (by positivity) ?_
      rw [one_div]
      linarith [inv_anti₀ hfr0 hdle]
    have hL : 0 ≤ Real.log (1 / infDist z Uᶜ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hd0]; linarith)
    calc |H' z| ≤ C₀ * (1 + Real.log (1 / infDist z Uᶜ)) := h1
      _ ≤ |C₀| * (1 + Real.log (1 + (infDist z (frontier C))⁻¹)) := by
          refine (mul_le_mul_of_nonneg_right (le_abs_self C₀) (by linarith)).trans ?_
          gcongr
      _ ≤ (|C₀| + |B|) * (1 + Real.log (1 + (infDist z (frontier C))⁻¹)) := by
          gcongr; linarith [abs_nonneg B]
  · push Not at hd1
    have hzK : z ∈ K := ⟨by rw [mem_closedBall, dist_zero_right]; exact hzR, hd1.le⟩
    calc |H' z| ≤ B := by have := hB z hzK; rwa [Real.norm_eq_abs] at this
      _ ≤ |B| := le_abs_self B
      _ ≤ (|C₀| + |B|) * 1 := by linarith [abs_nonneg C₀]
      _ ≤ (|C₀| + |B|) * (1 + Real.log (1 + (infDist z (frontier C))⁻¹)) := by
          gcongr; linarith

/-- **Corollary 4.8 (identification of a component mean)**, for bounded components. Under the
hypotheses of Lemma 4.6, almost surely the following holds for every harmonic representative `H'`
of the conditional mean on `ℍ \ A`: if `C ⊆ ℍ \ A` is a bounded open set with a Riemann map
`f : 𝔻 → C`, and `v` is a bounded harmonic function on `C` such that `H' ∘ f − v ∘ f → 0` at
every boundary point of the disc outside a finite set (the finitely many exceptional prime ends),
then `H' = v` on `C`. -/
theorem ae_eqOn_of_condMean [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (QuantumZipper.H \ A ω)) :
    ∀ᵐ ω ∂P, ∀ H' : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd H' (QuantumZipper.H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ QuantumZipper.H \ A ω →
        h₁ ω φ = ∫ z, H' z * φ z) →
      ∀ C : Set ℂ, IsOpen C → C ⊆ QuantumZipper.H \ A ω → Bornology.IsBounded C →
      ∀ f : ℂ → ℂ, SupercriticalConformalCovariance.IsConformalBijection f (ball 0 1) C →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v C → (∃ M, ∀ z ∈ C, |v z| ≤ M) →
      ∀ E : Set ℂ, E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => H' (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) →
      EqOn H' v C := by
  filter_upwards [ae_all_iff.2 fun R : ℕ => ae_abs_le_log_of_condMean hh hmean hopen R, hopen]
    with ω hω hUo
  intro H' hH' hrep C hCo hCU hCb f hf v hv hvb E hE hbd
  refine eqOn_of_window_log_bound hUo sdiff_subset hH' (fun R => ?_) hCo hCU hCb hf hv hvb hE hbd
  obtain ⟨C₀, hC₀⟩ := hω R
  exact ⟨C₀, fun z hz hzR hd1 => hC₀ H' hH' hrep z hz hzR hd1⟩

/-- **Corollary 4.8 for a field with bounded harmonic mean** (`F = h + F₀`, `|F₀| ≤ M_F` on `ℍ`,
`h₁(ψ) = E[h(ψ) + ∫ F₀ ψ | 𝒜]`), for bounded components. -/
theorem ae_eqOn_of_condMean_add [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) {F₀ : ℂ → ℝ} {MF : ℝ}
    (hF₀ : ∀ z ∈ QuantumZipper.H, |F₀ z| ≤ MF)
    {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ + ∫ z, F₀ z * φ z | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (QuantumZipper.H \ A ω)) :
    ∀ᵐ ω ∂P, ∀ H' : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd H' (QuantumZipper.H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ QuantumZipper.H \ A ω →
        h₁ ω φ = ∫ z, H' z * φ z) →
      ∀ C : Set ℂ, IsOpen C → C ⊆ QuantumZipper.H \ A ω → Bornology.IsBounded C →
      ∀ f : ℂ → ℂ, SupercriticalConformalCovariance.IsConformalBijection f (ball 0 1) C →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v C → (∃ M, ∀ z ∈ C, |v z| ≤ M) →
      ∀ E : Set ℂ, E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => H' (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) →
      EqOn H' v C := by
  filter_upwards [ae_all_iff.2 fun R : ℕ =>
    ae_abs_le_log_of_condMean_add hh h𝒜 hF₀ hmean hopen R, hopen] with ω hω hUo
  intro H' hH' hrep C hCo hCU hCb f hf v hv hvb E hE hbd
  refine eqOn_of_window_log_bound hUo sdiff_subset hH' (fun R => ?_) hCo hCU hCb hf hv hvb hE hbd
  obtain ⟨C₀, hC₀⟩ := hω R
  exact ⟨C₀, fun z hz hzR hd1 => hC₀ H' hH' hrep z hz hzR hd1⟩

end InteractingSLE.WangWu
