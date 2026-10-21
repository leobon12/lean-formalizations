import SmallGammaGeodesics.Variance.FourKernel
import SmallGammaGeodesics.Variance.Clock
import GaussianLQG.Metric.Geodesic

/-!
# Lemma 3.1′ (packet P-A4)

Source: `source/small-parameter-lqg-geodesics.pdf`, §3, Lemma 3.1, (3.1)–(3.2). Mathematics:
planning audit GA2, "Details for later use", D1 (Lemma 3.1′, corrected statement and proof), with
the statement of GA2 Details (c) and the frozen `maxDev` for `heightDev`.

**Lemma 3.1′.** Let `d : ℂ × ℂ → ℝ` be any function and `0 ≤ Δ ≤ 1/100` with
`|d(z,w) - |z-w|| ≤ Δ` for `|z|, |w| ≤ 3`; let `η ∈ C([0,1], ℂ)` with `η 0 = 0`, `η 1 = 1` and
`d(η s, η t) = |t - s| d(0,1)`; and let `μ = lengthMeasure η` satisfy `μ(B_u(z)) ≤ A u^s` for all
`z` and `0 < u ≤ 1` (`A > 0`, `0 < s ≤ 1`). Then `μ` is regular and
`‖μ - λ‖_G² ≤ 66 M + (66 + 2/s) Δ (1 + log⁺ A + |log Δ|)`, `M = maxDev η` (`lemma31`).

Proof (GA2 D1): `|η t - t| ≤ r := 2(M + Δ) ≤ 0.82` (`ApproxGeod.norm_sub_le_two_mul`,
`ApproxGeod.maxDev_le_two_fifths`); first/last visit gives `μ(B_u(z)) ≤ 3u + 2Δ`
(`ApproxGeod.lengthMeasure_ball_le`); the four-kernel lemma with `c₁ = 3`, `c₂ = 2`
(`energyDistSq_pathMeasure_le`) and `2 + 16 log 2 + 17π/8 + 3 ≤ 33`,
`log⁺(1/(2Δ)) ≤ |log Δ|`. If `r = 0` then `η t = t` and `μ = λ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Real

namespace SmallGammaGeodesics

open GaussianLQG

/-- First/last visit (no metric needed): if `tmin`, `tmax` are the first and last times at which
`η` visits the closed set `F`, then `ν_η(F) ≤ tmax - tmin`. -/
theorem lengthMeasure_toReal_le_of_isLeast_isGreatest (η : C(unitInterval, ℂ)) {F : Set ℂ}
    (hF : IsClosed F) {tmin tmax : unitInterval} (hmin : IsLeast (η ⁻¹' F) tmin)
    (hmax : IsGreatest (η ⁻¹' F) tmax) :
    (lengthMeasure η F).toReal ≤ (tmax : ℝ) - tmin := by
  have hle : (tmin : ℝ) ≤ tmax := hmin.2 hmax.1
  refine ENNReal.toReal_le_of_le_ofReal (sub_nonneg.2 hle) ?_
  rw [lengthMeasure_apply η hF.measurableSet, ← Real.volume_Icc]
  refine measure_mono fun t ht => ?_
  obtain ⟨htF, ht01⟩ := ht
  have hmem : (⟨t, ht01⟩ : unitInterval) ∈ η ⁻¹' F := by
    simpa only [mem_preimage, projIcc_of_mem _ ht01] using htF
  exact ⟨Subtype.coe_le_coe.2 (hmin.2 hmem), Subtype.coe_le_coe.2 (hmax.2 hmem)⟩

namespace ApproxGeod

variable {d : ℂ × ℂ → ℝ} {η : C(unitInterval, ℂ)} {Δ : ℝ}

/-- **GA2 D1 (vi), first/last visit**: `μ(B_u(z)) ≤ (2u + Δ)/(1 - Δ) ≤ 3u + 2Δ`. -/
theorem lengthMeasure_ball_le (h : ApproxGeod d η Δ) (z : ℂ) {u : ℝ} (hu : 0 < u) :
    (lengthMeasure η (ball z u)).toReal ≤ 3 * u + 2 * Δ := by
  have hmono : (lengthMeasure η (ball z u)).toReal ≤ (lengthMeasure η (closedBall z u)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ball_subset_closedBall)
  by_cases hne : (closedBall z u ∩ range η).Nonempty
  · obtain ⟨tmin, tmax, hmin, hmax⟩ :=
      exists_isLeast_isGreatest_preimage η isClosed_closedBall hne
    have hle := lengthMeasure_toReal_le_of_isLeast_isGreatest η isClosed_closedBall hmin hmax
    have hlt : (tmin : ℝ) ≤ tmax := hmin.2 hmax.1
    have hgeo := h.geod tmin tmax
    rw [abs_of_nonneg (sub_nonneg.2 hlt)] at hgeo
    have herr := h.err (η tmin) (η tmax) (h.norm_le_three tmin) (h.norm_le_three tmax)
    have hdist : ‖η tmin - η tmax‖ ≤ 2 * u := by
      have h1 : dist (η tmin) z ≤ u := hmin.1
      have h2 : dist (η tmax) z ≤ u := hmax.1
      rw [← dist_eq_norm]
      linarith [dist_triangle_right (η tmin) (η tmax) z]
    have hx0 : 0 ≤ (tmax : ℝ) - tmin := sub_nonneg.2 hlt
    have hx1 : (tmax : ℝ) - tmin ≤ 1 := by linarith [tmax.2.2, tmin.2.1]
    have h3 : ((tmax : ℝ) - tmin) * d (0, 1) ≤ 2 * u + Δ := by
      rw [← hgeo]
      linarith [(abs_le.1 herr).2]
    have h4 : ((tmax : ℝ) - tmin) * (1 - Δ) ≤ ((tmax : ℝ) - tmin) * d (0, 1) :=
      mul_le_mul_of_nonneg_left h.le_d01 hx0
    have h5 : ((tmax : ℝ) - tmin) * Δ ≤ 1 * Δ := mul_le_mul_of_nonneg_right hx1 h.nonneg
    calc (lengthMeasure η (ball z u)).toReal ≤ (tmax : ℝ) - tmin := hmono.trans hle
      _ ≤ 3 * u + 2 * Δ := by nlinarith
  · have h0 : lengthMeasure η (closedBall z u) = 0 :=
      measure_mono_null (fun x hx hxr => hne ⟨x, hx, hxr⟩) (lengthMeasure_compl_range η)
    rw [h0, ENNReal.toReal_zero] at hmono
    linarith [h.nonneg]

/-- Under a Frostman bound `μ(B_u(z)) ≤ A u^s` (`s > 0`), the length measure of an approximate
geodesic is regular (it is supported in `B̄₂(0)`). -/
theorem isRegular_lengthMeasure (h : ApproxGeod d η Δ) {A s : ℝ} (hs : 0 < s)
    (hfr : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → (lengthMeasure η (ball u r)).toReal ≤ A * r ^ s) :
    IsRegular (lengthMeasure η) := by
  rw [lengthMeasure_eq_pathMeasure] at hfr ⊢
  exact isRegular_pathMeasure (continuous_comp_projIcc η).measurable (R := 2) hs
    (fun t _ => (h.norm_lt_two _).le) hfr

/-- `|η(t) - t| ≤ 2(M + Δ)` for the parametrization `t ↦ η(proj t)` on `[0,1]`. -/
theorem norm_comp_projIcc_sub_le (h : ApproxGeod d η Δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖η (projIcc 0 1 zero_le_one t) - t‖ ≤ 2 * (maxDev η + Δ) := by
  have := h.norm_sub_le_two_mul ⟨t, ht⟩
  rwa [projIcc_of_mem zero_le_one ht]

end ApproxGeod

/-- `log⁺(1/(2Δ)) ≤ |log Δ|` for `0 ≤ Δ ≤ 1`. -/
theorem posLog_one_div_two_mul_le {Δ : ℝ} (hΔ0 : 0 ≤ Δ) :
    log⁺ (1 / (2 * Δ)) ≤ |Real.log Δ| := by
  rcases hΔ0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero, div_zero, Real.posLog_zero]
    exact abs_nonneg _
  rw [Real.posLog_apply]
  refine max_le (abs_nonneg _) ?_
  calc Real.log (1 / (2 * Δ)) ≤ Real.log (1 / Δ) :=
        Real.log_le_log (by positivity) (one_div_le_one_div_of_le hpos (by linarith))
    _ = -Real.log Δ := by rw [one_div, Real.log_inv]
    _ ≤ |Real.log Δ| := neg_le_abs _

/-- `2 + 16 log 2 + 17π/8 + 3 ≤ 33` (`log 2 ≤ 1`, `π ≤ 4`). -/
theorem lemma31_const_le : 2 + 16 * Real.log 2 + 17 / 8 * π + 3 ≤ 33 := by
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
    linarith
  linarith [Real.pi_le_four]

/-- **Lemma 3.1′** (GA2 D1 and Details (c), with the frozen `maxDev` for `heightDev` and the
explicit constant `C₀ = 66`). Deterministic: `d` is any function (no metric axioms are used), `η`
a constant-speed `d`-geodesic from `0` to `1`, `Δ ≤ 1/100` the additive Euclidean error of `d` on
`B̄₃(0)`, and `A r^s` a Frostman bound for the occupation measure. -/
theorem lemma31 :
    ∀ (d : ℂ × ℂ → ℝ) (η : C(unitInterval, ℂ)) (Δ A s : ℝ),
      0 ≤ Δ → Δ ≤ 1 / 100 → 0 < s → s ≤ 1 → 0 < A →
      (∀ z w : ℂ, ‖z‖ ≤ 3 → ‖w‖ ≤ 3 → |d (z, w) - ‖z - w‖| ≤ Δ) →
      η 0 = 0 → η 1 = 1 →
      (∀ s t : unitInterval, d (η s, η t) = |(t : ℝ) - s| * d (0, 1)) →
      (∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → (lengthMeasure η (ball u r)).toReal ≤ A * r ^ s) →
      IsRegular (lengthMeasure η) ∧
        energyDistSq (lengthMeasure η) (segMeasure 0 1) ≤
          66 * maxDev η + (66 + 2 / s) * Δ * (1 + log⁺ A + |Real.log Δ|) := by
  intro d η Δ A s hΔ0 hΔ hs _ hA hd h0 h1 hgeo hfr
  have h : ApproxGeod d η Δ := ⟨hΔ0, hΔ, hd, h0, h1, hgeo⟩
  have hreg : IsRegular (lengthMeasure η) := h.isRegular_lengthMeasure hs hfr
  refine ⟨hreg, ?_⟩
  set M := maxDev η with hM_def
  set B := 1 + log⁺ A + |Real.log Δ| with hB_def
  have hM0 : 0 ≤ M := maxDev_nonneg η
  have hB1 : 1 ≤ B := by
    rw [hB_def]
    linarith [Real.posLog_nonneg (x := A), abs_nonneg (Real.log Δ)]
  have hRHS : 0 ≤ 66 * M + (66 + 2 / s) * Δ * B := by positivity
  set P : ℝ → ℂ := fun t => η (projIcc 0 1 zero_le_one t) with hP_def
  have hPc : Continuous P := continuous_comp_projIcc η
  set r := 2 * (M + Δ) with hr_def
  have hdisp : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t - t‖ ≤ r := fun t ht =>
    h.norm_comp_projIcc_sub_le ht
  rcases (show 0 ≤ r by positivity).eq_or_lt with hr0 | hrpos
  · -- `r = 0`: then `η t = t` on `[0,1]` and `μ = λ`
    have hP : ∀ t ∈ Icc (0 : ℝ) 1, P t = Complex.ofReal t := fun t ht => by
      have := hdisp t ht
      rw [← hr0] at this
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    rw [lengthMeasure_eq_pathMeasure, segMeasure_zero_one_eq_pathMeasure, pathMeasure_congr hP,
      energyDistSq_self]
    exact hRHS
  · -- `r > 0`: the four-kernel lemma with `c₁ = 3`, `c₂ = 2`
    have hr1 : r ≤ 1 := by
      have := h.maxDev_le_two_fifths
      rw [hr_def]
      linarith
    have hball : ∀ z : ℂ, ∀ u : ℝ, 0 < u → u ≤ 1 →
        ((pathMeasure P) (ball z u)).toReal ≤ min (A * u ^ s) (3 * u + 2 * Δ) := by
      intro z u hu hu1
      rw [← lengthMeasure_eq_pathMeasure]
      exact le_min (hfr z u hu hu1) (h.lengthMeasure_ball_le z hu)
    have hreg' : IsRegular (pathMeasure P) := hreg
    have hFK := energyDistSq_pathMeasure_le hPc.measurable hreg' hrpos hr1 hA.le hs
      (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 2) hΔ0 hdisp hball
    rw [lengthMeasure_eq_pathMeasure]
    refine hFK.trans ?_
    have e1 : (2 + 16 * Real.log 2 + 17 / 8 * π + 3) * r ≤ 33 * r :=
      mul_le_mul_of_nonneg_right lemma31_const_le hrpos.le
    have e2 : 2 * Δ / s * (1 + log⁺ A + log⁺ (1 / (2 * Δ))) ≤ 2 * Δ / s * B := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hB_def]
      linarith [posLog_one_div_two_mul_le hΔ0]
    have e3 : 66 * Δ ≤ 66 * Δ * B := by nlinarith
    calc (2 + 16 * Real.log 2 + 17 / 8 * π + 3) * r +
          2 * Δ / s * (1 + log⁺ A + log⁺ (1 / (2 * Δ)))
        ≤ 33 * r + 2 * Δ / s * B := add_le_add e1 e2
      _ = 66 * M + 66 * Δ + 2 / s * Δ * B := by rw [hr_def]; ring
      _ ≤ 66 * M + 66 * Δ * B + 2 / s * Δ * B := by linarith
      _ = 66 * M + (66 + 2 / s) * Δ * B := by ring

/-- **Lemma 3.1′ in the existential form of GA2 Details (c)** (`C₀ = 66`). -/
theorem lemma31_exists :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (d : ℂ × ℂ → ℝ) (η : C(unitInterval, ℂ)) (Δ A s : ℝ),
      0 ≤ Δ → Δ ≤ 1 / 100 → 0 < s → s ≤ 1 → 0 < A →
      (∀ z w : ℂ, ‖z‖ ≤ 3 → ‖w‖ ≤ 3 → |d (z, w) - ‖z - w‖| ≤ Δ) →
      η 0 = 0 → η 1 = 1 →
      (∀ s t : unitInterval, d (η s, η t) = |(t : ℝ) - s| * d (0, 1)) →
      (∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → (lengthMeasure η (ball u r)).toReal ≤ A * r ^ s) →
      IsRegular (lengthMeasure η) ∧
        energyDistSq (lengthMeasure η) (segMeasure 0 1) ≤
          C₀ * maxDev η + (C₀ + 2 / s) * Δ * (1 + log⁺ A + |Real.log Δ|) :=
  ⟨66, by norm_num, lemma31⟩

end SmallGammaGeodesics
