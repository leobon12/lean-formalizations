/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.CapacityCutoff
import InteractingSLE.Spec.Sec6.PolarDisk
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Energy of the capacity cutoffs

Packet PROVE-SEC6-A2 (specification §6.1, proof of Aux. lemma 29, `source/spec/p145-192.md`,
pp. 164–165): "Direct integration of the radial derivative gives
`∫_ℂ |∇b_{j,r}|² = 2π / log(R/r)`, `∫_ℂ |∇b_r|² ≤ 2πN / log(R/r)`."

* `lintegral_comp_norm_eq`: polar coordinates for radial functions on `ℂ`;
* `lintegral_annulus_le`: `∫_{r ≤ |z − p| ≤ 1} |z − p|^{−2} = 2π log(1/r)` (upper bound form);
* `lintegral_logCutoffDeriv_le`: the single-point energy `∫ ‖D b_{p,r}‖² ≤ 18π D² / log(1/r)`;
* `capCutoff P r = 1 − ∏_{p ∈ P} (1 − b_{p,r})`: a `C¹` multi-point cutoff, `= 1` within `r` of
  `P`, values in `[0, 1]`, tending to `0` off `P` as `r → 0`, with energy
  `≤ |P|² · 18π D² / log(1/r)` (`lintegral_capCutoffDeriv_le`).

The source takes `b_r = max_j b_{j,r}` with the Sobolev chain rule for the maximum; the product form
used here is `C¹` and avoids the chain rule (its energy bound has `N²` instead of `N`, which is
immaterial: only `→ 0` is used).
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real ENNReal

namespace InteractingSLE.Sec6

/-! ## Radial integration -/

/-- **Polar coordinates for radial functions**: `∫_ℂ g(|z|) = 2π ∫₀^∞ ρ g(ρ) dρ`. -/
theorem lintegral_comp_norm_eq {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z : ℂ, g ‖z‖ = ENNReal.ofReal (2 * π) * ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * g ρ := by
  have h1 := Complex.lintegral_comp_polarCoord_symm (fun z => g ‖z‖)
  have ht : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  rw [← h1, ht, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • g ‖Complex.polarCoord.symm p‖ := by
    simp_rw [polarCoord_symm_eq_polarPt]
    exact (measurable_fst.ennreal_ofReal).smul (hg.comp (continuous_norm.measurable.comp
      measurable_polarPt))
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hin : ∀ ρ ∈ Ioi (0 : ℝ), (∫⁻ t in Ioo (-π) π, ENNReal.ofReal (ρ, t).1 •
      g ‖Complex.polarCoord.symm (ρ, t)‖) = ENNReal.ofReal (2 * π) * (ENNReal.ofReal ρ * g ρ) := by
    intro ρ hρ
    have hc : ∀ t : ℝ, ENNReal.ofReal (ρ, t).1 • g ‖Complex.polarCoord.symm (ρ, t)‖ =
        ENNReal.ofReal ρ * g ρ := by
      intro t
      rw [polarCoord_symm_eq_polarPt, norm_polarPt (le_of_lt hρ), smul_eq_mul]
    simp_rw [hc]
    rw [setLIntegral_const, Real.volume_Ioo, mul_comm, show π - -π = 2 * π by ring]
  rw [setLIntegral_congr_fun measurableSet_Ioi hin, lintegral_const_mul]
  exact measurable_id.ennreal_ofReal.mul hg

/-- The radial profile of the annulus integrand. -/
def annulusProfile (r : ℝ) (ρ : ℝ) : ℝ≥0∞ := (Icc r 1).indicator (fun ρ => ENNReal.ofReal (ρ ^ 2)⁻¹) ρ

theorem measurable_annulusProfile (r : ℝ) : Measurable (annulusProfile r) :=
  (Measurable.ennreal_ofReal ((measurable_id.pow_const 2).inv)).indicator measurableSet_Icc

/-- `∫₀^∞ ρ · 1_{[r,1]}(ρ) ρ^{−2} dρ = log(1/r)`. -/
theorem lintegral_Ioi_annulusProfile {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * annulusProfile r ρ = ENNReal.ofReal (-Real.log r) := by
  have hind : ∀ ρ : ℝ, ENNReal.ofReal ρ * annulusProfile r ρ =
      (Icc r 1).indicator (fun ρ => ENNReal.ofReal ρ⁻¹) ρ := by
    intro ρ
    unfold annulusProfile
    by_cases hρ : ρ ∈ Icc r 1
    · rw [indicator_of_mem hρ, indicator_of_mem hρ, ← ENNReal.ofReal_mul (by linarith [hρ.1])]
      congr 1
      have : 0 < ρ := lt_of_lt_of_le hr0 hρ.1
      field_simp
    · rw [indicator_of_notMem hρ, indicator_of_notMem hρ, mul_zero]
  simp_rw [hind]
  rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.2 (show Icc r 1 ⊆ Ioi 0 from fun ρ hρ => lt_of_lt_of_le hr0 hρ.1)]
  have hcont : ContinuousOn (fun ρ : ℝ => ρ⁻¹) (Icc r 1) :=
    continuousOn_inv₀.mono fun ρ hρ => (lt_of_lt_of_le hr0 hρ.1).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with ρ hρ
        exact inv_nonneg.2 (le_trans hr0.le hρ.1))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr1,
    integral_inv_of_pos hr0 one_pos, Real.log_div one_ne_zero hr0.ne', Real.log_one, zero_sub]

/-- **The annulus integral**: `∫_ℂ 1_{r ≤ |z − p| ≤ 1} |z − p|^{−2} = 2π log(1/r)`. -/
theorem lintegral_annulus_eq {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (p : ℂ) :
    ∫⁻ z : ℂ, annulusProfile r ‖z - p‖ = ENNReal.ofReal (2 * π * -Real.log r) := by
  rw [lintegral_sub_right_eq_self (fun z => annulusProfile r ‖z‖) p,
    lintegral_comp_norm_eq (measurable_annulusProfile r), lintegral_Ioi_annulusProfile hr0 hr1,
    ← ENNReal.ofReal_mul (by positivity)]

/-! ## Energy of a single cutoff -/

theorem ofReal_sq_logCutoffDeriv_le {D : ℝ} (hD : ∀ s, |deriv cutProfile s| ≤ D) {p : ℂ} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (z : ℂ) :
    ENNReal.ofReal (‖logCutoffDeriv p r z‖ ^ 2) ≤
      ENNReal.ofReal (9 * D ^ 2 / (-Real.log r) ^ 2) * annulusProfile r ‖z - p‖ := by
  have hL : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr0 hr1)
  by_cases hz : ‖z - p‖ ∈ Icc r 1
  · have hpos : 0 < ‖z - p‖ := lt_of_lt_of_le hr0 hz.1
    have hzp : z ≠ p := fun h => by rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos
    rw [annulusProfile, indicator_of_mem hz, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := norm_logCutoffDeriv_le hD hr0 hr1 hzp
    calc ‖logCutoffDeriv p r z‖ ^ 2 ≤ (D * (3 / (-Real.log r * ‖z - p‖))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = 9 * D ^ 2 / (-Real.log r) ^ 2 * (‖z - p‖ ^ 2)⁻¹ := by field_simp; ring
  · have hz' : ‖z - p‖ < r ∨ 1 < ‖z - p‖ := by
      simp only [mem_Icc, not_and_or, not_le] at hz; exact hz
    rw [logCutoffDeriv_eq_zero hr0 hr1 hz', norm_zero]
    simp

/-- **Energy of a single cutoff**: `∫_ℂ ‖D b_{p,r}‖² ≤ 18π D² / log(1/r)`. -/
theorem lintegral_logCutoffDeriv_le {D : ℝ} (hD : ∀ s, |deriv cutProfile s| ≤ D) (p : ℂ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∫⁻ z, ENNReal.ofReal (‖logCutoffDeriv p r z‖ ^ 2) ≤
      ENNReal.ofReal (18 * π * D ^ 2 / -Real.log r) := by
  have hL : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr0 hr1)
  calc ∫⁻ z, ENNReal.ofReal (‖logCutoffDeriv p r z‖ ^ 2)
      ≤ ∫⁻ z, ENNReal.ofReal (9 * D ^ 2 / (-Real.log r) ^ 2) * annulusProfile r ‖z - p‖ :=
        lintegral_mono fun z => ofReal_sq_logCutoffDeriv_le hD hr0 hr1 z
    _ = ENNReal.ofReal (9 * D ^ 2 / (-Real.log r) ^ 2) *
          ENNReal.ofReal (2 * π * -Real.log r) := by
        rw [lintegral_const_mul _ (show Measurable fun z : ℂ => annulusProfile r ‖z - p‖ from
          (measurable_annulusProfile r).comp (measurable_id.sub_const p).norm),
          lintegral_annulus_eq hr0 hr1.le p]
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- Off `p`, the cutoff `b_{p,r}(z)` tends to `0` as `r → 0`. -/
theorem tendsto_logCutoff_zero {p z : ℂ} (hz : z ≠ p) :
    Tendsto (fun r => logCutoff p r z) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h2 : Tendsto (fun r : ℝ => (2 * -Real.log r)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (h1.const_mul_atTop two_pos)
  have h3 : Tendsto (fun r => logVar p r z) (𝓝[>] 0) (𝓝 1) := by
    have := (h2.mul_const (3 * -Real.log (‖z - p‖ ^ 2))).const_add 1
    simpa [logVar] using this
  have h4 := (contDiff_cutProfile.continuous.tendsto 1).comp h3
  rw [cutProfile_eq_zero le_rfl] at h4
  refine h4.congr' ?_
  filter_upwards with r
  simp [logCutoff, hz]

theorem continuous_logCutoff {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (p : ℂ) :
    Continuous (logCutoff p r) :=
  continuous_iff_continuousAt.2 fun z => (hasFDerivAt_logCutoff hr0 hr1 z).continuousAt

/-! ## The multi-point cutoff -/

/-- The multi-point capacity cutoff `b_r = 1 − ∏_{p ∈ P} (1 − b_{p,r})`. -/
def capCutoff (P : Finset ℂ) (r : ℝ) (z : ℂ) : ℝ := 1 - ∏ p ∈ P, (1 - logCutoff p r z)

open Classical in
/-- Its derivative `∑_p (∏_{q ≠ p} (1 − b_{q,r})) D b_{p,r}`. -/
def capCutoffDeriv (P : Finset ℂ) (r : ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  ∑ p ∈ P, (∏ q ∈ P.erase p, (1 - logCutoff q r z)) • logCutoffDeriv p r z

variable {P : Finset ℂ} {r : ℝ}

theorem hasFDerivAt_capCutoff (hr0 : 0 < r) (hr1 : r < 1) (z : ℂ) :
    HasFDerivAt (capCutoff P r) (capCutoffDeriv P r z) z := by
  classical
  have h := (HasFDerivAt.finsetProd (u := P) (g := fun p z => 1 - logCutoff p r z)
    (g' := fun p => -logCutoffDeriv p r z) (x := z)
    fun p _ => (hasFDerivAt_logCutoff hr0 hr1 z).const_sub 1).const_sub 1
  refine h.congr_fderiv ?_
  simp only [capCutoffDeriv, smul_neg, Finset.sum_neg_distrib, neg_neg]

theorem prod_one_sub_logCutoff_mem (s : Finset ℂ) (z : ℂ) :
    0 ≤ ∏ q ∈ s, (1 - logCutoff q r z) ∧ ∏ q ∈ s, (1 - logCutoff q r z) ≤ 1 :=
  ⟨Finset.prod_nonneg fun q _ => sub_nonneg.2 (logCutoff_le_one z),
    Finset.prod_le_one₀ (fun q _ => sub_nonneg.2 (logCutoff_le_one z))
      (fun q _ => by linarith [logCutoff_nonneg (p := q) (r := r) z])⟩

theorem capCutoff_nonneg (z : ℂ) : 0 ≤ capCutoff P r z := by
  unfold capCutoff; linarith [(prod_one_sub_logCutoff_mem (r := r) P z).2]

theorem capCutoff_le_one (z : ℂ) : capCutoff P r z ≤ 1 := by
  unfold capCutoff; linarith [(prod_one_sub_logCutoff_mem (r := r) P z).1]

/-- `b_r = 1` within distance `r` of `P`. -/
theorem capCutoff_eq_one (hr0 : 0 < r) (hr1 : r < 1) {p z : ℂ} (hp : p ∈ P)
    (hz : ‖z - p‖ ≤ r) : capCutoff P r z = 1 := by
  unfold capCutoff
  rw [Finset.prod_eq_zero hp (by rw [logCutoff_eq_one hr0 hr1 hz, sub_self]), sub_zero]

/-- Off `P`, `b_r(z) → 0` as `r → 0`. -/
theorem tendsto_capCutoff_zero {z : ℂ} (hz : z ∉ P) :
    Tendsto (fun r => capCutoff P r z) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun r => ∏ p ∈ P, (1 - logCutoff p r z)) (𝓝[>] 0)
      (𝓝 (∏ p ∈ P, (1 - 0))) :=
    tendsto_finsetProd _ fun p hp =>
      (tendsto_logCutoff_zero (fun h : z = p => hz (h ▸ hp))).const_sub 1
  simpa [capCutoff] using h.const_sub 1

theorem continuous_capCutoffDeriv (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (capCutoffDeriv P r) := by
  unfold capCutoffDeriv
  refine continuous_finsetSum _ fun p _ => ?_
  exact (continuous_finsetProd _ fun q _ =>
    continuous_const.sub (continuous_logCutoff hr0 hr1 q)).smul
      (continuous_logCutoffDeriv hr0 hr1)

theorem norm_capCutoffDeriv_le (z : ℂ) :
    ‖capCutoffDeriv P r z‖ ≤ ∑ p ∈ P, ‖logCutoffDeriv p r z‖ := by
  classical
  unfold capCutoffDeriv
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  obtain ⟨h0, h1⟩ := prod_one_sub_logCutoff_mem (r := r) (P.erase p) z
  convert mul_le_of_le_one_left (norm_nonneg _) h1 using 2
  exact abs_of_nonneg h0

/-- **Energy of the multi-point cutoff**: `∫_ℂ ‖D b_r‖² ≤ |P|² · 18π D² / log(1/r)`. -/
theorem lintegral_capCutoffDeriv_le {D : ℝ} (hD : ∀ s, |deriv cutProfile s| ≤ D) (hr0 : 0 < r)
    (hr1 : r < 1) :
    ∫⁻ z, ENNReal.ofReal (‖capCutoffDeriv P r z‖ ^ 2) ≤
      ENNReal.ofReal ((P.card : ℝ) ^ 2 * (18 * π * D ^ 2 / -Real.log r)) := by
  have hL : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr0 hr1)
  have hpt : ∀ z, ENNReal.ofReal (‖capCutoffDeriv P r z‖ ^ 2) ≤
      ∑ p ∈ P, ENNReal.ofReal (P.card : ℝ) * ENNReal.ofReal (‖logCutoffDeriv p r z‖ ^ 2) := by
    intro z
    simp_rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖capCutoffDeriv P r z‖ ^ 2 ≤ (∑ p ∈ P, ‖logCutoffDeriv p r z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_capCutoffDeriv_le z) 2
      _ ≤ P.card * ∑ p ∈ P, ‖logCutoffDeriv p r z‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = ∑ p ∈ P, P.card * ‖logCutoffDeriv p r z‖ ^ 2 := by rw [Finset.mul_sum]
  have hmeas : ∀ p : ℂ, Measurable fun z => ENNReal.ofReal (‖logCutoffDeriv p r z‖ ^ 2) :=
    fun p => ((continuous_logCutoffDeriv hr0 hr1).norm.pow 2).measurable.ennreal_ofReal
  calc ∫⁻ z, ENNReal.ofReal (‖capCutoffDeriv P r z‖ ^ 2)
      ≤ ∫⁻ z, ∑ p ∈ P, ENNReal.ofReal (P.card : ℝ) *
          ENNReal.ofReal (‖logCutoffDeriv p r z‖ ^ 2) := lintegral_mono hpt
    _ = ∑ p ∈ P, ∫⁻ z, ENNReal.ofReal (P.card : ℝ) *
          ENNReal.ofReal (‖logCutoffDeriv p r z‖ ^ 2) :=
        lintegral_finsetSum _ fun p _ => (hmeas p).const_mul _
    _ ≤ ∑ p ∈ P, ENNReal.ofReal (P.card : ℝ) * ENNReal.ofReal (18 * π * D ^ 2 / -Real.log r) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [lintegral_const_mul _ (hmeas p)]
        exact mul_le_mul' le_rfl (lintegral_logCutoffDeriv_le hD p hr0 hr1)
    _ = _ := by
        have hD0 : 0 ≤ D ^ 2 := sq_nonneg D
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end InteractingSLE.Sec6
