import QuantumZipper.Proofs.Zipper.JointModAssembly

/-!
# UNIF-TIPEXP, deterministic part: an upper bound for `Ddet` on unit semicircles

For a continuous driver `W` with `W 0 = 0` and `|W| ≤ M` on `[0,1]` (`M ≥ 0`), at every time
`u ∈ [0,1]` and every real centre `t` with `|t| ≤ 1`,

`Ddet κ γ W (u, (t, 1)) ≤ (2/√κ) · log (20 M + 13) + |Q| · 39`   (`Ddet_unit_le`).

* The `h⁰` term: the pushed circle `ν_u = (fwdMapInv W u)_* fc(t,1)` is supported in
  `‖z‖ ≤ revBound (2M) 1 2 ≤ 20 M + 13` (`RegCont.fwdMapInv_mem_H_bound`).
* The coordinate-change term: `|log ‖ψ_u'(v)‖| ≤ |log √(R² + 4u)| + |log Im v|`
  (`TwoPoint.abs_log_norm_deriv_revMap_le`, a bound **independent of the driver**), and the
  layer-cake bound `∫ log⁺(1/Im) dfc ≤ 36` (`TwoPoint.lintegral_logRatio_le`).

Own elementary argument (assembling the repository's Loewner bounds); no further literature input.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint UnzipInvariance

variable {W : ℝ → ℝ}

/-- `log‖z‖ ≤ log L` whenever `‖z‖ ≤ L` and `1 ≤ L`. -/
theorem log_norm_le_of_le {z : ℂ} {L : ℝ} (hL : 1 ≤ L) (hz : ‖z‖ ≤ L) :
    Real.log ‖z‖ ≤ Real.log L := by
  rcases (norm_nonneg z).eq_or_lt with h | h
  · rw [← h, Real.log_zero]; exact Real.log_nonneg hL
  · exact Real.log_le_log h hz

/-- The `h⁰` term of `Ddet` on a unit circle with real centre. -/
theorem integral_log_norm_νT_unit_le (hW : Continuous W) (hW0 : W 0 = 0) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, |W s| ≤ M) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) {t : ℝ}
    (ht : |t| ≤ 1) :
    ∫ z, Real.log ‖z‖ ∂νT W (t : ℂ) 1 u ≤ Real.log (20 * M + 13) := by
  have hmeas := aemeasurable_fwdMapInv hW hW0 hu.1 (t : ℂ) one_pos
  have : IsProbabilityMeasure (νT W (t : ℂ) 1 u) :=
    (Measure.isProbabilityMeasure_map_iff hmeas).2 inferInstance
  have hL : (1 : ℝ) ≤ 20 * M + 13 := by linarith
  have hae : ∀ᵐ z ∂νT W (t : ℂ) 1 u, Real.log ‖z‖ ≤ Real.log (20 * M + 13) := by
    refine (ae_map_iff hmeas ?_).2 ?_
    · exact measurableSet_le (Real.measurable_log.comp measurable_norm) measurable_const
    filter_upwards [foldedCircle_ae_mem_H (t : ℂ) one_pos,
      foldedCircle_ae_norm_le (t : ℂ) zero_le_one] with v hv hvn
    have hvn' : ‖v‖ ≤ 2 := by
      have : ‖(t : ℂ)‖ = |t| := Complex.norm_real t
      linarith
    obtain ⟨-, h2⟩ := fwdMapInv_mem_H_bound hW hW0 hM hu.1 hu.2 hv hvn'
    refine log_norm_le_of_le hL (h2.trans ?_)
    simp only [revBound, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  by_cases hi : Integrable (fun z : ℂ => Real.log ‖z‖) (νT W (t : ℂ) 1 u)
  · calc ∫ z, Real.log ‖z‖ ∂νT W (t : ℂ) 1 u ≤ ∫ _z, Real.log (20 * M + 13) ∂νT W (t : ℂ) 1 u :=
          integral_mono_ae hi (integrable_const _) hae
      _ = Real.log (20 * M + 13) := by simp
  · rw [integral_undef hi]; exact Real.log_nonneg hL

/-- `|log x| ≤ log⁺ (1/x) + 1` for `0 < x ≤ 2`. -/
theorem abs_log_le_logRatio_add_one {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 2) :
    |Real.log x| ≤ max (Real.log (1 / |x|)) 0 + 1 := by
  rw [abs_of_pos hx, one_div, Real.log_inv]
  rcases le_total x 1 with h | h
  · rw [abs_of_nonpos (Real.log_nonpos hx.le h)]
    linarith [le_max_left (-Real.log x) 0]
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos hx
    linarith [le_max_right (-Real.log x) 0]

/-- The coordinate-change term of `Ddet` on a unit circle with real centre. -/
theorem abs_integral_log_deriv_unit_le (hW : Continuous W) (hW0 : W 0 = 0) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : |t| ≤ 1) :
    |∫ v, Real.log ‖deriv (fwdMapInv W u) v‖ ∂foldedCircle (t : ℂ) 1| ≤ 39 := by
  set g : ℂ → ℝ := fun v => Real.log ‖deriv (fwdMapInv W u) v‖ with hg
  set h : ℂ → ℝ := fun v => max (Real.log (1 / |v.im|)) 0 with hh
  have hptw : ∀ᵐ v ∂foldedCircle (t : ℂ) 1, |g v| ≤ h v + 3 := by
    filter_upwards [foldedCircle_ae_mem_H (t : ℂ) one_pos,
      foldedCircle_ae_abs_im_le (t : ℂ) zero_le_one] with v hv hvi
    have hvi' : v.im ≤ 2 := by
      have : ‖(t : ℂ)‖ = |t| := Complex.norm_real t
      linarith [le_abs_self v.im]
    simp only [hg]
    rw [deriv_fwdMapInv_eq hW hW0 hu.1 hv]
    have hb := abs_log_norm_deriv_revMap_le (continuous_vRev hW u) hu.1 hv hvi'
    have hs1 : (1 : ℝ) ≤ Real.sqrt (2 ^ 2 + 4 * u) :=
      Real.one_le_sqrt.2 (by nlinarith [hu.1])
    have hs3 : Real.sqrt (2 ^ 2 + 4 * u) ≤ 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [hu.2])
    have hl : |Real.log (Real.sqrt (2 ^ 2 + 4 * u))| ≤ 2 := by
      rw [abs_of_nonneg (Real.log_nonneg hs1)]
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.sqrt (2 ^ 2 + 4 * u) by linarith)]
    have hi := abs_log_le_logRatio_add_one (show (0 : ℝ) < v.im from hv) hvi'
    linarith
  have hhm : Measurable h :=
    (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp Complex.measurable_im))).max measurable_const
  have hlin : ∫⁻ v, ENNReal.ofReal ‖g v‖ ∂foldedCircle (t : ℂ) 1 ≤ ENNReal.ofReal 39 := by
    calc ∫⁻ v, ENNReal.ofReal ‖g v‖ ∂foldedCircle (t : ℂ) 1
        ≤ ∫⁻ v, (ENNReal.ofReal (h v) + ENNReal.ofReal 3) ∂foldedCircle (t : ℂ) 1 := by
          refine lintegral_mono_ae (hptw.mono fun v hv => ?_)
          rw [Real.norm_eq_abs, ← ENNReal.ofReal_add (le_max_right _ _) (by norm_num)]
          exact ENNReal.ofReal_le_ofReal hv
      _ = ∫⁻ v, ENNReal.ofReal (h v) ∂foldedCircle (t : ℂ) 1 + ENNReal.ofReal 3 := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (36 * Real.sqrt (1 / 1)) + ENNReal.ofReal 3 := by
          gcongr
          exact lintegral_logRatio_le (t : ℂ) one_pos one_pos
      _ = ENNReal.ofReal 39 := by
          rw [div_one, Real.sqrt_one, mul_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  calc |∫ v, g v ∂foldedCircle (t : ℂ) 1| = ‖∫ v, g v ∂foldedCircle (t : ℂ) 1‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ (∫⁻ v, ENNReal.ofReal ‖g v‖ ∂foldedCircle (t : ℂ) 1).toReal := norm_integral_le_lintegral_norm _
    _ ≤ 39 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hlin

/-- **Deterministic bound on unit semicircles.** -/
theorem Ddet_unit_le (κ γ : ℝ) (hW : Continuous W) (hW0 : W 0 = 0) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, |W s| ≤ M) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) {t : ℝ}
    (ht : |t| ≤ 1) :
    Ddet κ γ W (u, ((t : ℂ), 1)) ≤ 2 / Real.sqrt κ * Real.log (20 * M + 13) + |Qc γ| * 39 := by
  unfold Ddet
  have h1 := integral_log_norm_νT_unit_le hW hW0 hM0 hM hu ht
  have h2 := abs_integral_log_deriv_unit_le hW hW0 hu ht
  have hk : 0 ≤ 2 / Real.sqrt κ := by positivity
  refine add_le_add (mul_le_mul_of_nonneg_left h1 hk) ?_
  calc Qc γ * ∫ v, Real.log ‖deriv (fwdMapInv W u) v‖ ∂foldedCircle (t : ℂ) 1
      ≤ |Qc γ * ∫ v, Real.log ‖deriv (fwdMapInv W u) v‖ ∂foldedCircle (t : ℂ) 1| := le_abs_self _
    _ = |Qc γ| * |∫ v, Real.log ‖deriv (fwdMapInv W u) v‖ ∂foldedCircle (t : ℂ) 1| := abs_mul _ _
    _ ≤ |Qc γ| * 39 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

end RegUnif
end QuantumZipper
