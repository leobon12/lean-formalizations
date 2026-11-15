/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.PointVariance
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens

/-!
# Variance bounds for mollified GFF values (Wang–Wu, Lemma 4.6, first step)

Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.2, proof of
Lemma 4.6 (text dump lines 1060–1124): "Covariance domination by the larger-disc GFF and its
explicit logarithmic Green kernel give `sup_z Var(F_n(z)) ≤ C(n + 1)`,
`E|F_n(z) − F_n(w)|² ≤ C 2^{2n} |z − w|²`."

Here the zero-boundary GFF lives on `ℍ` and the Green kernel is the explicit
`G_ℍ(x, y) = log|x − ȳ| − log|x − y|` (`LQGMetric.zeroGFFTestCov_eq_green`), so no larger disc is
needed: on a window `|x|, |y| ≤ R`, `G_ℍ(x, y) ≤ log(2R) + log(1/|x − y|)`, and the logarithm is
integrated in polar coordinates.

## Main results

* `lintegral_ball_log_div_norm_sub_le`: `∫_{B(x,ρ)} log(ρ/|y − x|) dy ≤ 2πρ²`;
* `zeroGFFTestCov_self_le_of_ball`: `Var⟨h, φ⟩ ≤ B² (πr²)(πr² log((|c| + r)/r) + 8πr²)` for
  `|φ| ≤ B` vanishing off `B(c, r)`;
* `normBump`, `zeroGFFTestCov_le_of_abs_le_normBump`, `zeroGFFTestCov_le_of_abs_le_normBump_sub`:
  the two variance
  bounds of the source for the normalized radial mollifier `F_n(z) = ⟨h, bump_{z,δ}/(δ²m)⟩`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory
open scoped ENNReal Real

namespace InteractingSLE.WangWu

/-- `s log(ρ/s) ≤ ρ` on `(0, ρ)`. -/
lemma mul_log_div_le {ρ s : ℝ} (hs : 0 < s) (hsρ : s < ρ) : s * Real.log (ρ / s) ≤ ρ := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos (hs.trans hsρ) hs)
  have h2 : s * Real.log (ρ / s) ≤ s * (ρ / s - 1) := mul_le_mul_of_nonneg_left h1 hs.le
  have h3 : s * (ρ / s - 1) = ρ - s := by field_simp
  linarith

/-- **Radial logarithmic integral.** `∫_{B(0,ρ)} log(ρ/|u|) du ≤ 2πρ²`. -/
theorem lintegral_ball_zero_log_div_norm_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ u in ball (0 : ℂ) ρ, ENNReal.ofReal (Real.log (ρ / ‖u‖)) ≤
      ENNReal.ofReal (2 * π * ρ ^ 2) := by
  set f : ℝ → ℝ := (Iio ρ).indicator fun s => Real.log (ρ / s) with hf
  have hfm : Measurable f :=
    (Real.measurable_log.comp (measurable_const.div measurable_id)).indicator measurableSet_Iio
  have hf0 : ∀ s, 0 ≤ s → 0 ≤ f s := by
    intro s hs
    simp only [hf, indicator]
    split_ifs with h
    · rcases hs.eq_or_lt with rfl | hs'
      · simp
      · exact Real.log_nonneg (by rw [le_div_iff₀ hs', one_mul]; exact (mem_Iio.1 h).le)
    · exact le_rfl
  have hind : ∀ u : ℂ, (ball (0 : ℂ) ρ).indicator (fun u => Real.log (ρ / ‖u‖)) u = f ‖u‖ := by
    intro u
    simp only [hf, indicator, mem_ball_zero_iff, mem_Iio]
  have hlhs : ∫⁻ u in ball (0 : ℂ) ρ, ENNReal.ofReal (Real.log (ρ / ‖u‖)) =
      ∫⁻ u : ℂ, ENNReal.ofReal (f ‖u‖) := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun u => ?_
    rw [← hind u]
    simp only [indicator]
    split_ifs <;> simp
  -- integrability of the radial profile
  set g : ℝ → ℝ := fun s => s ^ (Module.finrank ℝ ℂ - 1) • f s with hg
  have hgle : ∀ s ∈ Ioi (0 : ℝ), ‖g s‖ ≤ (Ioo 0 ρ).indicator (fun _ => ρ) s := by
    intro s hs
    have hs0 : 0 < s := hs
    simp only [hg, Complex.finrank_real_complex, smul_eq_mul, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    by_cases hsρ : s < ρ
    · rw [indicator_of_mem (show s ∈ Ioo 0 ρ from ⟨hs0, hsρ⟩)]
      have hfs : f s = Real.log (ρ / s) := by simp [hf, hsρ]
      rw [hfs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0.le
        (Real.log_nonneg (by rw [le_div_iff₀ hs0, one_mul]; exact hsρ.le)))]
      exact mul_log_div_le hs0 hsρ
    · rw [indicator_of_notMem (fun h => hsρ h.2)]
      have hfs : f s = 0 := by simp [hf, hsρ]
      simp [hfs]
  have hgint : IntegrableOn g (Ioi 0) := by
    refine Integrable.mono' (g := (Ioo 0 ρ).indicator fun _ => ρ) ?_ ?_ ?_
    · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioo |>.restrict
    · exact ((measurable_id.pow_const _).smul hfm).aestronglyMeasurable
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hgle)
  have hint : Integrable (fun u : ℂ => f ‖u‖) :=
    (integrable_fun_norm_addHaar (volume : Measure ℂ) (f := f)).2 hgint
  rw [hlhs, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun u => hf0 _ (norm_nonneg u))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) f]
  have hvol : (volume : Measure ℂ).real (ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • f y ≤ ρ * ρ := by
    calc ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • f y
        ≤ ∫ y in Ioi (0 : ℝ), (Ioo 0 ρ).indicator (fun _ => ρ) y := by
          refine setIntegral_mono_on hgint ?_ measurableSet_Ioi fun s hs => ?_
          · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioo |>.restrict
          · exact (le_abs_self _).trans (hgle s hs)
      _ = ρ * ρ := by
          rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
            Ioo_inter_Ioi, max_self, setIntegral_const]
          simp [Measure.real, hρ.le]
  rw [Complex.finrank_real_complex] at hI
  rw [hvol, nsmul_eq_mul, smul_eq_mul, Complex.finrank_real_complex]
  push_cast
  nlinarith [Real.pi_pos]


/-- Translated form: `∫_{B(x,ρ)} log(ρ/|y − x|) dy ≤ 2πρ²`. -/
theorem lintegral_ball_log_div_norm_sub_le (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ y in ball x ρ, ENNReal.ofReal (Real.log (ρ / ‖y - x‖)) ≤
      ENNReal.ofReal (2 * π * ρ ^ 2) := by
  have h := lintegral_add_right_eq_self (μ := (volume : Measure ℂ))
    ((ball x ρ).indicator fun y => ENNReal.ofReal (Real.log (ρ / ‖y - x‖))) x
  rw [← lintegral_indicator measurableSet_ball, ← h]
  refine le_of_eq_of_le ?_ (lintegral_ball_zero_log_div_norm_le hρ)
  rw [← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun u => ?_
  simp only [indicator, mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]

open QuantumZipper in
/-- **Variance of a test function supported in a small ball** (Green-kernel bound). For
`φ ∈ 𝓓(ℍ)` with `|φ| ≤ B`, vanishing off `B(c, r)`,
`Var⟨h, φ⟩ = ∫∫ φ φ G_ℍ ≤ B² (πr²) (πr² log((|c| + r)/r) + 8πr²)`. -/
theorem zeroGFFTestCov_self_le_of_ball (φ : LQGMetric.TestOn upperHalfPlaneOpens) {c : ℂ}
    {r B : ℝ} (hr : 0 < r) (hB : ∀ x, |φ x| ≤ B) (hsupp : ∀ x, x ∉ ball c r → φ x = 0) :
    zeroGFFTestCov upperHalfPlaneOpens φ φ ≤
      B ^ 2 * (π * r ^ 2) * (π * r ^ 2 * Real.log ((‖c‖ + r) / r) + 8 * π * r ^ 2) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set L : ℝ := Real.log ((‖c‖ + r) / r) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by
    rw [le_div_iff₀ hr, one_mul]; linarith [norm_nonneg c])
  set K : ℝ := B ^ 2 * (π * r ^ 2) * (π * r ^ 2 * L + 8 * π * r ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  rw [LQGMetric.zeroGFFTestCov_eq_green (V := upperHalfPlaneOpens) subset_rfl
    GFF.isConformalOnto_id_H φ φ]
  set F : ℂ × ℂ → ℝ≥0∞ := fun p => (ball c r).indicator 1 p.1 * ((ball c r).indicator 1 p.2 *
    (ENNReal.ofReal (B ^ 2) * (ENNReal.ofReal L + ENNReal.ofReal (Real.log (2 * r / ‖p.2 - p.1‖)))))
    with hF
  have hFm : Measurable F := by
    have hi : Measurable ((ball c r).indicator (1 : ℂ → ℝ≥0∞)) :=
      measurable_one.indicator measurableSet_ball
    have hlog : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (Real.log (2 * r / ‖p.2 - p.1‖)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_log.comp (measurable_const.div
        ((measurable_snd.sub measurable_fst).norm)))
    exact (hi.comp measurable_fst).mul ((hi.comp measurable_snd).mul
      ((hlog.const_add _).const_mul _))
  have hpt : ∀ᵐ p ∂((volume : Measure ℂ).prod volume),
      ENNReal.ofReal ‖φ p.1 * φ p.2 * greenH (id p.1) (id p.2)‖ ≤ F p := by
    filter_upwards [LQGMetric.ae_ne_diag] with p hp
    obtain ⟨x, y⟩ := p
    simp only [id] at hp ⊢
    by_cases hx : x ∈ ball c r
    swap
    · rw [hsupp x hx]; simp
    by_cases hy : y ∈ ball c r
    swap
    · rw [hsupp y hy]; simp
    by_cases hxH : x ∈ H
    swap
    · rw [φ.zero_on_compl hxH]; simp
    by_cases hyH : y ∈ H
    swap
    · rw [φ.zero_on_compl hyH]; simp
    simp only [hF, indicator_of_mem hx, indicator_of_mem hy, Pi.one_apply, one_mul]
    have hG0 : 0 ≤ greenH x y := greenH_nonneg (show (0 : ℝ) ≤ x.im from le_of_lt hxH)
      (show (0 : ℝ) ≤ y.im from le_of_lt hyH) hp
    have hxy : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
    have hxc : 0 < ‖x - (starRingEnd ℂ) y‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      have h1 : (0 : ℝ) < x.im := hxH
      have h2 : (0 : ℝ) < y.im := hyH
      linarith
    have hxn : ‖x‖ < ‖c‖ + r := by
      have := norm_le_norm_add_norm_sub' x c
      rw [mem_ball, dist_eq_norm] at hx
      linarith [norm_sub_rev x c]
    have hyn : ‖y‖ < ‖c‖ + r := by
      have := norm_le_norm_add_norm_sub' y c
      rw [mem_ball, dist_eq_norm] at hy
      linarith [norm_sub_rev y c]
    have hxcb : ‖x - (starRingEnd ℂ) y‖ ≤ 2 * (‖c‖ + r) := by
      calc ‖x - (starRingEnd ℂ) y‖ ≤ ‖x‖ + ‖(starRingEnd ℂ) y‖ := norm_sub_le _ _
        _ = ‖x‖ + ‖y‖ := by rw [Complex.norm_conj]
        _ ≤ 2 * (‖c‖ + r) := by linarith
    have hGle : greenH x y ≤ L + Real.log (2 * r / ‖y - x‖) := by
      unfold greenH
      rw [norm_sub_rev y x, Real.log_div (by positivity) hxy.ne', hL,
        Real.log_div (by linarith [norm_nonneg c]) hr.ne']
      have := Real.log_le_log hxc hxcb
      rw [Real.log_mul (by norm_num) (by linarith [norm_nonneg c] : ‖c‖ + r ≠ 0)] at this
      rw [Real.log_mul (by norm_num) hr.ne']
      linarith
    have habs : ‖φ x * φ y * greenH x y‖ ≤ B ^ 2 * (L + Real.log (2 * r / ‖y - x‖)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hG0, sq]
      exact mul_le_mul (mul_le_mul (hB x) (hB y) (abs_nonneg _) hB0) hGle hG0 (by positivity)
    calc ENNReal.ofReal ‖φ x * φ y * greenH x y‖
        ≤ ENNReal.ofReal (B ^ 2 * (L + Real.log (2 * r / ‖y - x‖))) := ENNReal.ofReal_le_ofReal habs
      _ = ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (L + Real.log (2 * r / ‖y - x‖)) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := mul_le_mul_right ENNReal.ofReal_add_le _
  have hint : ∫⁻ p, F p ∂((volume : Measure ℂ).prod volume) ≤ ENNReal.ofReal K := by
    rw [lintegral_prod _ hFm.aemeasurable]
    have hinner : ∀ x ∈ ball c r, ∫⁻ y, F (x, y) ≤
        ENNReal.ofReal (B ^ 2) * (ENNReal.ofReal L * ENNReal.ofReal (π * r ^ 2) +
          ENNReal.ofReal (2 * π * (2 * r) ^ 2)) := by
      intro x hx
      simp only [hF, indicator_of_mem hx, Pi.one_apply, one_mul]
      have hm : Measurable fun y : ℂ => ENNReal.ofReal L +
          ENNReal.ofReal (Real.log (2 * r / ‖y - x‖)) :=
        measurable_const.add (ENNReal.measurable_ofReal.comp (Real.measurable_log.comp
          (measurable_const.div ((measurable_id.sub measurable_const).norm))))
      have heq : ∀ y, (ball c r).indicator (1 : ℂ → ℝ≥0∞) y * (ENNReal.ofReal (B ^ 2) *
          (ENNReal.ofReal L + ENNReal.ofReal (Real.log (2 * r / ‖y - x‖)))) =
          ENNReal.ofReal (B ^ 2) * (ball c r).indicator (fun y => ENNReal.ofReal L +
            ENNReal.ofReal (Real.log (2 * r / ‖y - x‖))) y := by
        intro y
        by_cases hy : y ∈ ball c r
        · simp [indicator_of_mem hy]
        · simp [indicator_of_notMem hy]
      simp_rw [heq]
      rw [lintegral_const_mul _ (hm.indicator measurableSet_ball),
        lintegral_indicator measurableSet_ball, lintegral_add_left measurable_const]
      refine mul_le_mul_right (add_le_add ?_ ?_) _
      · rw [setLIntegral_const, Complex.volume_ball, ← ENNReal.ofReal_pow hr.le,
          ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
          mul_comm (r ^ 2)]
      · have hsub : ball c r ⊆ ball x (2 * r) := by
          intro y hy
          rw [mem_ball] at hx hy ⊢
          linarith [dist_triangle_right y x c]
        refine (lintegral_mono_set hsub).trans ?_
        refine (setLIntegral_mono' measurableSet_ball fun y _ => le_rfl).trans ?_
        exact lintegral_ball_log_div_norm_sub_le x (by positivity)
    calc ∫⁻ x, ∫⁻ y, F (x, y)
        ≤ ∫⁻ x, (ball c r).indicator (fun _ => ENNReal.ofReal (B ^ 2) *
            (ENNReal.ofReal L * ENNReal.ofReal (π * r ^ 2) +
              ENNReal.ofReal (2 * π * (2 * r) ^ 2))) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ ball c r
          · rw [indicator_of_mem hx]; exact hinner x hx
          · rw [indicator_of_notMem hx]; simp [hF, indicator_of_notMem hx]
      _ = ENNReal.ofReal K := by
          rw [lintegral_indicator measurableSet_ball, setLIntegral_const, Complex.volume_ball,
            ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
            ← ENNReal.ofReal_mul hL0, ← ENNReal.ofReal_mul (sq_nonneg r),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (sq_nonneg B), ← ENNReal.ofReal_mul (by positivity), hK]
          congr 1; ring
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  exact ENNReal.toReal_le_of_le_ofReal hK0 ((lintegral_mono_ae hpt).trans hint)


/-! ### Normalized bumps -/

open GFF (bumpFun bumpMass bumpMass_pos bumpFun_le bumpFun_nonneg bumpFun_eq_zero contDiff_bumpFun)

/-- The normalized radial bump `bump_{x,δ} / (δ² m)` (integral one). -/
def normBump (x : ℂ) (δ : ℝ) (y : ℂ) : ℝ := bumpFun x δ y / (δ ^ 2 * bumpMass)

lemma abs_normBump_le (x : ℂ) {δ : ℝ} (hδ : 0 < δ) (y : ℂ) :
    |normBump x δ y| ≤ expNegInvGlue 1 / (δ ^ 2 * bumpMass) := by
  have hm := bumpMass_pos
  rw [normBump, abs_div, abs_of_nonneg (bumpFun_nonneg _ _ _), abs_of_pos (by positivity)]
  exact div_le_div_of_nonneg_right (bumpFun_le _ _ _) (by positivity)

lemma normBump_eq_zero {x : ℂ} {δ : ℝ} (hδ : 0 < δ) {y : ℂ} (hy : y ∉ ball x δ) :
    normBump x δ y = 0 := by
  rw [normBump, bumpFun_eq_zero hδ (not_lt.1 hy), zero_div]

/-- The unit radial profile is Lipschitz. -/
lemma exists_lipschitzWith_radProf : ∃ C : NNReal, LipschitzWith C (LQGMetric.GM.radProf 1) := by
  have h0 : bumpFun 0 1 = LQGMetric.GM.radProf 1 := by
    funext y; simp [bumpFun]
  rw [← h0]
  exact ContDiff.lipschitzWith_of_hasCompactSupport (GFF.hasCompactSupport_bumpFun one_pos)
    (contDiff_bumpFun 0 1) (by simp)

/-- A Lipschitz constant of the unit radial profile. -/
def bumpLip : NNReal := Classical.choose exists_lipschitzWith_radProf

lemma abs_bumpFun_sub_le (x w : ℂ) {δ : ℝ} (hδ : 0 < δ) (y : ℂ) :
    |bumpFun x δ y - bumpFun w δ y| ≤ bumpLip * (‖x - w‖ / δ) := by
  have h := (Classical.choose_spec exists_lipschitzWith_radProf).dist_le_mul
    ((y - x) / δ) ((y - w) / δ)
  rw [Real.dist_eq, dist_eq_norm] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ,
    sub_sub_sub_cancel_left, norm_sub_rev]

/-- **Variance of a normalized bump**: if `|φ| ≤ |bump_{x,δ}/(δ²m)|`, then
`Var⟨h, φ⟩ ≤ (eπ/m)² (log((|x| + δ)/δ) + 8)`. -/
theorem zeroGFFTestCov_le_of_abs_le_normBump (φ : LQGMetric.TestOn upperHalfPlaneOpens) {x : ℂ}
    {δ : ℝ} (hδ : 0 < δ) (hφ : ∀ y, |φ y| ≤ |normBump x δ y|) :
    QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens φ φ ≤
      (expNegInvGlue 1 * π / bumpMass) ^ 2 * (Real.log ((‖x‖ + δ) / δ) + 8) := by
  have hm := bumpMass_pos
  refine (zeroGFFTestCov_self_le_of_ball φ (c := x) hδ (B := expNegInvGlue 1 / (δ ^ 2 * bumpMass))
    (fun y => (hφ y).trans (abs_normBump_le x hδ y))
    (fun y hy => abs_eq_zero.1 (le_antisymm ((hφ y).trans_eq (by
      rw [normBump_eq_zero hδ hy, abs_zero])) (abs_nonneg _)))).trans (le_of_eq ?_)
  field_simp

/-- **Variance of an increment of normalized bumps**: if `|φ| ≤ |b_x − b_w|` (normalized bumps)
and `|x − w| ≤ 2δ`, then `Var⟨h, φ⟩ ≤ (9πL/m)² (|x − w|/δ)² (log((|x| + 3δ)/(3δ)) + 8)`. -/
theorem zeroGFFTestCov_le_of_abs_le_normBump_sub (φ : LQGMetric.TestOn upperHalfPlaneOpens)
    {x w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hφ : ∀ y, |φ y| ≤ |normBump x δ y - normBump w δ y|)
    (hxw : ‖x - w‖ ≤ 2 * δ) :
    QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens φ φ ≤
      (9 * π * bumpLip / bumpMass) ^ 2 * (‖x - w‖ / δ) ^ 2 *
        (Real.log ((‖x‖ + 3 * δ) / (3 * δ)) + 8) := by
  have hm := bumpMass_pos
  have hB : ∀ y, |φ y| ≤ bumpLip * (‖x - w‖ / δ) / (δ ^ 2 * bumpMass) := by
    intro y
    refine (hφ y).trans ?_
    simp only [normBump]
    rw [← sub_div, abs_div, abs_of_pos (show (0 : ℝ) < δ ^ 2 * bumpMass by positivity)]
    exact div_le_div_of_nonneg_right (abs_bumpFun_sub_le x w hδ y) (by positivity)
  have hsupp : ∀ y, y ∉ ball x (3 * δ) → φ y = 0 := by
    intro y hy
    rw [mem_ball, not_lt] at hy
    have h1 : y ∉ ball x δ := by rw [mem_ball, not_lt]; linarith
    have h2 : y ∉ ball w δ := by
      rw [mem_ball, not_lt]
      have := dist_triangle y w x
      rw [dist_comm w x, dist_eq_norm x w] at this
      linarith
    refine abs_eq_zero.1 (le_antisymm ((hφ y).trans_eq ?_) (abs_nonneg _))
    rw [normBump_eq_zero hδ h1, normBump_eq_zero hδ h2, sub_zero, abs_zero]
  refine (zeroGFFTestCov_self_le_of_ball φ (c := x) (by positivity) hB hsupp).trans
    (le_of_eq ?_)
  field_simp
  ring

end InteractingSLE.WangWu
