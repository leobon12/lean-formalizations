import GaussianLQG.Core.Defs
import LQGDimension.LFPP.CouplingAux1

/-!
# Regular measures, segment measures and circle measures

Blueprint §1.2: Definition `def:regular`, Definition `def:segment` and Lemma `lem:segment-mass`.

* API for `IsRegular`: a support radius `R ≥ 1`, the ball-mass bound in `ℝ≥0∞` and absence of
  atoms.
* `segMeasure z w`: a probability measure (`isProbabilityMeasure_segMeasure`), the integral
  formula `∫ f d λ_{z,w} = ∫₀¹ f((1-u)z + uw) du` (`integral_segMeasure`), the ball-mass bound
  `λ_{z,w}(B_r(u)) ≤ 2r/|z-w|` (`segMeasure_ball_le`) and regularity for `z ≠ w`
  (`isRegular_segMeasure`).
* `circleMeasure z ρ`: a probability measure (`isProbabilityMeasure_circleMeasure`), the integral
  formula `∫ f dσ_{z,ρ} = circleAverage f z ρ` (`integral_circleMeasure`), the ball-mass bound
  `σ_{z,ρ}(B_r(u)) ≤ 2r/ρ` (`circleMeasure_ball_le`) and regularity for `ρ > 0`
  (`isRegular_circleMeasure`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace GaussianLQG

/-! ## Supports -/

/-- A measure that gives no mass outside `closedBall 0 R` is a.e. supported in it. -/
theorem ae_norm_le_of_compl_closedBall_eq_zero {μ : Measure ℂ} {R : ℝ}
    (h : μ (closedBall (0 : ℂ) R)ᶜ = 0) : ∀ᵐ x ∂μ, ‖x‖ ≤ R := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h
  simp only [mem_ofPred_eq, not_le] at hx
  simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
  exact hx

/-- Conversely, an a.e. bound on the norm gives no mass outside the closed ball. -/
theorem compl_closedBall_eq_zero_of_ae_norm_le {μ : Measure ℂ} {R : ℝ}
    (h : ∀ᵐ x ∂μ, ‖x‖ ≤ R) : μ (closedBall (0 : ℂ) R)ᶜ = 0 := by
  rw [ae_iff] at h
  refine measure_mono_null (fun x hx => ?_) h
  simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hx
  simp only [mem_ofPred_eq, not_le]
  exact hx

/-! ## Regular measures -/

namespace IsRegular

variable {μ ν : Measure ℂ}

/-- A regular measure has a support radius `R ≥ 1`. -/
theorem exists_support (h : IsRegular μ) :
    ∃ R : ℝ, 1 ≤ R ∧ μ (closedBall (0 : ℂ) R)ᶜ = 0 := by
  obtain ⟨R, hR⟩ := h.2.1
  refine ⟨max R 1, le_max_right _ _, measure_mono_null ?_ hR⟩
  exact compl_subset_compl.2 (closedBall_subset_closedBall (le_max_left _ _))

/-- The ball-mass bound of a regular measure, in `ℝ≥0∞`, with a nonnegative constant. -/
theorem exists_ballBound (h : IsRegular μ) :
    ∃ C α : ℝ, 0 < α ∧ 0 ≤ C ∧ ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ (ball u r) ≤ ENNReal.ofReal (C * r ^ α) := by
  have := h.1
  obtain ⟨C, α, hα, hb⟩ := h.2.2
  have hC : 0 ≤ C := by
    have h1 := hb 0 1 one_pos le_rfl
    rw [Real.one_rpow, mul_one] at h1
    exact ENNReal.toReal_nonneg.trans h1
  refine ⟨C, α, hα, hC, fun u r hr hr1 => ?_⟩
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal (hb u r hr hr1)

/-- A regular measure has no atoms. -/
theorem measure_singleton (h : IsRegular μ) (x : ℂ) : μ {x} = 0 := by
  obtain ⟨C, α, hα, -, hb⟩ := h.exists_ballBound
  have h1 : Tendsto (fun r : ℝ => C * r ^ α) (𝓝[>] 0) (𝓝 0) := by
    have h2 := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).const_mul C
    rw [Real.zero_rpow hα.ne', mul_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hT : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ α)) (𝓝[>] 0) (𝓝 0) := by
    have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h3
    exact h3
  refine le_antisymm (ge_of_tendsto hT ?_) zero_le
  filter_upwards [Ioc_mem_nhdsGT one_pos] with r hr
  exact (measure_mono (singleton_subset_iff.2 (mem_ball_self hr.1))).trans (hb x r hr.1 hr.2)

end IsRegular

/-! ## Segment measures -/

/-- The affine parametrization `u ↦ (1-u) z + u w` of the segment `[z, w]`. -/
def segPath (z w : ℂ) (u : ℝ) : ℂ := ((1 - u : ℝ) : ℂ) * z + (u : ℂ) * w

@[fun_prop]
theorem continuous_segPath (z w : ℂ) : Continuous (segPath z w) := by
  unfold segPath
  fun_prop

@[fun_prop]
theorem measurable_segPath (z w : ℂ) : Measurable (segPath z w) :=
  (continuous_segPath z w).measurable

theorem segMeasure_eq_map (z w : ℂ) :
    segMeasure z w = (volume.restrict (Icc (0 : ℝ) 1)).map (segPath z w) :=
  rfl

/-- Lebesgue measure on `[0, 1]` is a probability measure. -/
instance isProbabilityMeasure_restrict_Icc01 :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

/-- `λ_{z,w}` is a probability measure. -/
instance isProbabilityMeasure_segMeasure (z w : ℂ) : IsProbabilityMeasure (segMeasure z w) := by
  rw [segMeasure_eq_map]
  infer_instance

theorem segPath_sub_segPath (z w : ℂ) (s t : ℝ) :
    segPath z w s - segPath z w t = ((s - t : ℝ) : ℂ) * (w - z) := by
  unfold segPath
  push_cast
  ring

theorem norm_segPath_le (z w : ℂ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖segPath z w u‖ ≤ max ‖z‖ ‖w‖ := by
  unfold segPath
  have h1 : 0 ≤ 1 - u := by linarith [hu.2]
  calc ‖((1 - u : ℝ) : ℂ) * z + (u : ℂ) * w‖
      ≤ ‖((1 - u : ℝ) : ℂ) * z‖ + ‖(u : ℂ) * w‖ := norm_add_le _ _
    _ = (1 - u) * ‖z‖ + u * ‖w‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h1,
          Real.norm_of_nonneg hu.1]
    _ ≤ (1 - u) * max ‖z‖ ‖w‖ + u * max ‖z‖ ‖w‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h1)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hu.1)
    _ = max ‖z‖ ‖w‖ := by ring

/-- The integral against `λ_{z,w}` is the integral over the parametrization. -/
theorem integral_segMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (z w : ℂ)
    {f : ℂ → E} (hf : AEStronglyMeasurable f (segMeasure z w)) :
    ∫ x, f x ∂(segMeasure z w) = ∫ u in (0 : ℝ)..1, f (((1 - u : ℝ) : ℂ) * z + (u : ℂ) * w) := by
  rw [segMeasure_eq_map] at hf ⊢
  rw [integral_map (measurable_segPath z w).aemeasurable hf,
    intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rfl

/-- `λ_{z,w}` is supported in `closedBall 0 (max |z| |w|)`. -/
theorem ae_norm_le_segMeasure (z w : ℂ) : ∀ᵐ x ∂(segMeasure z w), ‖x‖ ≤ max ‖z‖ ‖w‖ := by
  rw [segMeasure_eq_map, ae_map_iff (measurable_segPath z w).aemeasurable
    (measurableSet_le (by fun_prop) measurable_const),
    ae_restrict_iff' measurableSet_Icc]
  exact ae_of_all _ fun u hu => norm_segPath_le z w hu

theorem segMeasure_compl_closedBall (z w : ℂ) :
    segMeasure z w (closedBall (0 : ℂ) (max ‖z‖ ‖w‖))ᶜ = 0 :=
  compl_closedBall_eq_zero_of_ae_norm_le (ae_norm_le_segMeasure z w)

/-- Lemma `lem:segment-mass`, segment part: `λ_{z,w}(B_r(u)) ≤ 2r/|z-w|`. -/
theorem segMeasure_ball_le {z w : ℂ} (hzw : z ≠ w) (u : ℂ) (r : ℝ) :
    segMeasure z w (ball u r) ≤ ENNReal.ofReal (2 * r / ‖z - w‖) := by
  have hzw' : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  rw [segMeasure_eq_map, Measure.map_apply (measurable_segPath z w) measurableSet_ball,
    Measure.restrict_apply' measurableSet_Icc]
  refine (measure_mono inter_subset_left).trans ((Real.volume_le_diam _).trans ?_)
  refine Metric.ediam_le_of_forall_dist_le fun s hs t ht => ?_
  simp only [mem_preimage, mem_ball, dist_eq_norm] at hs ht
  rw [Real.dist_eq, le_div_iff₀ hzw']
  have e : |s - t| * ‖z - w‖ = ‖segPath z w s - segPath z w t‖ := by
    rw [segPath_sub_segPath, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev w z]
  rw [e]
  calc ‖segPath z w s - segPath z w t‖
      ≤ ‖segPath z w s - u‖ + ‖u - segPath z w t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖segPath z w s - u‖ + ‖segPath z w t - u‖ := by rw [norm_sub_rev u]
    _ ≤ 2 * r := by linarith

/-- Lemma `lem:segment-mass`, real form: `λ_{z,w}(B_r(u)) ≤ (2/|z-w|) r` for `r ≥ 0`. -/
theorem segMeasure_ball_toReal_le {z w : ℂ} (hzw : z ≠ w) (u : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (segMeasure z w (ball u r)).toReal ≤ 2 / ‖z - w‖ * r := by
  have hzw' : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  calc (segMeasure z w (ball u r)).toReal
      ≤ (ENNReal.ofReal (2 * r / ‖z - w‖)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (segMeasure_ball_le hzw u r)
    _ = 2 / ‖z - w‖ * r := by
        rw [ENNReal.toReal_ofReal (by positivity)]
        ring

/-- Lemma `lem:segment-mass`: `λ_{z,w}` is regular for `z ≠ w`. -/
theorem isRegular_segMeasure {z w : ℂ} (hzw : z ≠ w) : IsRegular (segMeasure z w) := by
  refine ⟨inferInstance, ⟨max ‖z‖ ‖w‖, segMeasure_compl_closedBall z w⟩, 2 / ‖z - w‖, 1,
    one_pos, fun u r hr _ => ?_⟩
  rw [Real.rpow_one]
  exact segMeasure_ball_toReal_le hzw u hr.le

/-! ## Circle measures -/

/-- `circleMeasure` agrees with `LQGDimension.Coupling.circMeas`. -/
theorem circleMeasure_eq_circMeas (z : ℂ) (r : ℝ) :
    circleMeasure z r = LQGDimension.Coupling.circMeas z r := by
  unfold circleMeasure LQGDimension.Coupling.circMeas LQGDimension.Coupling.angMeas
  rw [ENNReal.ofReal_inv_of_pos (by positivity)]

/-- `σ_{z,r}` is a probability measure. -/
instance isProbabilityMeasure_circleMeasure (z : ℂ) (r : ℝ) :
    IsProbabilityMeasure (circleMeasure z r) := by
  rw [circleMeasure_eq_circMeas]
  infer_instance

/-- The integral against `σ_{z,r}` is the circle average. -/
theorem integral_circleMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : ℂ)
    (r : ℝ) {f : ℂ → E} (hf : AEStronglyMeasurable f (circleMeasure z r)) :
    ∫ x, f x ∂(circleMeasure z r) = Real.circleAverage f z r := by
  have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  unfold circleMeasure at hf ⊢
  rw [integral_map (continuous_circleMap z r).aemeasurable hf, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), Real.circleAverage_def,
    intervalIntegral.integral_of_le h2]

/-- `σ_{z,ρ}` is supported in `closedBall 0 (|z| + |ρ|)`. -/
theorem ae_norm_le_circleMeasure (z : ℂ) (ρ : ℝ) :
    ∀ᵐ x ∂(circleMeasure z ρ), ‖x‖ ≤ ‖z‖ + |ρ| := by
  rw [circleMeasure_eq_circMeas]
  filter_upwards [LQGDimension.Coupling.ae_circMeas z ρ] with x hx
  calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
    _ = ‖z‖ + |ρ| := by rw [hx]; ring

/-- Chord bound for the circle: for `|θ - θ'| ≤ π/2`,
`(2/π) |θ - θ'| ρ ≤ |circleMap z ρ θ - circleMap z ρ θ'|`. -/
theorem le_norm_circleMap_sub_circleMap {ρ : ℝ} (hρ : 0 ≤ ρ) (z : ℂ) {θ θ' : ℝ}
    (h : |θ - θ'| ≤ Real.pi / 2) :
    2 / Real.pi * |θ - θ'| * ρ ≤ ‖circleMap z ρ θ - circleMap z ρ θ'‖ := by
  have e : circleMap z ρ θ - circleMap z ρ θ' =
      (ρ : ℂ) * Complex.exp (θ' * Complex.I) * (Complex.exp ((θ - θ' : ℝ) * Complex.I) - 1) := by
    unfold circleMap
    have : Complex.exp (θ * Complex.I) =
        Complex.exp (θ' * Complex.I) * Complex.exp ((θ - θ' : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  have hsin : |Real.sin (θ - θ')| ≤ ‖Complex.exp ((θ - θ' : ℝ) * Complex.I) - 1‖ := by
    have := Complex.abs_im_le_norm (Complex.exp ((θ - θ' : ℝ) * Complex.I) - 1)
    rwa [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero] at this
  rw [e, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hρ, mul_comm ρ]
  exact mul_le_mul_of_nonneg_right ((Real.mul_abs_le_abs_sin h).trans hsin) hρ

/-- On an interval of angles of length `π/2`, the angles whose image lies in `B_r(u)` form a
set of Lebesgue measure at most `π r / ρ`. -/
theorem volume_circleMap_preimage_ball_inter_Icc_le {ρ : ℝ} (hρ : 0 < ρ) (z u : ℂ) (r a : ℝ) :
    volume (circleMap z ρ ⁻¹' ball u r ∩ Icc a (a + Real.pi / 2)) ≤
      ENNReal.ofReal (Real.pi * r / ρ) := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le fun s hs t ht => ?_)
  simp only [mem_inter_iff, mem_preimage, mem_ball, dist_eq_norm, mem_Icc] at hs ht
  have hst : |s - t| ≤ Real.pi / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have h1 := le_norm_circleMap_sub_circleMap hρ.le z hst
  have h2 : ‖circleMap z ρ s - circleMap z ρ t‖ < 2 * r := by
    calc ‖circleMap z ρ s - circleMap z ρ t‖
        ≤ ‖circleMap z ρ s - u‖ + ‖u - circleMap z ρ t‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖circleMap z ρ s - u‖ + ‖circleMap z ρ t - u‖ := by rw [norm_sub_rev u]
      _ < 2 * r := by linarith [hs.1, ht.1]
  rw [Real.dist_eq, le_div_iff₀ hρ]
  have h4 : 2 / Real.pi * |s - t| * ρ < 2 * r := h1.trans_lt h2
  have h5 : 2 / Real.pi * |s - t| * ρ = 2 * (|s - t| * ρ) / Real.pi := by ring
  rw [h5, div_lt_iff₀ Real.pi_pos] at h4
  linarith

/-- Lemma `lem:segment-mass`, circle part: `σ_{z,ρ}(B_r(u)) ≤ 2r/ρ`. -/
theorem circleMeasure_ball_le {ρ : ℝ} (hρ : 0 < ρ) (z u : ℂ) (r : ℝ) :
    circleMeasure z ρ (ball u r) ≤ ENNReal.ofReal (2 * r / ρ) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, measure_empty]
    exact zero_le
  have hpi := Real.pi_pos
  set A := circleMap z ρ ⁻¹' ball u r with hA
  have hcover : A ∩ Ioc 0 (2 * Real.pi) ⊆
      ((A ∩ Icc 0 (0 + Real.pi / 2) ∪ A ∩ Icc (Real.pi / 2) (Real.pi / 2 + Real.pi / 2)) ∪
        A ∩ Icc Real.pi (Real.pi + Real.pi / 2)) ∪
        A ∩ Icc (3 * Real.pi / 2) (3 * Real.pi / 2 + Real.pi / 2) := by
    rintro θ ⟨hθA, hθ0, hθ1⟩
    rcases le_total θ (Real.pi / 2) with h1 | h1
    · exact Or.inl (Or.inl (Or.inl ⟨hθA, hθ0.le, by linarith⟩))
    rcases le_total θ Real.pi with h2 | h2
    · exact Or.inl (Or.inl (Or.inr ⟨hθA, h1, by linarith⟩))
    rcases le_total θ (3 * Real.pi / 2) with h3 | h3
    · exact Or.inl (Or.inr ⟨hθA, h2, by linarith⟩)
    · exact Or.inr ⟨hθA, h3, by linarith⟩
  have hvol : volume (A ∩ Ioc 0 (2 * Real.pi)) ≤ 4 * ENNReal.ofReal (Real.pi * r / ρ) := by
    refine (measure_mono hcover).trans ?_
    refine (measure_union_le _ _).trans ?_
    have hb := volume_circleMap_preimage_ball_inter_Icc_le hρ z u r
    calc volume ((A ∩ Icc 0 (0 + Real.pi / 2) ∪
            A ∩ Icc (Real.pi / 2) (Real.pi / 2 + Real.pi / 2)) ∪
            A ∩ Icc Real.pi (Real.pi + Real.pi / 2)) +
          volume (A ∩ Icc (3 * Real.pi / 2) (3 * Real.pi / 2 + Real.pi / 2))
        ≤ (volume (A ∩ Icc 0 (0 + Real.pi / 2)) +
            volume (A ∩ Icc (Real.pi / 2) (Real.pi / 2 + Real.pi / 2)) +
            volume (A ∩ Icc Real.pi (Real.pi + Real.pi / 2))) +
          volume (A ∩ Icc (3 * Real.pi / 2) (3 * Real.pi / 2 + Real.pi / 2)) := by
          gcongr
          exact (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
      _ ≤ (ENNReal.ofReal (Real.pi * r / ρ) + ENNReal.ofReal (Real.pi * r / ρ) +
            ENNReal.ofReal (Real.pi * r / ρ)) + ENNReal.ofReal (Real.pi * r / ρ) := by
          gcongr
          · exact hb 0
          · exact hb _
          · exact hb _
          · exact hb _
      _ = 4 * ENNReal.ofReal (Real.pi * r / ρ) := by ring
  rw [circleMeasure, Measure.map_apply (continuous_circleMap z ρ).measurable measurableSet_ball,
    Measure.smul_apply, Measure.restrict_apply' measurableSet_Ioc, smul_eq_mul]
  calc ENNReal.ofReal (2 * Real.pi)⁻¹ * volume (A ∩ Ioc 0 (2 * Real.pi))
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * (4 * ENNReal.ofReal (Real.pi * r / ρ)) := by
        gcongr
    _ = ENNReal.ofReal (2 * r / ρ) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- Lemma `lem:segment-mass`, real form: `σ_{z,ρ}(B_r(u)) ≤ (2/ρ) r` for `r ≥ 0`. -/
theorem circleMeasure_ball_toReal_le {ρ : ℝ} (hρ : 0 < ρ) (z u : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (circleMeasure z ρ (ball u r)).toReal ≤ 2 / ρ * r := by
  calc (circleMeasure z ρ (ball u r)).toReal
      ≤ (ENNReal.ofReal (2 * r / ρ)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (circleMeasure_ball_le hρ z u r)
    _ = 2 / ρ * r := by
        rw [ENNReal.toReal_ofReal (by positivity)]
        ring

/-- Lemma `lem:segment-mass`: `σ_{z,ρ}` is regular for `ρ > 0`. -/
theorem isRegular_circleMeasure (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) : IsRegular (circleMeasure z ρ) := by
  refine ⟨inferInstance, ⟨‖z‖ + |ρ|, compl_closedBall_eq_zero_of_ae_norm_le
    (ae_norm_le_circleMeasure z ρ)⟩, 2 / ρ, 1, one_pos, fun u r hr _ => ?_⟩
  rw [Real.rpow_one]
  exact circleMeasure_ball_toReal_le hρ z u hr.le

/-! ## Compatibility names (cleanup W15) -/

alias two_div_pi_mul_abs_le_abs_sin := Real.mul_abs_le_abs_sin

end GaussianLQG
