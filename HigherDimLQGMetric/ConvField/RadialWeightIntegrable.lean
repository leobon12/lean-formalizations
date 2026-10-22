import HigherDimLQGMetric.ConvField.RadialIntegrable

/-! The radial kernel is integrable against the sphere-average growth weight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_continuousOn_growthWeight : ContinuousOn l2b_growthWeight (Ioi (0 : ℝ)) := by
  have hlog : ContinuousOn (fun r : ℝ => Real.log r) (Ioi 0) :=
    Real.continuousOn_log.mono (fun r hr => hr.ne')
  have hinv : ContinuousOn (fun r : ℝ => r⁻¹) (Ioi 0) :=
    continuousOn_id.inv₀ (fun r hr => hr.ne')
  have hloginv : ContinuousOn (fun r : ℝ => Real.log r⁻¹) (Ioi 0) :=
    hlog.comp hinv (fun r hr => show 0 < r⁻¹ from inv_pos.mpr hr)
  have hlogpos : ContinuousOn (fun r : ℝ => max (Real.log r) 0) (Ioi 0) :=
    hlog.sup continuousOn_const
  change ContinuousOn (fun r : ℝ => max (Real.log r⁻¹)
    (max ((max (Real.log r) 0) ^ (1 / 2 + 1 / 2 : ℝ)) 1)) (Ioi 0)
  simp only [show (1 / 2 + 1 / 2 : ℝ) = 1 by ring, Real.rpow_one]
  exact hloginv.sup (hlogpos.sup continuousOn_const)

theorem l2b_growthWeight_le_log_add_one {r : ℝ} (hr : 1 ≤ r) :
    l2b_growthWeight r ≤ Real.log (2 + r) + 1 := by
  have hr0 : 0 < r := by linarith
  have hlog : 0 ≤ Real.log r := Real.log_nonneg hr
  have hloginv : Real.log r⁻¹ ≤ 0 := by rw [Real.log_inv]; linarith
  have hlogle : Real.log r ≤ Real.log (2 + r) :=
    Real.log_le_log hr0 (by linarith)
  simp only [l2b_growthWeight, max_eq_left hlog,
    show (1 / 2 + 1 / 2 : ℝ) = 1 by ring, Real.rpow_one]
  have hmax : max (Real.log r) 1 ≤ Real.log (2 + r) + 1 :=
    max_le (by linarith) (by
      have : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
      linarith)
  exact (max_le (by linarith) hmax)

set_option maxHeartbeats 1000000 in
theorem l2b_integrable_radial_growth_kernel (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      convKernelEps κ ε (r • e₁ d) * l2b_growthWeight r) (Ioi (0 : ℝ)) := by
  let K : ℝ → ℝ := fun r => convKernelEps κ ε (r • e₁ d)
  let f : ℝ → ℝ := fun r => r ^ (d - 1) * K r * l2b_growthWeight r
  have hKc : Continuous K := by
    dsimp [K, convKernelEps]
    exact continuous_const.mul
      ((convKernel_contDiff (by omega) hκ).continuous.comp
        ((continuous_const : Continuous fun _ : ℝ => ε⁻¹).smul
          (continuous_id.smul continuous_const)))
  have hfc : ContinuousOn f (Ioi (0 : ℝ)) :=
    ((continuous_id.pow _).mul hKc).continuousOn.mul l2b_continuousOn_growthWeight
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) :=
    hfc.aestronglyMeasurable measurableSet_Ioi
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).bddAbove_image
    hKc.abs.continuousOn
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ r ∈ Icc (0 : ℝ) 1, |K r| ≤ M := by
    intro r hr
    exact (hM₀ (mem_image_of_mem _ hr)).trans (le_max_left _ _)
  have hnear : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    have hbound : IntegrableOn (fun _ : ℝ => M * 2) (Ioc (0 : ℝ) 1) :=
      (integrableOn_const isCompact_Icc.measure_ne_top).mono_set Ioc_subset_Icc_self
    apply hbound.mono' ?_ ?_
    · exact hfm.mono_measure (Measure.restrict_mono_set volume
        (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0))
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      have hr0 : 0 < r := hr.1
      have hw := l2b_polar_log_weight_bounded hd (R := 1) (by norm_num) hr0 hr.2
      have hW0 : 0 ≤ l2b_growthWeight r := by
        exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
      have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr0.le _
      have hk := hM r ⟨hr0.le, hr.2⟩
      have hw2 : r ^ (d - 1) * l2b_growthWeight r ≤ 2 := by
        simpa only [l2b_growthWeight, one_pow, Real.log_one, max_eq_right zero_le_one,
          one_mul, one_add_one_eq_two] using hw
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp0,
        abs_of_nonneg hW0]
      calc r ^ (d - 1) * |K r| * l2b_growthWeight r
          = (r ^ (d - 1) * l2b_growthWeight r) * |K r| := by ring
        _ ≤ 2 * M := mul_le_mul hw2 hk (abs_nonneg _) (by norm_num)
        _ = M * 2 := by ring
  have hplain := l2b_integrable_radial_kernel hd hκ hε
  have hlog := l2b_integrable_radial_logKernel hd hκ hε
  have hfar : IntegrableOn f (Ioi (1 : ℝ)) := by
    have hsource : IntegrableOn (fun r : ℝ =>
        |r ^ (d - 1) * (Real.log (2 + r) * K r)| +
          |r ^ (d - 1) * K r|) (Ioi (1 : ℝ)) :=
      ((hlog.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).norm).add
        ((hplain.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).norm)
    apply hsource.mono' ?_ ?_
    · exact hfm.mono_measure (Measure.restrict_mono_set volume (Ioi_subset_Ioi
        (by norm_num : (0 : ℝ) ≤ 1)))
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
      have hr1 : 1 ≤ r := le_of_lt hr
      have hr0 : 0 ≤ r := by linarith
      have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr0 _
      have hW0 : 0 ≤ l2b_growthWeight r := by
        exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
      have hlog0 : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
      have hw := l2b_growthWeight_le_log_add_one hr1
      change |r ^ (d - 1) * K r * l2b_growthWeight r| ≤
        |r ^ (d - 1) * (Real.log (2 + r) * K r)| + |r ^ (d - 1) * K r|
      simp only [abs_mul, abs_of_nonneg hp0,
        abs_of_nonneg hW0, abs_of_nonneg hlog0]
      calc r ^ (d - 1) * |K r| * l2b_growthWeight r
          ≤ r ^ (d - 1) * |K r| * (Real.log (2 + r) + 1) := by gcongr
        _ = r ^ (d - 1) * (Real.log (2 + r) * |K r|) +
            r ^ (d - 1) * |K r| := by ring
  have hu : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) := by ext r; simp
  rw [← hu]
  exact hnear.union hfar

/-- The same radial integrability argument for a continuous envelope with one log moment. -/
theorem l2b_integrable_radial_growth_of_log (hd : 2 ≤ d)
    (K : ℝ → ℝ) (hKc : Continuous K)
    (hplain : IntegrableOn (fun r : ℝ => r ^ (d - 1) * K r) (Ioi (0 : ℝ)))
    (hlog : IntegrableOn (fun r : ℝ => r ^ (d - 1) * (Real.log (2 + r) * K r))
      (Ioi (0 : ℝ))) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) * K r * l2b_growthWeight r)
      (Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun r => r ^ (d - 1) * K r * l2b_growthWeight r
  have hfc : ContinuousOn f (Ioi (0 : ℝ)) :=
    ((continuous_id.pow _).mul hKc).continuousOn.mul l2b_continuousOn_growthWeight
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) :=
    hfc.aestronglyMeasurable measurableSet_Ioi
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).bddAbove_image
    hKc.abs.continuousOn
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ r ∈ Icc (0 : ℝ) 1, |K r| ≤ M := by
    intro r hr
    exact (hM₀ (mem_image_of_mem _ hr)).trans (le_max_left _ _)
  have hnear : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    have hbound : IntegrableOn (fun _ : ℝ => M * 2) (Ioc (0 : ℝ) 1) :=
      (integrableOn_const isCompact_Icc.measure_ne_top).mono_set Ioc_subset_Icc_self
    apply hbound.mono' ?_ ?_
    · exact hfm.mono_measure (Measure.restrict_mono_set volume
        (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0))
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
      have hr0 : 0 < r := hr.1
      have hw := l2b_polar_log_weight_bounded hd (R := 1) (by norm_num) hr0 hr.2
      have hW0 : 0 ≤ l2b_growthWeight r :=
        (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
      have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr0.le _
      have hk := hM r ⟨hr0.le, hr.2⟩
      have hw2 : r ^ (d - 1) * l2b_growthWeight r ≤ 2 := by
        simpa only [l2b_growthWeight, one_pow, Real.log_one, max_eq_right zero_le_one,
          one_mul, one_add_one_eq_two] using hw
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp0,
        abs_of_nonneg hW0]
      calc r ^ (d - 1) * |K r| * l2b_growthWeight r
          = (r ^ (d - 1) * l2b_growthWeight r) * |K r| := by ring
        _ ≤ 2 * M := mul_le_mul hw2 hk (abs_nonneg _) (by norm_num)
        _ = M * 2 := by ring
  have hfar : IntegrableOn f (Ioi (1 : ℝ)) := by
    have hsource : IntegrableOn (fun r : ℝ =>
        |r ^ (d - 1) * (Real.log (2 + r) * K r)| +
          |r ^ (d - 1) * K r|) (Ioi (1 : ℝ)) :=
      ((hlog.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).norm).add
        ((hplain.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).norm)
    apply hsource.mono' ?_ ?_
    · exact hfm.mono_measure (Measure.restrict_mono_set volume (Ioi_subset_Ioi
        (by norm_num : (0 : ℝ) ≤ 1)))
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
      have hr1 : 1 ≤ r := le_of_lt hr
      have hr0 : 0 ≤ r := by linarith
      have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr0 _
      have hW0 : 0 ≤ l2b_growthWeight r :=
        (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
      have hlog0 : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
      have hw := l2b_growthWeight_le_log_add_one hr1
      change |r ^ (d - 1) * K r * l2b_growthWeight r| ≤
        |r ^ (d - 1) * (Real.log (2 + r) * K r)| + |r ^ (d - 1) * K r|
      simp only [abs_mul, abs_of_nonneg hp0, abs_of_nonneg hW0, abs_of_nonneg hlog0]
      calc r ^ (d - 1) * |K r| * l2b_growthWeight r
          ≤ r ^ (d - 1) * |K r| * (Real.log (2 + r) + 1) := by gcongr
        _ = r ^ (d - 1) * (Real.log (2 + r) * |K r|) +
            r ^ (d - 1) * |K r| := by ring
  have hu : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) := by ext r; simp
  rw [← hu]
  exact hnear.union hfar

end HigherDimLQGMetric
