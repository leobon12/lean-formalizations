import HigherDimLQGMetric.ConvField.RateIntegral

/-! The integrable radial weight carried by a compactly supported test function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

theorem l2b_continuous_radial_weight (φ : TestRd d) (z : Rd d) :
    Continuous fun r : ℝ =>
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        r ^ (d - 1) * φ (z + r • e₁ d) := by
  exact (continuous_const.mul (continuous_id.pow _)).mul
    (φ.continuous.comp (by fun_prop : Continuous fun r : ℝ => z + r • e₁ d))

theorem l2b_exists_radial_weight_support (hd : 2 ≤ d) (φ : TestRd d) (z : Rd d) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R < r →
      ((volume : Measure (Rd d)).toSphere univ).toReal *
        r ^ (d - 1) * φ (z + r • e₁ d) = 0 := by
  obtain ⟨R₀, hR₀⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall z
  let R : ℝ := max 0 R₀
  refine ⟨R, le_max_left _ _, fun r hr => ?_⟩
  have hφ0 : φ (z + r • e₁ d) = 0 := image_eq_zero_of_notMem_tsupport fun ht => by
    have hx := hR₀ ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      HigherDimLFPP.norm_e₁ (by omega : 0 < d), mul_one,
      Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt (le_max_left _ _) hr)] at hx
    exact (not_lt_of_ge (hx.trans (le_max_right _ _))) hr
  simp [hφ0]

theorem l2b_integrable_radial_weight_mul (hd : 2 ≤ d)
    (φ : TestRd d) (z : Rd d) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun r : ℝ =>
      (((volume : Measure (Rd d)).toSphere univ).toReal *
        r ^ (d - 1) * φ (z + r • e₁ d)) * g r)
      (volume.restrict (Ioi (0 : ℝ))) := by
  obtain ⟨R, hR0, hR⟩ := l2b_exists_radial_weight_support hd φ z
  have hc : Continuous fun r : ℝ =>
      (((volume : Measure (Rd d)).toSphere univ).toReal *
        r ^ (d - 1) * φ (z + r • e₁ d)) * g r :=
    (l2b_continuous_radial_weight φ z).mul hg
  refine (hc.continuousOn.integrableOn_compact (isCompact_Icc (a := 0) (b := R))).of_forall_sdiff_eq_zero
    measurableSet_Ioi fun r ⟨hr, hn⟩ => ?_
  have hRr : R < r := by
    by_contra hle
    exact hn ⟨hr.le, le_of_not_gt hle⟩
  change (((volume : Measure (Rd d)).toSphere univ).toReal *
    r ^ (d - 1) * φ (z + r • e₁ d)) * g r = 0
  rw [hR r hRr, zero_mul]

theorem l2b_lintegral_radial_weight_ne_top (hd : 2 ≤ d)
    (φ : TestRd d) (z : Rd d) {A : ℝ} (hA : 0 ≤ A) :
    (∫⁻ r in Ioi (0 : ℝ),
      ‖((volume : Measure (Rd d)).toSphere univ).toReal *
        r ^ (d - 1) * φ (z + r • e₁ d)‖ₑ * ENNReal.ofReal (A / Real.sqrt r)) ≠ ⊤ := by
  obtain ⟨R₀, hR₀⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall z
  let R : ℝ := max 1 R₀
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith
  have hsup : ∀ x ∈ tsupport (⇑φ), x ∈ closedBall z R := by
    intro x hx
    rw [mem_closedBall]
    exact (show dist x z ≤ R₀ from hR₀ hx).trans (le_max_right _ _)
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hM0 : 0 ≤ M := (norm_nonneg (φ z)).trans (hM z)
  let area : ℝ := ((volume : Measure (Rd d)).toSphere univ).toReal
  have harea : 0 ≤ area := ENNReal.toReal_nonneg
  let w : ℝ → ℝ := fun r => area * r ^ (d - 1) * φ (z + r • e₁ d)
  let C : ℝ := area * A * M * (R ^ (d - 2) * Real.sqrt R)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hwR : ∀ r : ℝ, R < r → w r = 0 := by
    intro r hr
    have hφ0 : φ (z + r • e₁ d) = 0 := image_eq_zero_of_notMem_tsupport fun ht => by
      have hx := hsup _ ht
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        HigherDimLFPP.norm_e₁ (by omega : 0 < d), mul_one,
        Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hR0 hr)] at hx
      linarith
    simp [w, hφ0]
  have hbound : ∀ r : ℝ, 0 < r → r ≤ R → |w r| * (A / Real.sqrt r) ≤ C := by
    intro r hr hrR
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
    have hpow : r ^ (d - 1) / Real.sqrt r ≤ R ^ (d - 2) * Real.sqrt R := by
      have e : d - 1 = d - 2 + 1 := by omega
      have hdiv : r / Real.sqrt r = Real.sqrt r := by
        apply (div_eq_iff (Real.sqrt_ne_zero'.2 hr)).2
        rw [← pow_two]
        exact (Real.sq_sqrt hr.le).symm
      rw [e, pow_succ, mul_div_assoc, hdiv]
      exact mul_le_mul (pow_le_pow_left₀ hr.le hrR _) (Real.sqrt_le_sqrt hrR)
        (Real.sqrt_nonneg _) (pow_nonneg hR0 _)
    have hφM : |φ (z + r • e₁ d)| ≤ M := by simpa [Real.norm_eq_abs] using hM (z + r • e₁ d)
    have hcoeff : area * A * |φ (z + r • e₁ d)| ≤ area * A * M :=
      mul_le_mul_of_nonneg_left hφM (mul_nonneg harea hA)
    have hcoeff0 : 0 ≤ area * A * |φ (z + r • e₁ d)| := by positivity
    have hpow0 : 0 ≤ R ^ (d - 2) * Real.sqrt R := by positivity
    calc
      |w r| * (A / Real.sqrt r) =
          (area * A * |φ (z + r • e₁ d)|) * (r ^ (d - 1) / Real.sqrt r) := by
            dsimp [w]
            rw [abs_mul, abs_mul, abs_of_nonneg harea,
              abs_of_nonneg (pow_nonneg hr.le _)]
            ring
      _ ≤ (area * A * M) * (R ^ (d - 2) * Real.sqrt R) :=
        mul_le_mul hcoeff hpow (div_nonneg (pow_nonneg hr.le _) hsr.le)
          (by positivity)
      _ = C := rfl
  have hle : (∫⁻ r in Ioi (0 : ℝ), ‖w r‖ₑ * ENNReal.ofReal (A / Real.sqrt r)) ≤
      ∫⁻ r in Ioi (0 : ℝ), (Iic R).indicator (fun _ => ENNReal.ofReal C) r := by
    refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
    by_cases hrR : r ≤ R
    · rw [indicator_of_mem (show r ∈ Iic R from hrR), ← ofReal_norm,
        ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hbound r hr hrR)
    · rw [hwR r (lt_of_not_ge hrR), enorm_zero, zero_mul]
      exact zero_le
  refine ne_top_of_le_ne_top ?_ hle
  rw [lintegral_indicator_const measurableSet_Iic]
  simp only [Measure.restrict_apply measurableSet_Iic]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top (measure_Icc_lt_top (a := (0 : ℝ)) (b := R)).ne
      (measure_mono fun r hr => ⟨le_of_lt hr.2, hr.1⟩))

end HigherDimLQGMetric
