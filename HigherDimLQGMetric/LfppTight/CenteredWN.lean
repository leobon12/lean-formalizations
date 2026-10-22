import HigherDimLQGMetric.WNSplit.Generic
import HigherDimLQGMetric.Sphere.Var
import HigherDimLQGMetric.B3.Interfaces
import HigherDimLFPP.Field.VarBounds

/-!
# The centered infinite-band white-noise vectors

At every positive cutoff, `bandVecM κ (Ioi ε) δ_x σ₁` is pairable.  Its
increments cancel the common sphere measure, reducing to `δ_x - δ_y`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM IsPairable)

theorem l6a_isPairable_centeredIoi {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (x : Rd d) :
    IsPairable κ (Ioi ε) (Measure.dirac x) (unitSphereProb d) := by
  letI : IsProbabilityMeasure (unitSphereProb d) :=
    isProbabilityMeasure_unitSphereProb (by omega : 1 ≤ d)
  refine HigherDimLFPP.isPairable_of_subset_Ici hκ measurableSet_Ioi hε Ioi_subset_Ici_self
    (Measure.dirac x) (unitSphereProb d) ?_ (D := max ‖x‖ 1) ?_ ?_
  · simp only [Measure.real, measure_univ, ENNReal.toReal_one]
  · exact (ae_dirac_iff (measurableSet_le continuous_norm.measurable measurable_const)).2
      (le_max_left _ _)
  · filter_upwards [ae_unitSphereProb_norm_le d] with y hy
    exact hy.trans (le_max_right _ _)

theorem l6a_centeredIoi_sub {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (x y : Rd d) :
    bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d) -
      bandVecM κ (Ioi ε) (Measure.dirac y) (unitSphereProb d) =
      bandVecM κ (Ioi ε) (Measure.dirac x) (Measure.dirac y) := by
  letI : IsProbabilityMeasure (unitSphereProb d) :=
    isProbabilityMeasure_unitSphereProb (by omega : 1 ≤ d)
  rw [HigherDimLFPP.bandVecM_sub_bandVecM hκ
    (l6a_isPairable_centeredIoi hd hκ hε x)
    (l6a_isPairable_centeredIoi hd hκ hε y)]
  rw [add_comm (unitSphereProb d) (Measure.dirac y)]
  exact HigherDimLFPP.bandVecM_add_right hκ (Ioi ε)
    (Measure.dirac x) (Measure.dirac y) (unitSphereProb d)

theorem l6a_scalePair_dirac_sub {d : ℕ}
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (t : ℝ) (x y : Rd d) :
    HigherDimLFPP.scalePair κ t (Measure.dirac x) (Measure.dirac y)
      (Measure.dirac x) (Measure.dirac y) =
      2 * (1 - HigherDimLFPP.autoCorr κ (t⁻¹ • (x - y))) / t := by
  simp only [HigherDimLFPP.scalePair, HigherDimLFPP.mixInt, Measure.dirac_prod_dirac,
    integral_dirac, sub_self, smul_zero,
    HigherDimLFPP.autoCorr_zero hκ]
  rw [show y - x = -(x - y) by abel, smul_neg, HigherDimLFPP.autoCorr_neg]
  ring

theorem l6a_isPairable_diracIoi {d : ℕ}
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (x y : Rd d) :
    IsPairable κ (Ioi ε) (Measure.dirac x) (Measure.dirac y) := by
  refine HigherDimLFPP.isPairable_of_subset_Ici hκ measurableSet_Ioi hε Ioi_subset_Ici_self
    (Measure.dirac x) (Measure.dirac y) ?_ (D := max ‖x‖ ‖y‖) ?_ ?_
  · simp only [Measure.real, measure_univ, ENNReal.toReal_one]
  · exact (ae_dirac_iff (measurableSet_le continuous_norm.measurable measurable_const)).2
      (le_max_left _ _)
  · exact (ae_dirac_iff (measurableSet_le continuous_norm.measurable measurable_const)).2
      (le_max_right _ _)

theorem l6a_norm_centeredIoi_sub_sq_le {d : ℕ}
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {L : ℝ}
    (hL : ∀ v : Rd d, 1 - HigherDimLFPP.autoCorr κ v ≤ L * ‖v‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) (x y : Rd d) :
    ‖bandVecM κ (Ioi ε) (Measure.dirac x) (Measure.dirac y)‖ ^ 2 ≤
      L * ‖x - y‖ ^ 2 / ε ^ 2 := by
  have hp := l6a_isPairable_diracIoi hκ hε x y
  have hCov := HigherDimLFPP.scaleCov_eq_integral hκ measurableSet_Ioi
    (fun t ht => lt_trans hε ht) hp hp
  rw [HigherDimLFPP.scaleCov, real_inner_self_eq_norm_sq] at hCov
  rw [hCov]
  simp_rw [l6a_scalePair_dirac_sub hκ]
  let f : ℝ → ℝ := fun t => 2 * L * ‖x - y‖ ^ 2 * t ^ (-3 : ℝ)
  have hfint : IntegrableOn f (Ioi ε) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hε).const_mul _
  have hpairint : IntegrableOn
      (fun t => 2 * (1 - HigherDimLFPP.autoCorr κ (t⁻¹ • (x - y))) / t)
      (Ioi ε) := by
    simpa only [l6a_scalePair_dirac_sub hκ] using
      HigherDimLFPP.integrableOn_scalePair hκ measurableSet_Ioi
        (fun t ht => lt_trans hε ht) hp hp
  have hpt : ∀ t ∈ Ioi ε,
      2 * (1 - HigherDimLFPP.autoCorr κ (t⁻¹ • (x - y))) / t ≤ f t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hε ht
    have h1 := hL (t⁻¹ • (x - y))
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)] at h1
    have h3 : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le,
        Real.rpow_natCast]
    calc
      2 * (1 - HigherDimLFPP.autoCorr κ (t⁻¹ • (x - y))) / t ≤
          2 * (L * (t⁻¹ * ‖x - y‖) ^ 2) / t := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) ht0.le
      _ = f t := by
        change 2 * (L * (t⁻¹ * ‖x - y‖) ^ 2) / t =
          2 * L * ‖x - y‖ ^ 2 * t ^ (-3 : ℝ)
        rw [h3]
        field_simp
  have hle := setIntegral_mono_on hpairint hfint measurableSet_Ioi hpt
  have hval : ∫ t in Ioi ε, f t = L * ‖x - y‖ ^ 2 / ε ^ 2 := by
    change (∫ t in Ioi ε, (2 * L * ‖x - y‖ ^ 2) * t ^ (-3 : ℝ)) = _
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hε]
    have h2 : ε ^ ((-3 : ℝ) + 1) = (ε ^ 2)⁻¹ := by
      rw [show (-3 : ℝ) + 1 = -((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hε.le, Real.rpow_natCast]
    rw [h2]
    field_simp
    ring
  exact hle.trans_eq hval

/-- A continuous version of the centered infinite-band field, on any white-noise
space. This supplies the missing version premise when using `L1e_law`. -/
theorem l6a_exists_centeredIoi_version {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : HigherDimLFPP.IsWhiteNoise P W) :
    ∃ Φ : Rd d → Ω → ℝ,
      (∀ ω, Continuous fun x => Φ x ω) ∧
      (∀ x, Measurable (Φ x)) ∧
      ∀ x, Φ x =ᵐ[P]
        W (bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d)) := by
  obtain ⟨L, hL0, hL⟩ := HigherDimLFPP.exists_one_sub_autoCorr_le hκ
  let u : Rd d → WN d := fun x =>
    bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d)
  have hu : ∀ x y : Rd d, ‖u x - u y‖ ^ 2 ≤ (L / ε ^ 2) * ‖x - y‖ ^ 2 := by
    intro x y
    change ‖bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d) -
      bandVecM κ (Ioi ε) (Measure.dirac y) (unitSphereProb d)‖ ^ 2 ≤ _
    rw [l6a_centeredIoi_sub hd hκ hε x y]
    convert l6a_norm_centeredIoi_sub_sq_le hκ (fun v => (hL v).2) hε x y using 1
    ring
  exact wns_exists_version hW (u := u) (c := L / ε ^ 2)
    (div_nonneg hL0 (sq_nonneg ε)) hu

/-- Instantiate `L1e_law` with a certified continuous version of the
centered infinite-band white-noise field. -/
theorem l6a_centered_law (hL1e : L1e_law) {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W) :
    ∃ Φ : Rd d → Ω' → ℝ,
      (∀ ω', Continuous fun x => Φ x ω') ∧
      (∀ x, Measurable (Φ x)) ∧
      (∀ᵐ ω ∂P, Continuous (convMollifyNorm κ ε (h ω))) ∧
      ∀ A : Set (Rd d → ℝ), MeasurableSet A →
        P {ω | convMollifyNorm κ ε (h ω) ∈ A} =
          P' {ω' | (fun x => Φ x ω') ∈ A} := by
  obtain ⟨Φ, hΦc, hΦm, hΦW⟩ := l6a_exists_centeredIoi_version hd hκ hε hW
  obtain ⟨hcont, hlaw⟩ := hL1e d hd κ hκ ε hε P h hh P' W Φ hW hΦc hΦW
  exact ⟨Φ, hΦc, hΦm, hcont, hlaw⟩

/-- The variance of the spherical mean of a finite white-noise band is
uniformly bounded for all real `0 < ε < 1`. -/
theorem l6a_uniform_sphereBand_var {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      ‖bandVecM κ (Ioo ε 1) (unitSphereProb d) 0‖ ^ 2 ≤ C := by
  letI : IsProbabilityMeasure (unitSphereProb d) :=
    isProbabilityMeasure_unitSphereProb (by omega : 1 ≤ d)
  obtain ⟨C, hC0, hC⟩ := HigherDimLFPP.single_measure_bound hκ (2 ^ d)
  refine ⟨C, hC0, ?_⟩
  intro ε hε
  have hS0 : Ioo ε 1 ⊆ Ioi (0 : ℝ) := fun t ht => hε.1.trans ht.1
  have hSf : volume (Ioo ε 1) ≠ ⊤ := measure_Ioo_lt_top.ne
  obtain ⟨_, hvar⟩ := hC (Ioo ε 1) measurableSet_Ioo hS0 hSf
    (unitSphereProb d) (growthBound_unitSphereProb hd)
  rw [HigherDimLFPP.scaleCov_self] at hvar
  have hvol : volume.real (Ioo ε 1) ≤ 1 := by
    rw [Real.volume_real_Ioo_of_le hε.2.le]
    linarith [hε.1]
  exact hvar.trans (by nlinarith [mul_le_mul_of_nonneg_left hvol hC0])

/-- Quantitative uniform tail bound for the finite-band spherical mean as a
white-noise coordinate. -/
theorem l6a_uniform_sphereBand_tail {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ M : ℝ, 0 < M →
      P {ω | M ≤ |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω|} ≤
        ENNReal.ofReal (C / M ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := l6a_uniform_sphereBand_var hd hκ
  refine ⟨C, hC0, ?_⟩
  intro ε hε M hM
  let v : WN d := bandVecM κ (Ioo ε 1) (unitSphereProb d) 0
  have hcheb := meas_ge_le_variance_div_sq (hW.memLp v 2 (by simp)) hM
  rw [hW.integral_eq_zero, hW.variance_eq] at hcheb
  simp only [sub_zero] at hcheb
  exact hcheb.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (hC ε hε) (sq_nonneg M)))

end HigherDimLQGMetric
