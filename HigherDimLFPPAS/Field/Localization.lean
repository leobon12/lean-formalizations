import HigherDimLFPPAS.Field.Prelim
import HigherDimLFPPAS.Signed.KernelDecay

/-!
# Pathwise localization bounds for Lemma 2.3

This module contains deterministic consequences of the radial formula and the sphere-average growth
bound.  The logarithmic tail estimate uses only the pinned `(d+1)` decay of the convolution kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open HigherDimLFPP (Rd e₁)
open HigherDimLQGMetric

namespace HigherDimLFPPAS.Field

variable {d : ℕ} {κ : Rd d → ℝ}

private theorem radial_power_decay_F1 (hd : 2 ≤ d) {u : ℝ} (hu : 1 ≤ u) :
    u ^ (d - 1) * (1 + u) ^ (-((d : ℝ) + 1)) ≤ u ^ (-2 : ℝ) := by
  have hu0 : 0 < u := by linarith
  have hnat : ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) := by norm_num
  have hleftPow : (1 + u) ^ (-((d : ℝ) + 1)) =
      ((1 + u) ^ (d + 1))⁻¹ := by
    rw [hnat, Real.rpow_neg (by positivity : 0 ≤ 1 + u), Real.rpow_natCast]
  have hrightPow : u ^ (-2 : ℝ) = (u ^ (2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg hu0.le]
  rw [hleftPow, hrightPow]
  have hpow : u ^ (d - 1) * u ^ 2 = u ^ (d + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hle : u ^ (d + 1) ≤ (1 + u) ^ (d + 1) := by
    gcongr
    linarith
  rw [← hpow] at hle
  rw [← div_eq_mul_inv, ← one_div]
  rw [show u ^ (2 : ℝ) = u ^ (2 : ℕ) by rw [Real.rpow_two, pow_two]]
  rw [div_le_div_iff₀ (by positivity : 0 < (1 + u) ^ (d + 1))
    (by positivity : 0 < u ^ 2)]
  simpa [mul_comm] using hle

/-- Sharp mass tail from the repository's `(d+1)` radial kernel decay. -/
theorem radial_kernel_mass_tail_F1 (hd : 2 ≤ d) (hκ : IsAdmissibleSeed κ)
    {CK A : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤
      CK * (1 + u) ^ (-((d : ℝ) + 1))) (hA : 1 ≤ A) :
    ∫ u in Ioi A, u ^ (d - 1) * |convKernel κ (u • e₁ d)| ≤ CK / A := by
  have hA0 : 0 < A := by linarith
  have hleft := Signed.l2b_integrable_radial_kernel_seed (d := d) hd hκ one_pos
  have hleftAbs : IntegrableOn
      (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)|) (Ioi A) := by
    have h : IntegrableOn (fun u : ℝ => ‖u ^ (d - 1) *
        convKernelEps κ 1 (u • e₁ d)‖) (Ioi A) :=
      (hleft.mono_set (Ioi_subset_Ioi hA0.le)).norm
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu0 : 0 < u := lt_trans hA0 hu
    change |u ^ (d - 1) * convKernelEps κ 1 (u • e₁ d)| = _
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0.le _)]
    rw [convKernelEps_one]
  have hright : IntegrableOn (fun u : ℝ => CK * u ^ (-2 : ℝ)) (Ioi A) := by
    have hp := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hA0
    exact hp.const_mul CK
  have hpt : ∀ u ∈ Ioi A,
      u ^ (d - 1) * |convKernel κ (u • e₁ d)| ≤ CK * u ^ (-2 : ℝ) := by
    intro u hu
    have hu1 : 1 ≤ u := hA.trans (le_of_lt hu)
    have hu0 : 0 ≤ u := le_trans (by norm_num) hu1
    have hp := radial_power_decay_F1 hd hu1
    have hk := hCK u hu0
    have hpow0 : 0 ≤ u ^ (d - 1) := pow_nonneg hu0 _
    calc u ^ (d - 1) * |convKernel κ (u • e₁ d)|
        ≤ u ^ (d - 1) * (CK * (1 + u) ^ (-((d : ℝ) + 1))) := by gcongr
      _ = CK * (u ^ (d - 1) * (1 + u) ^ (-((d : ℝ) + 1))) := by ring
      _ ≤ CK * u ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hp hCK0
  calc ∫ u in Ioi A, u ^ (d - 1) * |convKernel κ (u • e₁ d)|
      ≤ ∫ u in Ioi A, CK * u ^ (-2 : ℝ) :=
        setIntegral_mono_on hleftAbs hright measurableSet_Ioi hpt
    _ = CK / A := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hA0]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num]
      norm_num [Real.rpow_neg hA0.le]
      field_simp
    _ = CK / A := rfl

set_option maxHeartbeats 800000 in
/-- Normalization estimate for a radial cutoff at `s = εL`, with the sharp `L⁻¹` rate. -/
theorem locMass_cutoff_log_bound_F1 (hd : 2 ≤ d) (hκ : IsAdmissibleSeed κ)
    {CK ε L : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤
      CK * (1 + u) ^ (-((d : ℝ) + 1))) (hε : 0 < ε) (hL : 2 ≤ L) :
    |locMass κ ε (ε * L) - 1| ≤ 2 * sphArea d * CK / L := by
  let s := ε * L
  have hs : 0 < s := mul_pos hε (by linarith)
  have hA : 1 ≤ s / (2 * ε) := by dsimp [s]; field_simp; linarith
  have hK := Signed.l2b_integrable_radial_kernel_seed (d := d) hd hκ hε
  set w : ℝ → ℝ := fun r => r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) with hw
  have hΨm : Measurable fun r : ℝ => radBump (s / 2) s (r • e₁ d) :=
    ((contDiff_radBump (d := d) (by positivity) (by linarith)).continuous.comp
      (continuous_id.smul continuous_const)).measurable
  have hL' : IntegrableOn (fun r : ℝ => r ^ (d - 1) * locKer κ ε s (r • e₁ d)) (Ioi (0 : ℝ)) := by
    refine (hK.norm).mono' ?_ ?_
    · exact ((hK.aestronglyMeasurable.mul hΨm.aestronglyMeasurable.restrict).congr
        (Eventually.of_forall fun r => by simp only [locKer, Pi.mul_apply, hw]; ring))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hr
      have hb := radBump_mem_Icc' (s / 2) s (r • e₁ d)
      simp only [locKer, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg hb.1]
      calc |r ^ (d - 1)| * (|convKernelEps κ ε (r • e₁ d)| * radBump (s / 2) s (r • e₁ d))
          ≤ |r ^ (d - 1)| * (|convKernelEps κ ε (r • e₁ d)| * 1) := by gcongr; exact hb.2
        _ = _ := by simp only [hw, abs_mul, mul_one]
  have hdiff : locMass κ ε s - 1 = sphArea d * ∫ r in Ioi (0 : ℝ),
      (r ^ (d - 1) * locKer κ ε s (r • e₁ d) - w r) := by
    rw [l9b_locMass_eq hd, ← Signed.l9b_one_eq_radial_seed hd hκ hε,
      ← mul_sub, integral_sub hL' hK]
  have hpt : ∀ r ∈ Ioi (0 : ℝ),
      ‖r ^ (d - 1) * locKer κ ε s (r • e₁ d) - w r‖ ≤
        (Ioi (s / 2)).indicator (fun r => r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)|) r := by
    intro r hr
    have hr0 : 0 < r := hr
    have hb := radBump_mem_Icc' (s / 2) s (r • e₁ d)
    have e : r ^ (d - 1) * locKer κ ε s (r • e₁ d) - w r =
        r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * (radBump (s / 2) s (r • e₁ d) - 1) := by
      simp only [hw, locKer]; ring
    rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr0.le _)]
    by_cases hrs : s / 2 < r
    · rw [indicator_of_mem (show r ∈ Ioi (s / 2) from hrs)]
      have h1 : |radBump (s / 2) s (r • e₁ d) - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
      calc r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
            |radBump (s / 2) s (r • e₁ d) - 1|
          ≤ r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| * 1 := by gcongr
        _ = _ := by ring
    · rw [indicator_of_notMem (show r ∉ Ioi (s / 2) from hrs)]
      rcases l9b_radBump_axis_eq_one (d := d) hs hr0.le (not_lt.1 hrs) with h1 | h0
      · rw [h1, sub_self, abs_zero, mul_zero]
      · omega
  have hind : IntegrableOn (fun r : ℝ => (Ioi (s / 2)).indicator
      (fun r => r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)|) r) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn ((Ioi (s / 2)).indicator fun r => ‖w r‖) (Ioi (0 : ℝ)) :=
      hK.norm.indicator measurableSet_Ioi
    refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp only [indicator, hw, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (le_of_lt (show (0 : ℝ) < r from hr)) _)]
  have herr : |∫ r in Ioi (0 : ℝ),
      (r ^ (d - 1) * locKer κ ε s (r • e₁ d) - w r)| ≤
      ∫ u in Ioi (L / 2), u ^ (d - 1) * |convKernel κ (u • e₁ d)| := by
    calc |∫ r in Ioi (0 : ℝ),
            (r ^ (d - 1) * locKer κ ε s (r • e₁ d) - w r)|
        ≤ ∫ r in Ioi (0 : ℝ), (Ioi (s / 2)).indicator
            (fun r => r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)|) r := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le hind
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpt))
      _ = ∫ r in Ioi (s / 2), r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| := by
          rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
            Ioi_inter_Ioi, max_eq_left (by positivity : (0 : ℝ) ≤ s / 2)]
      _ = ∫ u in Ioi (L / 2), u ^ (d - 1) * |convKernel κ (u • e₁ d)| * 1 := by
          have e1 : s / 2 = ε * (L / 2) := by dsimp [s]; ring
          rw [e1, ← l9b_radial_subst (by omega) hε (L / 2)
            (fun u => |convKernel κ (u • e₁ d)|) (fun _ => 1)]
          refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
          simp only [mul_one, l9b_abs_convKernelEps_axis κ hε r]
      _ = ∫ u in Ioi (L / 2), u ^ (d - 1) * |convKernel κ (u • e₁ d)| := by simp
  have hmass := radial_kernel_mass_tail_F1 (d := d) hd hκ hCK0 hCK
    (by linarith : 1 ≤ L / 2)
  rw [hdiff, abs_mul, abs_of_nonneg (sphArea_nonneg d)]
  calc sphArea d * |∫ r in Ioi (0 : ℝ),
        (r ^ (d - 1) * locKer κ ε s (r • e₁ d) - w r)|
      ≤ sphArea d * (CK / (L / 2)) :=
        mul_le_mul_of_nonneg_left (herr.trans hmass) (sphArea_nonneg d)
    _ = 2 * sphArea d * CK / L := by field_simp

set_option maxHeartbeats 800000 in
/-- Log-weighted kernel tail.  The logarithm is integrated using the exact `u⁻²` decay. -/
theorem radial_kernel_log_tail_F1 (hd : 2 ≤ d) (hκ : IsAdmissibleSeed κ)
    {CK A b : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤
      CK * (1 + u) ^ (-((d : ℝ) + 1))) (hA : 1 ≤ A) (hb : 0 ≤ b)
    (hlogA : Real.log A ≤ b) :
    ∫ u in Ioi A, u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
      (1 + b + Real.log u) ≤ 3 * CK * (1 + b) / A := by
  have hA0 : 0 < A := by linarith
  have hbase : IntegrableOn
      (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)|) (Ioi A) := by
    have h0 := Signed.l2b_integrable_radial_kernel_seed (d := d) hd hκ one_pos
    have h : IntegrableOn (fun u : ℝ => ‖u ^ (d - 1) *
        convKernelEps κ 1 (u • e₁ d)‖) (Ioi A) :=
      (h0.mono_set (Ioi_subset_Ioi hA0.le)).norm
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu0 : 0 < u := lt_trans hA0 hu
    change |u ^ (d - 1) * convKernelEps κ 1 (u • e₁ d)| = _
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0.le _), convKernelEps_one]
  have hlogSource := Signed.l2b_integrable_radial_logKernel_seed
    (d := d) hd hκ (ε := 1) one_pos
  have hlogBase : IntegrableOn
      (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| * Real.log (2 + u))
      (Ioi A) := by
    have h : IntegrableOn (fun u : ℝ => ‖u ^ (d - 1) *
        (Real.log (2 + u) * convKernelEps κ 1 (u • e₁ d))‖) (Ioi A) :=
      (hlogSource.mono_set (Ioi_subset_Ioi hA0.le)).norm
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu0 : 0 < u := lt_trans hA0 hu
    have hlogpos : 0 < Real.log (2 + u) := Real.log_pos (by linarith)
    change |u ^ (d - 1) * (Real.log (2 + u) * convKernelEps κ 1 (u • e₁ d))| = _
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hu0.le _),
      abs_of_pos hlogpos, convKernelEps_one]
    ring
  have hlog : IntegrableOn
      (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| * Real.log u) (Ioi A) := by
    refine hlogBase.mono' ?_ ?_
    · exact (((continuous_id.pow _).mul
        ((Signed.convKernel_contDiff_seed (by omega) hκ).continuous.comp
          (continuous_id.smul continuous_const)).abs).measurable.mul
        Real.measurable_log).aestronglyMeasurable.restrict
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      have hu0 : 0 < u := lt_trans hA0 hu
      have hu1 : 1 ≤ u := hA.trans hu.le
      have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
      have hlogle : Real.log u ≤ Real.log (2 + u) := Real.log_le_log hu0 (by linarith)
      have hp : 0 ≤ u ^ (d - 1) * |convKernel κ (u • e₁ d)| :=
        mul_nonneg (pow_nonneg hu0.le _) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hlogu0)]
      exact mul_le_mul_of_nonneg_left hlogle hp
  have hleft : IntegrableOn
      (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| * (1 + b + Real.log u))
      (Ioi A) := by
    have hc := hbase.const_mul (1 + b)
    have hadd : IntegrableOn
        (fun u : ℝ => (1 + b) * (u ^ (d - 1) * |convKernel κ (u • e₁ d)|) +
          u ^ (d - 1) * |convKernel κ (u • e₁ d)| * Real.log u) (Ioi A) := hc.add hlog
    refine hadd.congr_fun (fun u hu => ?_) measurableSet_Ioi
    ring
  have hpow2 : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Ioi A) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hA0
  have hpow32 : IntegrableOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (Ioi A) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hA0
  let q : ℝ → ℝ := fun u => (CK * (b + Real.log A - 1)) * u ^ (-2 : ℝ) +
    (2 * CK / Real.sqrt A) * u ^ (-(3 / 2 : ℝ))
  have hright : IntegrableOn q (Ioi A) := by
    dsimp [q]
    exact (hpow2.const_mul _).add (hpow32.const_mul _)
  have hpt : ∀ u ∈ Ioi A,
      u ^ (d - 1) * |convKernel κ (u • e₁ d)| * (1 + b + Real.log u) ≤ q u := by
    intro u hu
    have hu1 : 1 ≤ u := hA.trans hu.le
    have hu0 : 0 ≤ u := le_trans (by norm_num) hu1
    have hdec := radial_power_decay_F1 hd hu1
    have hk := hCK u hu0
    have hp0 : 0 ≤ u ^ (d - 1) := pow_nonneg hu0 _
    have hkernel : u ^ (d - 1) * |convKernel κ (u • e₁ d)| ≤ CK * u ^ (-2 : ℝ) := by
      calc u ^ (d - 1) * |convKernel κ (u • e₁ d)|
          ≤ u ^ (d - 1) * (CK * (1 + u) ^ (-((d : ℝ) + 1))) := by gcongr
        _ = CK * (u ^ (d - 1) * (1 + u) ^ (-((d : ℝ) + 1))) := by ring
        _ ≤ CK * u ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hdec hCK0
    have huA : A < u := hu
    have huPos : 0 < u := hA0.trans huA
    have hratio : 1 ≤ u / A := (le_div_iff₀ hA0).2 (by nlinarith)
    have hsqrt1 : 1 ≤ Real.sqrt (u / A) := (Real.one_le_sqrt).2 hratio
    have hsqrtpos : 0 < Real.sqrt (u / A) := Real.sqrt_pos.2 (by positivity)
    have hlogsqrt := Real.log_sqrt (by positivity : 0 ≤ u / A)
    have hlogsmall := Real.log_le_sub_one_of_pos hsqrtpos
    have hlogratio : Real.log (u / A) ≤ 2 * (Real.sqrt (u / A) - 1) := by
      nlinarith
    have hlogsplit : Real.log u = Real.log A + Real.log (u / A) := by
      have heq : A * (u / A) = u := by field_simp
      calc Real.log u = Real.log (A * (u / A)) := by rw [heq]
        _ = Real.log A + Real.log (u / A) := Real.log_mul hA0.ne' (div_ne_zero huPos.ne' hA0.ne')
    have hlogu : Real.log u ≤ Real.log A + 2 * (Real.sqrt (u / A) - 1) := by
      rw [hlogsplit]
      linarith
    have hbracket : 0 ≤ 1 + b + Real.log u := by
      have : 0 ≤ Real.log u := Real.log_nonneg hu1
      linarith
    have hbracket' : 0 ≤ 1 + b + Real.log A + 2 * (Real.sqrt (u / A) - 1) := by
      have : 0 ≤ Real.sqrt (u / A) - 1 := by linarith
      have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA
      nlinarith [hb, hlogA0]
    calc u ^ (d - 1) * |convKernel κ (u • e₁ d)| * (1 + b + Real.log u)
        ≤ CK * u ^ (-2 : ℝ) * (1 + b + Real.log u) :=
          mul_le_mul_of_nonneg_right hkernel hbracket
      _ ≤ CK * u ^ (-2 : ℝ) *
            (1 + b + Real.log A + 2 * (Real.sqrt (u / A) - 1)) := by
          have hbracketStep : 1 + b + Real.log u ≤
              1 + b + Real.log A + 2 * (Real.sqrt (u / A) - 1) := by linarith
          exact mul_le_mul_of_nonneg_left hbracketStep
            (mul_nonneg hCK0 (Real.rpow_nonneg hu0 _))
      _ = q u := by
          rw [Real.sqrt_div huPos.le A, Real.sqrt_eq_rpow]
          dsimp [q]
          have hcomb : u ^ (-2 : ℝ) * u ^ (1 / 2 : ℝ) = u ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_add huPos]
            congr 1
            ring
          have hcomb2 : u ^ (-2 : ℝ) *
              (u ^ (1 / 2 : ℝ) / Real.sqrt A) =
              u ^ (-(3 / 2 : ℝ)) / Real.sqrt A := by
            calc u ^ (-2 : ℝ) * (u ^ (1 / 2 : ℝ) / Real.sqrt A)
                = (u ^ (-2 : ℝ) * u ^ (1 / 2 : ℝ)) / Real.sqrt A := by ring
              _ = _ := by rw [hcomb]
          calc CK * u ^ (-2 : ℝ) *
                (1 + b + Real.log A + 2 * (u ^ (1 / 2 : ℝ) / Real.sqrt A - 1))
              = CK * (b + Real.log A - 1) * u ^ (-2 : ℝ) +
                  2 * CK * (u ^ (-2 : ℝ) * (u ^ (1 / 2 : ℝ) / Real.sqrt A)) := by ring
            _ = CK * (b + Real.log A - 1) * u ^ (-2 : ℝ) +
                  2 * CK * (u ^ (-(3 / 2 : ℝ)) / Real.sqrt A) := by rw [hcomb2]
            _ = q u := by dsimp [q]; ring
  have hint2 : ∫ u in Ioi A, u ^ (-2 : ℝ) = 1 / A := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hA0]
    norm_num [Real.rpow_neg hA0.le]
  have hint32 : ∫ u in Ioi A, u ^ (-(3 / 2 : ℝ)) = 2 / Real.sqrt A := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3 / 2 : ℝ)) < -1) hA0]
    rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num,
      Real.sqrt_eq_rpow, Real.rpow_neg hA0.le]
    field_simp
  calc ∫ u in Ioi A, u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
        (1 + b + Real.log u)
      ≤ ∫ u in Ioi A, q u := setIntegral_mono_on hleft hright measurableSet_Ioi hpt
    _ = CK * (b + Real.log A + 3) / A := by
      dsimp [q]
      rw [integral_add (hpow2.const_mul _) (hpow32.const_mul _), integral_const_mul,
        integral_const_mul, hint2, hint32]
      have hsqrtAsq : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0.le
      field_simp
      rw [pow_two, hsqrtAsq]
      <;> ring
    _ ≤ 3 * CK * (1 + b) / A := by
      have hcoef : b + Real.log A + 3 ≤ 3 * (1 + b) := by linarith
      have hfactor : 0 ≤ CK / A := div_nonneg hCK0 hA0.le
      calc CK * (b + Real.log A + 3) / A
          = (CK / A) * (b + Real.log A + 3) := by ring
        _ ≤ (CK / A) * (3 * (1 + b)) := mul_le_mul_of_nonneg_left hcoef hfactor
        _ = 3 * CK * (1 + b) / A := by ring


end HigherDimLFPPAS.Field
