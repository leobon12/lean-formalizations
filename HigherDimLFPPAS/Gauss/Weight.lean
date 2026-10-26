import HigherDimLFPPAS.Signed.Radial
import HigherDimLFPPAS.Signed.Sec4
import HigherDimLQGMetric.ConvField.Scaling
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The radial weight of the convolution field (packet F2b)

`w(u) = ω_d u^{d-1} K(u e₁)` (`radWeightF2b`). On one almost-sure event, for all `ε > 0` and all
`z`, `h ∗ K_ε(z) = ∫_0^∞ w(u) h_{εu}(z) du` (`ae_convMollify_eq_integral_radWeightF2b`; the radial
formula `l2b_radial_seed` after the substitution `r = εu`). The weight has mass one and the
moments `∫ |w(u)| (1 + |log u|) du`, `∫ |w(u)| u^{-1/2} du` are finite (planning audit MA3, Details
P3 and P4.1′; signed seeds).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLFPPAS.Gauss

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The radial weight `w(u) = ω_d u^{d-1} K(u e₁)` of the convolution field. -/
def radWeightF2b (κ : Rd d → ℝ) (u : ℝ) : ℝ :=
  sphArea d * (u ^ (d - 1) * convKernel κ (u • e₁ d))

lemma continuous_radWeightF2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    Continuous (radWeightF2b κ) :=
  continuous_const.mul ((continuous_pow _).mul
    ((Signed.convKernel_contDiff_seed (by omega) hκ).continuous.comp
      (continuous_id.smul continuous_const)))

lemma measurable_radWeightF2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    Measurable (radWeightF2b κ) :=
  (continuous_radWeightF2b hd hκ).measurable

/-- The weight has mass one. -/
lemma integral_radWeightF2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∫ u in Ioi (0 : ℝ), radWeightF2b κ u = 1 := by
  have h := Signed.l9b_one_eq_radial_seed hd hκ (ε := 1) one_pos
  rw [convKernelEps_one] at h
  simp only [radWeightF2b]
  rw [integral_const_mul]
  exact h

lemma abs_log_le_growthWeight_F2b {u : ℝ} (hu : 0 < u) :
    |Real.log u| ≤ l2b_growthWeight u := by
  rw [l9b_growthWeight_eq]
  rcases le_total u 1 with h | h
  · rw [abs_of_nonpos (Real.log_nonpos hu.le h), ← Real.log_inv]
    exact le_max_left _ _
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))

/-- `∫ |w(u)| G(u) du < ∞` for the growth weight `G` of (A.1). -/
lemma integrableOn_radWeightF2b_growth (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    IntegrableOn (fun u => |radWeightF2b κ u| * l2b_growthWeight u) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => sphArea d *
      (u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u)) (Ioi 0) :=
    (Signed.l9b_integrableOn_kernelGrowth_seed hd hκ).const_mul (sphArea d)
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu0 : (0 : ℝ) < u := hu
  simp only [radWeightF2b, abs_mul, abs_of_nonneg (sphArea_nonneg d),
    abs_of_nonneg (pow_nonneg hu0.le _)]
  ring

/-- `∫ |w(u)| (a + b |log u|) du < ∞`. -/
lemma integrableOn_radWeightF2b_log (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (a b : ℝ) :
    IntegrableOn (fun u => |radWeightF2b κ u| * (a + b * |Real.log u|)) (Ioi 0) := by
  have hG := integrableOn_radWeightF2b_growth hd hκ
  refine (hG.const_mul (|a| + |b|)).mono' ?_ ?_
  · exact (((continuous_radWeightF2b hd hκ).abs.measurable).mul
      (measurable_const.add (measurable_const.mul
        (continuous_abs.measurable.comp Real.measurable_log)))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hG1 : 1 ≤ l2b_growthWeight u := l9b_one_le_growthWeight u
    have hlog := abs_log_le_growthWeight_F2b hu0
    have hw := abs_nonneg (radWeightF2b κ u)
    rw [Real.norm_eq_abs, abs_mul, abs_abs]
    have h1 : |a + b * (|Real.log u|)| ≤ (|a| + |b|) * l2b_growthWeight u := by
      calc |a + b * (|Real.log u|)| ≤ |a| + |b| * |Real.log u| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_abs]
        _ ≤ |a| * l2b_growthWeight u + |b| * l2b_growthWeight u := by
            gcongr
            nlinarith [abs_nonneg a]
        _ = (|a| + |b|) * l2b_growthWeight u := by ring
    calc |radWeightF2b κ u| * |a + b * (|Real.log u|)|
        ≤ |radWeightF2b κ u| * ((|a| + |b|) * l2b_growthWeight u) :=
          mul_le_mul_of_nonneg_left h1 hw
      _ = (|a| + |b|) * (|radWeightF2b κ u| * l2b_growthWeight u) := by ring

/-- `∫ |w(u)| du < ∞`. -/
lemma integrableOn_abs_radWeightF2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    IntegrableOn (fun u => |radWeightF2b κ u|) (Ioi 0) := by
  have h := integrableOn_radWeightF2b_log hd hκ 1 0
  simpa only [zero_mul, add_zero, mul_one] using h

lemma integrableOn_radWeightF2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    IntegrableOn (radWeightF2b κ) (Ioi 0) :=
  (integrableOn_abs_radWeightF2b hd hκ).congr_fun_ae (Filter.Eventually.of_forall fun _ => rfl)
    |>.mono' (continuous_radWeightF2b hd hκ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => le_of_eq (Real.norm_eq_abs _))

/-- `∫ |w(u)| u^{-1/2} du < ∞` (uses `d ≥ 2` and the decay `|K(x)| ≤ C (1 + |x|)^{-(d+1)}`). -/
lemma integrableOn_radWeightF2b_rpow (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    IntegrableOn (fun u => |radWeightF2b κ u| * u ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := Signed.l9b_kernel_axis_decay_seed hd hκ
  have hfin : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 5 / 2 := by
    rw [Module.finrank_self]
    norm_num
  have hint : Integrable (fun u : ℝ => (1 + ‖u‖) ^ (-(5 / 2 : ℝ))) :=
    integrable_one_add_norm hfin
  refine (hint.integrableOn.const_mul (sphArea d * C)).mono' ?_ ?_
  · exact (((continuous_radWeightF2b hd hκ).abs.measurable).mul
      (measurable_id.pow_const _)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hv : (0 : ℝ) < 1 + u := by linarith
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hpow : u ^ (d - 1) * u ^ (-(1 / 2 : ℝ)) ≤ (1 + u) ^ ((d : ℝ) - 3 / 2) := by
      have he : u ^ (d - 1) * u ^ (-(1 / 2 : ℝ)) = u ^ ((d : ℝ) - 3 / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hu0, Nat.cast_sub (by omega : 1 ≤ d)]
        congr 1
        push_cast
        ring
      rw [he]
      exact Real.rpow_le_rpow hu0.le (by linarith) (by linarith)
    have hK := hC u hu0.le
    have hpu : (0 : ℝ) ≤ u ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hu0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hpu), Real.norm_eq_abs,
      abs_of_pos hu0]
    simp only [radWeightF2b, abs_mul, abs_of_nonneg (sphArea_nonneg d),
      abs_of_nonneg (pow_nonneg hu0.le _)]
    have hcomb : (1 + u) ^ ((d : ℝ) - 3 / 2) * (1 + u) ^ (-((d : ℝ) + 1)) =
        (1 + u) ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add hv]
      congr 1
      ring
    have hq : (0 : ℝ) ≤ (1 + u) ^ (-((d : ℝ) + 1)) := Real.rpow_nonneg hv.le _
    calc sphArea d * (u ^ (d - 1) * |convKernel κ (u • e₁ d)|) * u ^ (-(1 / 2 : ℝ))
        = sphArea d * ((u ^ (d - 1) * u ^ (-(1 / 2 : ℝ))) * |convKernel κ (u • e₁ d)|) := by
          ring
      _ ≤ sphArea d * ((1 + u) ^ ((d : ℝ) - 3 / 2) * (C * (1 + u) ^ (-((d : ℝ) + 1)))) := by
          gcongr
          exact sphArea_nonneg d
      _ = sphArea d * C * ((1 + u) ^ ((d : ℝ) - 3 / 2) * (1 + u) ^ (-((d : ℝ) + 1))) := by
          ring
      _ = sphArea d * C * (1 + u) ^ (-(5 / 2 : ℝ)) := by rw [hcomb]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistRd d}

/-- **The radial formula in the variable `u = r/ε`**, on one almost-sure event for all `ε > 0`
and all centres. -/
theorem ae_convMollify_eq_integral_radWeightF2b (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      convMollify κ ε (h ω) z = ∫ u in Ioi (0 : ℝ), radWeightF2b κ u * sphereAvg (h ω) (ε * u) z := by
  filter_upwards [Signed.l2b_radial_seed d hd κ hκ P h hh] with ω hω
  intro ε hε z
  rw [hω ε hε z, ← l2b_sphere_area d hd]
  have hs := l2b_radial_integral_scale (κ := κ) hd hε hε
    (fun r => sphereAvg (h ω) (ε * r) z) (fun s => sphereAvg (h ω) s z) (fun r _ => rfl)
  rw [div_self hε.ne', convKernelEps_one] at hs
  rw [← hs, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [radWeightF2b, sphArea]
  ring

omit [IsProbabilityMeasure P] in
/-- Joint measurability of the radial integrand. -/
lemma measurable_sphereAvg_scale_F2b (hh : IsNormalizedLGF h P) (ε : ℝ) (z : Rd d) :
    Measurable fun q : Ω × ℝ => sphereAvg (h q.1) (ε * q.2) z := by
  have hm := measurable_sphereAvg_uncurry (d := d) hh.1.measurable
  have hε : Measurable fun q : Ω × ℝ => ε * q.2 := measurable_const.mul measurable_snd
  have hf : Measurable fun q : Ω × ℝ => ((q.1, ε * q.2, z) : Ω × ℝ × Rd d) :=
    measurable_fst.prodMk (hε.prodMk measurable_const)
  exact Measurable.comp (g := fun p : Ω × ℝ × Rd d => sphereAvg (h p.1) p.2.1 p.2.2)
    (f := fun q : Ω × ℝ => ((q.1, ε * q.2, z) : Ω × ℝ × Rd d)) hm hf

end HigherDimLFPPAS.Gauss
