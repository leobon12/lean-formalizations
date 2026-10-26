import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Signed.Radial
import HigherDimLQGMetric.Sec4.LocAnalysis
import HigherDimLQGMetric.Sec4.Lemma41
import HigherDimLQGMetric.Sec4.Lemma41Uniform
import HigherDimLQGMetric.Sec4.Scale
import HigherDimLQGMetric.Sec4.Lemma43Meas

/-!
# Sign-free copies: localization ([3] Lemma 4.1), shell measurability, affine scaling

Packet G1 (ruling L7; planning audit `planning/audits/MA3-inputs.md` §4.1 and §4.3 items 1–2). The declarations of
`HigherDimLQGMetric.Sec4.LocAnalysis`, `HigherDimLQGMetric.Sec4.Lemma41`, `HigherDimLQGMetric.Sec4.Lemma41Uniform`,
`HigherDimLQGMetric.Sec4.Scale`, `HigherDimLQGMetric.Sec4.Lemma43Meas`
whose statements mention the kernel predicate, copied with hypothesis `HigherDimLFPPAS.IsAdmissibleSeed κ` (the
paper's seeds: no sign condition) in place of `HigherDimLFPP.IsLFPPKernel κ`. Each copy `<name>_seed` has the
statement of `HigherDimLQGMetric.<name>` except for the kernel hypothesis (kernel-dependent definitions it mentions
are replaced by their copies); its proof is the host proof, with calls to copied declarations redirected to the
copies and everything else reused directly. Host-private helpers called by the copied proofs are copied as private
`<name>_seed`.
No proof uses nonnegativity of the seed: `IsAdmissibleSeed` has no such field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Signed

open HigherDimLQGMetric

section LocAnalysis
/-! Copies from `HigherDimLQGMetric.Sec4.LocAnalysis`. -/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open HigherDimLFPP (Rd e₁)
variable {d : ℕ}

/-- Sign-free copy of `HigherDimLQGMetric.l9b_kernel_axis_decay`. -/
theorem l9b_kernel_axis_decay_seed {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      |convKernel κ (u • e₁ d)| ≤ C * (1 + u) ^ (-((d : ℝ) + 1)) := by
  obtain ⟨C₀, hC₀⟩ := convKernel_decay_seed hd hκ
  refine ⟨max C₀ 0, le_max_right _ _, fun u hu => ?_⟩
  have hn : ‖u • e₁ d‖ = u := by
    rw [norm_smul, HigherDimLFPP.norm_e₁ (by omega), mul_one, Real.norm_eq_abs, abs_of_nonneg hu]
  calc |convKernel κ (u • e₁ d)| ≤ C₀ * (1 + ‖u • e₁ d‖) ^ (-((d : ℝ) + 1)) := hC₀ _
    _ ≤ max C₀ 0 * (1 + ‖u • e₁ d‖) ^ (-((d : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [hn]

/-- integrability of `u ↦ u^{d-1} |K(u e₁)| G(u)` on `(0, ∞)`
Sign-free copy of `HigherDimLQGMetric.l9b_integrableOn_kernelGrowth`. -/
theorem l9b_integrableOn_kernelGrowth_seed {κ : Rd d → ℝ} (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    IntegrableOn (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u)
      (Ioi (0 : ℝ)) := by
  have h : IntegrableOn (fun u : ℝ => ‖u ^ (d - 1) * convKernelEps κ 1 (u • e₁ d) *
      l2b_growthWeight u‖) (Ioi (0 : ℝ)) :=
    (l2b_integrable_radial_growth_kernel_seed hd hκ (ε := 1) one_pos).norm
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu0 : 0 < u := hu
  simp only [convKernelEps_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu0.le _),
    abs_of_nonneg (l9b_growthWeight_nonneg u)]

/-- **Tail bound**: `∫_{u > a} u^{d-1} |K(u e₁)| G(u) du ≤ 6 C / √a` for `a ≥ 1`.
Sign-free copy of `HigherDimLQGMetric.l9b_tail_bound`. -/
theorem l9b_tail_bound_seed {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ C * (1 + u) ^ (-((d : ℝ) + 1)))
    {a : ℝ} (ha : 1 ≤ a) :
    ∫ u in Ioi a, u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u ≤
      6 * C / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
  have hint : IntegrableOn (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
      l2b_growthWeight u) (Ioi a) :=
    (l9b_integrableOn_kernelGrowth_seed hd hκ).mono_set (Ioi_subset_Ioi ha0.le)
  have hpow : IntegrableOn (fun u : ℝ => 3 * C * u ^ (-(3 / 2 : ℝ))) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ha0).const_mul _
  calc ∫ u in Ioi a, u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u
      ≤ ∫ u in Ioi a, 3 * C * u ^ (-(3 / 2 : ℝ)) :=
        setIntegral_mono_on hint hpow measurableSet_Ioi fun u hu =>
          l9b_tail_pointwise hd hC0 hC (ha.trans (le_of_lt hu))
    _ = 3 * C * (2 / Real.sqrt a) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha0]
        congr 1
        rw [Real.sqrt_eq_rpow, show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num,
          Real.rpow_neg ha0.le]
        field_simp
    _ = 6 * C / Real.sqrt a := by ring

/-- `∫ K_ε = 1` in polar coordinates
Sign-free copy of `HigherDimLQGMetric.l9b_one_eq_radial`. -/
theorem l9b_one_eq_radial_seed {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ε : ℝ}
    (hε : 0 < ε) :
    sphArea d * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) = 1 := by
  rw [← l9b_integral_radial hd (fun r => convKernelEps κ ε (r • e₁ d)),
    ← integral_convKernelEps_eq_one_seed hd hκ hε]
  congr 1
  funext v
  exact l2b_convKernelEps_axis_norm hd ε v

/-- **The normalizing constant**: `|Z_ε - 1| ≤ |S^{d-1}| · 6 C_K / √(s/(2ε))` once `s/(2ε) ≥ 1`.
Sign-free copy of `HigherDimLQGMetric.l9b_locMass_sub_one_le`. -/
theorem l9b_locMass_sub_one_le_seed {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ C * (1 + u) ^ (-((d : ℝ) + 1)))
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (ha : 1 ≤ s / (2 * ε)) :
    |locMass κ ε s - 1| ≤ sphArea d * (6 * C / Real.sqrt (s / (2 * ε))) := by
  have hK := l2b_integrable_radial_kernel_seed hd hκ hε
  set w : ℝ → ℝ := fun r => r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) with hw
  have hΨm : Measurable fun r : ℝ => radBump (s / 2) s (r • e₁ d) :=
    ((contDiff_radBump (d := d) (by positivity) (by linarith)).continuous.comp
      (continuous_id.smul continuous_const)).measurable
  have hL : IntegrableOn (fun r : ℝ => r ^ (d - 1) * locKer κ ε s (r • e₁ d)) (Ioi (0 : ℝ)) := by
    refine (hK.norm).mono' ?_ ?_
    · exact ((hK.aestronglyMeasurable.mul hΨm.aestronglyMeasurable.restrict).congr
        (Eventually.of_forall fun r => by simp only [locKer, Pi.mul_apply, hw]; ring))
    · refine Eventually.of_forall fun r => ?_
      have hb := radBump_mem_Icc' (s / 2) s (r • e₁ d)
      simp only [locKer, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg hb.1]
      calc |r ^ (d - 1)| * (|convKernelEps κ ε (r • e₁ d)| * radBump (s / 2) s (r • e₁ d))
          ≤ |r ^ (d - 1)| * (|convKernelEps κ ε (r • e₁ d)| * 1) := by gcongr; exact hb.2
        _ = _ := by simp only [hw, abs_mul, mul_one]
  have hdiff : locMass κ ε s - 1 = sphArea d * ∫ r in Ioi (0 : ℝ),
      (r ^ (d - 1) * locKer κ ε s (r • e₁ d) - w r) := by
    rw [l9b_locMass_eq hd, ← l9b_one_eq_radial_seed hd hκ hε, ← mul_sub, integral_sub hL hK]
  rw [hdiff, abs_mul, abs_of_nonneg (sphArea_nonneg d)]
  refine mul_le_mul_of_nonneg_left ?_ (sphArea_nonneg d)
  -- the integrand vanishes on `(0, s/2]` and is bounded by `|w|` beyond
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ‖r ^ (d - 1) * locKer κ ε s (r • e₁ d) - w r‖ ≤
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
      calc r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| * |radBump (s / 2) s (r • e₁ d) - 1|
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
  calc |∫ r in Ioi (0 : ℝ), (r ^ (d - 1) * locKer κ ε s (r • e₁ d) - w r)|
      ≤ ∫ r in Ioi (0 : ℝ), (Ioi (s / 2)).indicator
          (fun r => r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)|) r := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le hind
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpt))
    _ = ∫ r in Ioi (s / 2), r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| := by
        rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          Ioi_inter_Ioi, max_eq_left (by positivity : (0 : ℝ) ≤ s / 2)]
    _ = ∫ u in Ioi (s / (2 * ε)), u ^ (d - 1) * |convKernel κ (u • e₁ d)| * 1 := by
        have e1 : s / 2 = ε * (s / (2 * ε)) := by field_simp
        rw [e1, ← l9b_radial_subst (by omega) hε (s / (2 * ε))
          (fun u => |convKernel κ (u • e₁ d)|) (fun _ => 1)]
        refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
        simp only [mul_one, l9b_abs_convKernelEps_axis κ hε r]
    _ ≤ ∫ u in Ioi (s / (2 * ε)), u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
          l2b_growthWeight u := by
        have hint := (l9b_integrableOn_kernelGrowth_seed hd hκ).mono_set
          (Ioi_subset_Ioi (by positivity : (0 : ℝ) ≤ s / (2 * ε)))
        refine setIntegral_mono_on ?_ hint measurableSet_Ioi fun u hu => ?_
        · refine hint.mono' ?_ ?_
          · exact (((continuous_id.pow _).mul ((convKernel_contDiff_seed (by omega)
              hκ).continuous.comp (continuous_id.smul continuous_const)).abs).mul
              continuous_const).aestronglyMeasurable
          · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
            have hu0 : 0 < u := (by positivity : (0 : ℝ) < s / (2 * ε)).trans hu
            simp only [mul_one, Real.norm_eq_abs, abs_mul, abs_abs,
              abs_of_nonneg (pow_nonneg hu0.le _)]
            exact le_mul_of_one_le_right (by positivity) (l9b_one_le_growthWeight u)
        · have hu0 : 0 < u := (by positivity : (0 : ℝ) < s / (2 * ε)).trans hu
          exact mul_le_mul_of_nonneg_left (l9b_one_le_growthWeight u)
            (mul_nonneg (pow_nonneg hu0.le _) (abs_nonneg _))
    _ ≤ 6 * C / Real.sqrt (s / (2 * ε)) := l9b_tail_bound_seed hd hκ hC0 hC ha

/-- Sign-free copy of `HigherDimLQGMetric.l9b_continuous_convKernelEps_axis`. -/
theorem l9b_continuous_convKernelEps_axis_seed {κ : Rd d → ℝ} (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ε : ℝ) :
    Continuous fun r : ℝ => convKernelEps κ ε (r • e₁ d) := by
  have hK := (convKernel_contDiff_seed (d := d) (by omega) hκ).continuous
  unfold convKernelEps
  fun_prop

/-- substituted growth integrals: `∫_{r > εa} r^{d-1}|K_ε(re₁)| G(r) ≤ (1 + log ε⁻¹) ∫_{u > a} u^{d-1}|K(ue₁)|G(u)`
for `0 < ε ≤ 1`, `a ≥ 0`
Sign-free copy of `HigherDimLQGMetric.l9b_subst_growth_le`. -/
theorem l9b_subst_growth_le_seed {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    ∫ r in Ioi (ε * a), r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| * l2b_growthWeight r ≤
      (1 + Real.log ε⁻¹) * ∫ u in Ioi a, u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
        l2b_growthWeight u := by
  have hL : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε, hε1⟩)
  have e : ∫ r in Ioi (ε * a), r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
      l2b_growthWeight r = ∫ u in Ioi a, u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
        l2b_growthWeight (ε * u) := by
    rw [← l9b_radial_subst (by omega) hε a (fun u => |convKernel κ (u • e₁ d)|)
      l2b_growthWeight]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [l9b_abs_convKernelEps_axis κ hε r]
  rw [e, ← integral_const_mul]
  have hint := (l9b_integrableOn_kernelGrowth_seed hd hκ).mono_set (Ioi_subset_Ioi ha)
  have hKc : Continuous fun u : ℝ => convKernel κ (u • e₁ d) :=
    (convKernel_contDiff_seed (by omega) hκ).continuous.comp (continuous_id.smul continuous_const)
  have hGc : ContinuousOn (fun u : ℝ => l2b_growthWeight (ε * u)) (Ioi a) :=
    l2b_continuousOn_growthWeight.comp (continuous_const.mul continuous_id).continuousOn
      fun u hu => show 0 < ε * u from mul_pos hε (lt_of_le_of_lt ha hu)
  have hbd : ∀ u ∈ Ioi a, u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight (ε * u) ≤
      (1 + Real.log ε⁻¹) * (u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u) := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt ha hu
    have h := l9b_growthWeight_scale hε hε1 hu0
    have hp : 0 ≤ u ^ (d - 1) * |convKernel κ (u • e₁ d)| :=
      mul_nonneg (pow_nonneg hu0.le _) (abs_nonneg _)
    calc u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight (ε * u)
        ≤ u ^ (d - 1) * |convKernel κ (u • e₁ d)| * ((1 + Real.log ε⁻¹) * l2b_growthWeight u) :=
          mul_le_mul_of_nonneg_left h hp
      _ = _ := by ring
  have hint2 : IntegrableOn (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
      l2b_growthWeight (ε * u)) (Ioi a) := by
    refine (hint.const_mul (1 + Real.log ε⁻¹)).mono' ?_ ?_
    · exact (((continuous_id.pow _).mul hKc.abs).continuousOn.mul hGc).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := lt_of_le_of_lt ha hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hu0.le _)
        (abs_nonneg _)) (l9b_growthWeight_nonneg _))]
      exact hbd u hu
  exact setIntegral_mono_on hint2 (hint.const_mul _) measurableSet_Ioi hbd

/-- **Pointwise localization error** (MA6 P9): if the polar formulas of `h*_ε(z)` and of the pairing
`⟨h, locTest z⟩` hold at `z`, and `|h_r(z)| ≤ C G(r)` for all `r > 0`, then
`|h*_ε(z) - Z_ε⁻¹⟨h, locTest z⟩| ≤ C |S^{d-1}| (1 + log ε⁻¹) (6 C_K/√a) (1 + 2|S^{d-1}| M_G)`,
`a = s/(2ε) ≥ 1`.
Sign-free copy of `HigherDimLQGMetric.l9b_locField_error`. -/
theorem l9b_locField_error_seed {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ CK * (1 + u) ^ (-((d : ℝ) + 1)))
    {ε s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 < s) (ha : 1 ≤ s / (2 * ε))
    (hZ : 1 / 2 ≤ locMass κ ε s)
    {g : DistRd d} {z : Rd d} {C : ℝ} (hC0 : 0 ≤ C)
    (hφ : convMollify κ ε g z = sphArea d * ∫ r in Ioi (0 : ℝ),
      r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * sphereAvg g r z)
    (hψ : g (locTest κ ε s z) = sphArea d * ∫ r in Ioi (0 : ℝ),
      r ^ (d - 1) * locTest κ ε s z (z + r • e₁ d) * sphereAvg g r z)
    (hcont : ContinuousOn (fun r => sphereAvg g r z) (Ioi 0))
    (hgrowth : ∀ r : ℝ, 0 < r → |sphereAvg g r z| ≤ C * l2b_growthWeight r) :
    |convMollify κ ε g z - (locMass κ ε s)⁻¹ * g (locTest κ ε s z)| ≤
      C * sphArea d * (1 + Real.log ε⁻¹) * (6 * CK / Real.sqrt (s / (2 * ε))) *
        (1 + 2 * sphArea d * l9bKernelMoment κ) := by
  have hK := convKernel_contDiff_seed (d := d) (by omega) hκ
  have hL : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε, hε1⟩)
  have hA0 : 0 ≤ sphArea d := sphArea_nonneg d
  have hZ0 : 0 < locMass κ ε s := by linarith
  -- abbreviations as functions of `r`
  let W : ℝ → ℝ := fun r => r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)|
  let Ψ : ℝ → ℝ := fun r => radBump (s / 2) s (r • e₁ d)
  let H : ℝ → ℝ := fun r => sphereAvg g r z
  have hKc := l9b_continuous_convKernelEps_axis_seed hd hκ ε
  have hΨc : Continuous Ψ :=
    (contDiff_radBump (d := d) (by positivity) (by linarith)).continuous.comp
      (continuous_id.smul continuous_const)
  have hΨ01 : ∀ r, 0 ≤ Ψ r ∧ Ψ r ≤ 1 := fun r =>
    ⟨(radBump_mem_Icc' (s / 2) s (r • e₁ d)).1, (radBump_mem_Icc' (s / 2) s (r • e₁ d)).2⟩
  -- integrable majorant `C W G`
  have hgk := l2b_integrable_radial_growth_kernel_seed hd hκ hε
  have hWG : IntegrableOn (fun r => W r * l2b_growthWeight r) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun r : ℝ => ‖r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) *
        l2b_growthWeight r‖) (Ioi (0 : ℝ)) := hgk.norm
    refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hr0 : 0 < r := hr
    simp only [W, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0.le _),
      abs_of_nonneg (l9b_growthWeight_nonneg r)]
  -- integrability of the two integrands
  have hf1m : AEStronglyMeasurable (fun r => r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * H r)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((continuous_id.pow _).mul hKc).continuousOn.mul hcont).aestronglyMeasurable measurableSet_Ioi
  have hf1 : IntegrableOn (fun r => r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * H r)
      (Ioi (0 : ℝ)) := by
    refine (hWG.const_mul C).mono' hf1m ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hr0 : 0 < r := hr
    have hH := hgrowth r hr0
    have hW0 : 0 ≤ W r := mul_nonneg (pow_nonneg hr0.le _) (abs_nonneg _)
    calc ‖r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * H r‖ = W r * |H r| := by
          simp only [W, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0.le _)]
      _ ≤ W r * (C * l2b_growthWeight r) := mul_le_mul_of_nonneg_left hH hW0
      _ = C * (W r * l2b_growthWeight r) := by ring
  have hf2 : IntegrableOn (fun r => r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * Ψ r * H r)
      (Ioi (0 : ℝ)) := by
    refine hf1.norm.mono' ((((continuous_id.pow _).mul hKc).mul hΨc).continuousOn.mul
      hcont |>.aestronglyMeasurable measurableSet_Ioi) (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      show r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * Ψ r * H r =
        Ψ r * (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * H r) by ring,
      abs_mul, abs_of_nonneg (hΨ01 r).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hΨ01 r).2
  -- the pairing in terms of `Ψ`
  have hψ' : g (locTest κ ε s z) = sphArea d * ∫ r in Ioi (0 : ℝ),
      r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * Ψ r * H r := by
    rw [hψ]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [Ψ, H, locTest_axis hK hs, locKer]
    ring
  -- the difference as one integral
  have hdiff : convMollify κ ε g z - (locMass κ ε s)⁻¹ * g (locTest κ ε s z) =
      sphArea d * ∫ r in Ioi (0 : ℝ), (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * H r -
        (locMass κ ε s)⁻¹ * (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * Ψ r * H r)) := by
    rw [hφ, hψ', integral_sub hf1 (hf2.const_mul _), integral_const_mul]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg hA0]
  -- pointwise domination
  set c := |1 - (locMass κ ε s)⁻¹| with hc
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ‖r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * H r -
      (locMass κ ε s)⁻¹ * (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * Ψ r * H r)‖ ≤
      C * ((Ioi (s / 2)).indicator (fun r => W r * l2b_growthWeight r) r) +
      C * c * (W r * l2b_growthWeight r) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hHr := hgrowth r hr0
    have hG0 := l9b_growthWeight_nonneg r
    have hW0 : 0 ≤ W r := mul_nonneg (pow_nonneg hr0.le _) (abs_nonneg _)
    have e : r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * H r -
        (locMass κ ε s)⁻¹ * (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * Ψ r * H r) =
        (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d)) * H r * (1 - (locMass κ ε s)⁻¹ * Ψ r) := by
      ring
    have hWr : |r ^ (d - 1) * convKernelEps κ ε (r • e₁ d)| = W r := by
      simp only [W, abs_mul, abs_of_nonneg (pow_nonneg hr0.le _)]
    have hfac : |1 - (locMass κ ε s)⁻¹ * Ψ r| ≤
        (Ioi (s / 2)).indicator (fun _ => (1 : ℝ)) r + c := by
      by_cases hrs : s / 2 < r
      · rw [indicator_of_mem (show r ∈ Ioi (s / 2) from hrs)]
        have e2 : 1 - (locMass κ ε s)⁻¹ * Ψ r = (1 - Ψ r) + (1 - (locMass κ ε s)⁻¹) * Ψ r := by
          ring
        rw [e2]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_le]; constructor <;> linarith [(hΨ01 r).1, (hΨ01 r).2]
        · rw [abs_mul, abs_of_nonneg (hΨ01 r).1]
          exact mul_le_of_le_one_right (abs_nonneg _) (hΨ01 r).2
      · rw [indicator_of_notMem (show r ∉ Ioi (s / 2) from hrs), zero_add]
        rcases l9b_radBump_axis_eq_one (d := d) hs hr0.le (not_lt.1 hrs) with h1 | h0
        · simp only [Ψ, h1, mul_one]; exact le_rfl
        · omega
    have hI0 : 0 ≤ (Ioi (s / 2)).indicator (fun _ => (1 : ℝ)) r :=
      indicator_nonneg (fun _ _ => zero_le_one) r
    have hind : (Ioi (s / 2)).indicator (fun r => W r * l2b_growthWeight r) r =
        (Ioi (s / 2)).indicator (fun _ => (1 : ℝ)) r * (W r * l2b_growthWeight r) := by
      by_cases hrs : r ∈ Ioi (s / 2)
      · simp [indicator_of_mem hrs]
      · simp [indicator_of_notMem hrs]
    rw [e, Real.norm_eq_abs, abs_mul, abs_mul, hWr, hind]
    calc W r * |H r| * |1 - (locMass κ ε s)⁻¹ * Ψ r|
        ≤ W r * (C * l2b_growthWeight r) *
            ((Ioi (s / 2)).indicator (fun _ => (1 : ℝ)) r + c) := by gcongr
      _ = C * ((Ioi (s / 2)).indicator (fun _ => (1 : ℝ)) r * (W r * l2b_growthWeight r)) +
            C * c * (W r * l2b_growthWeight r) := by ring
  -- integrate the domination
  have hI1 : IntegrableOn (fun r : ℝ => C * ((Ioi (s / 2)).indicator
      (fun r => W r * l2b_growthWeight r) r)) (Ioi (0 : ℝ)) :=
    (hWG.indicator measurableSet_Ioi).const_mul C
  have hI2 : IntegrableOn (fun r : ℝ => C * c * (W r * l2b_growthWeight r)) (Ioi (0 : ℝ)) :=
    hWG.const_mul _
  have hmain := norm_integral_le_of_norm_le (hI1.add hI2)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpt))
  rw [Real.norm_eq_abs] at hmain
  simp only [Pi.add_apply] at hmain
  rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left (by positivity : (0 : ℝ) ≤ s / 2)] at hmain
  -- the two growth integrals
  have ha0 : 0 ≤ s / (2 * ε) := by positivity
  have hT1 : ∫ r in Ioi (s / 2), W r * l2b_growthWeight r ≤
      (1 + Real.log ε⁻¹) * (6 * CK / Real.sqrt (s / (2 * ε))) := by
    have e1 : s / 2 = ε * (s / (2 * ε)) := by field_simp
    rw [e1]
    exact (l9b_subst_growth_le_seed hd hκ hε hε1 ha0).trans
      (mul_le_mul_of_nonneg_left (l9b_tail_bound_seed hd hκ hCK0 hCK ha) (by linarith))
  have hT2 : ∫ r in Ioi (0 : ℝ), W r * l2b_growthWeight r ≤
      (1 + Real.log ε⁻¹) * l9bKernelMoment κ := by
    have h := l9b_subst_growth_le_seed (κ := κ) hd hκ hε hε1 le_rfl
    rw [mul_zero] at h
    exact h
  have hcbound : c ≤ 2 * (sphArea d * (6 * CK / Real.sqrt (s / (2 * ε)))) := by
    have hZ1 := l9b_locMass_sub_one_le_seed hd hκ hCK0 hCK hε hs ha
    have e : 1 - (locMass κ ε s)⁻¹ = (locMass κ ε s - 1) / locMass κ ε s := by field_simp
    rw [hc, e, abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
    nlinarith [abs_nonneg (locMass κ ε s - 1)]
  have hM0 := l9bKernelMoment_nonneg κ
  have hB0 : 0 ≤ 6 * CK / Real.sqrt (s / (2 * ε)) := by positivity
  have hc0 : 0 ≤ c := abs_nonneg _
  have hWG0 : 0 ≤ ∫ r in Ioi (0 : ℝ), W r * l2b_growthWeight r :=
    setIntegral_nonneg measurableSet_Ioi fun r hr => mul_nonneg
      (mul_nonneg (pow_nonneg (le_of_lt hr) _) (abs_nonneg _)) (l9b_growthWeight_nonneg r)
  calc sphArea d * |∫ r in Ioi (0 : ℝ), (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * H r -
        (locMass κ ε s)⁻¹ * (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * Ψ r * H r))|
      ≤ sphArea d * (C * (∫ r in Ioi (s / 2), W r * l2b_growthWeight r) +
          C * c * (∫ r in Ioi (0 : ℝ), W r * l2b_growthWeight r)) :=
        mul_le_mul_of_nonneg_left hmain hA0
    _ ≤ sphArea d * (C * ((1 + Real.log ε⁻¹) * (6 * CK / Real.sqrt (s / (2 * ε)))) +
          C * (2 * (sphArea d * (6 * CK / Real.sqrt (s / (2 * ε))))) *
            ((1 + Real.log ε⁻¹) * l9bKernelMoment κ)) := by
        gcongr
    _ = C * sphArea d * (1 + Real.log ε⁻¹) * (6 * CK / Real.sqrt (s / (2 * ε))) *
          (1 + 2 * sphArea d * l9bKernelMoment κ) := by ring

end LocAnalysis

section Lemma41
/-! Copies from `HigherDimLQGMetric.Sec4.Lemma41`. -/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open HigherDimLFPP (Rd e₁)
variable {d : ℕ}

/-- eventually (as `ε ↓ 0`) the hypotheses of `l9b_locField_error_seed` on `ε` hold at `s = locRad ε`
Sign-free copy of `HigherDimLQGMetric.l9b_eventually_locHyp`. -/
theorem l9b_eventually_locHyp_seed {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 ∧ 0 < locRad ε ∧ 1 ≤ locRad ε / (2 * ε) ∧
      1 / 2 ≤ locMass κ ε (locRad ε) := by
  obtain ⟨CK, hCK0, hCK⟩ := l9b_kernel_axis_decay_seed hd hκ
  have hL := tendsto_log_inv_nhdsGT_zero
  have hZ : Tendsto (fun ε : ℝ => sphArea d * (6 * CK / Real.sqrt ((Real.log ε⁻¹) ^ 10 / 2)))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => Real.sqrt (L ^ 10 / 2)) atTop atTop := by
      refine Real.tendsto_sqrt_atTop.comp ?_
      exact (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
    have h2 := (tendsto_const_nhds (x := 6 * CK)).div_atTop (h1.comp hL)
    simpa using h2.const_mul (sphArea d)
  have hZev := (hZ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  filter_upwards [self_mem_nhdsWithin, hL.eventually (eventually_ge_atTop 2),
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1), hZev] with ε hε hL2 hε1 hZε
  have hε0 : 0 < ε := hε
  have hLpos : 0 < Real.log ε⁻¹ := by linarith
  have hrad : 0 < locRad ε := by unfold locRad; positivity
  have ha : 1 ≤ locRad ε / (2 * ε) := by
    rw [locRad_div ε hε0]
    have : (2 : ℝ) ^ 10 ≤ (Real.log ε⁻¹) ^ 10 := pow_le_pow_left₀ (by norm_num) hL2 10
    linarith
  refine ⟨hε0, hε1.2.le, hrad, ha, ?_⟩
  have h := l9b_locMass_sub_one_le_seed hd hκ hCK0 hCK hε0 hrad ha
  rw [locRad_div ε hε0] at h
  have := abs_le.1 (h.trans hZε.le)
  linarith [this.1]

/-- For a fixed small cutoff, almost surely `|h*_ε - ĥ*_ε| ≤ Ĉ · err(ε)` on the ball.
Sign-free copy of `HigherDimLQGMetric.l9b_ae_locField_le`. -/
theorem l9b_ae_locField_le_seed (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ CK * (1 + u) ^ (-((d : ℝ) + 1)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) {R : ℝ} {Ĉ : Ω → ℝ≥0∞}
    (hĈ : ∀ᵐ ω ∂P, ∀ z ∈ closedBall (0 : Rd d) R, ∀ r : ℝ, 0 < r →
      |sphereAvg (h ω) r z| ≤ (Ĉ ω).toReal * l2b_growthWeight r)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hrad : 0 < locRad ε) (ha : 1 ≤ locRad ε / (2 * ε))
    (hZ : 1 / 2 ≤ locMass κ ε (locRad ε)) :
    ∀ᵐ ω ∂P, ∀ x ∈ closedBall (0 : Rd d) R,
      |convMollify κ ε (h ω) x - locField κ ε (h ω) x| ≤ (Ĉ ω).toReal * l9bErr d κ CK ε := by
  have hK := convKernel_contDiff_seed (d := d) (by omega) hκ
  obtain ⟨D, hDc, hDB, hBD⟩ := TopologicalSpace.exists_countable_dense_subset
    (closedBall (0 : Rd d) R)
  have hDc' : Countable D := hDc.to_subtype
  have hpair : ∀ᵐ ω ∂P, ∀ x : D, h ω (locTest κ ε (locRad ε) x) =
      sphArea d * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        locTest κ ε (locRad ε) x ((x : Rd d) + r • e₁ d) * sphereAvg (h ω) r x := by
    rw [ae_all_iff]
    intro x
    exact l2b_ae_radial_pairing hd hh.1 (locTest κ ε (locRad ε) x) x
      (locTest_radial (by omega) hK hrad x)
  filter_upwards [l2b_ae_radial_wholeSpace_seed d hd κ hκ P h hh.1, hpair, hĈ,
    hh.1.ae_continuousOn_sphereAvg hd, l2b_ae_convMollify_continuousOn_seed d hd κ hκ P h hh]
    with ω hφ hψ hgrowth ⟨_, hcont⟩ hcc
  have hconvc : Continuous fun z => convMollify κ ε (h ω) z := by
    have hc : Continuous fun z : Rd d => (ε, z) := continuous_const.prodMk continuous_id
    have hf := hcc.comp_continuous hc (fun _ => ⟨hε, mem_univ _⟩)
    simpa only [Function.comp_def] using hf
  have hfc : Continuous fun z => |convMollify κ ε (h ω) z - locField κ ε (h ω) z| :=
    (hconvc.sub (continuous_locField hK hrad _)).abs
  have hD : ∀ x ∈ D, |convMollify κ ε (h ω) x - locField κ ε (h ω) x| ≤
      (Ĉ ω).toReal * l9bErr d κ CK ε := by
    intro x hx
    have hxB := hDB hx
    have hmap : MapsTo (fun r : ℝ => ((r, x) : ℝ × Rd d)) (Ioi 0) (Ioi 0 ×ˢ univ) :=
      fun r hr => mk_mem_prod hr (mem_univ x)
    have hpc : Continuous fun r : ℝ => ((r, x) : ℝ × Rd d) :=
      continuous_id.prodMk continuous_const
    have hcx : ContinuousOn (fun r => sphereAvg (h ω) r x) (Ioi 0) :=
      ContinuousOn.comp (f := fun r : ℝ => ((r, x) : ℝ × Rd d))
        (g := fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2) hcont hpc.continuousOn hmap
    have := l9b_locField_error_seed hd hκ hCK0 hCK hε hε1 hrad ha hZ ENNReal.toReal_nonneg
      (hφ ε hε x) (hψ ⟨x, hx⟩) hcx (hgrowth x hxB)
    unfold locField
    calc |convMollify κ ε (h ω) x - (locMass κ ε (locRad ε))⁻¹ * h ω (locTest κ ε (locRad ε) x)|
        ≤ _ := this
      _ = (Ĉ ω).toReal * l9bErr d κ CK ε := by unfold l9bErr; ring
  intro x hx
  have hcl : IsClosed {z : Rd d | |convMollify κ ε (h ω) z - locField κ ε (h ω) z| ≤
      (Ĉ ω).toReal * l9bErr d κ CK ε} := isClosed_le hfc continuous_const
  exact hcl.closure_subset_iff.2 (fun z hz => hD z hz) (hBD hx)

/-- **[1] Lemma 4.1** (MA6 P9; in probability, which is what is consumed): for a normalized LGF and every
`R, η > 0`, `P[sup_{|x| ≤ R} |h*_ε(x) - ĥ*_ε(x)| > η] → 0` as `ε ↓ 0` (outer measure; no measurability of
the supremum is claimed).
Sign-free copy of `HigherDimLQGMetric.ref1_lemma41`. -/
theorem ref1_lemma41_seed (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {R : ℝ} (hR : 0 < R) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun ε => P {ω | ∃ x ∈ closedBall (0 : Rd d) R,
      η < |convMollify κ ε (h ω) x - locField κ ε (h ω) x|}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨CK, hCK0, hCK⟩ := l9b_kernel_axis_decay_seed hd hκ
  obtain ⟨Ĉ, hĈm, hĈfin, hĈ⟩ := l9b_exists_growth_const hd hh hR
  -- tail of the measurable constant
  let s : ℕ → Set Ω := fun n => {ω | (n : ℝ≥0∞) < Ĉ ω}
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_lt measurable_const hĈm
  have hsa : Antitone s := by
    intro m n hmn ω hω
    show (m : ℝ≥0∞) < Ĉ ω
    exact lt_of_le_of_lt (Nat.cast_le.2 hmn) hω
  have hsI : P (⋂ n, s n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hĈfin)
    simp only [mem_iInter, s, mem_ofPred_eq] at hω
    simp only [mem_ofPred_eq, not_lt, top_le_iff]
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
    exact (lt_asymm hn (hω n))
  have hstend : Tendsto (fun n => P (s n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P) (fun n => (hsm n).nullMeasurableSet) hsa
      ⟨0, measure_ne_top _ _⟩
    rwa [hsI] at this
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  obtain ⟨M, hM⟩ := (hstend.eventually (ge_mem_nhds hθ)).exists
  have herr := (tendsto_l9bErr κ CK).eventually
    (gt_mem_nhds (show (0 : ℝ) < η / (M + 1) by positivity))
  filter_upwards [herr, l9b_eventually_locHyp_seed hd hκ] with ε hεerr ⟨hε, hε1, hrad, ha, hZ⟩
  refine le_trans (measure_mono_ae ?_) hM
  filter_upwards [l9b_ae_locField_le_seed hd hκ hCK0 hCK hh hĈ hε hε1 hrad ha hZ] with ω hω hbad
  obtain ⟨x, hx, hlt⟩ := hbad
  show (M : ℝ≥0∞) < Ĉ ω
  by_contra hle
  push Not at hle
  have hfin : Ĉ ω ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top M) hle
  have hCM : (Ĉ ω).toReal ≤ M := by
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top M) hle
    simpa using this
  have he0 := l9bErr_nonneg κ hCK0 hε hε1
  have : (Ĉ ω).toReal * l9bErr d κ CK ε < η := by
    calc (Ĉ ω).toReal * l9bErr d κ CK ε ≤ M * l9bErr d κ CK ε :=
          mul_le_mul_of_nonneg_right hCM he0
      _ ≤ (M + 1) * l9bErr d κ CK ε := by nlinarith
      _ < (M + 1) * (η / (M + 1)) := by gcongr
      _ = η := by field_simp
  linarith [hω x hx]

end Lemma41

section Lemma41Uniform
/-! Copies from `HigherDimLQGMetric.Sec4.Lemma41Uniform`. -/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open HigherDimLFPP (Rd e₁)
variable {d : ℕ}

/-- a.s. for the recentred translate: `h*_ε - ĥ*_ε` at `x + u` equals the same quantity for `h_u` at `x`
Sign-free copy of `HigherDimLQGMetric.l9b_ae_locDiff_translate`. -/
theorem l9b_ae_locDiff_translate_seed (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) (u : Rd d) {ε : ℝ} (hε : 0 < ε) (hrad : 0 < locRad ε)
    (hZ : locMass κ ε (locRad ε) ≠ 0) :
    ∀ᵐ ω ∂P, ∀ x : Rd d,
      convMollify κ ε (h ω) (x + u) - locField κ ε (h ω) (x + u) =
        convMollify κ ε (recentAff 1 u (h ω)) x - locField κ ε (recentAff 1 u (h ω)) x := by
  have hK := convKernel_contDiff_seed (d := d) (by omega) hκ
  have hN := isNormalizedLGF_recentAff hd hh.1 one_pos u
  filter_upwards [l2b_ae_convMollify_addConst_seed d hd κ hκ P _ hN] with ω hω
  intro x
  set c := sphereAvg (affineComp 1 u (h ω)) 1 0
  have h1 : convMollify κ ε (h ω) (x + u) = convMollify κ ε (recentAff 1 u (h ω)) x + c := by
    rw [← l2b_convMollify_translate_seed d hd κ hκ ε (h ω) u x, ← addConst_recentAff 1 u (h ω)]
    exact hω ε hε x c
  have h2 : locField κ ε (h ω) (x + u) = locField κ ε (recentAff 1 u (h ω)) x + c := by
    rw [← locField_affineComp_one hK hrad (h ω) u x, ← addConst_recentAff 1 u (h ω)]
    exact locField_addConst hK hrad hZ _ c x
  rw [h1, h2]
  ring

/-- **[1] Lemma 4.1, uniform in the centre** (MA6 P9): for `η, θ > 0` there is `ε₀ > 0` such that for every
normalized LGF on any probability space, every `ε ∈ (0, ε₀)` and every `u`,
`P[∃ x ∈ B̄_4(u), |h*_ε(x) - ĥ*_ε(x)| > η] ≤ θ`.
Sign-free copy of `HigherDimLQGMetric.ref1_lemma41_uniform`. -/
theorem ref1_lemma41_uniform_seed (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {η : ℝ} (hη : 0 < η) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ u : Rd d,
        P {ω | ∃ x ∈ closedBall u 4,
          η < |convMollify κ ε (h ω) x - locField κ ε (h ω) x|} ≤ θ := by
  have := l9b_normLGFLaw_prob hd
  have hcan := ref1_lemma41_seed hd hκ (normLGFLaw d) id (l9b_normLGFLaw_normalized hd)
    (R := 4) (by norm_num) hη
  have hev := (ENNReal.tendsto_nhds_zero.1 hcan) θ hθ
  have hev' := hev.and (l9b_eventually_locHyp_seed hd hκ)
  obtain ⟨ε₀, hε₀, hball⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev'
  refine ⟨ε₀, hε₀, ?_⟩
  intro Ω _ P _ h hh ε hε u
  obtain ⟨hcanε, hε0, -, hrad, -, hZ⟩ := hball hε
  have hZ0 : locMass κ ε (locRad ε) ≠ 0 := by linarith
  let A : Set (DistRd d) := {g | ∃ x ∈ closedBall (0 : Rd d) 4,
    η < |convMollify κ ε g x - locField κ ε g x|}
  have hN := isNormalizedLGF_recentAff hd hh.1 one_pos u
  calc P {ω | ∃ x ∈ closedBall u 4, η < |convMollify κ ε (h ω) x - locField κ ε (h ω) x|}
      ≤ P ((fun ω => recentAff 1 u (h ω)) ⁻¹' A) := by
        refine measure_mono_ae ?_
        filter_upwards [l9b_ae_locDiff_translate_seed hd hκ hh u hε0 hrad hZ0] with ω hω hbad
        obtain ⟨x, hx, hlt⟩ := hbad
        refine ⟨x - u, ?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right]
          rw [mem_closedBall, dist_eq_norm] at hx
          exact hx
        · have := hω (x - u)
          rw [sub_add_cancel] at this
          rw [← this]
          exact hlt
    _ ≤ normLGFLaw d A := l9b_preimage_le_normLGFLaw hd hN A
    _ ≤ θ := by simpa [A] using hcanε

end Lemma41Uniform

section Scale
/-! Copies from `HigherDimLQGMetric.Sec4.Scale`. -/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open HigherDimLFPP (Rd e₁ lfppDistOn)
variable {d : ℕ}

/-- **The convolution field under `x ↦ u + r x`** (a.s.): `h*_ε(u + r x) = (h')*_{ε/r}(x) + c` with
`h' = recentAff r u h` and `c = (h(u + r·))_1(0)`, simultaneously for all `ε > 0` and `x`; and `c = h_r(u)`.
Sign-free copy of `HigherDimLQGMetric.l9b_ae_convMollify_affine`. -/
theorem l9b_ae_convMollify_affine_seed (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) (u : Rd d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, (∀ ε : ℝ, 0 < ε → ∀ x : Rd d,
      convMollify κ ε (h ω) (u + r • x) =
        convMollify κ (ε / r) (recentAff r u (h ω)) x + sphereAvg (affineComp r u (h ω)) 1 0) ∧
      sphereAvg (affineComp r u (h ω)) 1 0 = sphereAvg (h ω) r u := by
  have hu := hh.1.affineComp one_pos u
  have hN := isNormalizedLGF_recentAff hd hh.1 hr u
  filter_upwards [l2b_ae_convMollify_scale_seed d hd κ hκ P _ hu hr,
    l2b_ae_convMollify_addConst_seed d hd κ hκ P _ hN,
    hh.1.ae_sphereAvg_affineComp hd hr u one_pos 0] with ω hsc hadd hsph
  refine ⟨fun ε hε x => ?_, ?_⟩
  · have e1 : affineComp r 0 (affineComp 1 u (h ω)) = affineComp r u (h ω) := by
      rw [affineComp_affineComp, one_mul, smul_zero, zero_add]
    calc convMollify κ ε (h ω) (u + r • x)
        = convMollify κ ε (affineComp 1 u (h ω)) (r • x) := by
          rw [l2b_convMollify_translate_seed d hd κ hκ ε (h ω) u (r • x), add_comm]
      _ = convMollify κ (ε / r) (affineComp r u (h ω)) x := by rw [← e1, hsc ε hε x]
      _ = convMollify κ (ε / r) (addConst (recentAff r u (h ω))
            (sphereAvg (affineComp r u (h ω)) 1 0)) x := by rw [addConst_recentAff]
      _ = _ := hadd (ε / r) (div_pos hε hr) x _
  · rw [hsph, mul_one, smul_zero, zero_add]

end Scale

section Lemma43Meas
/-! Copies from `HigherDimLQGMetric.Sec4.Lemma43Meas`. -/

set_option warn.classDefReducibility false
open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open HigherDimLFPP (Rd e₁ lfppDistOn)
variable {d : ℕ}

/-- **Locality of the good shell event** (MA6 P3): for `24 s(ε) ≤ r` the event `E^ε_r(u; C)` is almost
surely equal to an event of `fieldSigma0 h (A_{r/4,4r}(u))`.
Sign-free copy of `HigherDimLQGMetric.ref1_lemma43_aeEventIn`. -/
theorem ref1_lemma43_aeEventIn_seed (hd : 3 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) {ξ : ℝ}
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ} (hD : IsWeakExpMetric d ξ D c)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) {ε : ℝ} (hrad : 0 < locRad ε) (hZ : locMass κ ε (locRad ε) ≠ 0)
    {r : ℝ} (hr24 : 24 * locRad ε ≤ r) (u : Rd d) {C : ℝ} (hC : 0 < C) :
    AEEventIn P (fieldSigma0 h (ann u (r / 4) (4 * r))) {ω | shellGood κ ξ D c ε C u r (h ω)} := by
  have hd2 : 2 ≤ d := by omega
  have hK := convKernel_contDiff_seed (d := d) (by omega) hκ
  have hr : 0 < r := by linarith
  set V := ann u (r / 4) (4 * r) with hV
  have hS : sphere u r ⊆ V := l9b_sphere_subset_ann (by linarith) (by linarith)
  obtain ⟨Fdiam, Facross, hFd, hFa, hae⟩ := hD.exists_shellVersions hd2 hh.1 u hr
  have hcr := hD.c_pos r hr
  -- the recentred field
  set h' : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) r u) with hh'
  have hshift : ∀ ω z, locField κ ε (h ω) z = locField κ ε (h' ω) z + sphereAvg (h ω) r u := by
    intro ω z
    have := locField_addConst hK hrad hZ (h' ω) (sphereAvg (h ω) r u) z
    rwa [hh', addConst_addConst, neg_add_cancel, addConst_zero] at this
  have hfun : ∀ ω, locField κ ε (h ω) = fun z => locField κ ε (h' ω) z + sphereAvg (h ω) r u :=
    fun ω => funext (hshift ω)
  obtain ⟨hm3, hm4⟩ := l9b_measurableSet_lfpp_shell hd2 hK ξ hrad hr24 u h'
    (C⁻¹ * (r * aEps κ ξ (ε / r))) (C * (r * aEps κ ξ (ε / r)))
  -- (1)
  have hE1 : AEEventIn P (fieldSigma0 h V) {ω | ENNReal.ofReal (C⁻¹ * c r *
      Real.exp (ξ * sphereAvg (h ω) r u)) ≤ acrossDist (D (h ω)) u (r / 2) r} := by
    refine l9b_aeEventIn_congr (E₁ := {ω | ENNReal.ofReal (C⁻¹ * c r) ≤ Facross ω})
      ⟨_, measurableSet_le measurable_const hFa, EventuallyEq.rfl⟩ ?_
    filter_upwards [hae] with ω hω'
    obtain ⟨-, hω⟩ := hω'
    apply propext
    show ENNReal.ofReal (C⁻¹ * c r) ≤ Facross ω ↔ ENNReal.ofReal (C⁻¹ * c r *
      Real.exp (ξ * sphereAvg (h ω) r u)) ≤ acrossDist (D (h ω)) u (r / 2) r
    rw [hω, l9b_ofReal_mul_le_iff (by positivity) (Real.exp_pos _), ← Real.exp_neg, ← neg_mul]
  -- (2)
  have hE2 : AEEventIn P (fieldSigma0 h V) {ω | sphereDiam (D (h ω)) u r ≤
      ENNReal.ofReal (C * c r * Real.exp (ξ * sphereAvg (h ω) r u))} := by
    refine l9b_aeEventIn_congr (E₁ := {ω | Fdiam ω ≤ ENNReal.ofReal (C * c r)})
      ⟨_, measurableSet_le hFd measurable_const, EventuallyEq.rfl⟩ ?_
    filter_upwards [hae] with ω hω'
    obtain ⟨hω, -⟩ := hω'
    apply propext
    show Fdiam ω ≤ ENNReal.ofReal (C * c r) ↔ sphereDiam (D (h ω)) u r ≤
      ENNReal.ofReal (C * c r * Real.exp (ξ * sphereAvg (h ω) r u))
    rw [hω, l9b_le_ofReal_mul_iff (by positivity) (Real.exp_pos _), ← Real.exp_neg, ← neg_mul]
  -- (3)
  have hE3 : AEEventIn P (fieldSigma0 h V) {ω | C⁻¹ * (r * aEps κ ξ (ε / r)) *
      Real.exp (ξ * sphereAvg (h ω) r u) ≤ DGZ.lfppSetDist ξ (locField κ ε (h ω))
        (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r)} := by
    have heq : {ω | C⁻¹ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) ≤
        DGZ.lfppSetDist ξ (locField κ ε (h ω)) (ann u (r / 3) (3 * r)) (sphere u (r / 2))
          (sphere u r)} = {ω | C⁻¹ * (r * aEps κ ξ (ε / r)) ≤ DGZ.lfppSetDist ξ
            (locField κ ε (h' ω)) (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r)} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [hfun ω, l9b_lfppSetDist_add_const, mul_comm (Real.exp _)]
      exact mul_le_mul_iff_left₀ (Real.exp_pos _)
    rw [heq]
    exact aeEventIn_of_recentred hd2 hh.1 (isOpen_ann _ _ _) hr hS hm3
  -- (4)
  have hE4 : AEEventIn P (fieldSigma0 h V) {ω | DGZ.lfppDiam ξ (locField κ ε (h ω))
      (sphere u r) (ann u (r / 2) (2 * r)) ≤ C * (r * aEps κ ξ (ε / r)) *
        Real.exp (ξ * sphereAvg (h ω) r u)} := by
    have heq : {ω | DGZ.lfppDiam ξ (locField κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r)) ≤
        C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)} = {ω | DGZ.lfppDiam ξ
          (locField κ ε (h' ω)) (sphere u r) (ann u (r / 2) (2 * r)) ≤
            C * (r * aEps κ ξ (ε / r))} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [hfun ω, l9b_lfppDiam_add_const, mul_comm (Real.exp _)]
      exact mul_le_mul_iff_left₀ (Real.exp_pos _)
    rw [heq]
    exact aeEventIn_of_recentred hd2 hh.1 (isOpen_ann _ _ _) hr hS hm4
  have hset : {ω | shellGood κ ξ D c ε C u r (h ω)} =
      {ω | ENNReal.ofReal (C⁻¹ * c r * Real.exp (ξ * sphereAvg (h ω) r u)) ≤
        acrossDist (D (h ω)) u (r / 2) r} ∩
      {ω | sphereDiam (D (h ω)) u r ≤
        ENNReal.ofReal (C * c r * Real.exp (ξ * sphereAvg (h ω) r u))} ∩
      {ω | C⁻¹ * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u) ≤
        DGZ.lfppSetDist ξ (locField κ ε (h ω)) (ann u (r / 3) (3 * r)) (sphere u (r / 2))
          (sphere u r)} ∩
      {ω | DGZ.lfppDiam ξ (locField κ ε (h ω)) (sphere u r) (ann u (r / 2) (2 * r)) ≤
        C * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg (h ω) r u)} := by
    ext ω
    simp only [shellGood, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [hset]
  exact l9b_aeEventIn_inter (l9b_aeEventIn_inter (l9b_aeEventIn_inter hE1 hE2) hE3) hE4

end Lemma43Meas

end HigherDimLFPPAS.Signed
