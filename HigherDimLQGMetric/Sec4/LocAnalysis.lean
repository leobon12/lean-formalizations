import HigherDimLQGMetric.Sec4.LocField
import HigherDimLQGMetric.ConvField.RadialWeightIntegrable
import HigherDimLQGMetric.ConvField.RadialIntegrable

/-!
# Real analysis for [1] Lemma 4.1 (packet L9b, MA6 P9)

Deterministic estimates behind the localization lemma: with `L = log ε⁻¹`, `T = s(ε)/ε = L^{10}` and the
growth weight `G(r) = max(log r⁻¹, log⁺ r, 1)` of [1] Lemma 2.13 (L2a, `ζ = 1/2`):

* `G(εu) ≤ (1 + L) G(u)` for `ε ∈ (0, 1]`;
* the radial substitution `r = εu` turning `K_ε` into `K`;
* the tail bound `∫_{u > a} u^{d-1} |K(u e₁)| G(u) du ≤ 6 C_K / √a` (`a ≥ 1`), from
  `|K(x)| ≤ C_K (1 + |x|)^{-(d+1)}` (L1c) and `G(u) ≤ 3 √u`;
* `|Z_ε - 1| ≤ |S^{d-1}| · tail(T/2)`;
* the **pointwise error bound**: if the polar formulas hold at `z` and `|h_r(z)| ≤ C G(r)`, then
  `|h*_ε(z) - ĥ*_ε(z)| ≤ C c (1 + L)/√(T/2)` with a constant `c` independent of `ε`, `z`, `h`.

This replaces [1]'s variance argument by the polar formula and the growth bound (MA6 P9, G-11).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## The growth weight -/

theorem l9b_growthWeight_eq (r : ℝ) :
    l2b_growthWeight r = max (Real.log r⁻¹) (max (max (Real.log r) 0) 1) := by
  simp only [l2b_growthWeight, show (1 / 2 + 1 / 2 : ℝ) = 1 by ring, Real.rpow_one]

theorem l9b_one_le_growthWeight (r : ℝ) : 1 ≤ l2b_growthWeight r := by
  rw [l9b_growthWeight_eq]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem l9b_growthWeight_nonneg (r : ℝ) : 0 ≤ l2b_growthWeight r :=
  zero_le_one.trans (l9b_one_le_growthWeight r)

/-- `G(εu) ≤ (1 + log ε⁻¹) G(u)` for `0 < ε ≤ 1`, `u > 0`. -/
theorem l9b_growthWeight_scale {ε u : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hu : 0 < u) :
    l2b_growthWeight (ε * u) ≤ (1 + Real.log ε⁻¹) * l2b_growthWeight u := by
  have hL : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε, hε1⟩)
  have hg1 := l9b_one_le_growthWeight u
  have hgu := l9b_growthWeight_eq u
  set g := l2b_growthWeight u with hg
  have h1 : Real.log u⁻¹ ≤ g := by rw [hgu]; exact le_max_left _ _
  have h2 : max (Real.log u) 0 ≤ g := by
    rw [hgu]; exact (le_max_left _ _).trans (le_max_right _ _)
  rw [l9b_growthWeight_eq (ε * u)]
  have e1 : Real.log (ε * u)⁻¹ = Real.log ε⁻¹ + Real.log u⁻¹ := by
    rw [mul_inv, Real.log_mul (inv_ne_zero hε.ne') (inv_ne_zero hu.ne')]
  have e2 : Real.log (ε * u) ≤ Real.log u := by
    rw [Real.log_mul hε.ne' hu.ne']
    have : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
    linarith
  have hLg : Real.log ε⁻¹ ≤ Real.log ε⁻¹ * g := le_mul_of_one_le_right hL hg1
  refine max_le ?_ (max_le ?_ ?_)
  · rw [e1]; nlinarith
  · exact (max_le_max e2 le_rfl).trans (h2.trans (by nlinarith))
  · nlinarith

theorem l9b_growthWeight_le_sqrt {u : ℝ} (hu : 1 ≤ u) :
    l2b_growthWeight u ≤ 3 * Real.sqrt u := by
  have hu0 : 0 < u := by linarith
  have hs1 : 1 ≤ Real.sqrt u := Real.one_le_sqrt.2 hu
  have hlog : Real.log u ≤ 2 * Real.sqrt u := by
    have h := Real.log_le_rpow_div hu0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu
  have hinv : Real.log u⁻¹ ≤ 0 := by rw [Real.log_inv]; linarith
  rw [l9b_growthWeight_eq, max_eq_left hlog0]
  refine max_le (by linarith) (max_le (by linarith) (by linarith))

/-! ## The kernel along the axis -/

theorem convKernelEps_one (κ : Rd d → ℝ) : convKernelEps κ 1 = convKernel κ := by
  funext x
  simp [convKernelEps]

theorem l9b_kernel_axis_decay {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      |convKernel κ (u • e₁ d)| ≤ C * (1 + u) ^ (-((d : ℝ) + 1)) := by
  obtain ⟨C₀, hC₀⟩ := convKernel_decay hd hκ
  refine ⟨max C₀ 0, le_max_right _ _, fun u hu => ?_⟩
  have hn : ‖u • e₁ d‖ = u := by
    rw [norm_smul, HigherDimLFPP.norm_e₁ (by omega), mul_one, Real.norm_eq_abs, abs_of_nonneg hu]
  calc |convKernel κ (u • e₁ d)| ≤ C₀ * (1 + ‖u • e₁ d‖) ^ (-((d : ℝ) + 1)) := hC₀ _
    _ ≤ max C₀ 0 * (1 + ‖u • e₁ d‖) ^ (-((d : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [hn]

/-- pointwise bound behind the tail estimate -/
theorem l9b_tail_pointwise {κ : Rd d → ℝ} (hd : 2 ≤ d) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ C * (1 + u) ^ (-((d : ℝ) + 1)))
    {u : ℝ} (hu : 1 ≤ u) :
    u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u ≤ 3 * C * u ^ (-(3 / 2 : ℝ)) := by
  have hu0 : 0 < u := by linarith
  have hpow : (1 + u) ^ (-((d : ℝ) + 1)) ≤ u ^ (-((d : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by linarith)
  have hnat : u ^ (d - 1) = u ^ ((d : ℝ) - 1) := by
    rw [← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    simp
  have hsq : Real.sqrt u = u ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow u
  have hcomb : u ^ ((d : ℝ) - 1) * u ^ (-((d : ℝ) + 1)) * u ^ (1 / 2 : ℝ) =
      u ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]
    congr 1
    ring
  have hG := l9b_growthWeight_le_sqrt hu
  have hp0 : 0 ≤ u ^ (d - 1) := pow_nonneg hu0.le _
  calc u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u
      ≤ u ^ (d - 1) * (C * u ^ (-((d : ℝ) + 1))) * (3 * Real.sqrt u) := by
        have hK : |convKernel κ (u • e₁ d)| ≤ C * u ^ (-((d : ℝ) + 1)) :=
          (hC u hu0.le).trans (mul_le_mul_of_nonneg_left hpow hC0)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hK hp0) hG
          (l9b_growthWeight_nonneg u) (mul_nonneg hp0 (mul_nonneg hC0
            (Real.rpow_nonneg hu0.le _)))
    _ = 3 * C * (u ^ ((d : ℝ) - 1) * u ^ (-((d : ℝ) + 1)) * u ^ (1 / 2 : ℝ)) := by
        rw [hnat, hsq]; ring
    _ = 3 * C * u ^ (-(3 / 2 : ℝ)) := by rw [hcomb]

/-- integrability of `u ↦ u^{d-1} |K(u e₁)| G(u)` on `(0, ∞)` -/
theorem l9b_integrableOn_kernelGrowth {κ : Rd d → ℝ} (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    IntegrableOn (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u)
      (Ioi (0 : ℝ)) := by
  have h : IntegrableOn (fun u : ℝ => ‖u ^ (d - 1) * convKernelEps κ 1 (u • e₁ d) *
      l2b_growthWeight u‖) (Ioi (0 : ℝ)) :=
    (l2b_integrable_radial_growth_kernel hd hκ (ε := 1) one_pos).norm
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu0 : 0 < u := hu
  simp only [convKernelEps_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu0.le _),
    abs_of_nonneg (l9b_growthWeight_nonneg u)]

/-- **Tail bound**: `∫_{u > a} u^{d-1} |K(u e₁)| G(u) du ≤ 6 C / √a` for `a ≥ 1`. -/
theorem l9b_tail_bound {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ C * (1 + u) ^ (-((d : ℝ) + 1)))
    {a : ℝ} (ha : 1 ≤ a) :
    ∫ u in Ioi a, u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u ≤
      6 * C / Real.sqrt a := by
  have ha0 : 0 < a := by linarith
  have hint : IntegrableOn (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
      l2b_growthWeight u) (Ioi a) :=
    (l9b_integrableOn_kernelGrowth hd hκ).mono_set (Ioi_subset_Ioi ha0.le)
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

/-! ## Radial substitution and polar coordinates -/

/-- `r = εu`: `∫_{r > εa} r^{d-1} (ε^{-d} Φ(r/ε)) F(r) dr = ∫_{u > a} u^{d-1} Φ(u) F(εu) du`. -/
theorem l9b_radial_subst (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (a : ℝ) (Φ F : ℝ → ℝ) :
    ∫ r in Ioi (ε * a), r ^ (d - 1) * (ε ^ (-(d : ℝ)) * Φ (ε⁻¹ * r)) * F r =
      ∫ u in Ioi a, u ^ (d - 1) * Φ u * F (ε * u) := by
  have h := integral_comp_mul_left_Ioi
    (fun r => r ^ (d - 1) * (ε ^ (-(d : ℝ)) * Φ (ε⁻¹ * r)) * F r) a hε
  have hεpow : ε ^ (d - 1) * ε ^ (-(d : ℝ)) = ε⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hε, Nat.cast_sub hd, ← Real.rpow_neg_one]
    congr 1
    push_cast
    ring
  have hpt : ∀ u : ℝ, (ε * u) ^ (d - 1) * (ε ^ (-(d : ℝ)) * Φ (ε⁻¹ * (ε * u))) * F (ε * u) =
      ε⁻¹ * (u ^ (d - 1) * Φ u * F (ε * u)) := by
    intro u
    rw [← mul_assoc ε⁻¹ ε u, inv_mul_cancel₀ hε.ne', one_mul, mul_pow, ← hεpow]
    ring
  simp only [hpt, integral_const_mul, smul_eq_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero hε.ne') h).symm

/-- the area of the unit sphere `|S^{d-1}|` -/
def sphArea (d : ℕ) : ℝ := ((volume : Measure (Rd d)).toSphere univ).toReal

theorem sphArea_nonneg (d : ℕ) : 0 ≤ sphArea d := ENNReal.toReal_nonneg

/-- polar coordinates for radial functions: `∫ f(|v|) dv = |S^{d-1}| ∫_0^∞ r^{d-1} f(r) dr` -/
theorem l9b_integral_radial (hd : 2 ≤ d) (f : ℝ → ℝ) :
    ∫ v : Rd d, f ‖v‖ = sphArea d * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * f r := by
  have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  rw [integral_fun_norm_addHaar volume f, finrank_euclideanSpace_fin, sphArea,
    Measure.toSphere_apply_univ, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_natCast]
  simp only [smul_eq_mul, nsmul_eq_mul, Measure.real]
  rw [mul_assoc, ← integral_const_mul]

theorem l9b_norm_smul_e₁ (hd : 2 ≤ d) (v : Rd d) : ‖‖v‖ • e₁ d‖ = ‖v‖ := by
  rw [norm_smul, HigherDimLFPP.norm_e₁ (by omega), mul_one, Real.norm_eq_abs, abs_norm]

/-- `Z_ε` in polar coordinates -/
theorem l9b_locMass_eq (hd : 2 ≤ d) (κ : Rd d → ℝ) (ε s : ℝ) :
    locMass κ ε s = sphArea d * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * locKer κ ε s (r • e₁ d) := by
  rw [← l9b_integral_radial hd (fun r => locKer κ ε s (r • e₁ d)), locMass]
  congr 1
  funext v
  exact locKer_radial κ ε s (l9b_norm_smul_e₁ hd v).symm

/-- `∫ K_ε = 1` in polar coordinates -/
theorem l9b_one_eq_radial {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ}
    (hε : 0 < ε) :
    sphArea d * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) = 1 := by
  rw [← l9b_integral_radial hd (fun r => convKernelEps κ ε (r • e₁ d)),
    ← integral_convKernelEps_eq_one hd hκ hε]
  congr 1
  funext v
  exact l2b_convKernelEps_axis_norm hd ε v

theorem l9b_convKernelEps_axis (κ : Rd d → ℝ) {ε : ℝ} (r : ℝ) :
    convKernelEps κ ε (r • e₁ d) = ε ^ (-(d : ℝ)) * convKernel κ ((ε⁻¹ * r) • e₁ d) := by
  rw [convKernelEps, smul_smul]

theorem l9b_abs_convKernelEps_axis (κ : Rd d → ℝ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |convKernelEps κ ε (r • e₁ d)| = ε ^ (-(d : ℝ)) * |convKernel κ ((ε⁻¹ * r) • e₁ d)| := by
  rw [l9b_convKernelEps_axis, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hε _)]

theorem l9b_radBump_axis_eq_one {s r : ℝ} (hs : 0 < s) (hr0 : 0 ≤ r) (hr : r ≤ s / 2) :
    radBump (s / 2) s (r • e₁ d) = 1 ∨ d = 0 := by
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · exact Or.inr h0
  left
  have hs2 : (0 : ℝ) < s / 2 := by positivity
  have hb : 1 < s / (s / 2) := by rw [div_div_eq_mul_div]; field_simp; norm_num
  unfold radBump
  apply (ContDiffBumpBase.ofInnerProductSpace (Rd d)).eq_one _ hb
  rw [norm_smul, norm_smul, HigherDimLFPP.norm_e₁ hpos, mul_one, Real.norm_eq_abs, abs_inv,
    abs_of_pos hs2, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact (inv_mul_le_iff₀ hs2).2 (by simpa using hr)

/-- **The normalizing constant**: `|Z_ε - 1| ≤ |S^{d-1}| · 6 C_K / √(s/(2ε))` once `s/(2ε) ≥ 1`. -/
theorem l9b_locMass_sub_one_le {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ C * (1 + u) ^ (-((d : ℝ) + 1)))
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (ha : 1 ≤ s / (2 * ε)) :
    |locMass κ ε s - 1| ≤ sphArea d * (6 * C / Real.sqrt (s / (2 * ε))) := by
  have hK := l2b_integrable_radial_kernel hd hκ hε
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
    rw [l9b_locMass_eq hd, ← l9b_one_eq_radial hd hκ hε, ← mul_sub, integral_sub hL hK]
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
        have hint := (l9b_integrableOn_kernelGrowth hd hκ).mono_set
          (Ioi_subset_Ioi (by positivity : (0 : ℝ) ≤ s / (2 * ε)))
        refine setIntegral_mono_on ?_ hint measurableSet_Ioi fun u hu => ?_
        · refine hint.mono' ?_ ?_
          · exact (((continuous_id.pow _).mul ((convKernel_contDiff (by omega)
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
    _ ≤ 6 * C / Real.sqrt (s / (2 * ε)) := l9b_tail_bound hd hκ hC0 hC ha

/-- the moment `M_G = ∫_0^∞ u^{d-1} |K(u e₁)| G(u) du` -/
def l9bKernelMoment (κ : Rd d → ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight u

theorem l9bKernelMoment_nonneg (κ : Rd d → ℝ) : 0 ≤ l9bKernelMoment κ :=
  setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt hu) _) (abs_nonneg _))
      (l9b_growthWeight_nonneg u)

theorem l9b_continuous_convKernelEps_axis {κ : Rd d → ℝ} (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ε : ℝ) :
    Continuous fun r : ℝ => convKernelEps κ ε (r • e₁ d) := by
  have hK := (convKernel_contDiff (d := d) (by omega) hκ).continuous
  unfold convKernelEps
  fun_prop

/-- substituted growth integrals: `∫_{r > εa} r^{d-1}|K_ε(re₁)| G(r) ≤ (1 + log ε⁻¹) ∫_{u > a} u^{d-1}|K(ue₁)|G(u)`
for `0 < ε ≤ 1`, `a ≥ 0` -/
theorem l9b_subst_growth_le {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
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
  have hint := (l9b_integrableOn_kernelGrowth hd hκ).mono_set (Ioi_subset_Ioi ha)
  have hKc : Continuous fun u : ℝ => convKernel κ (u • e₁ d) :=
    (convKernel_contDiff (by omega) hκ).continuous.comp (continuous_id.smul continuous_const)
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
`a = s/(2ε) ≥ 1`. -/
theorem l9b_locField_error {κ : Rd d → ℝ} (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
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
  have hK := convKernel_contDiff (d := d) (by omega) hκ
  have hL : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε, hε1⟩)
  have hA0 : 0 ≤ sphArea d := sphArea_nonneg d
  have hZ0 : 0 < locMass κ ε s := by linarith
  -- abbreviations as functions of `r`
  let W : ℝ → ℝ := fun r => r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)|
  let Ψ : ℝ → ℝ := fun r => radBump (s / 2) s (r • e₁ d)
  let H : ℝ → ℝ := fun r => sphereAvg g r z
  have hKc := l9b_continuous_convKernelEps_axis hd hκ ε
  have hΨc : Continuous Ψ :=
    (contDiff_radBump (d := d) (by positivity) (by linarith)).continuous.comp
      (continuous_id.smul continuous_const)
  have hΨ01 : ∀ r, 0 ≤ Ψ r ∧ Ψ r ≤ 1 := fun r =>
    ⟨(radBump_mem_Icc' (s / 2) s (r • e₁ d)).1, (radBump_mem_Icc' (s / 2) s (r • e₁ d)).2⟩
  -- integrable majorant `C W G`
  have hgk := l2b_integrable_radial_growth_kernel hd hκ hε
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
    exact (l9b_subst_growth_le hd hκ hε hε1 ha0).trans
      (mul_le_mul_of_nonneg_left (l9b_tail_bound hd hκ hCK0 hCK ha) (by linarith))
  have hT2 : ∫ r in Ioi (0 : ℝ), W r * l2b_growthWeight r ≤
      (1 + Real.log ε⁻¹) * l9bKernelMoment κ := by
    have h := l9b_subst_growth_le (κ := κ) hd hκ hε hε1 le_rfl
    rw [mul_zero] at h
    exact h
  have hcbound : c ≤ 2 * (sphArea d * (6 * CK / Real.sqrt (s / (2 * ε)))) := by
    have hZ1 := l9b_locMass_sub_one_le hd hκ hCK0 hCK hε hs ha
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

end HigherDimLQGMetric
