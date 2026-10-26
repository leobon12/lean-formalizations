import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Field.Localization
import HigherDimLFPPAS.Field.PathwiseRadial

/-!
# Lemma 2.3 (i), pathwise for all small `ε` on one event (packet F1b, MA3 P2.2–P2.4)

With `L_ε := (log ε⁻¹)^{10}` (so `locRad ε = ε L_ε`), `ĥ*_ε = locField κ ε h` and `h*_ε = convMollify κ ε h`:
almost surely, for every integer radius `N` there is a random constant `C(ω, N)` such that for **all**
`ε ∈ (0, ε₀)` (deterministic `ε₀`) and all `z ∈ B̄_N`,
`|ĥ*_ε(z) − h*_ε(z)| ≤ C(ω, N) (1 + log ε⁻¹) / L_ε`, and the rate tends to `0`
(`ae_locField_sub_convMollify_le_F1b`, `tendsto_locRate_F1b`). Consequently the interface `Core.Lemma23i` holds
(`lemma23i_F1b`, `lemma23i_of_setting_F1b`).

Proof (MA3 P2.3–P2.4). On the event where the radial formulas of `h*_ε` (`radial_formula_F1`) and of the localized
pairing (`ae_locTest_radial_all_F1b`, packet F1b's common-event identity) hold for all scales and centres, together
with the logarithmic sphere-average growth `|h_r(z)| ≤ C G(r)` (`l2b_ae_growth_all`):
`h*_ε − Z_ε⁻¹⟨h, ψ_ε K_ε(z − ·)⟩ = |S^{d−1}| ∫ r^{d−1} K_ε(r)(1 − Z_ε⁻¹ψ_ε(r)) h_r(z) dr`, whose modulus is at most
`|S^{d−1}| C (∫_{r > εL/2} r^{d−1}|K_ε| G + |1 − Z_ε⁻¹| ∫ r^{d−1}|K_ε| G)`
(`locField_error_sharp_F1b`). The first integral is `∫_{u > L/2} u^{d−1}|K(u)| G(εu) du` and `G(εu) ≤ 1 + log ε⁻¹ + log u`
for `u ≥ 1` (`growthWeight_mul_le_F1b`), so packet F1's log-weighted tail `radial_kernel_log_tail_F1` bounds it by
`6 C_K (1 + log ε⁻¹)/L` once `log(L/2) ≤ log ε⁻¹`; `|Z_ε − 1| ≤ 2|S^{d−1}| C_K / L` (`locMass_cutoff_log_bound_F1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open HigherDimLFPP (Rd e₁)
open HigherDimLQGMetric

namespace HigherDimLFPPAS.Field

variable {d : ℕ} {κ : Rd d → ℝ}

/-- `G(εu) ≤ 1 + log ε⁻¹ + log u` for `0 < ε ≤ 1 ≤ u` (MA3 P2.3, the sharp form of `l9b_growthWeight_scale`). -/
theorem growthWeight_mul_le_F1b {ε u : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hu : 1 ≤ u) :
    l2b_growthWeight (ε * u) ≤ 1 + Real.log ε⁻¹ + Real.log u := by
  have hu0 : 0 < u := by linarith
  have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  rw [l9b_growthWeight_eq, Real.log_inv, Real.log_inv, Real.log_mul hε.ne' hu0.ne']
  refine max_le (by linarith) (max_le (max_le (by linarith) (by linarith)) (by linarith))

/-- **Pointwise localization error with the sharp rate** (MA3 P2.3–P2.4): if the polar formulas of `h*_ε(z)` and of the
pairing `⟨g, locTest z⟩` hold at `z` with cutoff radius `s = εL`, and `|g_r(z)| ≤ C G(r)` for all `r > 0`, then
`|h*_ε(z) − Z_ε⁻¹⟨g, locTest z⟩| ≤ C |S^{d−1}| C_K (6 + 4|S^{d−1}| M_G) (1 + log ε⁻¹) / L`, for `0 < ε ≤ 1`, `L ≥ 2`,
`log(L/2) ≤ log ε⁻¹` and `Z_ε ≥ 1/2`. -/
theorem locField_error_sharp_F1b (hd : 2 ≤ d) (hκ : IsAdmissibleSeed κ)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ CK * (1 + u) ^ (-((d : ℝ) + 1)))
    {ε L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 2 ≤ L) (hlogL : Real.log (L / 2) ≤ Real.log ε⁻¹)
    (hZ : 1 / 2 ≤ locMass κ ε (ε * L))
    {g : DistRd d} {z : Rd d} {C : ℝ} (hC0 : 0 ≤ C)
    (hφ : convMollify κ ε g z = sphArea d * ∫ r in Ioi (0 : ℝ),
      r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * sphereAvg g r z)
    (hψ : g (locTest κ ε (ε * L) z) = sphArea d * ∫ r in Ioi (0 : ℝ),
      r ^ (d - 1) * locTest κ ε (ε * L) z (z + r • e₁ d) * sphereAvg g r z)
    (hcont : ContinuousOn (fun r => sphereAvg g r z) (Ioi 0))
    (hgrowth : ∀ r : ℝ, 0 < r → |sphereAvg g r z| ≤ C * l2b_growthWeight r) :
    |convMollify κ ε g z - (locMass κ ε (ε * L))⁻¹ * g (locTest κ ε (ε * L) z)| ≤
      C * sphArea d * CK * (6 + 4 * sphArea d * l9bKernelMoment κ) * (1 + Real.log ε⁻¹) / L := by
  set s : ℝ := ε * L with hsdef
  have hs : 0 < s := mul_pos hε (by linarith)
  have hK := Signed.convKernel_contDiff_seed (d := d) (by omega) hκ
  have hb : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε, hε1⟩)
  have hA0 : 0 ≤ sphArea d := sphArea_nonneg d
  have hZ0 : 0 < locMass κ ε s := by linarith
  have hL0 : 0 < L := by linarith
  -- abbreviations as functions of `r`
  let W : ℝ → ℝ := fun r => r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)|
  let Ψ : ℝ → ℝ := fun r => radBump (s / 2) s (r • e₁ d)
  let H : ℝ → ℝ := fun r => sphereAvg g r z
  have hKc := Signed.l9b_continuous_convKernelEps_axis_seed hd hκ ε
  have hΨc : Continuous Ψ :=
    (contDiff_radBump (d := d) (by positivity) (by linarith)).continuous.comp
      (continuous_id.smul continuous_const)
  have hΨ01 : ∀ r, 0 ≤ Ψ r ∧ Ψ r ≤ 1 := fun r =>
    ⟨(radBump_mem_Icc' (s / 2) s (r • e₁ d)).1, (radBump_mem_Icc' (s / 2) s (r • e₁ d)).2⟩
  -- integrable majorant `C W G`
  have hgk := Signed.l2b_integrable_radial_growth_kernel_seed hd hκ hε
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
  -- the tail integral, with the sharp rate
  have hT1 : ∫ r in Ioi (s / 2), W r * l2b_growthWeight r ≤
      6 * CK * (1 + Real.log ε⁻¹) / L := by
    have hA1 : 1 ≤ L / 2 := by linarith
    have hA0 : 0 < L / 2 := by linarith
    have e1 : s / 2 = ε * (L / 2) := by rw [hsdef]; ring
    have hsub : ∫ r in Ioi (ε * (L / 2)), W r * l2b_growthWeight r =
        ∫ u in Ioi (L / 2), u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
          l2b_growthWeight (ε * u) := by
      rw [← l9b_radial_subst (by omega) hε (L / 2) (fun u => |convKernel κ (u • e₁ d)|)
        l2b_growthWeight]
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      simp only [W, l9b_abs_convKernelEps_axis κ hε r]
    have hKa : Continuous fun u : ℝ => convKernel κ (u • e₁ d) :=
      hK.continuous.comp (continuous_id.smul continuous_const)
    have hint : IntegrableOn (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
        l2b_growthWeight u) (Ioi (L / 2)) :=
      (Signed.l9b_integrableOn_kernelGrowth_seed hd hκ).mono_set (Ioi_subset_Ioi hA0.le)
    have hGc : ContinuousOn (fun u : ℝ => l2b_growthWeight (ε * u)) (Ioi (L / 2)) :=
      l2b_continuousOn_growthWeight.comp (continuous_const.mul continuous_id).continuousOn
        fun u hu => show 0 < ε * u from mul_pos hε (lt_trans hA0 hu)
    have hlogc : ContinuousOn (fun u : ℝ => Real.log u) (Ioi (L / 2)) :=
      Real.continuousOn_log.mono fun u hu => (lt_trans hA0 hu).ne'
    -- the left integrand is dominated by `(1 + log ε⁻¹) u^{d-1}|K| G(u)`
    have hleft : IntegrableOn (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
        l2b_growthWeight (ε * u)) (Ioi (L / 2)) := by
      refine (hint.const_mul (1 + Real.log ε⁻¹)).mono' ?_ ?_
      · exact (((continuous_id.pow _).mul hKa.abs).continuousOn.mul hGc).aestronglyMeasurable
          measurableSet_Ioi
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
        have hu0 : 0 < u := lt_trans hA0 hu
        have hsc := l9b_growthWeight_scale hε hε1 hu0
        have hp : 0 ≤ u ^ (d - 1) * |convKernel κ (u • e₁ d)| :=
          mul_nonneg (pow_nonneg hu0.le _) (abs_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (l9b_growthWeight_nonneg _))]
        calc u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight (ε * u)
            ≤ u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
                ((1 + Real.log ε⁻¹) * l2b_growthWeight u) := mul_le_mul_of_nonneg_left hsc hp
          _ = _ := by ring
    -- the right integrand is dominated by `(2 + log ε⁻¹) u^{d-1}|K| G(u)` on `u ≥ 1`
    have hright : IntegrableOn (fun u : ℝ => u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
        (1 + Real.log ε⁻¹ + Real.log u)) (Ioi (L / 2)) := by
      refine (hint.const_mul (2 + Real.log ε⁻¹)).mono' ?_ ?_
      · exact (((continuous_id.pow _).mul hKa.abs).continuousOn.mul
          (continuousOn_const.add hlogc)).aestronglyMeasurable measurableSet_Ioi
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
        have hu1 : 1 ≤ u := hA1.trans (le_of_lt hu)
        have hu0 : 0 < u := by linarith
        have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu1
        have hG1 := l9b_one_le_growthWeight u
        have hGlog : Real.log u ≤ l2b_growthWeight u := by
          rw [l9b_growthWeight_eq]
          exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
        have hp : 0 ≤ u ^ (d - 1) * |convKernel κ (u • e₁ d)| :=
          mul_nonneg (pow_nonneg hu0.le _) (abs_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (by linarith))]
        have hw : 1 + Real.log ε⁻¹ + Real.log u ≤ (2 + Real.log ε⁻¹) * l2b_growthWeight u := by
          nlinarith
        calc u ^ (d - 1) * |convKernel κ (u • e₁ d)| * (1 + Real.log ε⁻¹ + Real.log u)
            ≤ u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
                ((2 + Real.log ε⁻¹) * l2b_growthWeight u) := mul_le_mul_of_nonneg_left hw hp
          _ = _ := by ring
    have hptw : ∀ u ∈ Ioi (L / 2), u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
        l2b_growthWeight (ε * u) ≤
          u ^ (d - 1) * |convKernel κ (u • e₁ d)| * (1 + Real.log ε⁻¹ + Real.log u) := by
      intro u hu
      have hu1 : 1 ≤ u := hA1.trans (le_of_lt hu)
      have hp : 0 ≤ u ^ (d - 1) * |convKernel κ (u • e₁ d)| :=
        mul_nonneg (pow_nonneg (by linarith) _) (abs_nonneg _)
      exact mul_le_mul_of_nonneg_left (growthWeight_mul_le_F1b hε hε1 hu1) hp
    have htail := radial_kernel_log_tail_F1 hd hκ hCK0 hCK hA1 hb hlogL
    rw [e1, hsub]
    calc ∫ u in Ioi (L / 2), u ^ (d - 1) * |convKernel κ (u • e₁ d)| * l2b_growthWeight (ε * u)
        ≤ ∫ u in Ioi (L / 2), u ^ (d - 1) * |convKernel κ (u • e₁ d)| *
            (1 + Real.log ε⁻¹ + Real.log u) :=
          setIntegral_mono_on hleft hright measurableSet_Ioi hptw
      _ ≤ 3 * CK * (1 + Real.log ε⁻¹) / (L / 2) := htail
      _ = 6 * CK * (1 + Real.log ε⁻¹) / L := by field_simp; ring
  have hT2 : ∫ r in Ioi (0 : ℝ), W r * l2b_growthWeight r ≤
      (1 + Real.log ε⁻¹) * l9bKernelMoment κ := by
    have h := Signed.l9b_subst_growth_le_seed (κ := κ) hd hκ hε hε1 le_rfl
    rw [mul_zero] at h
    exact h
  have hcbound : c ≤ 4 * sphArea d * CK / L := by
    have hZ1 := locMass_cutoff_log_bound_F1 hd hκ hCK0 hCK hε hL
    have e : 1 - (locMass κ ε s)⁻¹ = (locMass κ ε s - 1) / locMass κ ε s := by field_simp
    rw [hc, e, abs_div, abs_of_pos hZ0, div_le_iff₀ hZ0]
    have hZ1' : |locMass κ ε s - 1| ≤ 2 * sphArea d * CK / L := hZ1
    have hq : 0 ≤ 2 * sphArea d * CK / L := by positivity
    have h4 : 4 * sphArea d * CK / L = 2 * (2 * sphArea d * CK / L) := by ring
    rw [h4]
    nlinarith [abs_nonneg (locMass κ ε s - 1)]
  have hM0 := l9bKernelMoment_nonneg κ
  have hc0 : 0 ≤ c := abs_nonneg _
  have hWG0 : 0 ≤ ∫ r in Ioi (0 : ℝ), W r * l2b_growthWeight r :=
    setIntegral_nonneg measurableSet_Ioi fun r hr => mul_nonneg
      (mul_nonneg (pow_nonneg (le_of_lt hr) _) (abs_nonneg _)) (l9b_growthWeight_nonneg r)
  calc sphArea d * |∫ r in Ioi (0 : ℝ), (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * H r -
        (locMass κ ε s)⁻¹ * (r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * Ψ r * H r))|
      ≤ sphArea d * (C * (∫ r in Ioi (s / 2), W r * l2b_growthWeight r) +
          C * c * (∫ r in Ioi (0 : ℝ), W r * l2b_growthWeight r)) :=
        mul_le_mul_of_nonneg_left hmain hA0
    _ ≤ sphArea d * (C * (6 * CK * (1 + Real.log ε⁻¹) / L) +
          C * (4 * sphArea d * CK / L) * ((1 + Real.log ε⁻¹) * l9bKernelMoment κ)) := by
        gcongr
    _ = C * sphArea d * CK * (6 + 4 * sphArea d * l9bKernelMoment κ) * (1 + Real.log ε⁻¹) / L := by
        ring

/-- Eventually as `ε ↓ 0`, `log(L_ε/2) ≤ log ε⁻¹` for `L_ε = (log ε⁻¹)^{10}`. -/
theorem eventually_log_locLog_le_F1b :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.log (Real.log ε⁻¹ ^ 10 / 2) ≤ Real.log ε⁻¹ := by
  have hx : ∀ᶠ x in atTop, Real.log (Real.log x ^ 10 / 2) ≤ Real.log x := by
    have hO := (Real.isLittleO_pow_log_id_atTop (n := 10)).bound (c := 1) one_pos
    filter_upwards [hO, eventually_ge_atTop (Real.exp 1)] with x hxO hxe
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hlog1 : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
    have hpos : 0 < Real.log x ^ 10 / 2 := by positivity
    have hle : Real.log x ^ 10 / 2 ≤ x := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx0, one_mul,
        abs_of_nonneg (by positivity)] at hxO
      have : 0 ≤ Real.log x ^ 10 := by positivity
      linarith
    exact Real.log_le_log hpos hle
  exact tendsto_inv_nhdsGT_zero.eventually hx

/-- The rate `(1 + log ε⁻¹) / L_ε`, `L_ε = (log ε⁻¹)^{10}`, tends to `0` as `ε ↓ 0`. -/
theorem tendsto_locRate_F1b :
    Tendsto (fun ε : ℝ => (1 + Real.log ε⁻¹) / Real.log ε⁻¹ ^ 10) (𝓝[>] 0) (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => (1 + x) / x ^ 10) atTop (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => 2 / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have : 0 < x := by linarith
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : 0 < x := by linarith
      have hp : x ^ 2 ≤ x ^ 10 := pow_le_pow_right₀ hx (by norm_num)
      rw [div_le_div_iff₀ (by positivity) hx0]
      nlinarith
  exact hg.comp tendsto_log_inv_nhdsGT_zero

/-- **Lemma 2.3 (i), pathwise with the sharp rate** (MA3 P2.3–P2.4, all `ε ≤ ε₀` on one event): there is a
deterministic `ε₀ ∈ (0, 1)` such that, almost surely, for every integer radius `N` there is a random `C ≥ 0` with
`|ĥ*_ε(z) − h*_ε(z)| ≤ C (1 + log ε⁻¹) / L_ε` (`L_ε = (log ε⁻¹)^{10}`) for **all** `ε ∈ (0, ε₀)` and `z ∈ B̄_N`. -/
theorem ae_locField_sub_convMollify_le_F1b (hd : 2 ≤ d) (hκ : IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ z ∈ closedBall (0 : Rd d) (N : ℝ),
        |locField κ ε (h ω) z - convMollify κ ε (h ω) z| ≤
          C * ((1 + Real.log ε⁻¹) / Real.log ε⁻¹ ^ 10) := by
  have hK := Signed.convKernel_contDiff_seed (d := d) (by omega) hκ
  obtain ⟨CK, hCK0, hCK⟩ := Signed.l9b_kernel_axis_decay_seed hd hκ
  have hev := (Signed.l9b_eventually_locHyp_seed hd hκ).and eventually_log_locLog_le_F1b
  obtain ⟨ε₁, hε₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hε₁0 : 0 < ε₁ := hε₁
  refine ⟨min ε₁ (1 / 2), lt_min hε₁0 (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  filter_upwards [radial_formula_F1 hd hκ hh, ae_locTest_radial_all_F1b hd hK hh,
    l2b_ae_growth_all hd hh, hh.1.ae_continuousOn_sphereAvg hd]
    with ω hφ hψ hgrowth hcont
  intro N
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  have hA0 : 0 ≤ sphArea d := sphArea_nonneg d
  have hM0 : 0 ≤ l9bKernelMoment κ := l9bKernelMoment_nonneg κ
  refine ⟨C * sphArea d * CK * (6 + 4 * sphArea d * l9bKernelMoment κ), by positivity, ?_⟩
  intro ε hε z hz
  obtain ⟨⟨hε0, hε1, hrad, ha, hZ⟩, hlog⟩ :=
    hsub ⟨hε.1, lt_of_lt_of_le hε.2 (min_le_left _ _)⟩
  set L : ℝ := Real.log ε⁻¹ ^ 10 with hLdef
  have hsL : locRad ε = ε * L := rfl
  have hL2 : 2 ≤ L := by
    rw [locRad_div ε hε0] at ha
    linarith
  have hcx : ContinuousOn (fun r => sphereAvg (h ω) r z) (Ioi 0) := by
    have hpc : Continuous fun r : ℝ => ((r, z) : ℝ × Rd d) :=
      continuous_id.prodMk continuous_const
    exact ContinuousOn.comp (f := fun r : ℝ => ((r, z) : ℝ × Rd d))
      (g := fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2) hcont.2 hpc.continuousOn
      (fun r hr => mk_mem_prod hr (mem_univ _))
  rw [hsL] at hZ hrad
  have key := locField_error_sharp_F1b hd hκ hCK0 hCK hε0 hε1 hL2 hlog hZ hC0 (hφ ε hε0 z)
    (hψ ε (ε * L) hε0 hrad z) hcx (hC z hz)
  unfold locField
  rw [hsL, abs_sub_comm]
  calc |convMollify κ ε (h ω) z - (locMass κ ε (ε * L))⁻¹ * h ω (locTest κ ε (ε * L) z)|
      ≤ C * sphArea d * CK * (6 + 4 * sphArea d * l9bKernelMoment κ) *
          (1 + Real.log ε⁻¹) / L := key
    _ = C * sphArea d * CK * (6 + 4 * sphArea d * l9bKernelMoment κ) *
          ((1 + Real.log ε⁻¹) / L) := by ring

/-- **Lemma 2.3 (i)** in the interface shape `Core.Lemma23i` (MA2 m5 and flag; MA3 P2.4): almost surely, for every
`R > 0`, `ĥ*_ε − h*_ε → 0` uniformly on `B̄_R` as `ε ↓ 0`. -/
theorem lemma23i_F1b (hd : 2 ≤ d) (hκ : IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) : Core.Lemma23i κ P h := by
  obtain ⟨ε₀, hε₀, -, hmain⟩ := ae_locField_sub_convMollify_le_F1b hd hκ hh
  filter_upwards [hmain] with ω hω
  intro R _
  obtain ⟨N, hN⟩ := exists_nat_ge R
  obtain ⟨C, -, hC⟩ := hω N
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hrate := tendsto_locRate_F1b.const_mul C
  rw [mul_zero] at hrate
  filter_upwards [hrate.eventually (gt_mem_nhds hδ), Ioo_mem_nhdsGT hε₀] with ε hεδ hεI x hx
  have hxN : x ∈ closedBall (0 : Rd d) (N : ℝ) := closedBall_subset_closedBall hN hx
  rw [Real.dist_eq, zero_sub, abs_neg]
  exact lt_of_le_of_lt (hC ε hεI x hxN) hεδ

/-- **Lemma 2.3 (i)** from the standing hypotheses (`Core.Setting`: `d ≥ 3`, admissible seed, normalized LGF). -/
theorem lemma23i_of_setting_F1b {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) : Core.Lemma23i κ P h :=
  lemma23i_F1b (by have := hS.dim; omega) hS.admissible hS.field

end HigherDimLFPPAS.Field
