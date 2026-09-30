import QuantumZipper.Proofs.Section5.Prop16LitRegP4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: local regularity of chart zooms, convergence at all radii (D98)

`tendsto_areaR_zoomLit` (exponential tilt along `𝓝[>] 0` of the offset-uniform limit of
`y ∘ ψ + Q log|ψ'|`) and the assembly `localAreaRegular_zoomLit`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric Real
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open CoordChangeArea GoodSample SWCore

theorem areaDens_nonneg' (γ : ℝ) (Z : FieldSample) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    0 ≤ areaDens γ Z r z :=
  mul_nonneg (rpow_nonneg hr.le _) (exp_pos _).le

set_option maxHeartbeats 400000 in
theorem tendsto_areaR_zoomLit {γ : ℝ} {ψ : ℂ → ℂ} {y : FieldSample} {ν : Measure ℂ}
    (hy : ChartY γ ψ y ν) (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hψH : MapsTo ψ H H) {V : Set ℂ} (hVo : IsOpen V)
    {g : ℂ → ℝ} (hg : ContinuousOn g V) {x' : FieldSample} {t : ℝ}
    (hag : Prop16Area.G.CircAgree V (translate x' (t : ℂ)) (y + ofFun g)) {U : Set ℂ}
    (hUo : IsOpen U) (hUH : U ⊆ H) (hUV : MapsTo ψ U V) (C : ℝ) {f : ℂ → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun r => ∫ z, f z ∂areaR γ (zoomFieldLit γ C x' t ψ) r) (𝓝[>] 0)
      (𝓝 (∫ z, Real.exp (γ * (g (ψ z) + C / γ)) * f z ∂ν)) := by
  set K := tsupport f with hKdef
  have hK : IsCompact K := hfs
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hK.exists_cthickening_subset_open hUo hfU
  have hK₁ : IsCompact (cthickening ε₀ K) := hK.cthickening
  have hK₁H : cthickening ε₀ K ⊆ H := hε₀U.trans hUH
  set U' := thickening (ε₀ / 2) K with hU'def
  have hU'K : U' ⊆ cthickening ε₀ K :=
    (thickening_subset_cthickening _ _).trans (cthickening_mono (by linarith) K)
  obtain ⟨g', hg'c, hg'⟩ := exists_ext_comp hψd hg hK₁ hK₁H (hUV.mono_left hε₀U) (C / γ)
  obtain ⟨ρy, hρy, hy'⟩ := evalReg_coordChange_y hy hψd hψ0 hK₁ hK₁H
  obtain ⟨ρE, hρE, hE⟩ := evalReg_zoomLit_fc hy hψm hψd hψ0 hψH hVo hg hag hUo hUH hUV C hK hfU
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 (min (min ρy ρE) ε₀) :=
    Ioo_mem_nhdsGT (by positivity)
  have hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ K', IsCompact K' → K' ⊆ U' →
      areaR γ (coordChange y ψ (Qc γ)) r K' < ∞ := by
    filter_upwards [hsmall] with r hr K' _ hK'U
    have h1 : r < ρy := lt_of_lt_of_le hr.2 ((min_le_left _ _).trans (min_le_left _ _))
    exact (measure_mono (hK'U.trans hU'K)).trans_lt
      (areaR_lt_top_of_continuousOn hK₁ (hy' r hr.1 h1).1)
  have hU'H : U' ⊆ H := hU'K.trans hK₁H
  have ht := tendsto_integral_exp_mul (X := ℂ) (L := 𝓝[>] (0 : ℝ)) (U := U') isOpen_thickening
    hfin (fun f' hf' hfc' hfU' => GoodTransforms.HasAreaLimit.tendsto_nhdsGT hy.lim hf' hfc'
      (hfU'.trans hU'H))
    (v := fun r z => γ * smoothFun g' z r) (v0 := fun z => γ * g' z)
    (continuous_const.mul hg'c).continuousOn
    (Eventually.of_forall fun r => (continuous_const.mul
      (continuous_smoothFun hg'c.continuousOn r)).continuousOn)
    (fun K' hK' hK'U ε hε => by
      have hs := smooth_unif hg'c.continuousOn hK'
        (fun z hz => H_subset_Hbar (hU'H (hK'U hz))) (ε / (|γ| + 1)) (by positivity)
      filter_upwards [hs] with r hr z hz
      show |γ * smoothFun g' z r - γ * g' z| < ε
      rw [← mul_sub, abs_mul]
      calc |γ| * |smoothFun g' z r - g' z| ≤ |γ| * (ε / (|γ| + 1)) :=
            mul_le_mul_of_nonneg_left (hr z hz).le (abs_nonneg _)
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith [abs_nonneg γ])
    hf hfs (self_subset_thickening (by linarith) K)
  have hlim : ∫ z, Real.exp (γ * g' z) * f z ∂ν =
      ∫ z, Real.exp (γ * (g (ψ z) + C / γ)) * f z ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ K
    · simp only [hg' (self_subset_cthickening K hz)]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  rw [← hlim]
  refine ht.congr' ?_
  filter_upwards [hsmall] with r hr
  have h1 : r < ρy := lt_of_lt_of_le hr.2 ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : r < ρE := lt_of_lt_of_le hr.2 ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : r < ε₀ := lt_of_lt_of_le hr.2 (min_le_right _ _)
  rw [areaR, areaR, integral_withDensity_ofReal (measurable_areaDens_z γ _ _)
      (areaDens_nonneg' γ _ hr.1),
    integral_withDensity_ofReal (measurable_areaDens_z γ _ _) (areaDens_nonneg' γ _ hr.1)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ K
  · have hB : closedBall z r ⊆ cthickening ε₀ K :=
      (closedBall_subset_cthickening hz _).trans (cthickening_mono h3.le K)
    have hzH : z ∈ Hbar := H_subset_Hbar (hK₁H (self_subset_cthickening K hz))
    simp only [areaDens]
    rw [(hy' r hr.1 h1).2 z (self_subset_cthickening K hz), hE z hz r hr.1 h2,
      integral_fc_eq_smoothFun hzH hr.1 hB hg', mul_add, exp_add]
    ring
  · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- **Local regularity of the chart zoom** (deterministic). -/
theorem localAreaRegular_zoomLit {γ : ℝ} {ψ : ℂ → ℂ} {y : FieldSample} {ν : Measure ℂ}
    (hy : ChartY γ ψ y ν) (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hψH : MapsTo ψ H H) {V : Set ℂ} (hVo : IsOpen V)
    {g : ℂ → ℝ} (hg : ContinuousOn g V) {x' : FieldSample} {t : ℝ}
    (hag : Prop16Area.G.CircAgree V (translate x' (t : ℂ)) (y + ofFun g)) {U : Set ℂ}
    (hUo : IsOpen U) (hUH : U ⊆ H) (hUV : MapsTo ψ U V) (C : ℝ) :
    ∃ μ, LocalAreaRegular γ (zoomFieldLit γ C x' t ψ) U μ := by
  classical
  set Φ : ℂ → ℝ := U.piecewise (fun z => g (ψ z) + C / γ) 0 with hΦdef
  have hΦU : EqOn Φ (fun z => g (ψ z) + C / γ) U := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  have hcU : ContinuousOn (fun z => g (ψ z) + C / γ) U :=
    (hg.comp (hψd.continuousOn.mono hUH) hUV).add continuousOn_const
  have hΦm : Measurable Φ := hcU.measurable_piecewise continuousOn_const hUo.measurableSet
  have hd : Measurable fun z => Real.exp (γ * Φ z) := Real.measurable_exp.comp (hΦm.const_mul γ)
  refine ⟨(ν.restrict U).withDensity fun z => ENNReal.ofReal (Real.exp (γ * Φ z)),
    ?_, fun K hK hKU => ?_, fun K hK hKU => ?_, fun K hK hKU => ?_, fun f hf hfs hfU => ?_⟩
  · refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' hUo.measurableSet, compl_inter_self, measure_empty]
  · refine withDensity_lt_top hK ((Measure.restrict_apply_le _ _).trans_lt
      (hy.lim.2.1 K hK (hKU.trans hUH))) ?_
    have hc : ContinuousOn (fun z => Real.exp (γ * (g (ψ z) + C / γ))) K :=
      ((continuousOn_const (c := γ)).mul (hcU.mono hKU)).rexp
    exact hc.congr fun z hz => by simp only [hΦU (hKU hz)]
  · exact continuousOn_evalReg_zoomLit hy hψm hψd hψ0 hψH hVo hg hag hUo hUH hUV C hK hKU
  · exact eventually_avgReg_zoomLit hy hψm hψd hψ0 hψH hVo hg hag hUo hUH hUV C hK hKU
  · have ht := tendsto_areaR_zoomLit hy hψm hψd hψ0 hψH hVo hg hag hUo hUH hUV C hf hfs hfU
    convert ht using 2
    rw [GoodSample.integral_withDensity_ofReal hd (fun z => (exp_pos _).le),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hz (hfU h), mul_zero]]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ U
    · simp only [hΦU hz]
    · simp only [image_eq_zero_of_notMem_tsupport fun h => hz (hfU h), mul_zero]

end Prop16Lit
end QuantumZipper
