import SupercriticalConformalCovariance.TV.EnergyExpectation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.TV

def cmMixIntegrand (E : ℝ) : ℝ≥0∞ :=
  min 1 (ENNReal.ofReal (Real.sqrt (Real.exp E - 1)))

theorem measurable_cmMixIntegrand : Measurable cmMixIntegrand := by
  exact Measurable.min measurable_const
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp
        (Real.continuous_exp.measurable.sub_const 1)))

theorem cmMixIntegrand_le_const_add_energy
    {E δ : ℝ} (hE : 0 ≤ E) (hδ : 0 < δ) :
    cmMixIntegrand E ≤ cmMixIntegrand δ + ENNReal.ofReal (E / δ) := by
  by_cases hEd : E ≤ δ
  · have hmono : Real.sqrt (Real.exp E - 1) ≤ Real.sqrt (Real.exp δ - 1) :=
      Real.sqrt_le_sqrt (sub_le_sub_right (Real.exp_le_exp.mpr hEd) 1)
    have hm : cmMixIntegrand E ≤ cmMixIntegrand δ := by
      unfold cmMixIntegrand
      exact min_le_min_left 1 (ENNReal.ofReal_le_ofReal hmono)
    exact hm.trans (le_add_of_nonneg_right bot_le)
  · have hEδ : 1 ≤ E / δ := (le_div_iff₀ hδ).2 (by linarith)
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (E / δ) := by
      simpa using ENNReal.ofReal_le_ofReal hEδ
    exact (min_le_left _ _).trans (h1.trans (le_add_of_nonneg_left bot_le))

theorem lintegral_cmMixIntegrand_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Ω → ℝ) (hE : Measurable E) (hEn : ∀ᵐ ω ∂P, 0 ≤ E ω)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ ω, cmMixIntegrand (E ω) ∂P) ≤
      cmMixIntegrand δ + ENNReal.ofReal δ⁻¹ *
        (∫⁻ ω, ENNReal.ofReal (E ω) ∂P) := by
  have hm : Measurable (fun ω => ENNReal.ofReal (E ω)) :=
    ENNReal.measurable_ofReal.comp hE
  have hpoint : ∀ᵐ ω ∂P,
      cmMixIntegrand (E ω) ≤ cmMixIntegrand δ +
        ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (E ω) := by
    filter_upwards [hEn] with ω hn
    have hk := cmMixIntegrand_le_const_add_energy hn hδ
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hδ.le)]
    simpa only [div_eq_mul_inv, mul_comm] using hk
  calc
    ∫⁻ ω, cmMixIntegrand (E ω) ∂P
        ≤ ∫⁻ ω, (cmMixIntegrand δ +
            ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (E ω)) ∂P :=
          lintegral_mono_ae hpoint
    _ = cmMixIntegrand δ +
        ENNReal.ofReal δ⁻¹ * (∫⁻ ω, ENNReal.ofReal (E ω) ∂P) := by
          rw [lintegral_add_left (μ := P) measurable_const,
            lintegral_const_mul _ hm, lintegral_const, measure_univ,
            mul_one]

/-- A vanishing mean Dirichlet energy makes the Cameron–Martin mixture bound vanish. -/
theorem tendsto_lintegral_cmMixIntegrand_zero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ)
    (hE : ∀ n, Measurable (E n))
    (hEn : ∀ n, ∀ᵐ ω ∂P, 0 ≤ E n ω)
    (hmean : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (E n ω) ∂P)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, cmMixIntegrand (E n ω) ∂P) atTop (𝓝 0) := by
  have hcont : Continuous cmMixIntegrand := by
    unfold cmMixIntegrand
    exact continuous_const.min
      (ENNReal.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (Real.continuous_exp.sub continuous_const)))
  have hzero : cmMixIntegrand 0 = 0 := by simp [cmMixIntegrand]
  have hlim : Tendsto cmMixIntegrand (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [hzero] using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hev : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), cmMixIntegrand δ < ε :=
    hlim.eventually (Iio_mem_nhds hε)
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hδsmall⟩ : ∃ δ : ℝ, 0 < δ ∧ cmMixIntegrand δ < ε := by
    exact (hpos.and hev).exists
  have hterm : Tendsto
      (fun n => ENNReal.ofReal δ⁻¹ *
        (∫⁻ ω, ENNReal.ofReal (E n ω) ∂P)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul hmean (Or.inr ENNReal.ofReal_ne_top))
  have hupper : Tendsto
      (fun n => cmMixIntegrand δ + ENNReal.ofReal δ⁻¹ *
        (∫⁻ ω, ENNReal.ofReal (E n ω) ∂P)) atTop
      (𝓝 (cmMixIntegrand δ)) := by
    convert tendsto_const_nhds.add hterm using 1 <;> simp
  filter_upwards [hupper.eventually (Iio_mem_nhds hδsmall)] with n hn
  exact ((lintegral_cmMixIntegrand_le P (E n) (hE n) (hEn n) hδ).trans_lt hn).le

end SupercriticalConformalCovariance.TV
