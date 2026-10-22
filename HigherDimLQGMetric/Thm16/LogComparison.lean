import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! The logarithmic exponent is unchanged by a uniformly bounded positive factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGMetric

theorem l9c_exponent_of_comparable {a b : ℝ → ℝ} {m M lam : ℝ}
    (hm : 0 < m)
    (hp : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < a ε ∧ 0 < b ε)
    (hc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), m * b ε ≤ a ε ∧ a ε ≤ M * b ε)
    (hb : Tendsto (fun ε => Real.log (b ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 lam)) :
    Tendsto (fun ε => Real.log (a ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 lam) := by
  have hzero : Tendsto (fun ε : ℝ => (Real.log ε)⁻¹)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have hconst (K : ℝ) : Tendsto (fun ε : ℝ => K / Real.log ε)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hzero : Tendsto (fun ε : ℝ => K * (Real.log ε)⁻¹)
        (𝓝[>] 0) (𝓝 (K * 0)))
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 from Iio_mem_nhds (by norm_num))]
      with ε hε hε1
    exact ⟨hε, hε1⟩
  have hdiff : Tendsto (fun ε =>
      (Real.log (a ε) - Real.log (b ε)) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hbounds : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Real.log M / Real.log ε ≤
          (Real.log (a ε) - Real.log (b ε)) / Real.log ε ∧
        (Real.log (a ε) - Real.log (b ε)) / Real.log ε ≤
          Real.log m / Real.log ε := by
      filter_upwards [hp, hc, hsmall] with ε hpos hcmp hε
      have hlog : Real.log ε < 0 := Real.log_neg hε.1 hε.2
      have hratio : m ≤ a ε / b ε ∧ a ε / b ε ≤ M := by
        exact ⟨(le_div_iff₀ hpos.2).2 hcmp.1, (div_le_iff₀ hpos.2).2 hcmp.2⟩
      have hloglo : Real.log m ≤ Real.log (a ε) - Real.log (b ε) := by
        rw [← Real.log_div hpos.1.ne' hpos.2.ne']
        exact Real.log_le_log hm hratio.1
      have hloghi : Real.log (a ε) - Real.log (b ε) ≤ Real.log M := by
        rw [← Real.log_div hpos.1.ne' hpos.2.ne']
        exact Real.log_le_log (div_pos hpos.1 hpos.2) hratio.2
      exact ⟨(div_le_div_of_nonpos_of_le hlog.le hloghi),
        (div_le_div_of_nonpos_of_le hlog.le hloglo)⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (hconst (Real.log M)) (hconst (Real.log m))
      (hbounds.mono fun ε h => h.1) (hbounds.mono fun ε h => h.2)
  have hsum : Tendsto (fun ε => Real.log (b ε) / Real.log ε +
      (Real.log (a ε) - Real.log (b ε)) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 lam) := by simpa only [add_zero] using hb.add hdiff
  refine hsum.congr' ?_
  filter_upwards [hsmall] with ε hε
  have hne : Real.log ε ≠ 0 := (Real.log_neg hε.1 hε.2).ne
  field_simp
  ring

end HigherDimLQGMetric
