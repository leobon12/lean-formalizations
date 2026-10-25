import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTwoEnvelopeMoment

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_max_conditional_two_envelope_L2
    {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (F : ι → Ω → ℝ≥0∞)
    {U V : Ω → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V)
    {t : ℝ} (ht : 0 < t) (ht4 : 4 * t < 1)
    (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hF : ∀ᵐ ω ∂P, ∀ i ∈ s, F i ω ≤
      (∫⁻ x, U x ∂(condExpKernel P m ω)) ^ t *
      (∫⁻ x, V x ∂(condExpKernel P m ω)) ^ t * c) :
    (∫⁻ ω, (s.sup' hs (fun i => F i ω)) ^ (2 : ℝ) ∂P) ≤
      ((∫⁻ x, U x ∂P) ^ (2 * t) *
        (∫⁻ x, V x ∂P) ^ (2 * t)) * c ^ (2 : ℝ) := by
  let A : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, U x ∂(condExpKernel P m ω)
  let B : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, V x ∂(condExpKernel P m ω)
  have hpoint : ∀ᵐ ω ∂P,
      (s.sup' hs (fun i => F i ω)) ^ (2 : ℝ) ≤
        (A ω ^ (2 * t) * B ω ^ (2 * t)) * c ^ (2 : ℝ) := by
    filter_upwards [hF] with ω hω
    have hmax : s.sup' hs (fun i => F i ω) ≤ A ω ^ t * B ω ^ t * c := by
      apply Finset.sup'_le
      intro i hi
      exact hω i hi
    calc
      _ ≤ (A ω ^ t * B ω ^ t * c) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hmax (by norm_num)
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 2 <;> ring
  calc
    _ ≤ ∫⁻ ω, (A ω ^ (2 * t) * B ω ^ (2 * t)) * c ^ (2 : ℝ) ∂P :=
      lintegral_mono_ae hpoint
    _ = (∫⁻ ω, A ω ^ (2 * t) * B ω ^ (2 * t) ∂P) * c ^ (2 : ℝ) := by
      rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc)]
    _ ≤ ((∫⁻ x, U x ∂P) ^ (2 * t) *
        (∫⁻ x, V x ∂P) ^ (2 * t)) * c ^ (2 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (laneC_conditional_two_envelope_moment P hm hU hV
          (by linarith) (by linarith)) bot_le

end SupercriticalLQGUniqueness.B2.DG20Conc
