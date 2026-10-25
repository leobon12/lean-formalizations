import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4CondGaussian
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA4_good_conditional_integral_le
    {Ω : Type*} [MeasurableSpace Ω]
    (κ : Measure Ω) (F E H : Set Ω)
    (X Y : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hH : MeasurableSet H) (hX : Measurable X)
    (hhit : F ∩ E ⊆ H)
    (hregular : ∀ ω ∈ E, Y ω ≤ c * X ω) :
    (∫⁻ ω, (F ∩ E).indicator Y ω ∂κ) ≤
      c * (∫⁻ ω, H.indicator X ω ∂κ) := by
  have hpoint : ∀ ω,
      (F ∩ E).indicator Y ω ≤ c * H.indicator X ω := by
    intro ω
    by_cases hω : ω ∈ F ∩ E
    · have hHω : ω ∈ H := hhit hω
      simpa only [Set.indicator_of_mem hω, Set.indicator_of_mem hHω] using
        hregular ω hω.2
    · simp only [Set.indicator_of_notMem hω]
      exact bot_le
  calc
    _ ≤ ∫⁻ ω, c * H.indicator X ω ∂κ := lintegral_mono hpoint
    _ = c * (∫⁻ ω, H.indicator X ω ∂κ) :=
      lintegral_const_mul c (hX.indicator hH)

 


theorem laneA4_good_max_square_le
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Finset ι) (hs : s.Nonempty)
    (Z : ι → Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hB : ∀ᵐ ω ∂P, ∀ i ∈ s, Z i ω ≤ B) :
    (∫⁻ ω, (s.sup' hs (fun i => Z i ω)) ^ (2 : ℝ) ∂P) ≤
      B ^ (2 : ℝ) := by
  have hpoint : ∀ᵐ ω ∂P,
      (s.sup' hs (fun i => Z i ω)) ^ (2 : ℝ) ≤ B ^ (2 : ℝ) := by
    filter_upwards [hB] with ω hω
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply Finset.sup'_le
    intro i hi
    exact hω i hi
  calc
    _ ≤ ∫⁻ ω, B ^ (2 : ℝ) ∂P := lintegral_mono_ae hpoint
    _ = B ^ (2 : ℝ) := by simp

end SupercriticalLQGUniqueness.B2.DG20Conc
