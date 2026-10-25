import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSourceL2Rate

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_max_scale_L2
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Finset ι) (hs : s.Nonempty) (F : ι → Ω → ℝ≥0∞)
    {c B : ℝ≥0∞} (hc : c ≠ 0) (hcTop : c ≠ ⊤)
    (hB : (∫⁻ ω, (s.sup' hs (fun i => F i ω)) ^ (2 : ℝ) ∂P) ≤ B) :
    (∫⁻ ω, (s.sup' hs (fun i => c⁻¹ * F i ω)) ^ (2 : ℝ) ∂P) ≤
      c⁻¹ ^ (2 : ℝ) * B := by
  have hpoint (ω : Ω) :
      (s.sup' hs (fun i => c⁻¹ * F i ω)) ^ (2 : ℝ) ≤
        c⁻¹ ^ (2 : ℝ) * (s.sup' hs (fun i => F i ω)) ^ (2 : ℝ) := by
    have hsup : s.sup' hs (fun i => c⁻¹ * F i ω) ≤
        c⁻¹ * s.sup' hs (fun i => F i ω) := by
      apply Finset.sup'_le
      intro i hi
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' (s := s) (f := fun j => F j ω) hi) bot_le
    calc
      _ ≤ (c⁻¹ * s.sup' hs (fun i => F i ω)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hsup (by norm_num)
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  calc
    _ ≤ ∫⁻ ω, c⁻¹ ^ (2 : ℝ) *
        (s.sup' hs (fun i => F i ω)) ^ (2 : ℝ) ∂P :=
      lintegral_mono hpoint
    _ = c⁻¹ ^ (2 : ℝ) *
        (∫⁻ ω, (s.sup' hs (fun i => F i ω)) ^ (2 : ℝ) ∂P) := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.inv_ne_top.mpr hc))]
    _ ≤ c⁻¹ ^ (2 : ℝ) * B :=
      mul_le_mul_of_nonneg_left hB bot_le

end SupercriticalLQGUniqueness.B2.DG20Conc
