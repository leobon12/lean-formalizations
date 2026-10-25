import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.WeylMonotone
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Lebesgue.Map




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer

 

theorem lintegral_image_le_mul
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (σ : ℝ → ℝ) (K : ℝ≥0) (hσ : LipschitzOnWith K σ s)
    (himage : σ '' s = t) (g : ℝ → ℝ≥0∞) :
    (∫⁻ u in t, g u) ≤ (K : ℝ≥0∞) * ∫⁻ v in s, g (σ v) := by
  have hσm : AEMeasurable σ (volume.restrict s) :=
    hσ.continuousOn.aemeasurable hs
  have hmeasure : volume.restrict t ≤
      (K : ℝ≥0∞) • Measure.map σ (volume.restrict s) := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply,
      Measure.map_apply_of_aemeasurable hσm hA, Measure.restrict_apply' hs]
    have hset : A ∩ t = σ '' (s ∩ σ ⁻¹' A) := by
      rw [image_inter_preimage, himage, inter_comm]
    rw [hset, ← hausdorffMeasure_real]
    have hLip := (hσ.mono (inter_subset_left : s ∩ σ ⁻¹' A ⊆ s)).hausdorffMeasure_image_le
      (d := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [hausdorffMeasure_real, ENNReal.rpow_one, smul_eq_mul,
      inter_comm (σ ⁻¹' A) s] using hLip
  have hlin := lintegral_mono' hmeasure (le_refl g)
  rw [lintegral_smul_measure] at hlin
  have hmap := lintegral_map_le g hσm
  have hstep : (K : ℝ≥0∞) * (∫⁻ a, g a ∂Measure.map σ (volume.restrict s)) ≤
      (K : ℝ≥0∞) * ∫⁻ a in s, g (σ a) := by gcongr
  have hlin2 : (∫⁻ u in t, g u) ≤
      (K : ℝ≥0∞) * (∫⁻ a, g a ∂Measure.map σ (volume.restrict s)) := by
    simpa only [smul_eq_mul] using hlin
  exact hlin2.trans hstep

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
