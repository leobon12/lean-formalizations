import QuantumZipper.Field.Sample
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# FCR-PAIR, part 6: the folded circle at a real centre is the uniform semicircle

For a real centre `c` and `s ≥ 0`,

  `foldedCircle c s = π⁻¹ • (Lebesgue on (0, π)).map (circleMap c s)`

(`foldedCircle_real_eq`): the lower half of the circle folds onto the upper half by
`θ ↦ 2π − θ`. Own elementary proof.
-/

noncomputable section

open MeasureTheory Set
open scoped Real ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm14WDG

theorem im_circleMap_real (c s θ : ℝ) : (circleMap (c : ℂ) s θ).im = s * Real.sin θ := by
  simp [circleMap, Complex.exp_ofReal_mul_I_im]

theorem conj_circleMap_real (c s θ : ℝ) :
    conj (circleMap (c : ℂ) s θ) = circleMap (c : ℂ) s (2 * π - θ) := by
  have h1 : circleMap (c : ℂ) s (2 * π - θ) = circleMap (c : ℂ) s (-θ) := by
    rw [sub_eq_add_neg, add_comm, (periodic_circleMap (c : ℂ) s) (-θ)]
  rw [h1]
  simp only [circleMap, map_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I]
  push_cast
  ring_nf

/-- **Semicircle formula.** -/
theorem foldedCircle_real_eq (c : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    foldedCircle (c : ℂ) s =
      (ENNReal.ofReal π)⁻¹ • (volume.restrict (Ioo 0 π)).map (circleMap (c : ℂ) s) := by
  have hcm := measurable_circleMap (c : ℂ) s
  have hπ := Real.pi_pos
  unfold foldedCircle circleUnif
  rw [Measure.map_smul, Measure.map_map measurable_foldH hcm]
  have hsplit : volume.restrict (Ico (0 : ℝ) (2 * π)) =
      volume.restrict (Ioo 0 π) + volume.restrict (Ioo π (2 * π)) := by
    rw [← Ico_union_Ico_eq_Ico hπ.le (by linarith), Measure.restrict_union
      (Ico_disjoint_Ico_same) measurableSet_Ico, Measure.restrict_congr_set Ioo_ae_eq_Ico.symm,
      Measure.restrict_congr_set (Ioo_ae_eq_Ico (a := π)).symm]
  have h1 : (volume.restrict (Ioo 0 π)).map (foldH ∘ circleMap (c : ℂ) s) =
      (volume.restrict (Ioo 0 π)).map (circleMap (c : ℂ) s) := by
    refine Measure.map_congr ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun θ hθ => ?_))
    have : 0 ≤ (circleMap (c : ℂ) s θ).im := by
      rw [im_circleMap_real]; exact mul_nonneg hs (Real.sin_nonneg_of_nonneg_of_le_pi
        hθ.1.le hθ.2.le)
    simp [Function.comp, foldH, this]
  have h2 : (volume.restrict (Ioo π (2 * π))).map (foldH ∘ circleMap (c : ℂ) s) =
      (volume.restrict (Ioo 0 π)).map (circleMap (c : ℂ) s) := by
    have hr : (volume.restrict (Ioo π (2 * π))).map (foldH ∘ circleMap (c : ℂ) s) =
        (volume.restrict (Ioo π (2 * π))).map
          (circleMap (c : ℂ) s ∘ fun θ => 2 * π - θ) := by
      refine Measure.map_congr ((ae_restrict_iff' measurableSet_Ioo).2
        (ae_of_all _ fun θ hθ => ?_))
      by_cases h0 : 0 ≤ (circleMap (c : ℂ) s θ).im
      · -- then `s sin θ = 0`, so both sides agree
        have hsin : Real.sin θ < 0 := by
          have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith [hθ.1])
            (by linarith [hθ.2])
          rw [Real.sin_sub_pi] at this; linarith
        rw [im_circleMap_real] at h0
        have hs0 : s = 0 := by nlinarith
        subst hs0
        simp [Function.comp, circleMap, foldH]
      · simp only [Function.comp, foldH, h0, ite_false]
        exact conj_circleMap_real c s θ
    rw [hr, ← Measure.map_map hcm (by fun_prop)]
    congr 1
    have hmp := (volume : Measure ℝ).measurePreserving_sub_left (2 * π)
    have hg : Measurable fun θ : ℝ => 2 * π - θ := by fun_prop
    calc (volume.restrict (Ioo π (2 * π))).map (fun θ : ℝ => 2 * π - θ) =
          (volume.restrict ((fun θ : ℝ => 2 * π - θ) ⁻¹' Ioo 0 π)).map
            (fun θ : ℝ => 2 * π - θ) := by
          congr 2
          ext θ
          simp only [mem_preimage, mem_Ioo]
          constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      _ = ((volume : Measure ℝ).map (fun θ : ℝ => 2 * π - θ)).restrict (Ioo 0 π) :=
          (Measure.restrict_map hg measurableSet_Ioo).symm
      _ = _ := by rw [hmp.map_eq]
  rw [hsplit, Measure.map_add _ _ (measurable_foldH.comp hcm), h1, h2, ← two_smul ℝ≥0∞,
    smul_smul]
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.mul_inv (by simp)
    (by simp), mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  all_goals exact measurable_foldH.aemeasurable

end Thm14WDG
end QuantumZipper
