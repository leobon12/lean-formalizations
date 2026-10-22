import HigherDimLQGContinuity.MomentsW1.CoarseJoint
import HigherDimLQGContinuity.MomentsW1.BadScaleMoment

/-! Exponential moment of a sum from separate doubled moments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory
open scoped ENNReal

private theorem exp_add_le_exp_double_add (x y : ℝ) :
    Real.exp (x+y) ≤ Real.exp (2*x)+Real.exp (2*y) := by
  rw [Real.exp_add]
  have hx : Real.exp (2*x) = (Real.exp x)^2 := by rw [pow_two, ← Real.exp_add]; ring_nf
  have hy : Real.exp (2*y) = (Real.exp y)^2 := by rw [pow_two, ← Real.exp_add]; ring_nf
  rw [hx,hy]
  nlinarith [sq_nonneg (Real.exp x - Real.exp y)]

theorem wnExp_sum_moment {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∫⁻ ω, ENNReal.ofReal (Real.exp (2*f ω)) ∂P ≤ ENNReal.ofReal C₁)
    (h₂ : ∫⁻ ω, ENNReal.ofReal (Real.exp (2*g ω)) ∂P ≤ ENNReal.ofReal C₂)
    (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t+f ω+g ω)) ∂P ≤
      ENNReal.ofReal (Real.exp t * (C₁+C₂)) := by
  have hf' : Measurable (fun ω => ENNReal.ofReal (Real.exp (2*f ω))) :=
    (Real.measurable_exp.comp (measurable_const.mul hf)).ennreal_ofReal
  have hg' : Measurable (fun ω => ENNReal.ofReal (Real.exp (2*g ω))) :=
    (Real.measurable_exp.comp (measurable_const.mul hg)).ennreal_ofReal
  let a : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (2*f ω))
  let c : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (2*g ω))
  have ha : Measurable a := hf'
  have hc : Measurable c := hg'
  have hpoint (ω : Ω) :
      ENNReal.ofReal (Real.exp (t+f ω+g ω)) ≤
        ENNReal.ofReal (Real.exp t) *
          (ENNReal.ofReal (Real.exp (2*f ω)) +
            ENNReal.ofReal (Real.exp (2*g ω))) := by
    have hreal := exp_add_le_exp_double_add (f ω) (g ω)
    have hmul := mul_le_mul_of_nonneg_left hreal (Real.exp_pos t).le
    have heq : Real.exp (t+f ω+g ω) = Real.exp t * Real.exp (f ω+g ω) := by
      rw [← Real.exp_add]; ring_nf
    rw [heq]
    calc
      ENNReal.ofReal (Real.exp t * Real.exp (f ω+g ω))
          ≤ ENNReal.ofReal (Real.exp t *
              (Real.exp (2*f ω)+Real.exp (2*g ω))) := ENNReal.ofReal_le_ofReal hmul
      _ = _ := by
        rw [ENNReal.ofReal_mul (Real.exp_pos t).le,
          ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  calc
    (∫⁻ ω, ENNReal.ofReal (Real.exp (t+f ω+g ω)) ∂P)
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp t) *
            (ENNReal.ofReal (Real.exp (2*f ω))+
              ENNReal.ofReal (Real.exp (2*g ω))) ∂P := lintegral_mono hpoint
    _ = ENNReal.ofReal (Real.exp t) *
          ((∫⁻ ω, ENNReal.ofReal (Real.exp (2*f ω)) ∂P) +
            (∫⁻ ω, ENNReal.ofReal (Real.exp (2*g ω)) ∂P)) := by
        change (∫⁻ ω, ENNReal.ofReal (Real.exp t) * (a ω+c ω) ∂P) =
          ENNReal.ofReal (Real.exp t) * ((∫⁻ ω, a ω ∂P)+(∫⁻ ω, c ω ∂P))
        calc
          (∫⁻ ω, ENNReal.ofReal (Real.exp t) * (a ω+c ω) ∂P) =
              ENNReal.ofReal (Real.exp t) * (∫⁻ ω, a ω+c ω ∂P) := by
                exact lintegral_const_mul _ (ha.add hc)
          _ = _ := by rw [lintegral_add_left ha]
    _ ≤ ENNReal.ofReal (Real.exp t) *
          (ENNReal.ofReal C₁+ENNReal.ofReal C₂) :=
        by gcongr
    _ = ENNReal.ofReal (Real.exp t * (C₁+C₂)) := by
        rw [← ENNReal.ofReal_add hC₁ hC₂, ← ENNReal.ofReal_mul (Real.exp_pos t).le]

end HigherDimLQGContinuity
