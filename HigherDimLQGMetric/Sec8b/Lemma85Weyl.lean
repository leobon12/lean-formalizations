import HigherDimLQGMetric.Sec6.Defs
import HigherDimLQGMetric.Metric.WeylCompose

/-! Reverse Weyl scaling and shifted length metrics on the common LGF event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A Weyl perturbation is reversible when the base metric is a length
metric. This lets the whole almost-sure Weyl event handle every deterministic
bump sum simultaneously. -/
theorem s7b_weyl_reverse (D E : ContMetric d) (ξ : ℝ)
    (f : C(Rd d, ℝ)) (hD : D.IsLength)
    (hE : IsWeylOf ξ f D E) :
    IsWeylOf ξ (-f) E D := by
  intro x y
  have hzero : weylScale ξ (0 : C(Rd d, ℝ)) D x y =
      ENNReal.ofReal (D.1 (x, y)) := by
    simp only [show (0 : C(Rd d, ℝ)) =
      ContinuousMap.const (Rd d) 0 from rfl,
      weylScale_const_of_isLength hD, mul_zero, Real.exp_zero,
      one_mul]
  calc
    ENNReal.ofReal (D.1 (x, y)) =
        weylScale ξ (0 : C(Rd d, ℝ)) D x y := hzero.symm
    _ = weylScale ξ (-f) E x y := by
      rw [weylScale_of_eq_weylScale hE]
      simp

/-- A Weyl perturbation of a length metric is again a length metric. -/
theorem s7b_weyl_length (D E : ContMetric d) (ξ : ℝ)
    (f : C(Rd d, ℝ)) (hE : IsWeylOf ξ f D E) :
    E.IsLength :=
  isLength_of_eq_weylScale E hE

end HigherDimLQGMetric
