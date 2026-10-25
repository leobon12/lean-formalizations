import SupercriticalLQGUniqueness.B2.LscTop.LFPP
import LQGMetric.LFPP.WeylField

 





set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem isExtMetric_lfppDistance (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    IsExtMetric (lfppDistance ξ φ) := by
  constructor
  · intro z
    rw [B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_self convex_univ (Set.mem_univ z)
  constructor
  · intro z w hzw
    apply LQGMetric.LFPP.lfppDReal_eq_zero φ.continuous
    unfold LQGMetric.LFPP.lfppDReal
    rw [← B2.LscTop.lfppDistance_eq_lfppD, hzw]
    rfl
  constructor
  · intro z w
    rw [B2.LscTop.lfppDistance_eq_lfppD,
      B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_comm z w
  · intro x y z
    rw [B2.LscTop.lfppDistance_eq_lfppD,
      B2.LscTop.lfppDistance_eq_lfppD,
      B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_triangle x y z

 


def lfppLSCMetric (ξ : ℝ) (φ : C(ℂ, ℝ)) : LSCMetric :=
  ⟨lfppDistance ξ φ,
    isExtMetric_lfppDistance ξ φ,
    (B2.LscTop.continuous_lfppDistance ξ φ).lowerSemicontinuous⟩

@[simp] theorem lfppLSCMetric_apply (ξ : ℝ) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    lfppLSCMetric ξ φ p = lfppDistance ξ φ p := rfl

 
theorem lfppDistance_add_eq_weylScale (ξ : ℝ) (φ ψ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    lfppDistance ξ (φ + ψ) p =
      LQGMetric.weylScale ξ ψ
        (LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous) p.1 p.2 := by
  rw [SupercriticalLQGUniqueness.B2.LscTop.lfppDistance_eq_lfppD]
  exact LQGMetric.LFPP.lfppD_add_eq_weylScale φ.continuous ψ p.1 p.2

end SupercriticalLQGUniqueness.B2.PfeWeyl
