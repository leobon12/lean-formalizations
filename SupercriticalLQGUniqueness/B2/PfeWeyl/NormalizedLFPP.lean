import SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPBridge
import SupercriticalLQGUniqueness.B2.LscTop.Dilate
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.Gapc2

 




set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
def inverseNormalizer (a : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(a : ℝ)⁻¹, Set.mem_Ioi.mpr (inv_pos.mpr (Set.mem_Ioi.mp a.property))⟩

 
def normalizedLFPPMetric (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) : LSCMetric :=
  B2.LscTop.smulMetric (inverseNormalizer a) (lfppLSCMetric ξ φ)

@[simp] theorem normalizedLFPPMetric_apply (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    normalizedLFPPMetric ξ a φ p =
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDistance ξ φ p := by
  rw [normalizedLFPPMetric, B2.LscTop.smulMetric_apply,
    lfppLSCMetric_apply]
  rfl

 

theorem normalizedLFPPMetric_toLSCFun (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    (normalizedLFPPMetric ξ a φ).toLSCFun.1 p = rescaledLFPP ξ a φ p := by
  rw [LSCMetric.toLSCFun_apply, normalizedLFPPMetric_apply]
  rfl

 


theorem normalizedLFPPMetric_add_eq_weylScale
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    normalizedLFPPMetric ξ a (φ + ψ) p =
      weylScale ξ ψ (normalizedLFPPMetric ξ a φ) p := by
  rw [normalizedLFPPMetric_apply, lfppDistance_add_eq_lscWeylScale]
  exact (Uniqueness.TwoScale.GapChecks.weylScale_eq_mul_of_pointwise
      ξ ψ ((a : ℝ)⁻¹) (inv_pos.mpr (Set.mem_Ioi.mp a.property))
      (fun q => normalizedLFPPMetric_apply ξ a φ q) p).symm

end SupercriticalLQGUniqueness.B2.PfeWeyl
