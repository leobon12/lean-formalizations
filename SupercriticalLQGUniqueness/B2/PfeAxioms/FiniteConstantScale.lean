import SupercriticalLQGUniqueness.B2.PfeAxioms.AnnulusScale
import SupercriticalLQGUniqueness.B2.PfeAxioms.TranslationFiniteLFPP

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem normalizedLFPPMetric_add_const
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ)) (c : ℝ)
    (hψ : ∀ u, ψ u = φ u + c) (p : ℂ × ℂ) :
    PfeWeyl.normalizedLFPPMetric ξ a ψ p =
      ENNReal.ofReal (Real.exp (ξ * c)) *
        PfeWeyl.normalizedLFPPMetric ξ a φ p := by
  rw [PfeWeyl.normalizedLFPPMetric_apply,
    PfeWeyl.normalizedLFPPMetric_apply,
    B2.LscTop.lfppDistance_eq_lfppD,
    B2.LscTop.lfppDistance_eq_lfppD]
  have hφ : (ψ : ℂ → ℝ) = fun u => φ u + c := funext hψ
  rw [hφ]
  change ENNReal.ofReal ((a : ℝ)⁻¹) *
      LQGMetric.LFPP.lfppDOn ξ (fun u => φ u + c) Set.univ p.1 p.2 = _
  rw [lfppDOn_add_const]
  ac_rfl

end SupercriticalLQGUniqueness.B2.PfeAxioms
