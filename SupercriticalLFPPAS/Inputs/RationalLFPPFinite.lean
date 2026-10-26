import SupercriticalLQGUniqueness.B2.PfeLocal.L2RationalFinite

/-!
# Finiteness of finite-scale LFPP distances between rational circles

This is a deterministic adapter for the finite-scale side of rational-circle
convergence.  It reuses the rational point selected on each circle and the
pointwise finiteness of LFPP.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLFPPAS

/-- The normalized LFPP distance between any two rational circles is finite. -/
theorem setDistance_normalizedLFPPMetric_lt_top
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    {O O' : Set ℂ}
    (hO : SupercriticalLQGUniqueness.B2.Iface.IsRationalCircle O)
    (hO' : SupercriticalLQGUniqueness.B2.Iface.IsRationalCircle O') :
    SupercriticalLQGUniqueness.B2.Iface.setDistance
        (SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric ξ a φ) O O' < ⊤ := by
  obtain ⟨u, huO, -⟩ :=
    SupercriticalLQGUniqueness.B2.PfeLocal.l2_rationalCircle_point hO
  obtain ⟨v, hvO, -⟩ :=
    SupercriticalLQGUniqueness.B2.PfeLocal.l2_rationalCircle_point hO'
  refine lt_of_le_of_lt (iInf₂_le_of_le u huO (iInf₂_le v hvO)) ?_
  rw [SupercriticalLQGUniqueness.B2.PfeWeyl.normalizedLFPPMetric_apply]
  exact lt_top_iff_ne_top.mpr <|
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (SupercriticalLQGUniqueness.B2.LscTop.lfppDistance_ne_top ξ φ (u, v))

end SupercriticalLFPPAS
