import HigherDimLQGMetric.Weak.DetDefs

/-!
# Deterministic LFPP bridges for MA5 §3

The extended-real path length in MA5 agrees with the existing real-valued
HigherDimLFPP path length on piecewise C¹ paths and continuous fields.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- MA5's path length equals the certified HigherDimLFPP path length. -/
theorem lfppLen_eq_ofReal {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {P : ℝ → Rd d} {z w : Rd d} (hP : IsPiecewiseC1Path P z w) :
    lfppLen ξ φ P = ENNReal.ofReal (HigherDimLFPP.lfppLength ξ φ P) := by
  have hi : IntegrableOn (HigherDimLFPP.lfppIntegrand ξ φ P) (Icc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1
      (hP.intervalIntegrable_lfppIntegrand hφ ξ)
  have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      HigherDimLFPP.lfppIntegrand ξ φ P :=
    Filter.Eventually.of_forall (HigherDimLFPP.lfppIntegrand_nonneg ξ φ P)
  change (∫⁻ t in Icc (0 : ℝ) 1,
    ENNReal.ofReal (HigherDimLFPP.lfppIntegrand ξ φ P t)) =
    ENNReal.ofReal (HigherDimLFPP.lfppLength ξ φ P)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    HigherDimLFPP.lfppLength_eq_integral, intervalIntegral.integral_of_le zero_le_one]
  exact congrArg ENNReal.ofReal integral_Icc_eq_integral_Ioc

/-- The MA5 extended LFPP distance is the `ofReal` of the real path infimum. -/
theorem fieldLfppE_eq_ofReal_iInf {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    (z w : Rd d) :
    fieldLfppE ξ φ z w =
      ENNReal.ofReal (⨅ P : {P : ℝ → Rd d // IsPiecewiseC1Path P z w},
        HigherDimLFPP.lfppLength ξ φ P.1) := by
  let seg : {P : ℝ → Rd d // IsPiecewiseC1Path P z w} :=
    ⟨HigherDimLFPP.segPath z w, HigherDimLFPP.isPcwC1Path_segPath z w⟩
  have hne : Nonempty {P : ℝ → Rd d // IsPiecewiseC1Path P z w} := ⟨seg⟩
  unfold fieldLfppE
  calc
    (⨅ P : {P : ℝ → Rd d // IsPiecewiseC1Path P z w}, lfppLen ξ φ P.1) =
        ⨅ P : {P : ℝ → Rd d // IsPiecewiseC1Path P z w},
          ENNReal.ofReal (HigherDimLFPP.lfppLength ξ φ P.1) := by
            apply iInf_congr
            intro P
            exact lfppLen_eq_ofReal hφ P.2
    _ = _ := (@ENNReal.ofReal_iInf _ hne _).symm

/-- Identify MA5's extended LFPP distance with HigherDimLFPP's whole-space distance. -/
theorem fieldLfppE_eq_ofReal_lfppDistOn {ξ : ℝ} {φ : Rd d → ℝ}
    (hφ : Continuous φ) (z w : Rd d) :
    fieldLfppE ξ φ z w =
      ENNReal.ofReal (HigherDimLFPP.lfppDistOn ξ φ univ z w) := by
  rw [fieldLfppE_eq_ofReal_iInf hφ]
  congr 1
  unfold HigherDimLFPP.lfppDistOn
  let f : {P : ℝ → Rd d // IsPiecewiseC1Path P z w} →
      {P : ℝ → Rd d // HigherDimLFPP.IsPcwC1Path P z w ∧ MapsTo P (Icc 0 1) univ} :=
    fun P => ⟨P.1, P.2, fun _ _ => mem_univ _⟩
  apply Function.Surjective.iInf_congr f ?_ ?_
  · intro P
    refine ⟨⟨P.1, P.2.1⟩, ?_⟩
    exact Subtype.ext rfl
  · intro P
    rfl

end HigherDimLQGMetric
