import QuantumZipper.Proofs.Zipper.LocLenStmts
import QuantumZipper.Proofs.Zipper.RegShiftUnifF2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R7b: additive constants for the open-arc lengths

Open-arc copy of `F2.AddConstAgreeStmt` (F2Step2b.lean:92) and of its proof
`RegUnif.addConstAgreeStmt_holds` (RegShiftUnifF2.lean:220): adding a constant `c` to the field
multiplies both open-arc lengths by `e^{γc/2}` (Sheffield arXiv:1012.4797 §5.1, rule (5.1) for
constants, p. 56), so "the two lengths agree" is invariant. No global boundary limit is used:
the rule holds for the chosen local measures by `qBoundaryMeasureOn_smul_of_bdryApprox`
(copy of `LocalRule.qBoundaryMeasureOn_addConst`, exact, no convergence hypothesis).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- Open-arc copy of `F2.AddConstAgreeStmt`. -/
def AddConstAgreeArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ c : ℝ,
      (unzipLengthsArc (Real.sqrt κ) (addConst (X ω + F2.logSingField κ) c, drive κ B ω) t).1 =
        (unzipLengthsArc (Real.sqrt κ) (addConst (X ω + F2.logSingField κ) c, drive κ B ω) t).2 →
      (unzipLengthsArc (Real.sqrt κ) (X ω + F2.logSingField κ, drive κ B ω) t).1 =
        (unzipLengthsArc (Real.sqrt κ) (X ω + F2.logSingField κ, drive κ B ω) t).2

/-- If the dyadic approximations of `y` are `C` times those of `x` (`0 < C < ⊤`), the chosen
local measures on an open set are in the same ratio (junk case included). -/
theorem qBoundaryMeasureOn_smul_of_bdryApprox {γ : ℝ} {x y : FieldSample} {C : ℝ≥0∞}
    (hC0 : C ≠ 0) (hCT : C ≠ ⊤) (he : bdryApprox γ y = fun k => C • bdryApprox γ x k)
    {U : Set ℝ} (hU : IsOpen U) :
    qBoundaryMeasureOn γ y U = C • qBoundaryMeasureOn γ x U := by
  by_cases hex : ∃ ν, IsVagueLimitOnR U (bdryApprox γ x) ν
  · obtain ⟨ν, hν⟩ := hex
    rw [LocalRule.qBoundaryMeasureOn_eq hU hν]
    refine LocalRule.qBoundaryMeasureOn_eq hU ?_
    rw [he]; exact LocalRule.IsVagueLimitOnR.const_smul hν hCT
  · have hex' : ¬∃ ν, IsVagueLimitOnR U (bdryApprox γ y) ν := by
      rintro ⟨ν, hν⟩
      refine hex ⟨C⁻¹ • ν, ?_⟩
      have := LocalRule.IsVagueLimitOnR.const_smul hν (c := C⁻¹) (ENNReal.inv_ne_top.2 hC0)
      rw [he] at this
      simpa only [smul_smul, ENNReal.inv_mul_cancel hC0 hCT, one_smul] using this
    unfold qBoundaryMeasureOn
    rw [dif_neg hex, dif_neg hex', smul_zero]

/-- Open-arc lengths scale by `C` when the approximations do. -/
theorem arcLen_smul_of_bdryApprox {γ : ℝ} {x y : FieldSample} {C : ℝ≥0∞}
    (hC0 : C ≠ 0) (hCT : C ≠ ⊤) (he : bdryApprox γ y = fun k => C • bdryApprox γ x k) (a b : ℝ) :
    arcLen γ y a b = C * arcLen γ x a b := by
  unfold arcLen
  rw [qBoundaryMeasureOn_smul_of_bdryApprox hC0 hCT he isOpen_Ioo, Measure.smul_apply,
    smul_eq_mul]

/-- **Rule (5.1) for constants in the open-arc lengths, dyadic-radius form** (copy of
`RegUnif.agree_addConst_dy`). -/
theorem agree_addConst_dy_arc {γ c t : ℝ} {x : FieldSample} {W : ℝ → ℝ}
    (h : ∀ k : ℕ, ∀ d ∈ RegUnif.Dy, E1.RegShift x ((foldedCircle d (radius k)).map (fwdMapInv W t)))
    (hbc : Cor15Group.BdryConvAE (unzippedField γ (x, W) t)) :
    ((unzipLengthsArc γ (addConst x c, W) t).1 = (unzipLengthsArc γ (addConst x c, W) t).2) ↔
      (unzipLengthsArc γ (x, W) t).1 = (unzipLengthsArc γ (x, W) t).2 := by
  have hav : avgReg (unzippedField γ (addConst x c, W) t) =
      avgReg (addConst (unzippedField γ (x, W) t) c) :=
    RegUnif.avgReg_coordChange_addConst_dy (ψ := fwdMapInv W t) (Q := Qc γ) h
  have hb : bdryApprox γ (unzippedField γ (addConst x c, W) t) =
      fun k => ENNReal.ofReal (Real.exp (γ * c / 2)) • bdryApprox γ (unzippedField γ (x, W) t) k :=
    funext fun k => by
      rw [← Cor15Group.bdryApprox_addConst_ae hbc γ c k]
      unfold bdryApprox; rw [hav]
  have hC0 := LocalRule.ofReal_exp_ne_zero (γ * c / 2)
  exact F2.agree_of_smul_eq hC0 ENNReal.ofReal_ne_top
    (arcLen_smul_of_bdryApprox hC0 ENNReal.ofReal_ne_top hb _ _)
    (arcLen_smul_of_bdryApprox hC0 ENNReal.ofReal_ne_top hb _ _)

/-- **`AddConstAgreeArcStmt` holds** (copy of `RegUnif.addConstAgreeStmt_holds`, from the proved
`RegUnif.f2UnzipRegDyStmt_holds`). -/
theorem addConstAgreeArc_holds : AddConstAgreeArcStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  obtain ⟨hreg, hbc⟩ := RegUnif.f2UnzipRegDyStmt_holds κ hκ hκ4 P B X hB hX hind
  filter_upwards [hreg, hbc] with ω h1 h2 t ht c hlen
  exact (agree_addConst_dy_arc (h1 t ht) (h2 t ht)).1 hlen

end LocLen
end QuantumZipper
