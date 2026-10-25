import SupercriticalLQGUniqueness.Frozen.TranslateCompacts

/-! Scratch freeze split of SLUField.lean:52. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness
open TopologicalSpace

/-- `φ ↦ φ(· - z)`, from test functions supported in `K` to test functions supported in
`K + z`. -/
def testTranslateK (z : ℂ) (K : Compacts ℂ) :
    𝓓^{⊤}_{K}(ℂ, ℝ) →ₗ[ℝ] 𝓓^{⊤}_{translateCompacts z K}(ℂ, ℝ) where
  toFun φ :=
    { toFun := fun x => φ (x - z)
      contDiff' := φ.contDiff.comp (contDiff_id.sub contDiff_const)
      zero_on_compl' := fun x hx => φ.zero_on_compl fun hK => hx ⟨x - z, hK, sub_add_cancel x z⟩ }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end SupercriticalLQGUniqueness
