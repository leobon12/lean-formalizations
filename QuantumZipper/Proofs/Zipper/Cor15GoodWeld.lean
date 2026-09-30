import QuantumZipper.Proofs.Zipper.Cor15GoodConst
import QuantumZipper.Proofs.Thm14.WeldReadBasic
import QuantumZipper.Proofs.Zipper.Cor15LawB1

/-!
# Corollary 1.5(a), positive times: reading `R_h` from `b1Data`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18)
and p. 16 ("`h` determines `ν_h`, hence `R`"). Task COR15-R12, first step of
`Cor15WeldReadStmt` (`Cor15GoodCoords.lean`).

* `measurable_fromC`: the field rebuilt from coordinates depends measurably on them;
* `fieldOf_eq_b1Data`: `fieldOf x.1` is a function of `b1Data x`;
* `weldHomR_fieldOf`: the welding function of `x` is that of `fieldOf x` when the boundary circle
  averages converge a.e. (`BdryConvAE`);
* `weldHomR_eq_weldReadF`: at rational points it is the measurable functional
  `Thm14WDG.weldReadF` of `fieldOf x` when the boundary vague limit exists;
* `measurable_weldReadB1`: the rational values of `R` read from `b1Data`, measurably.

Own bookkeeping (reuses `Thm14WDG.weldReadF`, task WELD-READ).
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull

theorem measurable_fromC : Measurable E1.fromC := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ
  · simp only [E1.fromC, h, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [E1.fromC, h, ↓reduceDIte]
    exact measurable_const

theorem weldHomR_fieldOf {x : FieldSample} (hx : BdryConvAE x) (γ s : ℝ) :
    weldHomR γ (fieldOf x) s = weldHomR γ x s := by
  rw [weldHomR_congr_regEq (regEq_fieldOf x), nrm_eq_addConst]
  exact weldHomR_eq_of_smul (LocalRule.ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top
    (qBoundaryMeasure_addConst_ae hx γ _) s

theorem weldHomR_eq_weldReadF {x : FieldSample} (hx : BdryConvAE x) {γ : ℝ} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ (fieldOf x)) ν) (q : ℚ) :
    weldHomR γ x q = Thm14WDG.weldReadF γ q (fieldOf x) := by
  rw [← weldHomR_fieldOf hx, Thm14WDG.weldReadF_eq hν]
  show Thm14WDG.wRm (qBoundaryMeasure γ (fieldOf x)) q = _
  rw [qBoundaryMeasure_eq hν]

/-- The rational values of the welding function, read measurably from `b1Data`. -/
def weldReadB1 (γ : ℝ) (e : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) : ℚ → ℝ :=
  fun q => Thm14WDG.weldReadF γ q (E1.fromC e.1.1)

theorem measurable_weldReadB1 (γ : ℝ) : Measurable (weldReadB1 γ) :=
  measurable_pi_iff.2 fun q =>
    (Thm14WDG.measurable_weldReadF γ q).comp (measurable_fromC.comp (measurable_fst.comp
      measurable_fst))

/-- **`R_h` at rationals from `b1Data`.** -/
theorem weldHomR_eq_weldReadB1 {x : FieldSample × (ℝ → ℝ)} (hx : BdryConvAE x.1) {γ : ℝ}
    {ν : Measure ℝ} (hν : IsVagueLimitR (bdryApprox γ (fieldOf x.1)) ν) (q : ℚ) :
    weldHomR γ x.1 q = weldReadB1 γ (b1Data x) q :=
  weldHomR_eq_weldReadF hx hν q

end Cor15Group
end QuantumZipper
