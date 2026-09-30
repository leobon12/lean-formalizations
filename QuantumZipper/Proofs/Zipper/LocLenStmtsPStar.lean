import QuantumZipper.Proofs.Zipper.LocLenStmts
import QuantumZipper.Proofs.Zipper.F1LenScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R4c: the `P_*` field inputs with goodness off the root images

`PStarZipLenInputsLocStmt` is `F1.PStarZipLenInputsStmt` (`F1LenScale.lean`) with the goodness
clause `IsLQGGood γ (unzippedField γ c t)` replaced by `IsLQGGoodOff γ (unzippedField γ c t)
(offSet c.2 t)` (substitution rule of `handoff/FOLLOW-PAPER-13.md` §1). Sheffield,
arXiv:1012.4797, pp. 70–72 ("by scaling"); Berestycki–Powell arXiv:2404.16642, Def 6.41 p. 229.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- Local copy of `F1.PStarZipLenInputsStmt` (goodness off `offSet c.2 t`). -/
def PStarZipLenInputsLocStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ k : ℝ, ∀ᵐ ω ∂P',
      let γ := Real.sqrt κ
      let c := F1.pcfg κ Y B' ω
      let a := scaleParam γ (addConst c.1 k)
      0 < a ∧
      (∀ t, 0 ≤ t → ∃ l, Tendsto (fun r : ℝ => (fwdMap c.2 t r).re) (𝓝[<] (0 : ℝ)) (𝓝 l)) ∧
      (∀ t, 0 ≤ t → ∃ l, Tendsto (fun r : ℝ => (fwdMap c.2 t r).re) (𝓝[>] (0 : ℝ)) (𝓝 l)) ∧
      (∀ t, 0 ≤ t → IsLQGGoodOff γ (unzippedField γ c t) (offSet c.2 t)) ∧
      (∀ s, 0 ≤ s → RegEq (unzippedField γ (canonConfig γ (addConst c.1 k, c.2)) s)
        (rescale (addConst (unzippedField γ c (a ^ 2 * s)) k) (Qc γ) a))

end LocLen
end QuantumZipper
