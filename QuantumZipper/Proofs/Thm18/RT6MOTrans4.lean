import QuantumZipper.Proofs.Thm18.RT6MOTrans3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D87: the masked part of N1 from FarPull at the wedge

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, p. 26: zipping up re-welds the
pieces cut out by the curve, and the reverse map pulls circles off the new curve back to sets off
the old curve. At `c₁ = Z^A_{−ℓ} c₀` this geometric fact is proved (RT5, `rt5FarPullStmt_holds`),
which gives N2 (`zipOffExactUnzAStmt_holds`). At the wedge `c₀` itself it is the node
`ZipFarWedgeStmt` below (FarPull and positive zip scale at `c₀`; Loewner geometry of the wedge's
driver only, no field). From it we get the masked-coordinate form of N1 (`ZipOffExactπAStmt`),
which is all the round trip `Z_{−ℓ} ∘ Z_ℓ` and time zero need: unzipping the pieces only reads the
masked coordinates and driver (`zipLenDownMA_congr_πd`, from `configOfData_liftπ`).
Clause (3) (`lawMO_of`) still uses the full N1 (pairings with test functions).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **FarPull at the wedge** (open, geometric): a.s. the zip scale of `Z^A_ℓ c₀` is positive and
dyadic circles off the zipped curve pull back to sets at positive distance from the curve of `c₀`
(`Rt5FarPull`, the `c₀` analogue of `Rt5FarPullStmt`). -/
def ZipFarWedgeStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 ≤ ℓ → ∀ᵐ ω ∂P, Rt5FarPull γ ℓ (wedgeAConfig γ B Y ω)

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}

end R18
end QuantumZipper
