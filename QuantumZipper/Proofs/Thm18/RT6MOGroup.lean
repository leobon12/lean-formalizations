import QuantumZipper.Proofs.Thm18.RT6MOData
import QuantumZipper.Proofs.Thm18.R18ReadMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6 (D87): clause (2) for all signs by Sheffield's inverse argument

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2), p. 26:
`Z_t` (`t > 0`) is the inverse of `Z_{−t}` on the pair of surfaces, the maps preserve the law of
the pair, and the group law follows. Formally (decision D87): the D87 zipper `zipLenMO` acts on
the encoded pieces through `TR` (RT6MOData.lean), and `RT6Inv.InvFlow.group` gives the group law
for the law `μ` of the encoded wedge pieces from

* a.e.-measurability of the maps (`PiecesFlowMeasStmt`; the paper treats `Z_t` as measurable maps;
  cf. RT3 for `t < 0` and D81 for the zip of the full data);
* law invariance (clause (3)) and continuity of the output drivers (`MOLawContStmt`);
* the two inverse identities and `Z_0 = id`, exactly on the masked data (`MOInverseExactStmt`);
* the negative cocycle, exactly on the masked data (`MONegCocycleExactStmt`).

The a.s. identities at the wedge move to `μ`-a.e. identities because the data space is standard
Borel (`ae_law_of_ae`), and back to the sample by `ae_of_ae_map`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- Clause (3) for `zipLenMO`, with a.e.-measurability of the masked data and continuity of the
output driver. -/
def MOLawContStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ ℓ : ℝ,
      (ℓ ≠ 0 → AEMeasurable (fun ω => offData (zipLenMO γ ℓ (wedgeAConfig γ B Y ω)).toPair) P) ∧
      configLawOff (fun ω => (zipLenMO γ ℓ (wedgeAConfig γ B Y ω)).toPair) P =
        configLawOff (fun ω => (wedgeAConfig γ B Y ω).toPair) P ∧
      ∀ᵐ ω ∂P, Continuous (πdO (zipLenMO γ ℓ (wedgeAConfig γ B Y ω))).2

/-- The inverse identities and `Z_0 = id`, exactly on the masked data. -/
def MOInverseExactStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    (∀ᵐ ω ∂P, πdO (zipLenMO γ 0 (wedgeAConfig γ B Y ω)) = πdO (wedgeAConfig γ B Y ω)) ∧
    ∀ ℓ : ℝ, 0 < ℓ →
      (∀ᵐ ω ∂P, πdO (zipLenMO γ (-ℓ) (zipLenMO γ ℓ (wedgeAConfig γ B Y ω))) =
        πdO (wedgeAConfig γ B Y ω)) ∧
      ∀ᵐ ω ∂P, πdO (zipLenMO γ ℓ (zipLenMO γ (-ℓ) (wedgeAConfig γ B Y ω))) =
        πdO (wedgeAConfig γ B Y ω)

/-- **The negative cocycle, exactly on the masked data** (open). -/
def MONegCocycleExactStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ a b : ℝ, 0 < a → 0 < b → ∀ᵐ ω ∂P,
      πdO (zipLenMO γ (-(a + b)) (wedgeAConfig γ B Y ω)) =
        πdO (zipLenMO γ (-a) (zipLenMO γ (-b) (wedgeAConfig γ B Y ω)))

end R18
end QuantumZipper
