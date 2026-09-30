import QuantumZipper.Proofs.Thm18.R18RoundDown
import QuantumZipper.Proofs.Thm18.R18AreaNullMain
import QuantumZipper.Proofs.Thm18.R18G4Nodes
import QuantumZipper.Proofs.Thm18.G4WeldHull
import QuantumZipper.Proofs.Thm18.D74Curve
import QuantumZipper.Proofs.Thm18.D74Drv
import QuantumZipper.Proofs.Wire4
import QuantumZipper.Proofs.Zipper.WedgeLawReg
import QuantumZipper.Proofs.Zipper.AreaWinTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T7b: the second conjunct of `R18.G4RoundAStmt` (`Z^LEN_ℓ ∘ Z^LEN_{−ℓ} = id`), a.s.

Sheffield, arXiv:1012.4797, Theorem 1.8 (1), p. 26. The a.s. inputs of the deterministic round
trip `configEqOff_zipLenUpA_zipLenDownA_of` (R18RoundDown.lean):
* welding identification of the rescaled time reversal (node `G4UpWeldCoreAStmt`, the
  substitution-rule copy of `Thm18Asm.G4UpWeldCoreStmt`, G4RezipNodes.lean:179: open-arc length
  time `lenTimeOpen`, scale `areaScale` of the transported area, premises `E6ALaw`, `LenEqArc`);
* A-sep `Thm18Asm.G4DriverPushSepAllStmt` (G4CoreDefs3.lean:75) for the off-hull pushed-circle
  data (`D74R.pushRegOffAt_of_sepAll`);
* proved: removability (`ae_remHull_revDrv`), simple hull (`isSimpleCurveHull_revDrv`), zero
  area of the curve (`curveAreaNull_holds`), `curveOf = η[0,∞)` (`D74.ae_curveOf_drive_eq`),
  wedge regularity and unit scale (`wedgeRegSampleStmt_holds`, `Wire4.wedgeZeroRegStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core

/-- The rescaled time reversal `(t/a², u ↦ (W(t − a²u) − W t)/a)` of the driver at the open-arc
length time `t` and the scale `a` of the transported area: the candidate length-welding driver of
`Z^LEN_{−ℓ} c`. -/
def upDrvA (γ ℓ : ℝ) (c : AreaConfig) : ℝ × (ℝ → ℝ) :=
  revDrv c.drv (lenTimeOpen γ ℓ c.toPair)
    (areaScale (zipCapDownA γ (lenTimeOpen γ ℓ c.toPair) c).area)

/-- Welding data of `Z_ℓ ∘ Z_{−ℓ}` on area-carrying configurations (copy of
`Thm18Asm.RoundUpWeldCoreData`, G4Rezip2Weld.lean:152, by the R18 substitution rule). -/
def RoundUpWeldCoreAData (γ ℓ : ℝ) (c : AreaConfig) : Prop :=
  0 < areaScale (zipCapDownA γ (lenTimeOpen γ ℓ c.toPair) c).area ∧
    0 < lenTimeOpen γ ℓ c.toPair ∧
    zeroMinus (upDrvA γ ℓ c).2 (upDrvA γ ℓ c).1 = lenWeldPoint γ (zipLenDownA γ ℓ c).fld ℓ ∧
    ∀ s ∈ Icc (zeroMinus (upDrvA γ ℓ c).2 (upDrvA γ ℓ c).1) 0,
      weldingHom (upDrvA γ ℓ c).2 (upDrvA γ ℓ c).1 s = weldHomR γ (zipLenDownA γ ℓ c).fld s

/-- **Welding facts of `Z_ℓ ∘ Z_{−ℓ}`, area-carrying form** (open node; substitution-rule copy
of `Thm18Asm.G4UpWeldCoreStmt`, G4RezipNodes.lean:179). Sheffield p. 26: the inverse of
`Z^LEN_{−ℓ}` is "defined via conformal welding" of the two sides of `η[0,t]` by quantum length. -/
def G4UpWeldCoreAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → E6ALaw γ P B Y → LenEqArc γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P, RoundUpWeldCoreAData γ ℓ (wedgeAConfig γ B Y ω)

/-- The second conjunct of `G4RoundAStmt`: `Z^LEN_ℓ ∘ Z^LEN_{−ℓ} = id` off the curve. -/
def G4RoundDownAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → E6ALaw γ P B Y → LenEqArc γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
      ConfigEqOff (zipLenA γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω))).toPair
        (wedgeAConfig γ B Y ω).toPair

end R18
end QuantumZipper
