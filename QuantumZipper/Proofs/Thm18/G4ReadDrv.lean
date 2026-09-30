import QuantumZipper.Proofs.Thm18.G4ReadFix

/-!
# Theorem 1.8, node G4: both reading nodes from one measurable driver reading

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1) ("`Z^LEN_t`
is a.s. uniquely defined via conformal welding") and (3). Task G4-READ.

The two reading nodes of G4, `G4GoodDrvReadStmt` ("a good driver exists" is read by a measurable
set of data) and `G4ZipReadCStmt` (the data of `Z^LEN_t x` are a measurable function of the data
of `x`), share one core: the length-welding driver of the field is a measurable function of the
data on a measurable set of data that the unzipped configuration charges a.s.
(`G4LenDrvReadStmt`, the Theorem 1.8 analogue of Corollary 1.5's `Cor15WeldReadStmt`, with the
welding time random instead of fixed). Given the driver, the remaining part of `G4ZipReadCStmt`
is the measurability of the explicit zip-up `canonConfig γ (zipWeldUp γ T W' x)` in the data
and the driver (`G4ZipUpReadStmt`, the zip-up analogue of the MEAS-UNZIP library).

* `g4GoodDrvReadStmt_of_lenDrvRead`: `G4GoodDrvReadStmt` from `G4LenDrvReadStmt`.
* `g4ZipReadCStmt_of_lenDrvRead`: `G4ZipReadCStmt` from `G4LenDrvReadStmt` and
  `G4ZipUpReadStmt` (on the good set, `Z^LEN_t` is the zip-up along the read driver by
  uniqueness of good drivers, `zipLenC_eq_of_good`).
* `g4Stmt_of_coreNodesDrv`: `G4Stmt` with both reading nodes replaced by these two nodes.

**Own elementary argument** (bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- A **measurable reading of good length-welding drivers** on a set `G` of data: the time
`(F d).1` and the driver `(F d).2` are measurable (the driver jointly with the time argument), and
for every configuration `x` with data in `G`, `F (cfgData x)` is a good length-`ℓ` welding
driver of the field `x.1` (positive time, removable doubled hull). -/
def LenDrvReading (γ ℓ : ℝ) (G : Set E6.FullData) (F : E6.FullData → ℝ × (ℝ → ℝ)) : Prop :=
  MeasurableSet G ∧ Measurable (fun d => (F d).1) ∧
    Measurable (fun q : E6.FullData × ℝ => (F q.1).2 q.2) ∧
    ∀ x : FieldSample × (ℝ → ℝ), cfgData x ∈ G →
      IsLenWeldingDriver γ x.1 ℓ (F (cfgData x)) ∧ 0 < (F (cfgData x)).1 ∧
        RemHull (F (cfgData x))

end Thm18Asm
end QuantumZipper
