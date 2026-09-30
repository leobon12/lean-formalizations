import QuantumZipper.Proofs.Thm18.R18ReadMeas
import QuantumZipper.Proofs.Thm18.R18G1ArcWire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 ZIPFACTOR (D81), part 1: the factorization node read on the full configuration data

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26), (1) and (3): `Z^LEN_t`, `t > 0`, is the inverse
of `Z^LEN_{−t}`, which preserves the law of the configuration; hence `Z^LEN_t` preserves the law.
The paper transfers the law of the **whole configuration** `(h, η)`. Here the law transfer
(`Cor15Group.map_comp_eq_of_factor`) is run with the full configuration data `cfgData` as input
(E6 holds for `configLawFull`, `e6Arc_thm18`) and the masked data `offData` as output: the
node `G4ZipFactorFullAStmt` asks for a measurable `Φ` with `offData (Z_t x) = Φ (cfgData x)` a.s.
along `x = c` and `x = Z_{−t} c`. This replaces `G4ZipFactorAStmt` (masked input), which would
need the length-welding driver to be read from the masked field only (decision D81).

Own elementary argument (pushforward algebra), copy of `g4PosLawAStmt_of_read`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Factorization node, `t > 0`, full-data input** (D81): a.s. along `c` and along
`Z^LEN_{−t} c`, the masked data of `Z^LEN_t x` is one measurable function of the full data of
`x`. -/
def G4ZipFactorFullAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → E6ALaw γ P B Y → LenEqArc γ P B Y →
    ∀ t : ℝ, 0 < t → ∃ Φ : E6.FullData → E6.FullData, Measurable Φ ∧
      (∀ᵐ ω ∂P, offData (zipLenA γ t (wedgeAConfig γ B Y ω)).toPair =
        Φ (cfgData (wedgeAConfig γ B Y ω).toPair)) ∧
      ∀ᵐ ω ∂P, offData (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).toPair =
        Φ (cfgData (zipLenDownA γ t (wedgeAConfig γ B Y ω)).toPair)

/-- The full data of the area-carrying unzipped configuration is a.e.-measurable. -/
theorem aemeasurable_cfgData_zipLenDownA (hX1 : BaseFin.BaseFiniteStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) {t : ℝ} (ht : 0 < t) :
    AEMeasurable (fun ω => cfgData (zipLenDownA γ t (wedgeAConfig γ B Y ω)).toPair) P := by
  refine (aemeasurable_cfgData_zipLenDownArc (unzipMeasArcStmt_of_X1 hX1) hS ht).congr ?_
  filter_upwards [ae_toPair_zipLenDownA_eq hS t] with ω he
  rw [he]

/-- E6 on the full data, for the area-carrying unzipped configuration. -/
theorem map_cfgData_zipLenDownA (hX1 : BaseFin.BaseFiniteStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) {t : ℝ} (ht : 0 < t) :
    P.map (fun ω => cfgData (zipLenDownA γ t (wedgeAConfig γ B Y ω)).toPair) =
      P.map (fun ω => cfgData (wedgeAConfig γ B Y ω).toPair) := by
  have h : P.map (fun ω => cfgData (LocLen.zipLenDownArc γ t (wedgeConfig γ B Y ω))) =
      P.map (fun ω => cfgData (wedgeConfig γ B Y ω)) := e6Arc_thm18 (e6StmtArc_of_X1 hX1) hS t ht
  rw [Measure.map_congr (ae_toPair_zipLenDownA_eq hS t |>.mono fun ω he => by rw [he])]
  exact h

end R18
end QuantumZipper
