import QuantumZipper.Proofs.Thm18.R18Nodes
import QuantumZipper.Proofs.Thm18.G4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T5: the G4 sub-nodes on area-carrying configurations and their assembly

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26), zipper stationarity (1)–(3); layout of
`Thm18Asm.g4Stmt_of` (`G4.lean`) transported to `R18.G4AStmt` (D76: configurations carry their
quantum area; D74: fields compared off the curve; D75: open-arc lengths). Plan:
`handoff/R18-PLAN.md` T5 (this file), T7a/b (`G4RoundAStmt`), T8a–c (`G4GroupAStmt`), T9
(`G4PosLawAStmt` via the reading node), T10 (`G4ZeroAStmt`).

The D13 conjunct of clause (1) is the proved `Thm18Asm.ae_lenWeldPoint_measure` (reads only the
wedge field `Y ω`), from the unchanged `Thm18Asm.WedgeLeftInfStmt`. Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Existence and uniqueness of length-welding drivers** of the wedge field (clause (1), first
and third conjuncts), with the paper-form premises. -/
def G4WeldAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → E6ALaw γ P B Y → LenEqArc γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
      (∃ p : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p) ∧
      (∀ p q : ℝ × (ℝ → ℝ), IsLenWeldingDriver γ (Y ω) ℓ p → IsLenWeldingDriver γ (Y ω) ℓ q →
        p.1 = q.1 ∧ ∀ s ∈ Set.Icc 0 p.1, p.2 s = q.2 s)

/-- **Clause (3) at `t = 0`**: `Z^LEN_0` preserves the masked law. -/
def G4ZeroAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    configLawOff (fun ω => (zipLenA γ 0 (wedgeAConfig γ B Y ω)).toPair) P =
      configLawOff (wedgeConfig γ B Y) P

/-- **Clause (3) for `t > 0`** (to be proved by the law transfer of `G4FactorRead.lean` from E6,
the round trips and the reading node, T9). -/
def G4PosLawAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → E6ALaw γ P B Y → LenEqArc γ P B Y →
    ∀ t : ℝ, 0 < t → configLawOff (fun ω => (zipLenA γ t (wedgeAConfig γ B Y ω)).toPair) P =
      configLawOff (wedgeConfig γ B Y) P

end R18
end QuantumZipper
