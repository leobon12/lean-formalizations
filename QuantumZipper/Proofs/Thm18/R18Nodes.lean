import QuantumZipper.Proofs.Thm18.R18Basic
import QuantumZipper.Proofs.Thm18.Assembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18: the node statements of the paper-form Theorem 1.8 and their assembly (D76)

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26) and its proof (§5.4, pp. 69–72). The layout is
that of `Assembly.lean` (`theorem1_8_of_nodes`), transported to the paper-form statement
`theorem1_8Paper` (`Statements/Thm18Paper.lean`): configurations carry their quantum area (D76),
fields are compared off the curve (D74), lengths are read on open arcs (D73/D75).

Nodes (plan: `handoff/R18-PLAN.md`):

* `E6AStmt`: clause (3) for `t < 0` (unzipping preserves the masked law), on area-carrying
  configurations;
* `F1ArcStmt`, `LenPosArcStmt`: the open-arc lengths along `η` agree, positive and finite;
* `G1Stmt` (unchanged: each side is a wedge) and `G3PaperStmt` (independence, `G3Stmt` with the
  open-arc lengths clause as premise; route (b) of D77);
* `G4AStmt`: clauses (1), (2) and (3) for `t ≥ 0`, on area-carrying configurations.

`theorem1_8Paper_of_nodes` assembles them (wiring only).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The open-arc lengths of `η[0,t]` seen from `D₁` and `D₂` agree, a.s. for all `t ≥ 0`. -/
def LenEqArc (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    (unzipLengthsOpen γ (wedgeConfig γ B Y ω) t).1 = (unzipLengthsOpen γ (wedgeConfig γ B Y ω) t).2

/-- The masked law of the configuration unzipped by quantum length `ℓ` (area-carrying) is the
masked law of the configuration: clause (3) of Theorem 1.8 for `t < 0`. -/
def E6ALaw (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ →
    configLawOff (fun ω => (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair) P =
      configLawOff (wedgeConfig γ B Y) P

/-- **E6 on area-carrying configurations** (Sheffield p. 26 (3), `t < 0`; the Theorem 1.3 chain,
open arcs: `LocLen.E6StmtArc`). -/
def E6AStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → E6ALaw γ P B Y

/-- **F1 on open arcs** in the Theorem 1.8 variables (`LocLen.F1StmtArc`). -/
def F1ArcStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → LenEqArc γ P B Y

/-- **Length non-degeneracy on open arcs**: a.s. for `t > 0` the left open-arc length of
`η[0,t]` is in `(0, ⊤)`. -/
def LenPosArcStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      0 < (unzipLengthsOpen γ (wedgeConfig γ B Y ω) t).1 ∧
        (unzipLengthsOpen γ (wedgeConfig γ B Y ω) t).1 < ⊤

/-- **G3, paper form** (independence of the two wedges; Sheffield p. 70, route (b) of D77):
`G3Stmt` with the open-arc lengths clause as premise. -/
def G3PaperStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    IsQuantumWedge γ γ (componentSurface γ B Y true) P →
    IsQuantumWedge γ γ (componentSurface γ B Y false) P → LenEqArc γ P B Y →
    IndepFun (lawData (componentSurface γ B Y true)) (lawData (componentSurface γ B Y false)) P

end R18
end QuantumZipper
