import QuantumZipper.Proofs.Thm18.G1ZSplitDefs
import QuantumZipper.Proofs.Thm18.R18Nodes
import QuantumZipper.Proofs.Zipper.LocLenDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G1ARC: the open-arc copies of the G1 rerooting nodes (Theorem 1.8, paper form)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71): the configuration unzipped by a fixed quantum length `ℓ` has the same law, and
its side surfaces are the old ones rerooted at the point at quantum distance `ℓ`. The unzipping
by quantum length reads the lengths of `η[0,t]` on the OPEN arcs (D75, `handoff/FOLLOW-PAPER-13.md`
§1 substitution rule; Berestycki–Powell arXiv:2404.16642 Def 8.12 p. 281).

The statements below are the verbatim copies of the G1 zoom nodes `G1RerootPathStmt` (A1,
G1ZoomNodes.lean), `G1RerootRegStmt` (A1b), `G1RerootLenStmt` (A1c, G1ZSplitDefs.lean) and
`G1ZA1bSideExactStmt` (A1b-X, G1ZA1bMain.lean) with the substitution rule applied:
`zipLenDown ↦ LocLen.zipLenDownArc`, `unzipTime ↦ LocLen.lenTimeArc`,
`unzipScale ↦ unzipScaleArc`, `LenEqStmt ↦ R18.LenEqArc`. The side measure `g1SideNu` of the
NEW configuration (whose law is the wedge law by E6) is kept global, as in the original.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

/-- The scale `a` of the unzipped field used by `zipLenDownArc` (copy of `unzipScale`). -/
def unzipScaleArc (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : ℝ :=
  scaleParam γ (coordChange c.1 (fwdMapInv c.2 (lenTimeArc γ ℓ c)) (Qc γ))

/-- **A1 with open arcs** (copy of `Thm18Asm.G1RerootPathStmt`). -/
def G1RerootPathArcStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → LenEqArc γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ left : Bool, ∀ᵐ ω ∂P,
      WedgeMeas.dataFull H (canonical γ (g1CfgSideField γ left (wedgeConfig γ B Y ω))) =
        WedgeMeas.dataFull H (canonical γ (translate
          (g1CfgSideField γ left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)))
          (g1SidePt γ left (g1CfgSideField γ left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω))) ℓ :
            ℂ)))

/-- **A1b with open arcs** (copy of `Thm18Asm.G1RerootRegStmt`). -/
def G1RerootRegArcStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ left : Bool, ∀ᵐ ω ∂P,
      ∀ lam β : ℝ, 0 < lam →
        EqOn (fun u => fwdMapInv (drive (γ ^ 2) B ω) (lenTimeArc γ ℓ (wedgeConfig γ B Y ω))
            ((unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) : ℂ) *
              g1zSideMap left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)).2 (u + β)))
          (fun u => g1zSideMap left (drive (γ ^ 2) B ω) (u / lam)) H →
        WedgeMeas.dataFull H (canonical γ (g1CfgSideField γ left (wedgeConfig γ B Y ω))) =
          WedgeMeas.dataFull H (canonical γ
            (translate (g1CfgSideField γ left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω))) β))

/-- **A1c with open arcs** (copy of `Thm18Asm.G1RerootLenStmt`): a.s. `t' > 0`, `a > 0`, and the
side measure of the new configuration gives the segment between the preimage `β` of the old root
and the new root length `ℓ`, and charges open intervals of the side half-line. -/
def G1RerootLenArcStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → LenEqArc γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ left : Bool, ∀ᵐ ω ∂P,
      0 < lenTimeArc γ ℓ (wedgeConfig γ B Y ω) ∧ 0 < unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) ∧
      ∀ β : ℝ, β ∈ g1SideHalf left →
        Tendsto (fun u => (unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) : ℂ) *
            g1zSideMap left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)).2 u) (𝓝[H] (β : ℂ))
          (𝓝 (g1zSideImage left (drive (γ ^ 2) B ω)
            (lenTimeArc γ ℓ (wedgeConfig γ B Y ω)) : ℂ)) →
        g1SideNu γ left (g1CfgSideField γ left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)))
            (g1SideSeg left β) = ENNReal.ofReal ℓ ∧
          ∀ u v : ℝ, u < v → Ioo u v ⊆ g1SideHalf left →
            0 < g1SideNu γ left (g1CfgSideField γ left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)))
              (Ioo u v)

/-- **A1b-X with open arcs** (copy of `Thm18Asm.G1ZA1bSideExactStmt`, G1ZA1bMain.lean:54):
a.s., when the unzipping scale is positive, the regularized folded-circle values of the new side
field are those of the pullback of the original wedge field along `u ↦ f_{t'}⁻¹(a ψ'(u))`. -/
def G1ZA1bSideExactArcStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ left : Bool, ∀ᵐ ω ∂P,
      0 < unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) →
      ∀ e ∈ Hbar, ∀ r : ℝ, 0 < r →
        evalReg (g1CfgSideField γ left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)))
            (foldedCircle e r) =
          coordChange (Y ω)
            (fun u => fwdMapInv (drive (γ ^ 2) B ω) (lenTimeArc γ ℓ (wedgeConfig γ B Y ω))
              ((unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) : ℂ) *
                g1zSideMap left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)).2 u))
            (Qc γ) (foldedCircle e r)

end R18
end QuantumZipper
