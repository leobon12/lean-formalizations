import QuantumZipper.Proofs.Zipper.LocLenStmts
import QuantumZipper.Proofs.Zipper.F1LenInScale
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6a: the open-arc capacity cocycle in the `Γ⁰` picture (statements)

Copies, with `unzipLengths ↦ unzipLengthsArc` (substitution rule of `handoff/FOLLOW-PAPER-13.md`
§1), of `F1.PairCocycle` (F1LenInPair.lean:46) and `F1.LenPairCocycleCfgStmt`
(F1LenInCfg.lean:36): additivity of the open-arc lengths of the two sides of `η[0,t]` along the
capacity flow (Sheffield arXiv:1012.4797 p. 56 and p. 70; Berestycki–Powell arXiv:2404.16642
Def 8.12 p. 281).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- Open-arc copy of `F1.PairCocycle`: for all `u, s ≥ 0`,
`L±_{u+s}(c) = L±_u(c) + L±_s(zipCapDown γ u c)` with open-arc lengths. -/
def PairCocycleArc (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) : Prop :=
  ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
    (unzipLengthsArc γ c (u + s)).1 =
        (unzipLengthsArc γ c u).1 + (unzipLengthsArc γ (zipCapDown γ u c) s).1 ∧
    (unzipLengthsArc γ c (u + s)).2 =
        (unzipLengthsArc γ c u).2 + (unzipLengthsArc γ (zipCapDown γ u c) s).2

/-- Open-arc copy of `F1.LenPairCocycleCfgStmt`: a.s. `cfg κ B X ω = (h₀ + X, √κ B)` satisfies
the capacity cocycle of both open-arc lengths. -/
def LenPairCocycleCfgArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), 0 < κ → κ < 4 → IsBrownianReal B P →
    IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, PairCocycleArc (Real.sqrt κ) (B2.cfg κ B X ω)

end LocLen
end QuantumZipper
