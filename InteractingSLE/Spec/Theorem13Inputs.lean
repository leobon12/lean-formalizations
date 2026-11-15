/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Supplement.LPProbInduction
import InteractingSLE.Spec.Supplement.LPAmalgamate
import InteractingSLE.Spec.Supplement.R7Reference
import InteractingSLE.Spec.Sec7.TraceCodingUse
import InteractingSLE.Spec.Sec7.Lemma71Reduce
import InteractingSLE.Spec.Sec7.ContinuityProb5Aux106
import InteractingSLE.Spec.Sec7.ContinuityProb4Aux106
import InteractingSLE.Spec.Sec7.ContinuityProb4Aux113
import InteractingSLE.Spec.Sec7.ContinuityProb3Steps
import InteractingSLE.Spec.Sec7.ContinuityProb2Aux99
import InteractingSLE.Spec.Sec7.ContinuityProbInduction
import InteractingSLE.Spec.Sec2.Assembly2Entr
import InteractingSLE.Spec.ZhanGT4.PrefixAux7

/-!
# Theorem 1.3: the three parameter ranges, reduced to the open named inputs

Packet PROVE-T13-ASM. Corollary LP11 (`source/spec/p481-528.md` L175–L215, pp. 488–489) proves Theorem 1.3 by three
parameter ranges, and PROVE-LP assembled it (`LP.ae_exists_isGeneratingTrace_of_inputs`) from six range-level
inputs. Since then most of their proofs have landed as reductions to finer named statements. This file composes
every landed reduction and discharges every input that is now proved, so that each range is complete from
**exactly the named statements that are still open, each in its landed form**.

Discharged here (proved, not assumed):

* Theorem 2.2's existence, `Sec7.ExistsEvolutionStatement` (`existsEvolutionStatement`, from
  `exists_isIntegratedSLEEvolution_assembled`, sealed R42);
* the zero-force base `LP.ZeroForceStatement κ` (`zeroForceStatement`, from `Sec7.isCompleteForceWord_zero`);
* the codings and the Jacobi diffusion (already removed in `Sec7.TraceCodingUse`), the restart with a random force
  word (`Sec7.RandRestart.randomRestartTraceStatement`), the amalgamation of coincident marks.

## The open inputs, by range

| Range | Named input (landed form) | Source | Reduction used |
|---|---|---|---|
| `κ < 4` | `Sec7.Lemma71.Lemma71MappedSegmentStatement.{0}` | Lemma 7.1 (p. 223) | `…_of_mappedSegment` |
| `κ < 4` | `Sec7.Aux99StoppedStatement κ` | Aux. 99 (p. 340) | `aux99Statement_of_stopped` |
| `κ < 4` | `Sec7.Aux102BandStatement` | Aux. 102, 106 (pp. 348, 354) | `aux106TransienceStatement_of_inputs` |
| `κ < 4` | `Sec7.Aux106PositiveStatement` | Aux. 106, `a, b > 0` (p. 354) | `aux106TransienceStatement_of_inputs` |
| `κ < 4` | `Sec7.SeedEntranceStatement κ` | Aux. 103, `D₀ = 0` (p. 350) | `aux113PrefixStatement_of_inputs` |
| `κ < 4` | `Sec7.Aux113TransienceStatement` | Aux. 113, `τ = ∞` (pp. 370–372) | `aux113PrefixStatement_of_inputs` |
| `κ < 4` | `Sec7.OneSidedPrefixStatement` | one-sided step (pp. 378–380) | `oneSidedStepStatement_of_prefix` |
| `κ = 4` | `LP.WWTheorem18DistinctStatement` | Wang–Wu Theorem 1.8 (R31) | `wwTheorem18Statement_of_distinct` |
| `κ > 4` | `Sec7.Aux99StoppedStatement κ` | Aux. 99 (p. 340; LP10, p. 486) | `oneForceStatement_of_stopped` |
| `κ > 4` | `SeedOneForceGTFourStatement` (here) | one-seed theorem (p. 479) | `oneForceStatement_of_stopped` |
| `κ > 4` | `LP.Aux106Statement κ` | Aux. 106 (p. 354) | — |
| `κ > 4` | `LP.LP6Statement κ` | Prop. LP6 (p. 483) | — |
| `κ > 4` | `Sec7.SeedEntranceStatement κ` | Aux. 103, `D₀ = 0` (p. 350) | `lpAux113PrefixStatement_of_inputs` |
| `κ > 4` | `Sec7.LPAux113TransienceStatement κ` | Aux. 113, (LP10.1) (p. 487) | `lpAux113PrefixStatement_of_inputs` |
| `κ > 4` | `LP.LP8Statement κ` | Lemma LP8 (p. 485) | — |
| `κ > 4` | `Sec7.LP9PrefixStatement κ` | Lemma LP9 (p. 485) | `lp9Statement_of_prefix` |
| `κ > 4` | `R7.R7ReferenceStatement.{0}` | Theorem R.7 (p. 477) | `theoremR7TraceStatement_of_reference` |
| `κ > 4` | `Sec7.Lemma725ReferenceStatement.{0}` | Lemma 7.25 (p. 413) | `lemma725TraceStatement_of_…` |
| `κ > 4` | `Sec7.Aux126GirsanovStatement.{0}` | Aux. 126 (p. 399) | `lemma725TraceStatement_of_…` |
| `κ > 4` | `LP.LP4Statement` | Prop. LP4 (p. 482) | `LP.isCompleteForceWord_twoSeed` |

The only new named statement is `SeedOneForceGTFourStatement`: it is the `hseed` premise of the landed reduction
`Sec7.oneForceStatement_of_stopped`, verbatim, quantified over `κ > 4`. Reference statements (existential: one
evolution on some probability space) are taken at universe `0`; every other input is at the universe of the
evolution's probability space.

## Main results

* `revisedInductionLtFourStatement_of_open` (`0 < κ < 4`), `wwTheorem18Statement_of_open` (`κ = 4`),
  `lp10Statement_of_open`, `twoSeedComplete_of_open` and `isCompleteForceWord_of_four_lt_of_open` (`κ > 4`).
* `isCompleteForceWord_of_admissible`: words with admissible partial sums are complete for every `κ > 0` from
  separated transience alone (the landed trace with marks at the seed, `ZhanGT4.Prefix`, and Aux. lemma 7).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem13

/-! ### Inputs that are now proved -/

/-- **Theorem 2.2, existence**, in the named form `Sec7.ExistsEvolutionStatement` used by Aux. lemmas 103, 106 and 113:
the assembled existence theorem `exists_isIntegratedSLEEvolution_assembled` (PROVE-SEC2-PATCH3; anchor sealed, R42). -/
theorem existsEvolutionStatement : Sec7.ExistsEvolutionStatement := by
  intro _ ha _ _ _ _ _ _ hF
  exact exists_isIntegratedSLEEvolution_assembled ha hF

/-- **The zero-force base** `LP.ZeroForceStatement κ` of LP10 (p. 486: "With zero groups use ordinary SLE"), for every
`κ > 0`: `Sec7.isCompleteForceWord_zero` (PROVE-SEC7-C2). -/
theorem zeroForceStatement {κ : ℝ} (hκ : 0 < κ) : LP.ZeroForceStatement.{u} κ :=
  fun xL xR _ _ => Sec7.isCompleteForceWord_of_forall_eq_zero hκ xL xR (fun i => i.elim0) (fun i => i.elim0)

/-! ### The one new named statement -/

/-- **Named input (`κ > 4`): the one-seed theorem** (Theorem LP10's proof, `source/spec/p481-528.md` L138, p. 486:
"With one group use Aux. lemma 99 through its first swallow and the one-seed theorem for every admissible
continuation"; supplement §6.1, "One-seed parameter coverage", `source/spec/p433-480.md` L1119, p. 479: Lemma LP1 with
the references of Lemma 7.25, Aux. lemma 131 and Theorem R.7, and the noncolliding one-seed theorem for `ρ ≥ c`). For
`κ > 4`, one right mark at the seed `0⁺` with weight `ρ > −2` gives a complete force word. This is verbatim the
premise `hseed` of the landed reduction `Sec7.oneForceStatement_of_stopped`, quantified over `κ > 4`; for `κ < 4` its
counterpart is `Sec7.SeedOneForceTraceStatement`. -/
def SeedOneForceGTFourStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 →
    LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR

/-! ### `0 < κ < 4`: the revised §7.3 induction -/

/-- **The revised induction for Theorem 1.3, `0 < κ < 4`, from the open inputs** (Specification §7.3, pp. 378–380;
conditional helper, it replaces no source theorem). Composition of the landed reductions:

* Proposition 7.3 and the one-force seed case from the embedded reference of Lemma 7.1, which comes from the mapped
  pocket segment (`Sec7.Lemma71.lemma71TraceReferenceStatement_of_mappedSegment`,
  `Sec7.prop73TraceStatement_of_reference`, `Sec7.seedOneForceTraceStatement_of_reference`);
* Aux. lemma 99 from its stopped assertion (`Sec7.aux99Statement_of_stopped`);
* Aux. lemma 106 from Aux. 102 with its band switches and the positive case (`Sec7.aux106TransienceStatement_of_inputs`,
  `Sec7.aux106SeparatedStatement_of_inputs`, `Sec7.aux106Statement_of_separated`);
* Aux. lemma 113 from the seed entrance and transience without merger (`Sec7.aux113PrefixStatement_of_inputs`,
  `Sec7.aux113Statement_of_prefix`);
* the one-sided step from its prefix part (`Sec7.oneSidedStepStatement_of_prefix`);
* Theorem 2.2's existence (`existsEvolutionStatement`), then the induction
  `Sec7.revisedInductionLtFourStatement_of_inputs`. -/
theorem revisedInductionLtFourStatement_of_open
    (h71 : Sec7.Lemma71.Lemma71MappedSegmentStatement.{0})
    (h99 : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.Aux99StoppedStatement.{u} κ)
    (h102 : Sec7.Aux102BandStatement.{u}) (h106 : Sec7.Aux106PositiveStatement.{u})
    (hseed : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.SeedEntranceStatement.{u} κ)
    (h113 : Sec7.Aux113TransienceStatement.{u}) (h1s : Sec7.OneSidedPrefixStatement.{u}) :
    LP.RevisedInductionLtFourStatement.{u} := by
  have href : Sec7.Lemma71TraceReferenceStatement.{0} :=
    Sec7.Lemma71.lemma71TraceReferenceStatement_of_mappedSegment h71
  have h73 : Sec7.Prop73TraceStatement.{u} := Sec7.prop73TraceStatement_of_reference href
  have h1 : Sec7.SeedOneForceTraceStatement.{u} := Sec7.seedOneForceTraceStatement_of_reference href
  have h99' : Sec7.Aux99Statement.{u} := Sec7.aux99Statement_of_stopped h99 h1
  have h106' : Sec7.Aux106Statement.{u} :=
    Sec7.aux106Statement_of_separated (Sec7.aux106SeparatedStatement_of_inputs existsEvolutionStatement h1 h99'
      (Sec7.aux106TransienceStatement_of_inputs existsEvolutionStatement h1 h99' h102 h106))
  have h113' : Sec7.Aux113Statement.{u} :=
    Sec7.aux113Statement_of_prefix (Sec7.aux113PrefixStatement_of_inputs existsEvolutionStatement h73 hseed h113)
  exact Sec7.revisedInductionLtFourStatement_of_inputs h73 h1 h99' h106' h113'
    (Sec7.oneSidedStepStatement_of_prefix h1s)

/-! ### `κ = 4`: Wang–Wu -/

/-- **Wang–Wu's Theorem 1.8 on the frozen ordered force word** (`κ = 4`, ruling R31) from its distinct-position form,
by the proved amalgamation of coincident marks (`LP.wwTheorem18Statement_of_distinct`). -/
theorem wwTheorem18Statement_of_open (hWW : LP.WWTheorem18DistinctStatement.{u}) : LP.WWTheorem18Statement.{u} :=
  LP.wwTheorem18Statement_of_distinct hWW

/-! ### `κ > 4`: Theorem LP10 and the two-seed inputs -/

/-- **Theorem LP10 from the open inputs** (supplement §6.5, p. 486; conditional helper). The induction
`LP.lp10Statement_of_reductions` (PROVE-R17) with: the zero-force base proved (`zeroForceStatement`); one force group
from the stopped Aux. lemma 99 and the one-seed theorem (`Sec7.oneForceStatement_of_stopped`); Aux. lemma 113 in LP10's
form from the seed entrance and transience without merger, through Aux. lemma 103 and Theorem 2.2's existence
(`Sec7.lpAux113PrefixStatement_of_inputs`, `Sec7.lpAux113Statement_of_prefix`); Lemma LP9 from its prefix part
(`Sec7.lp9Statement_of_prefix`); Aux. lemma 106, Proposition LP6 and Lemma LP8 as named. -/
theorem lp10Statement_of_open
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h1 : SeedOneForceGTFourStatement.{u})
    (h106 : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (hseed : ∀ κ : ℝ, 4 < κ → Sec7.SeedEntranceStatement.{u} κ)
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ) :
    LP.LP10Statement.{u} :=
  LP.lp10Statement_of_reductions (fun _ hκ => zeroForceStatement (by linarith))
    (fun κ hκ => Sec7.oneForceStatement_of_stopped (h99 κ hκ) (h1 κ hκ)) h106 h6
    (fun κ hκ => Sec7.lpAux113Statement_of_prefix (by linarith)
      (Sec7.lpAux113PrefixStatement_of_inputs (by linarith) existsEvolutionStatement (hseed κ hκ) (h113 κ hκ)))
    h8 (fun κ hκ => Sec7.lp9Statement_of_prefix (by linarith) (h9 κ hκ))

/-- **The two-seed premise of LP10 from the open inputs** ("Two-seed inputs to the induction", p. 487): Theorem R.7 from
its reference (`R7.theoremR7TraceStatement_of_reference`), Lemma 7.25 from its reference and the change of measure of
Aux. lemma 126 (`Sec7.lemma725TraceStatement_of_reference_girsanov`), and Proposition LP4, combined by
`LP.isCompleteForceWord_twoSeed`. -/
theorem twoSeedComplete_of_open (hR7 : R7.R7ReferenceStatement.{0})
    (h725 : Sec7.Lemma725ReferenceStatement.{0}) (hGir : Sec7.Aux126GirsanovStatement.{0})
    (hLP4 : LP.LP4Statement.{u}) {κ : ℝ} (hκ : 4 < κ) : LP.TwoSeedComplete.{u} κ :=
  fun _ _ hL hR => LP.isCompleteForceWord_twoSeed (R7.theoremR7TraceStatement_of_reference hR7)
    (Sec7.lemma725TraceStatement_of_reference_girsanov h725 hGir) hLP4 hκ hL hR

/-- **Every ordered force word is complete for `κ > 4`**, from the open inputs of this range (LP11's proof, p. 488:
"For k > 4, apply LP10. Its two-seed inputs are R.7 when max(r_L, r_R) ≥ d, and LP4 when both seed weights are below
d"). -/
theorem isCompleteForceWord_of_four_lt_of_open
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h1 : SeedOneForceGTFourStatement.{u})
    (h106 : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (hseed : ∀ κ : ℝ, 4 < κ → Sec7.SeedEntranceStatement.{u} κ)
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Sec7.Lemma725ReferenceStatement.{0})
    (hGir : Sec7.Aux126GirsanovStatement.{0}) (hLP4 : LP.LP4Statement.{u})
    {κ : ℝ} (hκ : 4 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hF : IsOrderedForceWord xL xR) : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR :=
  lp10Statement_of_open h99 h1 h106 h6 hseed h113 h8 h9 κ hκ (twoSeedComplete_of_open hR7 h725 hGir hLP4 hκ)
    xL xR ρL ρR hF

/-! ### Admissible words, every `κ > 0` -/

/-- **Words with admissible partial sums are complete for every `κ > 0`, from separated transience alone.** The trace
with marks at the seed (`ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible`, Part B.1 of
the follow-up note) and Aux. lemma 7 from the separated core (`ZhanGT4.aux7Statement_of_separatedTransience_of_pos`):
the lifetime is infinite and every continuous generating trace on `[0, ∞)` tends to infinity. (Not used by the
assembly, whose induction also covers these words; it records what the landed admissible-word results give.) -/
theorem isCompleteForceWord_of_admissible {κ : ℝ} (hκ : 0 < κ) (hS : Zhan.SeparatedTransienceStatement.{u} κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  filter_upwards [ZhanGT4.aux7Statement_of_separatedTransience_of_pos hκ hS xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE]
    with ω ⟨hζ, ⟨η, hη⟩, htr⟩
  exact ⟨η, hζ ▸ hη, fun _ => htr η hη⟩

end Theorem13

end InteractingSLE
