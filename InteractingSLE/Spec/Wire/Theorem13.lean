/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem13
import InteractingSLE.Spec.Sec7.ContinuityProb6Positive
import InteractingSLE.Spec.Sec7.ContinuityProb6Seed
import InteractingSLE.Spec.Sec7.Aux126
import InteractingSLE.Spec.Zhan.WordsEscape

/-!
# Theorem 1.3 with the newly proved inputs discharged

Packet PROVE-WIRE1 (no new mathematics). PROVE-T13-ASM assembled the frozen conclusion of Theorem 1.3
(`Theorem13.ae_exists_isGeneratingTrace_of_open`, `Spec/Theorem13.lean`) from twenty named inputs. Four of them are
now theorems and are discharged here:

| Input of `Theorem13.ae_exists_isGeneratingTrace_of_open` | Now proved by |
|---|---|
| `h106lt : Sec7.Aux106PositiveStatement` (Aux. 106, `a, b > 0`) | `Sec7.Positive.aux106PositiveStatement` |
| `hseedlt : ∀ κ, 0 < κ → κ < 4 → Sec7.SeedEntranceStatement κ` (Aux. 103, `D₀ = 0`) | `Sec7.Positive.seedEntranceStatement` |
| `hseedgt : ∀ κ, 4 < κ → Sec7.SeedEntranceStatement κ` | `Sec7.Positive.seedEntranceStatement` |
| `hGir : Sec7.Aux126GirsanovStatement.{0}` (Aux. 126, change of measure) | `Sec7.Aux126.aux126GirsanovStatement` |

The theorems below carry the original statements' conclusions verbatim with these four hypotheses removed; they are
conditional helpers (distinct names, `_of_remaining`), not providers. Sixteen named inputs remain:
`0 < κ < 4` five, `κ = 4` one, `κ > 4` ten (handoff `planning/handoffs/PROVE-WIRE1.md` has the table).

Also recorded: for `0 < κ ≤ 4`, Aux. lemma 7 and separated transience are theorems (`Zhan.aux7Statement`,
`Zhan.separatedTransienceStatement`, `Spec/Zhan/WordsEscape.lean`), so every ordered word with admissible side partial
sums is complete (`isCompleteForceWord_of_admissible_of_le_four`, unconditional).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

open Theorem13

/-! ### The building blocks with the proved inputs discharged -/

/-- **The revised §7.3 induction for `0 < κ < 4`** (`Theorem13.revisedInductionLtFourStatement_of_open`) with Aux.
lemma 106 for `a, b > 0` (`Sec7.Positive.aux106PositiveStatement`) and the seed entrance of Aux. lemma 103
(`Sec7.Positive.seedEntranceStatement`) discharged (conditional helper). -/
theorem revisedInductionLtFourStatement_of_remaining
    (h71 : Sec7.Lemma71.Lemma71MappedSegmentStatement.{0})
    (h99 : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.Aux99StoppedStatement.{u} κ)
    (h102 : Sec7.Aux102BandStatement.{u}) (h113 : Sec7.Aux113TransienceStatement.{u})
    (h1s : Sec7.OneSidedPrefixStatement.{u}) :
    LP.RevisedInductionLtFourStatement.{u} :=
  revisedInductionLtFourStatement_of_open h71 h99 h102 Sec7.Positive.aux106PositiveStatement
    (fun _ hκ _ => Sec7.Positive.seedEntranceStatement hκ) h113 h1s

/-- **Theorem LP10** (`Theorem13.lp10Statement_of_open`) with the seed entrance discharged (conditional helper). -/
theorem lp10Statement_of_remaining
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h1 : SeedOneForceGTFourStatement.{u})
    (h106 : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ) :
    LP.LP10Statement.{u} :=
  lp10Statement_of_open h99 h1 h106 h6 (fun _ hκ => Sec7.Positive.seedEntranceStatement (by linarith)) h113 h8 h9

/-- **The two-seed premise of LP10** (`Theorem13.twoSeedComplete_of_open`) with the change of measure of Aux. lemma
126 discharged (`Sec7.Aux126.aux126GirsanovStatement`; conditional helper). -/
theorem twoSeedComplete_of_remaining (hR7 : R7.R7ReferenceStatement.{0})
    (h725 : Sec7.Lemma725ReferenceStatement.{0}) (hLP4 : LP.LP4Statement.{u}) {κ : ℝ} (hκ : 4 < κ) :
    LP.TwoSeedComplete.{u} κ :=
  twoSeedComplete_of_open hR7 h725 Sec7.Aux126.aux126GirsanovStatement hLP4 hκ

/-- **Every ordered force word is complete for `κ > 4`** (`Theorem13.isCompleteForceWord_of_four_lt_of_open`) with
the seed entrance and Aux. lemma 126's change of measure discharged (conditional helper). -/
theorem isCompleteForceWord_of_four_lt_of_remaining
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h1 : SeedOneForceGTFourStatement.{u})
    (h106 : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Sec7.Lemma725ReferenceStatement.{0}) (hLP4 : LP.LP4Statement.{u})
    {κ : ℝ} (hκ : 4 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hF : IsOrderedForceWord xL xR) : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR :=
  lp10Statement_of_remaining h99 h1 h106 h6 h113 h8 h9 κ hκ (twoSeedComplete_of_remaining hR7 h725 hLP4 hκ)
    xL xR ρL ρR hF

/-- **Words with admissible side partial sums are complete for `0 < κ ≤ 4`** (unconditional):
`Theorem13.isCompleteForceWord_of_admissible` with separated transience proved
(`Zhan.separatedTransienceStatement`, Astra §3). -/
theorem isCompleteForceWord_of_admissible_of_le_four {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR :=
  isCompleteForceWord_of_admissible hκ (Zhan.separatedTransienceStatement hκ hκ4) hF hadm

/-! ### Theorem 1.3, by range and assembled -/

/-- **Theorem 1.3 for `0 < a < 4`** (conditional helper), from the five remaining inputs of this range: the mapped
pocket segment of Lemma 7.1, Aux. 99 stopped, Aux. 102 with its band switches, Aux. 113's transience without merger,
the prefix of the one-sided step. -/
theorem ae_exists_isGeneratingTrace_of_lt_four_of_remaining
    (h71 : Sec7.Lemma71.Lemma71MappedSegmentStatement.{0})
    (h99 : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.Aux99StoppedStatement.{u} κ)
    (h102 : Sec7.Aux102BandStatement.{u}) (h113 : Sec7.Aux113TransienceStatement.{u})
    (h1s : Sec7.OneSidedPrefixStatement.{u})
    {a : ℝ} (ha : 0 < a) (ha4 : a < 4) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_lt_four h71 h99 h102 Sec7.Positive.aux106PositiveStatement
    (fun _ hκ _ => Sec7.Positive.seedEntranceStatement hκ) h113 h1s ha ha4 hF hE

/-- **Theorem 1.3 for `a > 4`** (conditional helper), from the ten remaining inputs of this range. -/
theorem ae_exists_isGeneratingTrace_of_four_lt_of_remaining
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h1 : SeedOneForceGTFourStatement.{u})
    (h106 : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Sec7.Lemma725ReferenceStatement.{0}) (hLP4 : LP.LP4Statement.{u})
    {a : ℝ} (ha4 : 4 < a) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  LP.ae_exists_isGeneratingTrace_of_isCompleteForceWord
    (isCompleteForceWord_of_four_lt_of_remaining h99 h1 h106 h6 h113 h8 h9 hR7 h725 hLP4 ha4 xL xR ρL ρR hF) hE

/-- **Theorem 1.3 (continuity and endpoint)**, with exactly the conclusion of the frozen
`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`, in the provider shape (all of the anchor's arguments implicit,
its hypotheses `ha`, `hF`, `hE` auto-parameters), from the **sixteen remaining** named inputs (conditional helper; it
is not the provider). This is `Theorem13.ae_exists_isGeneratingTrace_of_open` with Aux. 106 for `a, b > 0`, the seed
entrance of Aux. 103 (both ranges) and Aux. 126's change of measure discharged.

Remaining, `0 < κ < 4`: `h71`, `h99lt`, `h102`, `h113lt`, `h1s`. `κ = 4`: `hWW`. `κ > 4`: `h99gt`, `h1gt`, `h106gt`,
`h6`, `h113gt`, `h8`, `h9`, `hR7`, `h725`, `hLP4`. -/
theorem ae_exists_isGeneratingTrace_of_remaining
    (h71 : Sec7.Lemma71.Lemma71MappedSegmentStatement.{0})
    (h99lt : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.Aux99StoppedStatement.{u} κ)
    (h102 : Sec7.Aux102BandStatement.{u}) (h113lt : Sec7.Aux113TransienceStatement.{u})
    (h1s : Sec7.OneSidedPrefixStatement.{u})
    (hWW : LP.WWTheorem18DistinctStatement.{u})
    (h99gt : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h1gt : SeedOneForceGTFourStatement.{u})
    (h106gt : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (h113gt : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Sec7.Lemma725ReferenceStatement.{0}) (hLP4 : LP.LP4Statement.{u})
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_open h71 h99lt h102 Sec7.Positive.aux106PositiveStatement
    (fun _ hκ _ => Sec7.Positive.seedEntranceStatement hκ) h113lt h1s hWW h99gt h1gt h106gt h6
    (fun _ hκ => Sec7.Positive.seedEntranceStatement (by linarith)) h113gt h8 h9 hR7 h725
    Sec7.Aux126.aux126GirsanovStatement hLP4 ha hF hE

end Wire

end InteractingSLE
