/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem13Inputs

/-!
# Theorem 1.3 (continuity and endpoint), assembled from the open named inputs

Packet PROVE-T13-ASM. The frozen anchor `IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`
(`InteractingSLE/Frozen/Spec/IsIntegratedSLEEvolution_ae_exists_isGeneratingTrace.lean`; Specification p. 4, proof
interface Corollary LP11, p. 488) is proved here with **exactly its frozen conclusion**, in the provider shape (every
argument of the anchor implicit, its hypotheses `ha`, `hF`, `hE` as auto-parameters), from the twenty open named inputs
of `Theorem13Inputs.lean`, listed by parameter range. The theorem `ae_exists_isGeneratingTrace_of_open` carries a
distinct name: it is a conditional helper, not a provider. Once its inputs are proved, the provider is
`ae_exists_isGeneratingTrace_of_open p₁ … p₂₀` and the anchor's body is a bare `by exact`.

What is proved (no input involved):

* the inadmissible-seed clause (`IsIntegratedSLEEvolution.ae_eq_zero_of_thresholdCondition`, PROVE-LP, from the
  maximal-lifetime reading of the integrated path);
* the parameter split of LP11 and the passage from completeness of the word to the frozen conclusion
  (`LP.ae_exists_isGeneratingTrace_of_inputs`);
* every reduction composed in `Theorem13Inputs.lean`, Theorem 2.2's existence and the zero-force base.

The three range theorems `ae_exists_isGeneratingTrace_of_lt_four`, `ae_exists_isGeneratingTrace_four` and
`ae_exists_isGeneratingTrace_of_four_lt` state the frozen conclusion for one parameter range from that range's inputs
only (7, 1 and 12 inputs): they check in Lean which inputs each range needs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem13

/-- **Theorem 1.3 for `0 < a < 4`** (conditional helper; the revised §7.3 induction), from the seven open inputs of
this range. -/
theorem ae_exists_isGeneratingTrace_of_lt_four
    (h71 : Sec7.Lemma71.Lemma71MappedSegmentStatement.{0})
    (h99 : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.Aux99StoppedStatement.{u} κ)
    (h102 : Sec7.Aux102BandStatement.{u}) (h106 : Sec7.Aux106PositiveStatement.{u})
    (hseed : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.SeedEntranceStatement.{u} κ)
    (h113 : Sec7.Aux113TransienceStatement.{u}) (h1s : Sec7.OneSidedPrefixStatement.{u})
    {a : ℝ} (ha : 0 < a) (ha4 : a < 4) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  LP.ae_exists_isGeneratingTrace_of_isCompleteForceWord
    (revisedInductionLtFourStatement_of_open h71 h99 h102 h106 hseed h113 h1s a ha ha4 xL xR ρL ρR hF) hE

/-- **Theorem 1.3 for `a = 4`** (conditional helper; Wang–Wu's Theorem 1.8, ruling R31), from the one open input of
this range. -/
theorem ae_exists_isGeneratingTrace_four (hWW : LP.WWTheorem18DistinctStatement.{u})
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution 4 xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  LP.ae_exists_isGeneratingTrace_of_isCompleteForceWord (wwTheorem18Statement_of_open hWW xL xR ρL ρR hF) hE

/-- **Theorem 1.3 for `a > 4`** (conditional helper; Theorem LP10 with its two-seed inputs), from the twelve open
inputs of this range. -/
theorem ae_exists_isGeneratingTrace_of_four_lt
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h1 : SeedOneForceGTFourStatement.{u})
    (h106 : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (hseed : ∀ κ : ℝ, 4 < κ → Sec7.SeedEntranceStatement.{u} κ)
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Sec7.Lemma725ReferenceStatement.{0})
    (hGir : Sec7.Aux126GirsanovStatement.{0}) (hLP4 : LP.LP4Statement.{u})
    {a : ℝ} (ha4 : 4 < a) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  LP.ae_exists_isGeneratingTrace_of_isCompleteForceWord
    (isCompleteForceWord_of_four_lt_of_open h99 h1 h106 h6 hseed h113 h8 h9 hR7 h725 hGir hLP4 ha4 xL xR ρL ρR hF)
    hE

/-- **Theorem 1.3 (continuity and endpoint)**, with exactly the conclusion of the frozen
`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`, in the provider shape (all of the anchor's arguments implicit,
its hypotheses `ha`, `hF`, `hE` auto-parameters), from the open named inputs of the three parameter ranges
(conditional helper; it is not the provider). Almost surely: an inadmissible seed gives `ζ = 0`; there is a continuous
generating trace on `[0, ζ]` (on `[0, ∞)` when `ζ = ∞`); and it tends to infinity on `{ζ = ∞}`.

Inputs, `0 < κ < 4` (the revised §7.3 induction): the mapped pocket segment of Lemma 7.1 (`h71`), Aux. 99 stopped
(`h99lt`), Aux. 102 with its band switches (`h102`), Aux. 106 for `a, b > 0` (`h106lt`), the seed entrance of Aux. 103
(`hseedlt`), Aux. 113's transience without merger (`h113lt`), the prefix of the one-sided step (`h1s`).
Input, `κ = 4`: Wang–Wu's Theorem 1.8 for distinct positions (`hWW`).
Inputs, `κ > 4` (Theorem LP10 and its two-seed inputs): Aux. 99 stopped (`h99gt`), the one-seed theorem (`h1gt`),
Aux. 106 (`h106gt`), LP6 (`h6`), the seed entrance (`hseedgt`), Aux. 113's transience in LP10's form (`h113gt`), LP8
(`h8`), the prefix of LP9 (`h9`), the reference of R.7 (`hR7`), the reference of Lemma 7.25 (`h725`), the change of
measure of Aux. 126 (`hGir`), LP4 (`hLP4`). -/
theorem ae_exists_isGeneratingTrace_of_open
    (h71 : Sec7.Lemma71.Lemma71MappedSegmentStatement.{0})
    (h99lt : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.Aux99StoppedStatement.{u} κ)
    (h102 : Sec7.Aux102BandStatement.{u}) (h106lt : Sec7.Aux106PositiveStatement.{u})
    (hseedlt : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.SeedEntranceStatement.{u} κ)
    (h113lt : Sec7.Aux113TransienceStatement.{u}) (h1s : Sec7.OneSidedPrefixStatement.{u})
    (hWW : LP.WWTheorem18DistinctStatement.{u})
    (h99gt : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h1gt : SeedOneForceGTFourStatement.{u})
    (h106gt : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (hseedgt : ∀ κ : ℝ, 4 < κ → Sec7.SeedEntranceStatement.{u} κ)
    (h113gt : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Sec7.Lemma725ReferenceStatement.{0})
    (hGir : Sec7.Aux126GirsanovStatement.{0}) (hLP4 : LP.LP4Statement.{u})
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  rcases lt_trichotomy a 4 with h4 | rfl | h4
  · exact ae_exists_isGeneratingTrace_of_lt_four h71 h99lt h102 h106lt hseedlt h113lt h1s ha h4 hF hE
  · exact ae_exists_isGeneratingTrace_four hWW hF hE
  · exact ae_exists_isGeneratingTrace_of_four_lt h99gt h1gt h106gt h6 hseedgt h113gt h8 h9 hR7 h725 hGir hLP4 h4
      hF hE

end Theorem13

end InteractingSLE
