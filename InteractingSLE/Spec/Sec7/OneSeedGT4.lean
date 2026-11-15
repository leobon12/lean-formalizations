/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux126
import InteractingSLE.Spec.Supplement.LP1Seed
import InteractingSLE.Spec.Theorem13

/-!
# The one-seed theorem for `κ > 4`, and Theorem 1.3's `κ > 4` range with Aux. lemma 126 discharged

Packet PROVE-AUX126. The named input `Theorem13.SeedOneForceGTFourStatement` (the one-seed theorem, supplement §6.1,
"One-seed parameter coverage", `source/spec/p433-480.md` L1119, p. 479) is the `hseed` premise of
`Sec7.oneForceStatement_of_stopped` for `κ > 4`. PROVE-LP14 (`Spec/Supplement/LP1Seed`) proves it from LP10's two-seed
premise `LP.TwoSeedComplete κ` (`LP.seedOneForce_of_twoSeedComplete`: Lemma LP1 with `q = 0`, where the zero-weight
left seed is deleted). Theorem 1.3's `κ > 4` range already has the inputs of `LP.TwoSeedComplete κ` (Theorem R.7's
reference, Lemma 7.25's reference, Aux. lemma 126's change of measure, LP4), and the change of measure is now proved
(`Sec7.Aux126.aux126GirsanovStatement`). This file composes them:

* `seedOneForceGTFourStatement_of_twoSeedComplete`: the named input from the two-seed premise;
* `twoSeedComplete_of_driverReference`: the two-seed premise from R.7's reference, the driving part of Lemma 7.25's
  reference (`Sec7.Aux126.Lemma725DriverReferenceStatement`, implied by `Sec7.Lemma725ReferenceStatement`) and LP4;
* `seedOneForceGTFourStatement_of_open`;
* `ae_exists_isGeneratingTrace_of_four_lt_reduced` and `ae_exists_isGeneratingTrace_of_open_reduced`: Theorem 1.3
  (`a > 4`, and all `a` in provider shape) from 18 inputs instead of 20 — `h1gt` and `hGir` are discharged, and
  `h725` is weakened to the driving part of Lemma 7.25's reference.

The import of `Spec/Supplement/LP1Seed` (PROVE-LP14) is the only one outside the landed tree when this file was written.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace OneSeedGT4

/-- **The one-seed theorem for `κ > 4` from the two-seed premise** (`LP.seedOneForce_of_twoSeedComplete`). -/
theorem seedOneForceGTFourStatement_of_twoSeedComplete (h2 : ∀ κ : ℝ, 4 < κ → LP.TwoSeedComplete.{u} κ) :
    Theorem13.SeedOneForceGTFourStatement.{u} :=
  fun κ hκ => LP.seedOneForce_of_twoSeedComplete (by linarith) (h2 κ hκ)

/-- **LP10's two-seed premise** ("Two-seed inputs to the induction", p. 487) from the reference of Theorem R.7, the
driving part of the reference of Lemma 7.25 and LP4; the change of measure of Aux. lemma 126 is proved. -/
theorem twoSeedComplete_of_driverReference (hR7 : R7.R7ReferenceStatement.{0})
    (h725 : Aux126.Lemma725DriverReferenceStatement.{0}) (hLP4 : LP.LP4Statement.{u}) {κ : ℝ} (hκ : 4 < κ) :
    LP.TwoSeedComplete.{u} κ :=
  fun _ _ hL hR => LP.isCompleteForceWord_twoSeed (R7.theoremR7TraceStatement_of_reference hR7)
    (Aux126.lemma725TraceStatement_of_driverReference h725) hLP4 hκ hL hR

/-- **The one-seed theorem for `κ > 4`** (`Theorem13.SeedOneForceGTFourStatement`) from inputs Theorem 1.3's `κ > 4`
range already has: the reference of Theorem R.7, the driving part of the reference of Lemma 7.25, and LP4. -/
theorem seedOneForceGTFourStatement_of_open (hR7 : R7.R7ReferenceStatement.{0})
    (h725 : Aux126.Lemma725DriverReferenceStatement.{0}) (hLP4 : LP.LP4Statement.{u}) :
    Theorem13.SeedOneForceGTFourStatement.{u} :=
  seedOneForceGTFourStatement_of_twoSeedComplete fun _ hκ => twoSeedComplete_of_driverReference hR7 h725 hLP4 hκ

/-- **Theorem 1.3 for `a > 4`** (conditional helper), from ten open inputs: those of
`Theorem13.ae_exists_isGeneratingTrace_of_four_lt` without the one-seed theorem and the change of measure of Aux.
lemma 126, and with the reference of Lemma 7.25 replaced by its driving part. -/
theorem ae_exists_isGeneratingTrace_of_four_lt_reduced
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ)
    (h106 : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (hseed : ∀ κ : ℝ, 4 < κ → Sec7.SeedEntranceStatement.{u} κ)
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Aux126.Lemma725DriverReferenceStatement.{0})
    (hLP4 : LP.LP4Statement.{u})
    {a : ℝ} (ha4 : 4 < a) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  LP.ae_exists_isGeneratingTrace_of_isCompleteForceWord
    (Theorem13.lp10Statement_of_open h99 (seedOneForceGTFourStatement_of_open hR7 h725 hLP4) h106 h6 hseed h113
      h8 h9 a ha4 (twoSeedComplete_of_driverReference hR7 h725 hLP4 ha4) xL xR ρL ρR hF) hE

/-- **Theorem 1.3 (continuity and endpoint)**, with exactly the conclusion of the frozen
`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`, in the provider shape (all of the anchor's arguments implicit,
its hypotheses `ha`, `hF`, `hE` auto-parameters), from 18 open named inputs (conditional helper; it is not the
provider): the inputs of `Theorem13.ae_exists_isGeneratingTrace_of_open` without the one-seed theorem (`h1gt`) and the
change of measure of Aux. lemma 126 (`hGir`), both proved, and with the reference of Lemma 7.25 replaced by its driving
part (`Sec7.Aux126.lemma725DriverReferenceStatement_of_reference` gives it from the old input). -/
theorem ae_exists_isGeneratingTrace_of_open_reduced
    (h71 : Sec7.Lemma71.Lemma71MappedSegmentStatement.{0})
    (h99lt : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.Aux99StoppedStatement.{u} κ)
    (h102 : Sec7.Aux102BandStatement.{u}) (h106lt : Sec7.Aux106PositiveStatement.{u})
    (hseedlt : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.SeedEntranceStatement.{u} κ)
    (h113lt : Sec7.Aux113TransienceStatement.{u}) (h1s : Sec7.OneSidedPrefixStatement.{u})
    (hWW : LP.WWTheorem18DistinctStatement.{u})
    (h99gt : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ)
    (h106gt : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ) (h6 : ∀ κ : ℝ, 4 < κ → LP.LP6Statement.{u} κ)
    (hseedgt : ∀ κ : ℝ, 4 < κ → Sec7.SeedEntranceStatement.{u} κ)
    (h113gt : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP.LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Aux126.Lemma725DriverReferenceStatement.{0})
    (hLP4 : LP.LP4Statement.{u})
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  rcases lt_trichotomy a 4 with h4 | rfl | h4
  · exact Theorem13.ae_exists_isGeneratingTrace_of_lt_four h71 h99lt h102 h106lt hseedlt h113lt h1s ha h4 hF hE
  · exact Theorem13.ae_exists_isGeneratingTrace_four hWW hF hE
  · exact ae_exists_isGeneratingTrace_of_four_lt_reduced h99gt h106gt h6 hseedgt h113gt h8 h9 hR7 h725 hLP4 h4
      hF hE

end OneSeedGT4

end Sec7

end InteractingSLE
