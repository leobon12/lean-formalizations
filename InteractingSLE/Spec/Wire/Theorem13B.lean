/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Theorem13
import InteractingSLE.Spec.Sec7.OneSeedGT4
import InteractingSLE.Spec.Supplement.LP8Singleton
import InteractingSLE.Spec.Supplement.LP4ZeroOne
import InteractingSLE.WangWu.Theorem18

/-!
# Theorem 1.3 with PROVE-LP14's inputs discharged

Packet PROVE-FLOWEXIST, goal 3 (no new mathematics). PROVE-WIRE1 left Theorem 1.3
(`Wire.ae_exists_isGeneratingTrace_of_remaining`) with sixteen named inputs. Since then:

* PROVE-LP14 proved Proposition LP6 from LP9 (`LP.lp6Statement_of_lp9`), the one-seed theorem from LP10's two-seed premise
  (`LP.seedOneForce_of_twoSeedComplete`), reduced LP8 to its new-sector transience (`LP.lp8Statement_of_inputs`) and LP4
  to its positive-probability avoid step (`LP.lp4Statement_of_avoid`, with Aux. lemma 128 for driver events proved);
  `LP.lp10Statement_of_open_lp14` is Theorem LP10 from these;
* PROVE-AUX126 weakened Lemma 7.25's reference to its driving part (`Sec7.OneSeedGT4.twoSeedComplete_of_driverReference`);
* PROVE-WW-C2 proved Aux. lemma 106 in LP10's form from the one-force base and Aux. lemma 102
  (`WangWu.Theorem18.aux106Statement_of_oneForce`); the one-force base follows from Aux. lemma 99 and the two-seed premise
  (`LP.oneForceStatement_of_twoSeedComplete`), and Aux. lemma 102 is already an input of the `0 < κ < 4` range.

| PROVE-WIRE1 input (`κ > 4`) | Now |
|---|---|
| `h1gt : SeedOneForceGTFourStatement` | proved (`LP.seedOneForce_of_twoSeedComplete`) |
| `h6 : ∀ κ > 4, LP.LP6Statement κ` | proved (`LP.lp6Statement_of_lp9`) |
| `h106gt : ∀ κ > 4, LP.Aux106Statement κ` | proved from `h99gt` and `h102` (`aux106Statement_of_oneForce`) |
| `h8 : ∀ κ > 4, LP.LP8Statement κ` | narrowed to `LP.LP8TransienceStatement` |
| `hLP4 : LP.LP4Statement` | narrowed to `LP.LP4AvoidStatement` |
| `h725 : Sec7.Lemma725ReferenceStatement` | narrowed to `Sec7.Aux126.Lemma725DriverReferenceStatement` |

The narrowed inputs are implied by the old ones (`Sec7.Aux126.lemma725DriverReferenceStatement_of_reference`; LP8 and LP4
from their remaining parts by the lemmas above), so nothing is strengthened. **Thirteen named inputs remain**:
`0 < κ < 4` five (`h71`, `h99lt`, `h102`, `h113lt`, `h1s`), `κ = 4` one (`hWW`), `κ > 4` seven (`h99gt`, `h113gt`,
`h8T`, `h9`, `hR7`, `h725`, `hLP4A`); `h102` is also used for `κ > 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- **LP10's two-seed premise for `κ > 4`** from Theorem R.7's reference, the driving part of Lemma 7.25's reference
and the avoid step of LP4 (conditional helper). -/
theorem twoSeedComplete_of_remainingB (hR7 : R7.R7ReferenceStatement.{0})
    (h725 : Sec7.Aux126.Lemma725DriverReferenceStatement.{0}) (hLP4A : LP.LP4AvoidStatement.{u}) {κ : ℝ}
    (hκ : 4 < κ) : LP.TwoSeedComplete.{u} κ :=
  Sec7.OneSeedGT4.twoSeedComplete_of_driverReference hR7 h725 (LP.lp4Statement_of_avoid hLP4A) hκ

/-- **Every ordered force word is complete for `κ > 4`** (conditional helper), from the seven remaining inputs of this
range and Aux. lemma 102: Theorem LP10 (`LP.lp10Statement_of_open_lp14`) with the seed entrance proved
(`Sec7.Positive.seedEntranceStatement`) and Aux. lemma 106 from the one-force base and Aux. lemma 102. -/
theorem isCompleteForceWord_of_four_lt_of_remainingB
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h102 : Sec7.Aux102BandStatement.{u})
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8T : ∀ κ : ℝ, 4 < κ → LP.LP8TransienceStatement.{u} κ)
    (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Sec7.Aux126.Lemma725DriverReferenceStatement.{0})
    (hLP4A : LP.LP4AvoidStatement.{u})
    {κ : ℝ} (hκ : 4 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hF : IsOrderedForceWord xL xR) : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  have h2 : ∀ κ : ℝ, 4 < κ → LP.TwoSeedComplete.{u} κ := fun _ hκ' =>
    twoSeedComplete_of_remainingB hR7 h725 hLP4A hκ'
  have h106 : ∀ κ : ℝ, 4 < κ → LP.Aux106Statement.{u} κ := fun κ' hκ' =>
    WangWu.Theorem18.aux106Statement_of_oneForce (by linarith)
      (LP.oneForceStatement_of_twoSeedComplete (by linarith) (h99 κ' hκ') (h2 κ' hκ')) h102
  intro Ω mΩ
  exact LP.lp10Statement_of_open_lp14 h99 h106
    (fun _ hκ' => Sec7.Positive.seedEntranceStatement (by linarith)) h113 h8T h9 κ hκ (h2 κ hκ)
    xL xR ρL ρR hF

/-- **Theorem 1.3 for `a > 4`** (conditional helper), from the seven remaining inputs of this range and Aux. lemma
102. -/
theorem ae_exists_isGeneratingTrace_of_four_lt_of_remainingB
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ) (h102 : Sec7.Aux102BandStatement.{u})
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8T : ∀ κ : ℝ, 4 < κ → LP.LP8TransienceStatement.{u} κ)
    (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Sec7.Aux126.Lemma725DriverReferenceStatement.{0})
    (hLP4A : LP.LP4AvoidStatement.{u})
    {a : ℝ} (ha4 : 4 < a) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  LP.ae_exists_isGeneratingTrace_of_isCompleteForceWord
    (isCompleteForceWord_of_four_lt_of_remainingB h99 h102 h113 h8T h9 hR7 h725 hLP4A ha4 xL xR ρL ρR hF) hE

/-- **Theorem 1.3 (continuity and endpoint)**, with exactly the conclusion of the frozen
`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`, in the provider shape (all of the anchor's arguments implicit,
its hypotheses `ha`, `hF`, `hE` auto-parameters), from the **thirteen remaining** named inputs (conditional helper; it
is not the provider). Compared with `Wire.ae_exists_isGeneratingTrace_of_remaining`: the one-seed theorem, Proposition
LP6 and Aux. lemma 106 for `κ > 4` are discharged, and LP8, LP4 and Lemma 7.25's reference are narrowed to their
remaining parts.

Remaining, `0 < κ < 4`: `h71`, `h99lt`, `h102`, `h113lt`, `h1s`. `κ = 4`: `hWW`. `κ > 4`: `h99gt`, `h113gt`, `h8T`,
`h9`, `hR7`, `h725`, `hLP4A` (and `h102`). -/
theorem ae_exists_isGeneratingTrace_of_remainingB
    (h71 : Sec7.Lemma71.Lemma71MappedSegmentStatement.{0})
    (h99lt : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.Aux99StoppedStatement.{u} κ)
    (h102 : Sec7.Aux102BandStatement.{u}) (h113lt : Sec7.Aux113TransienceStatement.{u})
    (h1s : Sec7.OneSidedPrefixStatement.{u})
    (hWW : LP.WWTheorem18DistinctStatement.{u})
    (h99gt : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ)
    (h113gt : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8T : ∀ κ : ℝ, 4 < κ → LP.LP8TransienceStatement.{u} κ)
    (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0}) (h725 : Sec7.Aux126.Lemma725DriverReferenceStatement.{0})
    (hLP4A : LP.LP4AvoidStatement.{u})
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  rcases lt_trichotomy a 4 with h4 | rfl | h4
  · exact ae_exists_isGeneratingTrace_of_lt_four_of_remaining h71 h99lt h102 h113lt h1s ha h4 hF hE
  · exact Theorem13.ae_exists_isGeneratingTrace_four hWW hF hE
  · exact ae_exists_isGeneratingTrace_of_four_lt_of_remainingB h99gt h102 h113gt h8T h9 hR7 h725 hLP4A h4 hF hE

end Wire

end InteractingSLE
