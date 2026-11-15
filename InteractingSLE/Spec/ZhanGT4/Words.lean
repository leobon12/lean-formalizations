/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.WordsRef
import InteractingSLE.Spec.ZhanGT4.PrefixAux7
import InteractingSLE.Spec.Zhan.WordsEscape

/-!
# Transience for every separated word and Aux. lemma 7, `κ > 4` (Part B.5)

Packet PROVE-ZHAN-GT4-B3. Source: Astra, *Follow-up proofs*, §B.5 L1322–L1338 (ruling R38); additional note
Proposition 1.12 (ruling R39). "Thus all three statements in §B.1 follow from the two geometric outputs of Part A and
the already adopted analytic reductions."

For an ordered admissible word whose marks are all separated from the seed:

* with no marks, it is ordinary `SLE_κ` (`Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_empty`);
* otherwise PROVE-ZHAN-B4's whole-tail comparison (`Zhan.ae_tendsto_of_changeEnergy`) with B4's finite merge energy,
  which B4 proved for every `κ > 0` (`Zhan.mergeEnergyStatement_of_strict`, linear escape of the lower strip gaps,
  Lemma 1.11), and the `κ > 4` reference inputs of `WordsRef.lean` (one-force and two-force bases).

Then GT4-B's reduction gives Aux. lemma 7 (`aux7Statement_of_separatedTransience_of_pos`).

## Main results (named inputs: Part A's (G5) `StoppingInverseBoundaryStatement κ` and (G2) `SeparatedTwoForceStatement
κ`)

* `separatedTransienceStatement_of_gt_four`: **`Zhan.SeparatedTransienceStatement κ` for `κ > 4`**.
* `aux7Statement_of_gt_four`: **`Sec4.Aux7Statement κ` for `κ > 4`** (so Aux. 7 at `κ′ = 16/κ > 4` for `κ < 4`).
* `separatedTransienceStatement_of_pos`, `aux7Statement_of_pos`: every `κ > 0`, the inputs used only for `κ > 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan

/-- **Transience for every separated word, `κ > 4`** (B.5; additional note Proposition 1.12), given Part A's (G5) and
(G2): for an ordered word with admissible side partial sums and all marks strictly separated from the seed, almost
surely
every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem separatedTransienceStatement_of_gt_four {κ : ℝ} (hκ4 : 4 < κ)
    (hG5 : StoppingInverseBoundaryStatement.{0} κ) (hG2 : SeparatedTwoForceStatement.{0} κ) :
    Zhan.SeparatedTransienceStatement.{u} κ := by
  have hκ : 0 < κ := by linarith
  have hM : MergeEnergyStatement.{u} κ :=
    mergeEnergyStatement_of_strict hκ (strictLeftEnergyStatement_of_strip hκ (stripLeftEnergyStatement hκ))
  intro nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hF hadm hxL hxR hE
  rcases Nat.eq_zero_or_pos (nL + nR) with h0 | hn
  · obtain ⟨rfl, rfl⟩ : nL = 0 ∧ nR = 0 := ⟨by omega, by omega⟩
    exact Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_empty hκ hE
  · exact ae_tendsto_of_changeEnergy hκ (fun i j => (hxL i).trans (hxR j)) hE
      (Zhan.IsIntegratedSLEEvolution.ae_good_separated hκ hF hadm hxL hxR hE)
      (hM xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hxL hxR hE)
      (codeLaw_outerW_lifetime_of_pos hκ hF hadm hxL hxR)
      (codeLaw_outerW_lateSet_tendsto_zero_gt_four hκ4 hG5 hG2 hF hadm hxL hxR hn)

/-- **Aux. lemma 7 for `κ > 4`** (Specification §2.2, p. 33), given Part A's (G5) and (G2): infinite lifetime, a
continuous trace and transience for every admissible ordered word. -/
theorem aux7Statement_of_gt_four {κ : ℝ} (hκ4 : 4 < κ) (hG5 : StoppingInverseBoundaryStatement.{0} κ)
    (hG2 : SeparatedTwoForceStatement.{0} κ) : Sec4.Aux7Statement.{u} κ :=
  aux7Statement_of_separatedTransience_of_pos (by linarith) (separatedTransienceStatement_of_gt_four hκ4 hG5 hG2)

/-- **Transience for every separated word, every `κ > 0`**: PROVE-ZHAN-B4 for `κ ≤ 4`, and for `κ > 4` from Part A's
(G5) and (G2). -/
theorem separatedTransienceStatement_of_pos {κ : ℝ} (hκ : 0 < κ)
    (hA : 4 < κ → StoppingInverseBoundaryStatement.{0} κ ∧ SeparatedTwoForceStatement.{0} κ) :
    Zhan.SeparatedTransienceStatement.{u} κ := by
  rcases le_or_gt κ 4 with h4 | h4
  · exact Zhan.separatedTransienceStatement hκ h4
  · exact separatedTransienceStatement_of_gt_four h4 (hA h4).1 (hA h4).2

/-- **Aux. lemma 7, every `κ > 0`**: PROVE-ZHAN-B4 for `κ ≤ 4`, and for `κ > 4` from Part A's (G5) and (G2). -/
theorem aux7Statement_of_pos {κ : ℝ} (hκ : 0 < κ)
    (hA : 4 < κ → StoppingInverseBoundaryStatement.{0} κ ∧ SeparatedTwoForceStatement.{0} κ) :
    Sec4.Aux7Statement.{u} κ := by
  rcases le_or_gt κ 4 with h4 | h4
  · exact Zhan.aux7Statement hκ h4
  · exact aux7Statement_of_gt_four h4 (hA h4).1 (hA h4).2

end InteractingSLE.ZhanGT4
