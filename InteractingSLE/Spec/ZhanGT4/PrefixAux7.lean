/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.Prefix
import InteractingSLE.Spec.Zhan.Aux7
import InteractingSLE.Spec.Sec7.ContinuityProb3Random

/-!
# Aux. lemma 7 for every `κ > 0`, from transience for separated words

Packet PROVE-ZHAN-GT4-B. Aux. lemma 7 (`Sec4.Aux7Statement`, Specification §2.2, PDF p. 34) asserts, for an ordered
force word with admissible side partial sums (marks at `0⁻`, `0⁺` allowed): infinite lifetime, a continuous trace,
and transience. PROVE-ZHAN-B2 reduced it for `κ ≤ 4` to transience for words separated from the seed
(`Zhan.SeparatedTransienceStatement κ`); it used `κ ≤ 4` only through the simple trace with marks at the seed
(Remark 2.3). Part B.1's shrinking-prefix lemma (`ZhanGT4.IsIntegratedSLEEvolution.
ae_exists_isGeneratingTrace_top_of_admissible`, `Prefix.lean`) gives that trace for every `κ > 0` ("finite-prefix
continuity even for nonsimple seed laws", L1093), so the same reduction holds for every `κ > 0`:

* the lifetime and separation at positive times are Aux. lemma 6;
* the trace on `[0, ∞)` is B.1;
* transience: at time `1` the word is separated and admissible (`Zhan.word_of_mem_restartEventTies`), so, given the
  separated core, it is complete; the restart with a random word (`Sec7.RandRestart.randomRestartTraceStatement`)
  gives a transient trace of the shifted driver, and the join (`Sec7.IsGeneratingTraceIcc.join`) transfers
  transience (ZHAN-B2's argument verbatim).

## Main results

* `IsIntegratedSLEEvolution.ae_transient_of_separatedTransience_of_pos`;
* `aux7Statement_of_separatedTransience_of_pos : 0 < κ → Zhan.SeparatedTransienceStatement κ → Sec4.Aux7Statement κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan

variable {κ : ℝ} {nL nR : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Transience with marks at the seed, from the separated case, every `κ > 0`.** For an ordered word with
admissible side partial sums, almost surely `ζ = ∞`, there is a continuous generating trace on `[0, ∞)`, and every
such trace tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_transient_of_separatedTransience_of_pos (hκ : 0 < κ)
    (hS : SeparatedTransienceStatement.{u} κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hR : Sec7.RandomRestartTraceStatement.{u} κ := Sec7.RandRestart.randomRestartTraceStatement hκ
  have hT := isStoppingTime_const 𝓕 (1 : ℝ≥0)
  have hAm : MeasurableSet[hT.measurableSpace] (restartEventTies 1 xL xR W VL VR ζ) := by
    rw [IsStoppingTime.measurableSpace_const]
    exact measurableSet_restartEventTies 1 hE
  have hrest := hR xL xR ρL ρR P 𝓕 W VL VR B ζ hE (fun _ => 1) hT (restartEventTies 1 xL xR W VL VR ζ) hAm
    (fun ω hω => hω.1) fun ω hω => by
      obtain ⟨hFy, hadm', hxL', hxR'⟩ := word_of_mem_restartEventTies hF hadm hω
      intro Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE'
      exact isCompleteForceWord_of_separatedTransience hκ hS hFy hadm' hxL' hxR' P' 𝓕' W' VL' VR' B' ζ' hE'
  filter_upwards [IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hκ hF hadm hE, hrest,
    hE.2.2.2.2, Zhan.IsIntegratedSLEEvolution.ae_mem_restartEventTies hκ hF hadm hE] with ω
    ⟨hζ, _, η, hη⟩ hrω hp ⟨_, hmemσ⟩
  refine ⟨hζ, ⟨η, hη⟩, fun η' hη' => ?_⟩
  have hmem := hmemσ 1 one_pos
  obtain ⟨η₂, hη₂, htr₂⟩ := hrω hmem
  have hζ1 : ζ ω - ((1 : ℝ≥0) : ℝ≥0∞) = ⊤ := by rw [hζ]; exact ENNReal.top_sub_coe
  rw [hζ1] at hη₂
  have hwc : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ⊤} := by
    have := hp.2.2.2.1; rwa [hζ] at this
  have hw0 : (fun t => W t ω) 0 = 0 := hp.1
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη' hwc hw0 (σ := 1) ENNReal.coe_lt_top
  have hwc' : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞) + ⊤} := by
    rwa [add_top]
  obtain ⟨hjoin, htj⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hjoin
  have heq : ∀ t : ℝ≥0, η' t = Sec7.joinTrace (fun t => W t ω) 1 η' η₂ t := fun t =>
    hη'.eq_of_le hjoin hwc hw0 le_top
  refine (htj rfl (htr₂ hζ1)).congr fun t => ?_
  rw [heq t]

/-- **Aux. lemma 7 for every `κ > 0`**, from the core statement for separated words (the restart with a random force
word is proved: `Sec7.RandRestart.randomRestartTraceStatement`). -/
theorem aux7Statement_of_separatedTransience_of_pos (hκ : 0 < κ)
    (hS : SeparatedTransienceStatement.{u} κ) : Sec4.Aux7Statement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ P 𝓕 W VL VR B ζ hF hadm hE
  exact IsIntegratedSLEEvolution.ae_transient_of_separatedTransience_of_pos hκ hS hF hadm hE

end InteractingSLE.ZhanGT4
