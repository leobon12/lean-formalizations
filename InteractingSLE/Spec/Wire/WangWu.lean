/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.TraceTransience
import InteractingSLE.Spec.Sec7.ContinuityProb3Random
import InteractingSLE.Spec.Zhan.WordsEscape

/-!
# Wang–Wu Corollary 4.13 and Theorem 1.3 at `κ = 4` for nonnegative weights, unconditional

Packet PROVE-WIRE1 (no new mathematics). PROVE-WW-TRACE proved Wang–Wu's Corollary 4.13
(`WangWu.IsMarkedChain.ae_simple_transient_trace`, `WangWu/TraceTransience.lean`) from two named inputs, both of which
are now theorems:

* the restart with a random force word, `Sec7.RandomRestartTraceStatement 4`:
  `Sec7.RandRestart.randomRestartTraceStatement` (`Spec/Sec7/ContinuityProb3Random.lean`);
* Wang–Wu's external input 8.3 (Zhan's nonboundary transience at `κ = 4`), `WangWu.ZhanNonboundaryTransience`:
  `Zhan.zhanNonboundaryTransience` (`Spec/Zhan/WordsEscape.lean`).

Hence, unconditionally: Corollary 4.13 (`ae_simple_transient_trace`), the conclusion of the frozen Theorem 1.3 at
`κ = 4` for every ordered word with nonnegative cumulative weights (`ae_theorem13_of_nonneg`; marks at `0±` allowed),
and completeness of the separated such words (`isCompleteForceWord_four_of_separated`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

open WangWu
open QuantumZipper (H fwdHull)

variable {nL nR : ℕ}

/-- **Separated words with nonnegative cumulative weights are complete at `κ = 4`** (Lemma 4.12 and External input
8.3, now proved): `WangWu.isCompleteForceWord_of_separated` with `Zhan.zhanNonboundaryTransience`. -/
theorem isCompleteForceWord_four_of_separated {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j)
    (hcum : HasNonnegCumWeights ρL ρR) :
    LP.IsCompleteForceWord.{u} 4 xL xR ρL ρR :=
  WangWu.isCompleteForceWord_of_separated Zhan.zhanNonboundaryTransience hF hxL hxR hcum

section Chain

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Wang–Wu Corollary 4.13** (proper non-boundary-intersecting traces; `source/external/WW17LP`, §4.4),
unconditional: under the hypotheses of Lemma 4.12 (an ordered word with nonnegative cumulative weights at `κ = 4`),
almost surely the lifetime is infinite, the force points stay strictly away from the driver at positive times, and the
trace is simple, in `ℍ` at positive times, generates the hulls, and tends to `∞`. -/
theorem ae_simple_transient_trace (hF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ Function.Injective η ∧
        (∀ t, 0 < t → η t ∈ H) ∧
        (∀ t : ℝ≥0, fwdHull (fun s : ℝ => W s.toNNReal ω) t = η '' Ioc 0 t) ∧
        Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsMarkedChain.ae_simple_transient_trace (Sec7.RandRestart.randomRestartTraceStatement (by norm_num))
    Zhan.zhanNonboundaryTransience hF hcum hE

/-- **The conclusion of the frozen Theorem 1.3 at `κ = 4` for every ordered word with nonnegative cumulative
weights** (marks at `0±` allowed), unconditional: almost surely the threshold clause holds, the driver has a
generating trace on `[0, ζ]`, and it tends to `∞` when `ζ = ∞`. -/
theorem ae_theorem13_of_nonneg (hF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  IsMarkedChain.ae_theorem13_of_nonneg (Sec7.RandRestart.randomRestartTraceStatement (by norm_num))
    Zhan.zhanNonboundaryTransience hF hcum hE

end Chain

/-- **Ordered words with nonnegative cumulative weights are complete at `κ = 4`** (marks at `0±` allowed;
unconditional), from `ae_theorem13_of_nonneg`. -/
theorem isCompleteForceWord_four_of_nonneg {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (hcum : HasNonnegCumWeights ρL ρR) :
    LP.IsCompleteForceWord.{u} 4 xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact (ae_theorem13_of_nonneg hF hcum hE).mono fun _ h => h.2

end Wire

end InteractingSLE
