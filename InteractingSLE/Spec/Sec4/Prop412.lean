/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.SpecialHeights
import InteractingSLE.Spec.Zhan.Aux7
import InteractingSLE.Spec.Sec7.ContinuityProb3Random

/-!
# Proposition 4.12: transience under (4.4)

Packet PROVE-SEC4-B5 (specification §4.2, Proposition 4.12 and its proof, `source/spec/p097-144.md#prop-4.12`,
p. 122): "Suppose that `η ∼ SLE_κ(ρ)`, `κ ∈ (0, 4)`, from `0` to `∞` in `ℍ` with the weights `ρ` satisfying (4.4).
Then `lim_{t→∞} η(t) = ∞` almost surely." Proof: (4.4) gives the admissible partial sums of Aux. lemma 7
(`hasAdmissiblePartialSums_of_cond44`), and Aux. lemma 7 gives the limit.

Aux. lemma 7 for `0 < κ ≤ 4` is proved (`Zhan.aux7Statement_of_separatedTransience`) from the restart with a random
force word (`Sec7.RandRestart.randomRestartTraceStatement`, proved) and the transience of words separated from the seed,
`Zhan.SeparatedTransienceStatement κ`, a named statement that packet PROVE-ZHAN-B4 is discharging. Here:

* `prop412_of_separatedTransience`: Proposition 4.12 from `Zhan.SeparatedTransienceStatement κ` (conditional helper;
  everything else is proved);
* `ae_simple_trace_of_cond44`: the unconditional part under (4.4) — infinite lifetime, noncollision at positive
  times, and a simple generating trace on `[0, ∞)` in `ℍ` at positive times (Remark 2.3 for `κ ≤ 4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec4

open QuantumZipper (H)

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Under (4.4), the trace is simple and non-boundary-intersecting** (unconditional part of Proposition 4.12's
setting; Remark 2.3 for `κ ≤ 4` and Aux. lemma 6). For `0 < κ < 4` and an ordered word satisfying (4.4), almost
surely the lifetime is infinite, every force point stays strictly away from the driver at positive times, and there is
an injective generating trace on `[0, ∞)` lying in `ℍ` at positive times, with `K_t = η((0, t])`. -/
theorem ae_simple_trace_of_cond44 (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Cond44 κ ρL ρR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ Function.Injective η ∧
        (∀ t, 0 < t → η t ∈ H) ∧
        ∀ t : ℝ≥0, QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) t = η '' Ioc 0 t :=
  Zhan.IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4.le hF (hasAdmissiblePartialSums_of_cond44 hκ4 hF h44) hE

/-- **Proposition 4.12 from the separated-transience statement** (conditional helper; the named input
`Zhan.SeparatedTransienceStatement κ` is Aux. lemma 7's core, packet PROVE-ZHAN-B4). For `0 < κ < 4` and an ordered
force word whose weights satisfy (4.4), almost surely the lifetime is infinite, the driver has a continuous generating
trace on `[0, ∞)`, and every such trace tends to `∞`. -/
theorem prop412_of_separatedTransience (hκ : 0 < κ) (hκ4 : κ < 4)
    (hS : Zhan.SeparatedTransienceStatement.{u} κ) (hF : IsOrderedForceWord xL xR) (h44 : Cond44 κ ρL ρR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop := by
  have h7 : Aux7Statement.{u} κ :=
    Zhan.aux7Statement_of_separatedTransience hκ hκ4.le hS (Sec7.RandRestart.randomRestartTraceStatement hκ)
  exact prop412_of_aux7 hκ4 hF h44 hE fun hE' hadm => h7 xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE'

end Sec4

end InteractingSLE
