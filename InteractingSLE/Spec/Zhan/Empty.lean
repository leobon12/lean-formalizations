/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProbBase

/-!
# Transience for the word with no marks

Packet PROVE-ZHAN-B4. The word with no force marks (`nL = nR = 0`) is ordinary chordal `SLE_κ`: every integrated
evolution of it has, almost surely, infinite lifetime and driver `√κ B` (`IsIntegratedSLEPath.lifetime_eq_top_of_zero`,
`IsIntegratedSLEPath.w_eq_of_zero`), so Rohde–Schramm transience for every `κ > 0` (`ae_exists_trace_all`,
`Foundations/SLE/All.lean`) applies to every continuous generating trace.

## Main results

* `Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_empty`: for `κ > 0`, every integrated evolution of the empty
  word has, almost surely, every continuous generating trace on `[0, ∞)` tending to `∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

/-- **Transience for the empty word** (ordinary `SLE_κ`, [RS05, Theorem 7.1] for every `κ > 0`). Every integrated
evolution of the word with no marks has, almost surely, every continuous generating trace on `[0, ∞)` tending to
infinity. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_empty {κ : ℝ} (hκ : 0 < κ) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {xL ρL : Fin 0 → ℝ}
    {xR ρR : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain rfl : ρL = 0 := Subsingleton.elim _ _
  obtain rfl : ρR = 0 := Subsingleton.elim _ _
  obtain ⟨hB, -, -, -, hpath⟩ := hE
  filter_upwards [hpath, hB.1.cont, ae_exists_trace_all hB.1 hκ] with ω hp hc htr η hη
  have hζ : ζ ω = ⊤ := hp.lifetime_eq_top_of_zero hc
  have hW : (fun t => W t ω) = fun t => Real.sqrt κ * B t ω := funext fun t =>
    hp.w_eq_of_zero (by rw [hζ]; exact ENNReal.coe_lt_top)
  rw [hW] at hη
  exact htr.2 η hη

end InteractingSLE.Zhan
