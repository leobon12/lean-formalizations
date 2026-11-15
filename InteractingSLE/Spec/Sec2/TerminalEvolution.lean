/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalEscape
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution

/-!
# The lifetime of an integrated `SLE_κ(ρ)` evolution (almost-sure form)

Packet PROVE-SEC2-TERM. Aux. lemma 3 of the Specification (pp. 24–28) for the frozen evolution
`IsIntegratedSLEEvolution` (Definition 2.1):

* `IsIntegratedSLEEvolution.isStoppingTime`: the lifetime `ζ` is a stopping time;
* `IsIntegratedSLEEvolution.ae_tendsto_or_criticalEscape`: almost surely, at a finite positive
  lifetime either the state has a finite limit satisfying the continuation-threshold condition, or
  one side escapes to infinity with side total exactly `−2` while the other side stays bounded
  (in that case `Q = W − V^out` stays bounded and `∫ dt/Q` diverges,
  `Sec2.IsForcePath.exists_bound_gap_out`, `Sec2.IsForcePath.integral_inv_gap_out_unbounded`).

The Brownian motion `B` of the frozen definition is defined for all times, so "the Brownian motion
can be continued independently after a putative finite maximal lifetime" (p. 25) is automatic: its
paths are almost surely continuous on every `[0, T]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace IsIntegratedSLEEvolution

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

section

variable (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
include h

theorem isFilteredBrownianReal : IsFilteredBrownianReal 𝓕 B P := h.1

theorem adaptedBefore_W : AdaptedBefore 𝓕 ζ W := h.2.1

theorem adaptedBefore_VL (i : Fin nL) : AdaptedBefore 𝓕 ζ (VL i) := h.2.2.1 i

theorem adaptedBefore_VR (i : Fin nR) : AdaptedBefore 𝓕 ζ (VR i) := h.2.2.2.1 i

theorem ae_isIntegratedSLEPath : ∀ᵐ ω ∂P, IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) := h.2.2.2.2

theorem ae_continuous_B : ∀ᵐ ω ∂P, Continuous fun t => B t ω := h.1.1.cont

/-- `{t < ζ} ∈ 𝓕_t`. -/
theorem measurableSet_lt_lifetime (t : ℝ≥0) : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
  have := h.adaptedBefore_W t univ MeasurableSet.univ
  simpa using this

/-- **The lifetime is a stopping time** (Aux. lemma 3, "It is a … stopping time"). -/
theorem isStoppingTime : IsStoppingTime 𝓕 ζ := by
  intro t
  have := (h.measurableSet_lt_lifetime t).compl
  convert this using 1
  ext ω
  simp [not_lt]
  rfl

/-- **Aux. lemma 3, almost-sure form** (Specification pp. 24–28). Almost surely, for a finite
positive lifetime `ζ = T`: either the state `(W, V^L, V^R)` converges as `t ↑ T` and the limit
satisfies the continuation-threshold condition, or the left side escapes to `−∞` with total weight
exactly `−2` while the right side stays bounded, or the mirror image on the right. -/
theorem ae_tendsto_or_criticalEscape :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      (∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T)
          (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) ∨
      ((∑ i, ρL i = -2) ∧ (∃ i, ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ VL i s ω < m) ∧
        ∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → VR j s ω ≤ M) ∨
      ((∑ j, ρR j = -2) ∧ (∃ j, ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ m < VR j s ω) ∧
        ∀ i, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → M ≤ VL i s ω) := by
  filter_upwards [h.ae_isIntegratedSLEPath, h.ae_continuous_B] with ω hpath hB T hT hζ
  exact hpath.tendsto_or_criticalEscape hT hζ hB.continuousOn

/-- **Aux. lemma 3 without critical side totals**: if neither side total equals `−2`, then almost
surely at every finite positive lifetime the state converges and its limit satisfies the
continuation-threshold condition (the lifetime is the continuation threshold). -/
theorem ae_tendsto_threshold_of_ne (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T)
          (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  filter_upwards [h.ae_tendsto_or_criticalEscape] with ω hω T hT hζ
  rcases hω T hT hζ with h1 | h2 | h3
  · exact h1
  · exact absurd h2.1 hL
  · exact absurd h3.1 hR

end

end IsIntegratedSLEEvolution

end InteractingSLE
