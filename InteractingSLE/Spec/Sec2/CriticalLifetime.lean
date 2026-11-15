/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.CriticalEscape

/-!
# Aux. lemma 3: the lifetime of an integrated `SLE_κ(ρ)` evolution is the continuation threshold

Packet PROVE-SEC2-TERM2. For the frozen evolution `IsIntegratedSLEEvolution` with `κ > 0`
(Specification pp. 24–28):

* `IsIntegratedSLEEvolution.ae_bddBelow_VL_of_sum_eq`, `ae_bddAbove_VR_of_sum_eq`: no critical
  escape on either side (the right side by the reflection `x ↦ −x`, under which the evolution is
  driven by `−B`, i.e. `σ = −1` in `Sec2.ae_bddBelow_of_sum_eq`);
* **`IsIntegratedSLEEvolution.ae_tendsto_threshold`** (Aux. lemma 3): almost surely, at every
  finite positive lifetime `ζ = T`, all driving and force coordinates have finite limits as
  `t ↑ T`, and the limiting state satisfies the continuation-threshold condition, i.e. some whole
  group colliding with the driver has weight `≤ −2`. Hence no force coordinate escapes to infinity
  at a finite lifetime, and the maximal lifetime is the continuation threshold.

The predictability of the lifetime (also asserted by Aux. lemma 3) is not proved here; the proof
of the critical case does not use it (see `CriticalPath.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace IsIntegratedSLEEvolution

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

variable (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
include h

/-- **No critical escape on the left** (Aux. lemma 3, `s = −2`): if `∑ ρ^{i,L} = −2`, then
almost surely at a finite positive lifetime with the right side bounded, the left side is
bounded. -/
theorem ae_bddBelow_VL_of_sum_eq (ha : 0 < a) (hS : ∑ i, ρL i = -2) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      (∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → VR j s ω ≤ M) →
      ∀ i, ∃ m : ℝ, ∀ s : ℝ≥0, s < T → m ≤ VL i s ω := by
  refine Sec2.ae_bddBelow_of_sum_eq (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (W := W) (σ := 1) ha
    (LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal h.isFilteredBrownianReal)
    h.ae_continuous_B h.adaptedBefore_VL h.adaptedBefore_VR h.measurableSet_lt_lifetime
    (by norm_num) ?_ hS
  filter_upwards [h.ae_isIntegratedSLEPath] with ω hω
  simpa only [one_mul] using hω

/-- **No critical escape on the right** (Aux. lemma 3, "reflection handles right escape"). -/
theorem ae_bddAbove_VR_of_sum_eq (ha : 0 < a) (hS : ∑ j, ρR j = -2) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      (∀ i, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → M ≤ VL i s ω) →
      ∀ j, ∃ m : ℝ, ∀ s : ℝ≥0, s < T → VR j s ω ≤ m := by
  have hrefl := Sec2.ae_bddBelow_of_sum_eq (xL := -xR) (xR := -xL) (ρL := ρR) (ρR := ρL)
    (W := fun t ω => -W t ω) (VL := fun j t ω => -VR j t ω) (VR := fun i t ω => -VL i t ω)
    (σ := -1) ha
    (LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal h.isFilteredBrownianReal)
    h.ae_continuous_B (fun j => Sec2.adaptedBefore_neg (h.adaptedBefore_VR j))
    (fun i => Sec2.adaptedBefore_neg (h.adaptedBefore_VL i))
    h.measurableSet_lt_lifetime (by norm_num) ?_ hS
  · filter_upwards [hrefl] with ω hω T hT hζ hL j
    obtain ⟨m, hm⟩ := hω T hT hζ (fun i => by
      obtain ⟨M, hM⟩ := hL i
      exact ⟨-M, fun s hs => neg_le_neg (hM s hs)⟩) j
    exact ⟨-m, fun s hs => by linarith [hm s hs]⟩
  · filter_upwards [h.ae_isIntegratedSLEPath] with ω hω
    have e : (fun t => (-1 : ℝ) * B t ω) = -(fun t => B t ω) := by
      funext t; simp
    rw [e]
    exact hω.reflect

/-- **Aux. lemma 3** (Specification pp. 24–28, "Finite terminal coordinates of the driving
construction"): for `κ > 0`, almost surely, at every finite positive lifetime `ζ = T` the state
`(W, V^L, V^R)` has a finite limit as `t ↑ T`, and the limiting state satisfies the
continuation-threshold condition (some whole group colliding with the driver has weight `≤ −2`).
In particular no force coordinate escapes to infinity at a finite lifetime, and the maximal
lifetime is precisely the continuation threshold. -/
theorem ae_tendsto_threshold (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T)
          (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  have hL : ∀ᵐ ω ∂P, ∑ i, ρL i = -2 → ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      (∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → VR j s ω ≤ M) →
      ∀ i, ∃ m : ℝ, ∀ s : ℝ≥0, s < T → m ≤ VL i s ω := by
    by_cases hS : ∑ i, ρL i = -2
    · filter_upwards [h.ae_bddBelow_VL_of_sum_eq ha hS] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h' => absurd h' hS
  have hR : ∀ᵐ ω ∂P, ∑ j, ρR j = -2 → ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      (∀ i, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → M ≤ VL i s ω) →
      ∀ j, ∃ m : ℝ, ∀ s : ℝ≥0, s < T → VR j s ω ≤ m := by
    by_cases hS : ∑ j, ρR j = -2
    · filter_upwards [h.ae_bddAbove_VR_of_sum_eq ha hS] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h' => absurd h' hS
  filter_upwards [h.ae_tendsto_or_criticalEscape, hL, hR] with ω hω hLω hRω T hT hζ
  rcases hω T hT hζ with h1 | ⟨hS, ⟨i, hi⟩, hRb⟩ | ⟨hS, ⟨j, hj⟩, hLb⟩
  · exact h1
  · exfalso
    obtain ⟨m, hm⟩ := hLω hS T hT hζ hRb i
    obtain ⟨s, hs, hlt⟩ := hi m
    exact absurd (hm s hs) (not_le.2 hlt)
  · exfalso
    obtain ⟨m, hm⟩ := hRω hS T hT hζ hLb j
    obtain ⟨s, hs, hlt⟩ := hj m
    exact absurd (hm s hs) (not_le.2 hlt)

end IsIntegratedSLEEvolution

end InteractingSLE
