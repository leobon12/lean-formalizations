/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyUnique

/-!
# Theorem 2.2 assembly: uniqueness in law outside the admissible entrance

Packet PROVE-SEC2-PATCH. The frozen uniqueness statement
`IsIntegratedSLEEvolution.measure_killedState_eq` holds for every force word that is separated
(`∀ i j, xL i < xR j`, `AssemblyUnique`) **or** whose seed `(0, xL, xR)` is a threshold state
(then every evolution has lifetime `0` almost surely, `ae_lifetime_eq_zero_of_threshold`):
`IsIntegratedSLEEvolution.measure_killedState_eq_of_separated_or_threshold`.

The only words not covered are the *admissible entrances*: a left mark and a right mark both at
`0` and both seed groups of weight `> −2` (for one mark per side this is PROVE-SEC2-JAC2's
`TwoSeed.measure_killedState_eq_twoSeed`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace IsIntegratedSLEEvolution

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- If the seed is a threshold state, every evolution has lifetime `0` almost surely. -/
theorem ae_lifetime_eq_zero_of_threshold {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR) : ∀ᵐ ω ∂P, ζ ω = 0 := by
  filter_upwards [h.2.2.2.2] with ω hpath
  have hp := hpath.isForcePath
  by_contra hne
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
  apply hp.not_threshold h0
  have e1 : (fun i => VL i 0 ω) = xL := funext hp.vL_zero
  have e2 : (fun j => VR j 0 ω) = xR := funext hp.vR_zero
  rw [show W 0 ω = 0 from hp.w_zero, e1, e2]
  exact hthr

/-- With a threshold seed, the killed-state probabilities are those of lifetime `0`. -/
theorem measure_killedState_of_threshold {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR) (n : ℕ) (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) :
    P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} =
      if n = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [↓reduceIte]
    have : {ω | ∀ j : Fin 0, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} =
        univ := by
      ext ω; simp
    rw [this, measure_univ]
  · simp only [hn.ne', ↓reduceIte]
    refine measure_mono_null (t := {ω | ζ ω ≠ 0}) ?_ ?_
    · intro ω hω hz
      have := (hω ⟨0, hn⟩).1
      rw [hz] at this
      exact (not_lt.2 (zero_le : (0 : ℝ≥0∞) ≤ _)) this
    · exact ae_iff.1 (h.ae_lifetime_eq_zero_of_threshold hthr)

/-- **Theorem 2.2, uniqueness in law, for every force word that is separated or has a
threshold seed** (all weights): the frozen statement `measure_killedState_eq` with
`IsOrderedForceWord` replaced by `(∀ i j, xL i < xR j) ∨ ThresholdCondition ρL ρR 0 xL xR`. -/
theorem measure_killedState_eq_of_separated_or_threshold (ha : 0 < a)
    (hcase : (∀ i j, xL i < xR j) ∨ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j} := by
  rcases hcase with hsep | hthr
  · exact measure_killedState_eq_of_separated ha hsep h₁ h₂ n ts A hA
  · rw [h₁.measure_killedState_of_threshold hthr n ts A,
      h₂.measure_killedState_of_threshold hthr n ts A]

end IsIntegratedSLEEvolution

end InteractingSLE
