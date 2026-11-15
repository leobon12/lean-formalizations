/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofInputsSafe
import InteractingSLE.Spec.Restart.RetPlumbProofInputsModel

/-!
# Exact remaining observation and driver-reconstruction inputs

Packet PROVE-RETPLUMB. The named observation hypothesis below only asks for
past chart coordinates and physical survival. Its consequences include clock
and safe-event measurability, without a future regularity test or a separate
random-hull hypothesis. The adapted driver reconstruction is a distinct named
mathematical input, not an assertion about the arbitrary choice in `retDriver`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open QuantumZipper (H)
open Supp7 DomainMarkov.Aux79

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The remaining physical observation input. In the retained application,
`𝓖` is `retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r`. This is a named hypothesis,
not a theorem derived from the original flow-line assumptions. -/
structure RetPrefixObservations (𝓖 : Filtration ℝ≥0 mΩ) (F : Set Ω)
    (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞)
    (u r : ℝ≥0) : Prop where
  initial : MeasurableSet[𝓖 0] F
  coordinates : ∀ t s : ℝ≥0, s ≤ t → Measurable[𝓖 t]
    (F.indicator fun ω => retChartPath G η₁' η₂' ζ₂ u r ω s)
  survival : ∀ t : ℝ≥0, MeasurableSet[𝓖 t]
    (F ∩ {ω | (t : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω})

/-- A measurable adapted selection is additional mathematics beyond the
pointwise existence of a retained driver. No canonical flow code occurs here.
`𝓗` denotes the capacity-time filtration, not the physical-time filtration. -/
def RetAdaptedDriverExists (𝓗 : Filtration ℝ≥0 mΩ) (F : Set Ω)
    (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    (u r : ℝ≥0) (κ θ : ℝ) (c₀ : BoundaryWord) (g₃ g₄ : ℝ) : Prop :=
  ∃ W : ℝ≥0 → Ω → ℝ, (∀ ω, W 0 ω = 0) ∧
    (∀ ω, Continuous fun t => W t ω) ∧ StronglyAdapted 𝓗 W ∧
      ∀ ω ∈ F, IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω (fun t => W t ω)

variable {𝓖 : Filtration ℝ≥0 mΩ} {F : Set Ω} {G : ℝ≥0 → Set Ω}
  {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0} {x₂ : ℝ}

/-- The future regularity branch is unnecessary for an initial-event-supported
clock once the named prefix observations are available. -/
theorem RetPrefixObservations.measurable_clock
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : F ⊆ G r)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) (t : ℝ≥0) :
    Measurable[𝓖 t] (F.indicator (retClock G η₁' η₂' ζ₂ u r t)) :=
  measurable_indicator_retClock_of_prefix hd (𝓖.mono zero_le _ ho.initial)
    hG hp₂ hpair (ho.coordinates t)

/-- The physical-survival input gives the required supported capacity-survival
event, without measurability of the full future lifetime at the current line. -/
theorem RetPrefixObservations.measurableSet_live
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : F ⊆ G r)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) (t : ℝ≥0) :
    MeasurableSet[𝓖 t]
      (F ∩ {ω | (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) <
        retLife G η₁' η₂' ζ₂ u r ω}) := by
  convert ho.survival t using 1
  ext ω
  constructor
  · rintro ⟨hω, ht⟩
    exact ⟨hω, (retClock_lt_retLife_iff hd (hG hω) (hp₂ ω hω) (hpair ω hω)).1 ht⟩
  · rintro ⟨hω, ht⟩
    exact ⟨hω, (retClock_lt_retLife_iff hd (hG hω) (hp₂ ω hω) (hpair ω hω)).2 ht⟩

/-- All supported safe events follow from prefix observations and the landed
generating-trace property. No driver measurability is used in this implication. -/
theorem RetPrefixObservations.measurableSet_safe
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : F ⊆ G r)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    {W : ℝ≥0 → Ω → ℝ}
    (hgen : ∀ ω ∈ F, IsGeneratingTrace (fun s => W s ω)
      (retLife G η₁' η₂' ζ₂ u r ω) (retPath G η₁' η₂' ζ₂ u r ω))
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (t : ℝ≥0) :
    MeasurableSet[𝓖 t]
      (F ∩ lineSafe (retClock G η₁' η₂' ζ₂ u r) W (retLife G η₁' η₂' ζ₂ u r) C t) :=
  @measurableSet_inter_lineSafe_of_prefix Ω (𝓖 t) F
    (fun ω => retChartPath G η₁' η₂' ζ₂ u r ω)
    (retClock G η₁' η₂' ζ₂ u r) W (retLife G η₁' η₂' ζ₂ u r) t
    (fun ω hω => (retChartPath_continuous_zero hd (hG hω) (hp₂ ω hω) (hpair ω hω)).1)
    (ho.coordinates t) (ho.measurableSet_live hd hG hp₂ hpair t)
    (fun ω hω ht => fwdHull_retClock_eq_fillH hd (hG hω) (hp₂ ω hω) (hpair ω hω)
      (hgen ω hω) ((retClock_lt_retLife_iff hd (hG hω) (hp₂ ω hω) (hpair ω hω)).1 ht))
    C hC hCH

/-- Setting both clock and lifetime to zero off the initial event turns the
supported safe event into an ordinary safe event. This supplies an exact
measurable version for a conditional construction on that event. -/
theorem RetPrefixObservations.measurableSet_safe_indicator
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : F ⊆ G r)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    {W : ℝ≥0 → Ω → ℝ}
    (hgen : ∀ ω ∈ F, IsGeneratingTrace (fun s => W s ω)
      (retLife G η₁' η₂' ζ₂ u r ω) (retPath G η₁' η₂' ζ₂ u r ω))
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (t : ℝ≥0) :
    MeasurableSet[𝓖 t]
      (lineSafe (fun s => F.indicator (retClock G η₁' η₂' ζ₂ u r s)) W
        (F.indicator (retLife G η₁' η₂' ζ₂ u r)) C t) := by
  classical
  convert ho.measurableSet_safe hd hG hp₂ hpair hgen hC hCH t using 1
  ext ω
  by_cases hω : ω ∈ F <;> simp [lineSafe, hω]

end InteractingSLE.Restart.RetAux79
