/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverRead
import InteractingSLE.Spec.Restart.RetPlumbProofResidualTransfer

/-!
# Killed retained-driver observability

Packet PROVE-RETPLUMB. This discharges `RetKilledDriverObservable` from the
landed retained geometry and physical-prefix observations. The arbitrary driver
extension is used only strictly before the supported lifetime.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7 DomainMarkov.Aux79
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {𝓖 : Filtration ℝ≥0 mΩ} {F : Set Ω} {G : ℝ≥0 → Set Ω}
  {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
  {κ θ : ℝ} {c₀ : BoundaryWord} {g₃ g₄ x₁ x₂ : ℝ}

/-- The killed driver is observable in the supported clock's capacity
filtration. Every input is an existing physical observation or pathwise fact. -/
theorem RetPrefixObservations.retKilledDriverObservable
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood) (hG : F ⊆ G r)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂) (hx : x₂ < x₁)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hκ : 0 < κ) :
    RetKilledDriverObservable
      (timeChange 𝓖 (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t))
        (ho.measurable_clock (hd r) hG hp₂ hpair))
      F G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ := by
  classical
  let W := retDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄
  have hW : ∀ ω ∈ F, IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω (fun s => W s ω) :=
    fun ω hω => isRetDriver_retDriver
      (exists_isRetDriver hd (hG hω) (hp₁ ω hω) (hp₂ ω hω) hx (hpair ω hω) hc₀ hκ θ g₃ g₄)
  have hmem (ω : Ω) (q : ℝ≥0)
      (hq : (q : ℝ≥0∞) < F.indicator (retLife G η₁' η₂' ζ₂ u r) ω) : ω ∈ F := by
    by_contra hω
    simp only [indicator_of_notMem hω, not_lt_zero] at hq
  apply adaptedBefore_timeChange_of_reaches (ho.measurable_clock (hd r) hG hp₂ hpair)
  · intro ω s t hst
    by_cases hω : ω ∈ F
    · simpa only [indicator_of_mem hω] using monotone_retClock G η₁' η₂' ζ₂ u r ω hst
    · simp only [indicator_of_notMem hω, le_refl]
  · intro ω q hq
    have hω := hmem ω q hq
    rw [indicator_of_mem hω] at hq
    obtain ⟨t, ht⟩ := exists_retClock_ge (hd r) (hG hω) (hp₂ ω hω) (hpair ω hω) hq
    exact ⟨t, by simpa only [indicator_of_mem hω] using ht⟩
  · intro q t A hA
    let E := {ω | (q : ℝ≥0∞) < F.indicator (retLife G η₁' η₂' ζ₂ u r) ω ∧
      q ≤ F.indicator (retClock G η₁' η₂' ζ₂ u r t) ω}
    have hEF : E ⊆ F := fun ω hω => hmem ω q hω.1
    have hEV : ∀ ω ∈ E, (q : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω := by
      intro ω hω
      simpa only [indicator_of_mem (hEF hω)] using hω.1
    have hEQ : ∀ ω ∈ E, q ≤ retClock G η₁' η₂' ζ₂ u r t ω := by
      intro ω hω
      simpa only [indicator_of_mem (hEF hω)] using hω.2
    have hread := @measurableSet_driver_of_observed_prefix Ω (𝓖 t) E
      (ho.measurableSet_capacityCut (hd r) hG hp₂ hpair q t)
      (retPath G η₁' η₂' ζ₂ u r)
      (fun ω s => retCapacityPrefix F G η₁' η₂' ζ₂ u r t s ω)
      W (retLife G η₁' η₂' ζ₂ u r) q
      (fun s => ho.measurable_retCapacityPrefix (hd r) hG hp₂ hpair t s)
      (fun ω hω s hs => retCapacityPrefix_eq (hd r) (hEF hω) (hG (hEF hω))
        (hp₂ ω (hEF hω)) (hpair ω (hEF hω))
        ((ENNReal.coe_le_coe.2 hs).trans_lt (hEV ω hω)) (hs.trans (hEQ ω hω)))
      (fun ω hω => (hW ω (hEF hω)).1)
      (fun ω hω => (hW ω (hEF hω)).2.1)
      (fun ω hω => (hW ω (hEF hω)).2.2.1) hEV A hA
    convert hread using 1
    ext ω
    change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ _)
    exact and_right_comm

/-- The requested globally continuous adapted retained driver now follows
without an independent killed-observability premise. -/
theorem RetPrefixObservations.retAdaptedDriverExists
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood) (hG : F ⊆ G r)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂) (hx : x₂ < x₁)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hκ : 0 < κ) :
    RetAdaptedDriverExists
      (timeChange 𝓖 (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t))
        (ho.measurable_clock (hd r) hG hp₂ hpair))
      F G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ :=
  retAdaptedDriverExists_of_killedObservations hd hG hp₁ hp₂ hx hpair hc₀ hκ
    (ho.retKilledDriverObservable hd hG hp₁ hp₂ hx hpair hc₀ hκ)

end InteractingSLE.Restart.RetAux79
