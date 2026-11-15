/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverLife

/-!
# Observable retained capacity prefixes

Packet PROVE-RETPLUMB. The reader below uses the chart path clipped at the
current physical line, the clipped clock and the currently truncated lifetime.
No coordinate of the unobserved future enters the reader.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The capacity prefix computed entirely from observations through `t`. -/
def retCapacityPrefix (F : Set Ω) (G : ℝ≥0 → Set Ω)
    (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r t q : ℝ≥0) (ω : Ω) : ℂ :=
  let Γ : Ω → ℝ≥0 → ℂ := fun ω s =>
    F.indicator (fun ω => retChartPath G η₁' η₂' ζ₂ u r ω (min s t)) ω
  Γ ω (invClock
    (fun s => ((F.indicator (retClock G η₁' η₂' ζ₂ u r (min s t)) ω : ℝ≥0) : ℝ))
    (F.indicator (fun ω => min (retLifeP η₁' η₂' ζ₂ u r ω) (t : ℝ≥0∞)) ω) q)

variable {𝓖 : Filtration ℝ≥0 mΩ} {F : Set Ω} {G : ℝ≥0 → Set Ω}
  {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0} {x₂ : ℝ}

/-- Every coordinate of the prefix reader is measurable at its physical line. -/
theorem RetPrefixObservations.measurable_retCapacityPrefix
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : F ⊆ G r)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) (t q : ℝ≥0) :
    Measurable[𝓖 t] (retCapacityPrefix F G η₁' η₂' ζ₂ u r t q) := by
  classical
  let Γ : Ω → ℝ≥0 → ℂ := fun ω s =>
    F.indicator (fun ω => retChartPath G η₁' η₂' ζ₂ u r ω (min s t)) ω
  have hc : ∀ ω, Continuous (Γ ω) := by
    intro ω
    by_cases hω : ω ∈ F
    · have he : Γ ω = fun s => retChartPath G η₁' η₂' ζ₂ u r ω (min s t) :=
        funext fun _ => indicator_of_mem hω _
      rw [he]
      exact (retChartPath_continuous_zero hd (hG hω) (hp₂ ω hω) (hpair ω hω)).1.comp
        (continuous_id.min continuous_const)
    · have he : Γ ω = fun _ => 0 := funext fun _ => indicator_of_notMem hω _
      rw [he]
      exact continuous_const
  have hC : ∀ s, Measurable[𝓖 t] fun ω =>
      ((F.indicator (retClock G η₁' η₂' ζ₂ u r (min s t)) ω : ℝ≥0) : ℝ) := fun s =>
    (measurable_coe_nnreal_real.comp (ho.measurable_clock hd hG hp₂ hpair (min s t))).mono
      (𝓖.mono (min_le_right _ _)) le_rfl
  have hL := measurable_indicator_min_of_survival ho.initial ho.survival t
  have hi := @measurable_invClock_of_coordinates Ω (𝓖 t) _ _ hC hL q
  exact @measurable_eval_of_continuous_coordinates Ω (𝓖 t) Γ hc
    (fun s => ho.coordinates t (min s t) (min_le_right _ _)) _ hi

/-- On the live reached-capacity event, the prefix reader is the actual
canonical retained trace. Equality includes the currently observed endpoint. -/
theorem retCapacityPrefix_eq {ω : Ω}
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hω : ω ∈ F) (hG : ω ∈ G r)
    (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    {q t : ℝ≥0} (hq : (q : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω)
    (hqt : q ≤ retClock G η₁' η₂' ζ₂ u r t ω) :
    retCapacityPrefix F G η₁' η₂' ζ₂ u r t q ω = retPath G η₁' η₂' ζ₂ u r ω q := by
  classical
  let C := chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)
  let L := retLifeP η₁' η₂' ζ₂ u r ω
  obtain ⟨hC, hm, -⟩ := retChartPath_clock hd hG hp₂ hpair
  have hnonneg (s : ℝ≥0) : 0 ≤ C s := by
    rw [← hC.zero]
    exact hm (zero_le : (0 : ℝ≥0) ≤ s)
  have hclock (s : ℝ≥0) : (retClock G η₁' η₂' ζ₂ u r s ω : ℝ) = C s := by
    rw [retClock_eq hd hG hp₂ hpair]
    exact Real.coe_toNNReal _ (hnonneg s)
  have hqC : (q : ℝ) ≤ C t := by
    rw [← hclock t]
    exact_mod_cast hqt
  have hqL : (q : ℝ≥0∞) ≤ capLife C L := by
    simpa only [retLife_eq] using hq.le
  obtain ⟨he, ht⟩ := invClock_min_eq hC hqL hqC
  have heC : (fun s => ((F.indicator (retClock G η₁' η₂' ζ₂ u r (min s t)) ω : ℝ≥0) : ℝ)) =
      fun s => C (min s t) := by
    funext s
    rw [indicator_of_mem hω, hclock]
  unfold retCapacityPrefix
  dsimp only
  rw [indicator_of_mem hω, heC, indicator_of_mem hω, he, min_eq_left ht]
  change _ = canonRetPath _ _ _ _ _ _ 0 q
  rw [canonRetPath_zero]
  rfl

end InteractingSLE.Restart.RetAux79
