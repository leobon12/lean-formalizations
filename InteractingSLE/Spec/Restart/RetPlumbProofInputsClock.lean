/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofInputsCond

/-!
# Observable chart prefixes and clocks supported on an initial event

Packet PROVE-RETPLUMB. Coordinate observations before a physical line suffice
for both prefix hitting measurability and filled-prefix measurability. On a good
initial event they also suffice for the retained clock, without observing its
regularization test over the entire future.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open QuantumZipper (H)
open Supp7

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A continuous prefix is hitting measurable using only coordinates before its
cutoff. Clipping the path supplies the unused later coordinates. -/
theorem measurable_image_Icc_of_prefix {Γ : Ω → ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : ∀ ω, Continuous (Γ ω))
    (hm : ∀ s ≤ t, Measurable fun ω => Γ ω s) :
    Measurable[mΩ, hittingSigma] fun ω => Γ ω '' Icc 0 t := by
  have h := measurable_image_Icc
    (fun ω => (hc ω).comp (continuous_id.min continuous_const))
    (fun s => hm (min s t) (min_le_right _ _)) t
  convert h using 1
  funext ω
  apply image_congr
  intro s hs
  simp only [Function.comp_apply, id_eq, min_eq_left hs.2]

/-- Filling requires no separate random-hull hypothesis once the continuous
prefix coordinates are observable. -/
theorem measurable_fillH_image_Icc_of_prefix {Γ : Ω → ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : ∀ ω, Continuous (Γ ω))
    (hm : ∀ s ≤ t, Measurable fun ω => Γ ω s) :
    Measurable[mΩ, hittingSigma] fun ω => fillH (Γ ω '' Icc 0 t) :=
  measurable_fillH_of_dyadic (isDyadicHitMeasurable_prefix hc hm)
    (fun ω => isCompact_Icc.image (hc ω))

/-- The unregularized clock at one physical line is determined measurably by
the chart prefix at that line. -/
theorem measurable_chartClock_of_prefix {Γ : Ω → ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : ∀ ω, Continuous (Γ ω))
    (hm : ∀ s ≤ t, Measurable fun ω => Γ ω s)
    (h0 : ∀ ω, (Γ ω 0).im ≤ 0) :
    Measurable fun ω => (chartClock (Γ ω) t).toNNReal := by
  have h := (((WholeField.measurable_hcapHit.comp
    (measurable_image_Icc_of_prefix hc hm)).ennreal_toReal).div_const 2).real_toNNReal
  convert h using 1
  funext ω
  exact chartClock_toNNReal_eq_grid (hc ω).continuousOn (h0 ω)

/-- Event-supported clock measurability. Only coordinates on the event and
before `t` are observed; no measurability of a future regularity test is assumed. -/
theorem measurable_indicator_clock_of_prefix {F : Set Ω} (hF : MeasurableSet F)
    {Γ : Ω → ℝ≥0 → ℂ} {Q : Ω → ℝ≥0} {t : ℝ≥0}
    (hc : ∀ ω ∈ F, Continuous (Γ ω))
    (hm : ∀ s ≤ t, Measurable (F.indicator fun ω => Γ ω s))
    (h0 : ∀ ω ∈ F, (Γ ω 0).im ≤ 0)
    (hQ : ∀ ω ∈ F, Q ω = (chartClock (Γ ω) t).toNNReal) :
    Measurable (F.indicator Q) := by
  classical
  let ΓF : Ω → ℝ≥0 → ℂ := fun ω s => F.indicator (fun ω => Γ ω s) ω
  have he : ∀ ω ∈ F, ΓF ω = Γ ω := fun ω hω => by
    funext s
    exact indicator_of_mem hω _
  have hcF : ∀ ω, Continuous (ΓF ω) := by
    intro ω
    by_cases hω : ω ∈ F
    · rw [he ω hω]
      exact hc ω hω
    · have hz : ΓF ω = fun _ => 0 := funext fun _ => indicator_of_notMem hω _
      rw [hz]
      exact continuous_const
  have h0F : ∀ ω, (ΓF ω 0).im ≤ 0 := by
    intro ω
    by_cases hω : ω ∈ F
    · rw [he ω hω]
      exact h0 ω hω
    · simp only [ΓF, indicator_of_notMem hω, Complex.zero_im, le_refl]
  have hclock := (measurable_chartClock_of_prefix hcF hm h0F).indicator hF
  convert hclock using 1
  funext ω
  by_cases hω : ω ∈ F
  · simp only [indicator_of_mem hω, he ω hω, hQ ω hω]
  · simp only [indicator_of_notMem hω]

/-- Continuity and the starting point of the chart path follow from the landed
retained-continuation geometry, including the real-line boundary stop. -/
theorem retChartPath_continuous_zero {G : ℝ≥0 → Set Ω}
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    {x₂ : ℝ} {ω : Ω} (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hG : ω ∈ G r) (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) :
    Continuous (retChartPath G η₁' η₂' ζ₂ u r ω) ∧
      retChartPath G η₁' η₂' ζ₂ u r ω 0 = 0 := by
  obtain ⟨hR, hD, hL⟩ := isRetCont_retFam hd hG hp₂ hpair
  unfold retChartPath
  rw [hD, hL]
  exact ⟨hR.continuous_contPath, hR.contPath_zero⟩

/-- On a measurable initial event of good disjoint pairs, the supported
retained clock only needs the supported chart-prefix coordinate observations. -/
theorem measurable_indicator_retClock_of_prefix {G : ℝ≥0 → Set Ω}
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r t : ℝ≥0}
    {x₂ : ℝ} (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    {ℋ : MeasurableSpace Ω} {F : Set Ω} (hF : MeasurableSet[ℋ] F) (hG : F ⊆ G r)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (hm : ∀ s ≤ t, Measurable[ℋ]
      (F.indicator fun ω => retChartPath G η₁' η₂' ζ₂ u r ω s)) :
    Measurable[ℋ] (F.indicator (retClock G η₁' η₂' ζ₂ u r t)) := by
  let _ : MeasurableSpace Ω := mΩ
  exact @measurable_indicator_clock_of_prefix Ω ℋ F hF
    (fun ω => retChartPath G η₁' η₂' ζ₂ u r ω) (retClock G η₁' η₂' ζ₂ u r t) t
    (fun ω hω => (retChartPath_continuous_zero hd (hG hω) (hp₂ ω hω) (hpair ω hω)).1)
    hm (fun ω hω => by
      rw [(retChartPath_continuous_zero hd (hG hω) (hp₂ ω hω) (hpair ω hω)).2]
      exact le_rfl)
    (fun ω hω => retClock_eq hd (hG hω) (hp₂ ω hω) (hpair ω hω) t)

end InteractingSLE.Restart.RetAux79
