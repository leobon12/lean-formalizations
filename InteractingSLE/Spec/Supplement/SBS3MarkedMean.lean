/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedKernel
import InteractingSLE.Spec.Sec5.CrossCondStagedMean
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# S3: identify marked local-set means using the supplied conditional word

The conditional word is supplied by a stage witness; it is not reselected by
the mean-identification argument. The output holds on one conull event for
every harmonic representative and every test function. The retained chart
observations and marked locality remain explicit hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Restart LocalSets

/-- The deterministic chart observations measured by the retained record.
The harmonic lift is the real argument of the inherited analytic log. -/
structure RetainedChartData {Ω : Type u} (𝒢 : MeasurableSpace Ω) (c : Ω → Chart) : Prop where
  conformal : ∀ ω, (c ω).IsConformal
  domain : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom}
  forward : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)
  closed_ball : ∀ z ε, MeasurableSet[𝒢] {ω | Metric.closedBall z ε ⊆ ((c ω).dom : Set ℂ)}
  lift : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)
  harmonic_lift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom

/-- The centered physical mean of a word read in its retained chart. -/
def wordChartMean (κ : ℝ) (word : BoundaryWord) (c : Chart) (u₀ : ℂ → ℝ) (z : ℂ) : ℝ :=
  word.mean (c.1 z) - chiC κ * c.2.2 z - u₀ z

/-- Harmonicity follows from the conformal map and the inherited harmonic
lift; it is not an additional assumption on the candidate mean. -/
theorem harmonicOnNhd_wordChartMean {κ : ℝ} {word : BoundaryWord} (hs : word.IsSorted)
    {c : Chart} (hc : c.IsConformal)
    (hl : InnerProductSpace.HarmonicOnNhd c.2.2 c.dom) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) :
    InnerProductSpace.HarmonicOnNhd (wordChartMean κ word c u₀) c.dom := by
  intro z hz
  have hf := hc.differentiableOn_fwd.analyticAt (c.dom.isOpen.mem_nhds hz)
  have hm := QuantumZipper.FieldLawler.fl_harmonicAt_comp hf
    ((word.isBoundedHarmonicExtension_mean hs).1 _ (hc.fwd_mem hz))
  have harg : InnerProductSpace.HarmonicAt (fun z => chiC κ * c.2.2 z) z := by
    have he : (chiC κ • c.2.2) = (fun w => chiC κ * c.2.2 w) := by
      funext w
      rfl
    simpa only [he] using (hl z hz).const_smul (c := chiC κ)
  exact (hm.sub harg).sub (hu₀ z (hc.dom_subset hz))

/-- A conditional word law identifies every harmonic representative of the
actual local-set mean. Equality is asserted only on the chart domain, on the
retained event where that domain is a clopen part of the complement. -/
theorem ae_eqOn_mean_of_kernelWord {Ω : Type u} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    {κ : ℝ} {c : Ω → Chart} (hc : RetainedChartData 𝒢 c)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {h Y : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hY : Measurable Y)
    {β : Ω → BoundaryWord} {G : Set Ω} (hG : MeasurableSet[𝒢] G)
    (hsort : ∀ᵐ ω ∂P, ω ∈ G → (β ω).IsSorted)
    (htr : ∀ᵐ ω ∂P, ω ∈ G → IsChartTransport (c ω) 1 0 (chiC κ) (h ω) (Y ω))
    (hlaw : ∀ᵐ ω ∂P, ω ∈ G →
      IsGFFWithBoundaryData (condExpKernel P 𝒢 ω) Y (β ω).fn (β ω).jumps)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal 𝒢 A (WholeField.centredField h u₀) P)
    (hAD : ∀ᵐ ω ∂P, ω ∈ G →
      ((c ω).dom : Set ℂ) ⊆ H \ A ω ∧ IsOpen ((H \ A ω) \ (c ω).dom))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ G → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        g ω φ = ∫ z, v z * φ z) →
      EqOn (fun z => v z + u₀ z + chiC κ * (c ω).2.2 z)
        (fun z => (β ω).mean ((c ω).1 z)) (c ω).dom := by
  classical
  have hmean := fun φ => Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw
    h𝒢 hc.conformal hc.domain hc.forward hc.closed_ball hc.lift
    (fun ω z hz => (hc.harmonic_lift ω z hz).1.continuousAt.continuousWithinAt)
    hh hu₀ hY hG htr (ae_condExp_gaussCF_of_kernel h𝒢 hY hsort hlaw) hA hloc hmark hAD hg φ
  let A' : Ω → Set ℂ := fun ω => if ω ∈ G then H \ (c ω).dom else H
  have heG : ∀ ω ∈ G, H \ A' ω = (c ω).dom := by
    intro ω hω
    simp only [A', hω, ↓reduceIte, Set.sdiff_sdiff_right_self]
    exact inter_eq_right.2 (hc.conformal ω).dom_subset
  have heN : ∀ ω ∉ G, H \ A' ω = ∅ := by
    intro ω hω
    simp only [A', hω, ↓reduceIte, Set.sdiff_self]
  have hgh : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A' ω) := by
    filter_upwards [hg.2.1, hAD] with ω hghω hADω
    by_cases hω : ω ∈ G
    · rw [heG ω hω]
      obtain ⟨v, hv, hrep⟩ := hghω
      exact ⟨v, hv.mono (hADω hω).1, fun φ hφ => hrep φ (hφ.trans (hADω hω).1)⟩
    · rw [heN ω hω]
      refine ⟨fun _ => 0, fun _ hz => False.elim hz, fun φ hφ => ?_⟩
      rw [Restart.eq_zero_of_tsupport_subset_empty hφ, map_zero]
      simp
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · rw [heG ω hω]; exact (c ω).dom.isOpen
    · rw [heN ω hω]; exact isOpen_empty
  have hmh : ∀ᵐ ω ∂P,
      InnerProductSpace.HarmonicOnNhd (wordChartMean κ (β ω) (c ω) u₀) (H \ A' ω) := by
    filter_upwards [hsort] with ω hs
    by_cases hω : ω ∈ G
    · rw [heG ω hω]
      exact harmonicOnNhd_wordChartMean (κ := κ) (hs hω) (hc.conformal ω) (hc.harmonic_lift ω) hu₀.1
    · rw [heN ω hω]
      exact fun _ hz => False.elim hz
  have hpair : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      tsupport φ ⊆ H \ A' ω →
        g ω φ = ∫ z, wordChartMean κ (β ω) (c ω) u₀ z * φ z := by
    intro φ
    filter_upwards [hmean φ, hsort] with ω hω hs hφ
    by_cases hωG : ω ∈ G
    · rw [heG ω hωG] at hφ
      rw [hω hωG hφ]
      have hmhω := harmonicOnNhd_wordChartMean (κ := κ) (hs hωG) (hc.conformal ω) (hc.harmonic_lift ω) hu₀.1
      have hv := hmhω.add (hu₀.1.mono (hc.conformal ω).dom_subset)
      have hv' : ContinuousOn (fun z => (β ω).mean ((c ω).1 z) - chiC κ * (c ω).2.2 z) (c ω).dom := by
        convert hv.continuousOn using 1
        funext z
        simp only [Pi.add_apply, wordChartMean, sub_add_cancel]
      rw [← integral_sub (WholeField.integrable_mul_testOn hv' φ hφ)
        (WholeField.integrable_mul_testOn hu₀.1.continuousOn φ φ.tsupport_subset)]
      congr 1
      funext z
      dsimp only [wordChartMean]
      ring
    · rw [heN ω hωG] at hφ
      rw [Restart.eq_zero_of_tsupport_subset_empty hφ, map_zero]
      simp
  have hall := WangWu.ae_forall_apply_eq_of_forall_ae hgh hopen hmh hpair
  filter_upwards [hall, hsort, hAD] with ω hallω hs hADω hωG v hv hvr
  have hmω := harmonicOnNhd_wordChartMean (κ := κ) (hs hωG) (hc.conformal ω) (hc.harmonic_lift ω) hu₀.1
  have he : EqOn v (wordChartMean κ (β ω) (c ω) u₀) (c ω).dom :=
    Sec6.eqOn_of_integral_mul_eq (c ω).dom.isOpen (hc.conformal ω).dom_subset
      (hv.mono (hADω hωG).1) hmω (fun φ hφ => by
        rw [← hvr φ (hφ.trans (hADω hωG).1)]
        exact hallω φ (by rw [heG ω hωG]; exact hφ))
  intro z hz
  have hzEq := he hz
  dsimp only [wordChartMean] at hzEq
  linarith

end InteractingSLE.Theorem14.SB.S3
