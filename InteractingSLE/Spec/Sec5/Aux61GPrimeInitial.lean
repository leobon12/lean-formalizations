/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GRecBoundary
import InteractingSLE.Spec.Sec5.Aux61GPrimeChart
import InteractingSLE.Spec.Sec5.Aux61GContBoundary

/-! # The actual time-zero Gaussian boundary from free component accesses

Use the landed chart comparison theorem at fibre time zero. It identifies
any actual Gaussian mean, so no physical chart-mean equality is assumed.
A cover by componentwise physical comparison accesses and their reference germs supplies
the boundary values. The exact assertion then transfers to the record law.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GPrime
open Aux61Fib (FibCode FibData)
open Aux61FibK (codeFiltration)
open Aux61ChLoc (IsChartGaussAt liveSet liveEv)
open Aux61UnionK (chartHull)
open LocalSets (germSigma IsLocalSetMean lowerUnion)
open WholeField (centredField IsHistoryAvoidanceLocal)
open Aux61GRec
open InteractingSLE.Theorem14.SB.FinRel

universe u
variable {X : Type u} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X]
  {β : Type*} [mβ : MeasurableSpace β]

/-- The exact record-law boundary property from physical comparison wiring
at time zero and a cover by accessible reference germs. The physical mean
is identified by Gaussian uniqueness inside the reused comparison theorem. -/
theorem initialBoundary_of_zero_component_comparisons {μ : Measure X} [IsProbabilityMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) {Y : X → FibCode} (hY : Measurable Y)
    {h : X → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ)
    {c : X → Chart} (hc : ∀ x, (c x).IsConformal) (a k : ℝ)
    (hfield : ∀ x, Z x ∈ B → (0 : ℝ≥0∞) < (Y x).life → (Y x).field = Chart.chartTransport (hc x) 1 a k (h x))
    (hℋ : ℋ ≤ mX) (hZℋ : mβ.comap Z ≤ ℋ)
    (hYℋ : (codeFiltration.{u} 0).comap (fun x => ULift.up.{u} (Y x)) ≤ ℋ)
    (hdom : ∀ z, MeasurableSet[ℋ] {x | z ∈ (c x).dom})
    (hfwd : ∀ z, Measurable[ℋ] ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z))
    (hliftm : ∀ z, Measurable[ℋ] ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z))
    (hliftc : ∀ x, ContinuousOn (c x).2.2 (c x).dom)
    (hlift : ∀ x, InnerProductSpace.HarmonicOnNhd (c x).2.2 (c x).dom)
    {A : X → Set ℂ} (hAm : Measurable[mX, hittingSigma] A) (hAc : ∀ x, A x ⊆ H ∧ IsOpen (H \ A x))
    (hloc : IsHistoryAvoidanceLocal ℋ A (centredField h u₀) μ)
    (hgeo : ∀ᵐ x ∂μ, Z x ∈ B → (0 : ℝ≥0∞) < (Y x).life → H \ A x = (c x).2.1 '' (H \ chartHull Y 0 x))
    {ι : Type*} [Countable ι] {L : ι → X → Set ℂ} {g₂ : ι → X → DistOn upperHalfPlaneOpens}
    (hLm : ∀ i, Measurable[mX, hittingSigma] (L i)) (hLc : ∀ i, ∀ᵐ x ∂μ, L i x ⊆ H ∧ IsOpen (H \ L i x))
    (hLunb : ∀ i, ∀ᵐ x ∂μ, ∀ z ∈ lowerUnion (L i x),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (L i x)) z))
    (hg₂ : ∀ i, IsLocalSetMean (L i) (centredField h u₀) μ (g₂ i))
    {M₂ : ι → X → ℂ → ℝ} (hM₂h : ∀ i, ∀ᵐ x ∂μ, InnerProductSpace.HarmonicOnNhd (M₂ i x) (H \ L i x))
    (hM₂ : ∀ i, ∀ᵐ x ∂μ, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L i x →
      g₂ i x φ = ∫ z, (M₂ i x z - u₀ z) * φ z)
    {A' : ι → X → Set ℂ} {ℳ : ι → MeasurableSpace X} (hℳ : ∀ i, ℳ i ≤ mX)
    (hA'm : ∀ i, Measurable[mX, hittingSigma] (A' i)) (hA'c : ∀ i x, A' i x ⊆ H ∧ IsOpen (H \ A' i x))
    (hloc' : ∀ i, IsHistoryAvoidanceLocal (ℳ i) (A' i) (centredField h u₀) μ)
    (hℋℳ : ∀ i, ℋ ≤ ℳ i) (hAℳ : ∀ i, Measurable[ℳ i, hittingSigma] A) (hAA' : ∀ i x, A x ∩ H ⊆ A' i x)
    (hLℳ : ∀ i, Measurable[ℳ i, hittingSigma] (L i)) (hLA' : ∀ i x, L i x ∩ H ⊆ A' i x)
    {S' : ι → Set X} (hS' : ∀ i, MeasurableSet[ℋ] (S' i)) (hSA : ∀ i, ∀ᵐ x ∂μ, x ∈ S' i → A' i x = A x)
    {h₁ : X → DistOn upperHalfPlaneOpens}
    (hG : @IsChartGaussAt X mX β mβ μ Z B Y 0
      (germSigma (liveSet (liveEv Z B Y 0) A) (centredField h u₀) ⊔ ℋ) h₁)
    (d : FibData)
    (hlive : ∀ᵐ x ∂μ, Z x ∈ B → (0 : ℝ≥0∞) < (Y x).life)
    (hpatch_cover : ∀ᵐ x ∂μ, Z x ∈ B → ∀ b ∈ d.O₀, ∃ (i : ι) (z₀ : ℂ),
      x ∈ S' i ∧ z₀ ∈ L i x ∪ {z : ℂ | z.im = 0} ∧
      (∃ r > 0, ∀ᶠ z in 𝓝[H] (b : ℂ), (c x).2.1 z ∈ freeNear (A x) (L i x) z₀ r) ∧
      Tendsto (c x).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
      Tendsto (fun z => M₂ i x ((c x).2.1 z) + a +
        k * (c x).2.2 ((c x).2.1 z) - Aux61GlueK.refMean0 d z)
        (𝓝[H] (b : ℂ)) (𝓝 0)) :
    ∀ᵐ b ∂μ.map (Aux61GHist.meanHistory Z h₁),
      b.1 ∈ B → IsHarmonicDistOn b.2 H → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, b.2 ψ = ∫ z, v z * ψ z) →
      ∀ b₀ ∈ d.O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 d z)
        (𝓝[H] (b₀ : ℂ)) (𝓝 0) := by
  have hcompare := ae_tendsto_chart_sub_flowMean_comp hB hY 0 hhm hu₀ hh0
    hc a k hfield hℋ hZℋ hYℋ hdom hfwd hliftm hliftc hlift hAm hAc hloc hgeo
    hLm hLc hLunb hg₂ hM₂h hM₂ hℳ hA'm hA'c hloc' hℋℳ hAℳ hAA' hLℳ hLA' hS' hSA hG
  simp only [Aux61OldB.chartHull_zero, sdiff_empty] at hcompare
  have hZ : Measurable Z := Measurable.of_comap_le (hG.marksZ.trans hG.le)
  have hg : Measurable h₁ := hG.measurable.mono hG.le le_rfl
  apply (ae_map_iff (Aux61GHist.measurable_meanHistory hZ hg).aemeasurable
    (measurableSet_record_boundary d hB)).2
  filter_upwards [hcompare, hlive, hpatch_cover] with x hx hl hp hxB _
  intro v hv hrep b hb
  obtain ⟨i, z₀, hi, hz₀, hlocal, hinv, href⟩ := hp hxB b hb
  obtain ⟨r, hr, hfree⟩ := hlocal
  have hrelative := hx i hxB (hl hxB) hi v hv (fun ψ _ => hrep ψ)
    z₀ hz₀ r hr (𝓝[H] (b : ℂ)) (le_principal_iff.2 self_mem_nhdsWithin) hinv hfree
  exact Aux61GCont.tendsto_sub_reference_of_relative hrelative href

end InteractingSLE.Sec5.Aux61GPrime
