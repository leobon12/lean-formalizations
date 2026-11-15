/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BHMean

/-!
# The boundary-hitting mean identification: the conditional mean of the union

Packet PROVE-BHMEAN. The deterministic `RelUnionWordBoundaryStatement`, applied sample by sample, identifies the
conditional mean of the field given the marked union of the retained set and the explored hull (the mean
identification that GB6's relative stopped kernel and GW2's joint (Det) both need, Astra's Q3 §3.3):

* `IsRelConfig`: the deterministic hypotheses of `RelUnionWordBoundaryStatement` other than the two individual means,
  bundled; `IsRelConfig.hasUnionWordBoundary`;
* **`ae_eqOn_unionMean_of_relConfig`**: if the field minus `u₀` is a zero-boundary GFF, the retained set is
  field-determined, both sets and their union are local sets with the landed lower-union condition, the per-sample
  configuration holds almost surely on `D`, and the two individual local-set means are the explicit ones (the
  retained one through the chart, the explored one the coupling mean), then almost surely on `D` every harmonic
  representative of the union mean, plus `u₀`, is the candidate `v` (the relative coupling mean read through the
  chart) on the joint complement. Proof: `SB.SewGerm.ae_survivingWordBoundary_union` (Proposition 3.8 for the two
  sides) and `SB.SewGerm.ae_eqOn_physicalMean_of_boundary` (prime-end uniqueness, Aux. 28).

Conditional helpers with distinct names; they replace no source theorem. R48: serves Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Supp8.BHMean

open Theorem14.SB.SewGerm (HasUnionWordBoundary HasSurvivingWordBoundary)
open LocalSets

/-- **The deterministic relative configuration** (the hypotheses of `RelUnionWordBoundaryStatement` other than the
two individual means), bundled. -/
structure IsRelConfig (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (w Wr : ℝ → ℝ) (η ηr : ℝ → ℂ) (t u χ lam : ℝ)
    (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ) : Prop where
  chart : IsRetainedChart A Ψ Ψi LΨ
  hw : Continuous w
  hw0 : w 0 = 0
  hη : IsLoewnerTrace w η
  ht : 0 ≤ t
  hWr : Continuous Wr
  hWr0 : Wr 0 = 0
  hηr : IsLoewnerTrace Wr ηr
  hu : 0 ≤ u
  hull : Ψ '' fwdHull w t = fwdHull Wr u
  disj : Disjoint (closure (fwdHull w t)) (closure A)
  tip : Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0)
  bhe₀ : IsBoundedHarmonicExtension β₀ S₀ G₀
  bheE : IsBoundedHarmonicExtension βE SE GE
  bheu : IsBoundedHarmonicExtension βu Su G
  sideE : IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam
  sideu : IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam
  flow : IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u)
  cand : ∀ z, v z = G (fwdMap Wr u (Ψ z)) - χ * ((logDerivFwd Wr u (Ψ z)).im + (LΨ z).im)

theorem IsRelConfig.hasUnionWordBoundary (hBH : RelUnionWordBoundaryStatement) {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ}
    {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ} {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ}
    {G₀ GE G v : ℂ → ℝ} (hc : IsRelConfig A Ψ Ψi LΨ w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    {u₀ w₁ w₂ : ℂ → ℝ}
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t)) :
    HasUnionWordBoundary A (fwdHull w t) u₀ v w₁ w₂ χ βu Su :=
  hBH A Ψ Ψi LΨ w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G u₀ w₁ w₂ v hc.chart hc.hw hc.hw0 hc.hη hc.ht hc.hWr
    hc.hWr0 hc.hηr hc.hu hc.hull hc.disj hc.tip hc.bhe₀ hc.bheE hc.bheu hc.sideE hc.sideu hc.flow hw₁ hw₂ hc.cand

/-- **The conditional mean of the union of a retained set and an explored hull** (the boundary-hitting mean
identification, probabilistic form): see the module docstring. -/
theorem ae_eqOn_unionMean_of_relConfig (hBH : RelUnionWordBoundaryStatement)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ} {t u : Ω → ℝ} {χ lam : ℝ}
    {β₀ βE βu : Ω → ℝ → ℝ} {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] fun ω => fwdHull (w ω) (t ω))
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h u₀) P)
    (hlK : IsLocalSet (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (fwdHull (w ω) (t ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fwdHull (w ω) (t ω))) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField h u₀) P g₁)
    (hg₂ : IsLocalSetMean (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g₂)
    {D : Set Ω}
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfig (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (w ω) (Wr ω) (η ω) (ηr ω) (t ω) (u ω) χ lam
      (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω))
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ ω (Ψ ω z) - χ * (LΨ ω z).im) (H \ A ω))
    (hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (w ω) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (w ω) (t ω) → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (t ω) z) - χ * (logDerivFwd (w ω) (t ω) z).im)
        (H \ fwdHull (w ω) (t ω))) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ fwdHull (w ω) (t ω))) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ fwdHull (w ω) (t ω)) →
        g ω φ = ∫ z, wU z * φ z) →
      EqOn (fun z => wU z + u₀ z) (v ω) (H \ (A ω ∪ fwdHull (w ω) (t ω))) := by
  have hword : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ w₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (w ω) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (w ω) (t ω) → g₂ ω φ = ∫ z, w₂ z * φ z) →
      HasUnionWordBoundary (A ω) (fwdHull (w ω) (t ω)) u₀ (v ω) w₁ w₂ χ (βu ω) (Su ω) := by
    filter_upwards [hcfg, hind₁, hind₂] with ω hc h1 h2 hωD w₁ w₂ hw₁ hr₁ hw₂ hr₂
    exact (hc hωD).hasUnionWordBoundary hBH (h1 hωD w₁ hw₁ hr₁) (h2 hωD w₂ hw₂ hr₂)
  have hsurv := Theorem14.SB.SewGerm.ae_survivingWordBoundary_union hh0 hAm hKm hdA hlA hlK hunbA hunbK hg hg₁ hg₂
    u₀ v χ βu Su hword
  exact Theorem14.SB.SewGerm.ae_eqOn_physicalMean_of_boundary hh0 hu₀ hu₀b (measurable_union_hitting hAm hKm) hlU
    hg χ hsurv

end InteractingSLE.Supp8.BHMean
