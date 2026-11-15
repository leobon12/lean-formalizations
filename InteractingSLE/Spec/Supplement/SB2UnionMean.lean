/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2UnionWord

/-!
# Lemma SB2 at a junction: the union mean on the relative component

Packet PROVE-T14-SB2UNION. The probabilistic form of `SB2UnionWord`: the Gaussian local-set mean of the union of a
retained set `A` and an explored hull `K_t` that may touch `A` is the candidate of the relative chain on the relative
component (`ae_eqOn_unionMean_of_relConfigJ`, the junction analogue of `Supp8.Q3Rel.ae_eqOn_unionMean_of_relConfigOff`).

Both landed steps of that proof are per component: Proposition 3.8's side comparison
(`Sec6.ae_tendsto_comp_sub_of_union`, at every prime end) and the finite-exception Poisson uniqueness with Gaussian
growth (`Sec6.ae_eqOn_component_of_tendsto_global`, on the component through a point). So they are restated here for the
components through a random set `C`:

* `HasSurvivingWordBoundaryOn`, `ae_survivingWordBoundaryOn_union` (from `SB.SewGerm.ae_survivingWordBoundary_union`);
* `ae_eqOn_physicalMean_of_boundaryOn` (from `SB.SewGerm.ae_eqOn_physicalMean_of_boundary`);
* **`ae_eqOn_unionMean_of_relConfigJ`**.

R48: serves Theorem 1.4. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn CondIndepEv)
open SupercriticalConformalCovariance (IsConformalBijection)

universe u

namespace InteractingSLE.Theorem14.SB.Union

open LocalSets

/-- **The surviving word boundary datum on the components through `C`** (`SB.SewGerm.HasSurvivingWordBoundary`
restricted to `z₀ ∈ C`). -/
def HasSurvivingWordBoundaryOn (C A : Set ℂ) (u₀ v w : ℂ → ℝ) (χ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) : Prop :=
  ∀ z₀ ∈ C, ∃ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
    IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ A) z₀) ∧
    IsConformalBijection φc (connectedComponentIn (H \ A) z₀) H ∧
    IsBoundedHarmonicExtension b jumps G ∧
    ContinuousOn L (connectedComponentIn (H \ A) z₀) ∧
    (∀ z ∈ connectedComponentIn (H \ A) z₀,
      deriv φc z = ‖deriv φc z‖ * Complex.exp (L z * Complex.I)) ∧
    E.Finite ∧
    EqOn v (fun z => G (φc z) - χ * L z) (connectedComponentIn (H \ A) z₀) ∧
    ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
        (𝓝[ball 0 1] q) (𝓝 0)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens} {A₁ A₂ : Ω → Set ℂ}

/-- **The joint mean inherits the individual boundary values on the components through `C`**
(`SB.SewGerm.ae_survivingWordBoundary_union`, per component). -/
theorem ae_survivingWordBoundaryOn_union
    (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hd₁ : MeasurableSpace.comap A₁ hittingSigma ≤ aeSigma (MeasurableSpace.comap X inferInstance) P)
    (hl₁ : IsLocalSet A₁ X P) (hl₂ : IsLocalSet A₂ X P)
    (hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    (hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) X P g)
    (hg₁ : IsLocalSetMean A₁ X P g₁) (hg₂ : IsLocalSetMean A₂ X P g₂)
    (C : Ω → Set ℂ) (u₀ : ℂ → ℝ) (v : Ω → ℂ → ℝ) (χ : ℝ)
    (b : Ω → ℝ → ℝ) (jumps : Ω → Finset ℝ) {D : Set Ω}
    (hword : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ w₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      HasUnionWordBoundaryOn (C ω) (A₁ ω) (A₂ ω) u₀ (v ω) w₁ w₂ χ (b ω) (jumps ω)) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ w : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) → g ω φ = ∫ z, w z * φ z) →
      HasSurvivingWordBoundaryOn (C ω) (A₁ ω ∪ A₂ ω) u₀ (v ω) w χ (b ω) (jumps ω) := by
  have hci : CondIndepEv (MeasurableSpace.comap X inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P :=
    Sec6.condIndepEv_of_le_aeSigma hX.measurable.comap_le hA₂.comap_le hd₁
  have hcmp₁ := Sec6.ae_tendsto_comp_sub_of_union_symm hX hA₁ hA₂ hci hl₁ hl₂ hunb₁ hg hg₁
  have hcmp₂ := Sec6.ae_tendsto_comp_sub_of_union hX hA₁ hA₂ hci hl₁ hl₂ hunb₂ hg hg₂
  filter_upwards [hcmp₁, hcmp₂, hg₁.2.1, hg₂.2.1, hword]
    with ω hc₁ hc₂ hg₁ω hg₂ω hwω hωD w hw hrep z₀ hz₀
  obtain ⟨w₁, hw₁, hrep₁⟩ := hg₁ω
  obtain ⟨w₂, hw₂, hrep₂⟩ := hg₂ω
  obtain ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, hlim⟩ :=
    hwω hωD w₁ w₂ hw₁ hrep₁ hw₂ hrep₂ z₀ hz₀
  refine ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, ?_⟩
  intro q hq hqE
  have hmaps₁ : MapsTo f (ball 0 1) (H \ A₁ ω) := by
    intro ζ hζ
    have hz := connectedComponentIn_subset (H \ (A₁ ω ∪ A₂ ω)) z₀ (hf.2.mapsTo hζ)
    exact ⟨hz.1, fun hA => hz.2 (Or.inl hA)⟩
  have hmaps₂ : MapsTo f (ball 0 1) (H \ A₂ ω) := by
    intro ζ hζ
    have hz := connectedComponentIn_subset (H \ (A₁ ω ∪ A₂ ω)) z₀ (hf.2.mapsTo hζ)
    exact ⟨hz.1, fun hA => hz.2 (Or.inr hA)⟩
  rcases hlim q hq hqE with ⟨p, hp, hpA, hr, hs⟩ | ⟨p, hp, hpA, hr, hs⟩
  · have hc := hc₁ w w₁ hw hrep hw₁ hrep₁ f q p hmaps₁ hp hpA hr
    have ht := hc.add hs
    rw [zero_add] at ht
    exact ht.congr fun ζ => by ring
  · have hc := hc₂ w w₂ hw hrep hw₂ hrep₂ f q p hmaps₂ hp hpA hr
    have ht := hc.add hs
    rw [zero_add] at ht
    exact ht.congr fun ζ => by ring

variable {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

/-- **Prime-end uniqueness on the components through `C`** (`SB.SewGerm.ae_eqOn_physicalMean_of_boundary`, per
component). -/
theorem ae_eqOn_physicalMean_of_boundaryOn
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g)
    (C : Ω → Set ℂ) {v : Ω → ℂ → ℝ} {b : Ω → ℝ → ℝ} {jumps : Ω → Finset ℝ} (χ : ℝ) {D : Set Ω}
    (hC : ∀ᵐ ω ∂P, ω ∈ D → C ω ⊆ H \ A ω)
    (hbd : ∀ᵐ ω ∂P, ω ∈ D → ∀ w : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, w z * φ z) →
      HasSurvivingWordBoundaryOn (C ω) (A ω) u₀ (v ω) w χ (b ω) (jumps ω)) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ w : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, w z * φ z) →
      EqOn (fun z => w z + u₀ z) (v ω) (C ω) := by
  have huniq := Sec6.ae_eqOn_component_of_tendsto_global hh0 hAm hloc hg hu₀ hu₀b χ
  filter_upwards [huniq, hbd, hC] with ω hω hbω hCω hωD w hw hrep z hz
  have hzA : z ∈ H \ A ω := hCω hωD hz
  obtain ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, hlim⟩ := hbω hωD w hw hrep z hz
  have he := hω z hzA w hw hrep f φc G L E hf hφc hG.1 hG.2.1 hL hd hE hlim
  exact (he z (mem_connectedComponentIn hzA)).trans (hv (mem_connectedComponentIn hzA)).symm

open Supp8.BHMean (jointInv)

/-- **The conditional mean of the union of a retained set and an explored hull meeting it at junctions, on the
relative component** (SB2, pp. 631–632; the junction analogue of `Supp8.Q3Rel.ae_eqOn_unionMean_of_relConfigOff`): if
a.s. on `D` the junction configuration `IsRelConfigJ` holds and the two individual means are the retained-chart and the
explored-chain formulas, the union mean plus `u₀` equals the relative candidate `v` on `relComp A Ψ Wr u`. -/
theorem ae_eqOn_unionMean_of_relConfigJ
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ} {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ}
    {t u : Ω → ℝ} {χ lam : ℝ}
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
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigJ (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω) (t ω)
      (u ω) χ lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω))
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
      EqOn (fun z => wU z + u₀ z) (v ω) (relComp (A ω) (Ψ ω) (Wr ω) (u ω)) := by
  have hword : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ w₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (w ω) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (w ω) (t ω) → g₂ ω φ = ∫ z, w₂ z * φ z) →
      HasUnionWordBoundaryOn (relComp (A ω) (Ψ ω) (Wr ω) (u ω)) (A ω) (fwdHull (w ω) (t ω)) u₀ (v ω) w₁ w₂ χ
        (βu ω) (Su ω) := by
    filter_upwards [hcfg, hind₁, hind₂] with ω hc h1 h2 hωD w₁ w₂ hw₁ hr₁ hw₂ hr₂
    exact (hc hωD).hasUnionWordBoundaryOn (h1 hωD w₁ hw₁ hr₁) (h2 hωD w₂ hw₂ hr₂)
  have hsurv := ae_survivingWordBoundaryOn_union hh0 hAm hKm hdA hlA hlK hunbA hunbK hg hg₁ hg₂
    (fun ω => relComp (A ω) (Ψ ω) (Wr ω) (u ω)) u₀ v χ βu Su hword
  have hC : ∀ᵐ ω ∂P, ω ∈ D →
      relComp (A ω) (Ψ ω) (Wr ω) (u ω) ⊆ H \ (A ω ∪ fwdHull (w ω) (t ω)) := by
    filter_upwards [hcfg] with ω hc hωD
    exact relComp_subset (hc hωD).hullIn
  exact ae_eqOn_physicalMean_of_boundaryOn hh0 hu₀ hu₀b (measurable_union_hitting hAm hKm) hlU hg
    (fun ω => relComp (A ω) (Ψ ω) (Wr ω) (u ω)) χ hC hsurv

end InteractingSLE.Theorem14.SB.Union
