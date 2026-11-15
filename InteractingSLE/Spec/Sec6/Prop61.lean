/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61Compare

/-!
# Proposition 6.1 for two local sets: pockets of the full union, nested stopped sets

Packet PROVE-SEC6-C (specification §6.1, `source/spec/p145-192.md`, `#prop-6.1` p. 154,
`#prop-6.1-proof` pp. 166–169; supplement §2.3, `source/spec/p433-480.md`, "Conditional-mean
consequence, with its inputs stated", pp. 454–455).

The proof of Proposition 6.1 identifies the conditional mean in a component `C` of `ℍ ∖ A` from
(a) nested local-set comparisons (Propositions 3.8–3.9) with local sets whose means are already known
near the boundary of `C`, (b) the subpower bound of Aux. lemma 27 for the actual mean, and (c) the
finite-prime-end uniqueness of Aux. lemma 28. The supplement isolates this step as a conditional
statement: "Suppose the canonical own-flow mean on a right side of a piece of angle `θ` has
flattened height `λ − θχ`, and on a left side has height `−λ − θχ`. Assume the nested boundary
comparisons hold at the genuine own stopping times and that the actual conditional harmonic mean
has the subpower bound of Aux. 27. […] The bounded Poisson extension of these heights, pulled back
and corrected by `−χ Im L_φ`, is the conditional mean: the boundary comparison identifies it away
from the two endpoints and finitely many angle marks, and Aux. 28 excludes a remaining singular
harmonic term" (p. 454). Here (a)–(c) are **proved** (Propositions 3.8 and Aux. lemmas 27–28 are
landed), for two local sets `A₁, A₂` of a zero-boundary GFF on `ℍ` with a deterministic mean `F`:

* `ae_eqOn_component_union_of_tendsto` (the full union, "We start by working in the special case
  `τ = ∞` … Let `C` be a bounded two-arc Jordan pocket", p. 167): almost surely, in every bounded
  component `C` of `ℍ ∖ (A₁ ∪ A₂)` and for every chart, if at every prime end `q` outside a finite set
  the impression `p` is a point of `A₂ ∪ ℝ` near which `A₁ ⊆ A₂` and the mean of `A₂` has the
  boundary values of `𝔥_C` at `q` — or the same with `A₁` and `A₂` exchanged — then
  `𝒞_{A₁ ∪ A₂} + F = 𝔥_C` on `C`.
* `ae_eqOn_component_of_subset_of_tendsto` (a stopped set inside a full one, "Applying
  Proposition 3.8 to `A(τ) ⊆ A(∞)` therefore compares the conditional means on each of these local
  sides", p. 168): for local sets `S ⊆ L`, the same identification of `𝒞_S` in a bounded component of
  `ℍ ∖ S` from the boundary values of the mean of `L`, at prime ends whose impression `p ∈ S ∪ ℝ`
  has a neighbourhood in which `L ⊆ S`.
* `ae_eqOn_component_of_subset_of_eqOn` (completed pockets, "every pocket cut off before `τ` is also
  a component of `𝒮 ∖ A(∞)` … The conditional-mean comparison for nested local sets therefore
  identifies its mean with the already established full-curve mean", p. 168): if the mean of `L` is
  already identified on `C ⊆ ℍ ∖ L`, so is the mean of `S`.
* `ae_condExp_exp_eq_of_component_union_of_tendsto` : the Gaussian law of Proposition 6.1 on a
  pocket (germ σ-algebra; `ae_condExp_exp_eq_of_le_germSigma` forgets the germs).

* `ae_eqOn_of_union_of_components` (the outer components, p. 167): Proposition 3.9 at the level of
  harmonic representatives.

These are general lemmas about two local sets, not Proposition 6.1 itself. Their hypotheses are
(i) the geometry of the component (which prime ends of `C` have their impression on which set; the
finitely many exceptional prime ends: the pocket endpoints `x₀, y₀`, or the slit attachment and tip,
and marked boundary points), and (ii) the boundary values, **in the chart of `C`**, of the comparison
means. In the source, (ii) is obtained from the single-curve conditional laws ("flattened heights"
`±λ − θχ` in each curve's own chart) by the deterministic branch normalization of supplement §2.3
(p. 453); that normalization, the single-curve laws for the full curves, and the pocket topology are
not formalized here (see the packet handoff).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Real

namespace InteractingSLE.Sec6

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open SupercriticalConformalCovariance (IsConformalBijection)
open LocalSets

/-- If `a − b → 0` and `b − c → 0`, then `a − c → 0`. -/
lemma tendsto_sub_zero_trans {α : Type*} {l : Filter α} {a b c : α → ℝ}
    (h₁ : Tendsto (fun x => a x - b x) l (𝓝 0)) (h₂ : Tendsto (fun x => b x - c x) l (𝓝 0)) :
    Tendsto (fun x => a x - c x) l (𝓝 0) := by
  have := h₁.add h₂
  rw [add_zero] at this
  refine this.congr fun x => ?_
  ring

section Union

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A₁ A₂ : Ω → Set ℂ}

/-- **Proposition 6.1 for the full union `A₁ ∪ A₂`** (the case `τ = ∞`, p. 167; the
"Conditional-mean consequence" of supplement §2.3, p. 454, with its comparison and growth inputs
proved). Let `A₁, A₂` be local sets of the zero-boundary GFF `h` on `ℍ`, conditionally independent
given `h`, with every component of `Aᵢ ∪ {Im ≤ 0}` unbounded; `g, g₁, g₂` versions of
`𝒞_{A₁ ∪ A₂}, 𝒞_{A₁}, 𝒞_{A₂}`; `F` harmonic on `ℍ` and bounded on bounded sets. Almost surely, for
every bounded component `C` of `ℍ ∖ (A₁ ∪ A₂)`, all harmonic representatives `v, v₁, v₂` of
`g, g₁, g₂`, and every chart `(f, φ_C, G, L)` of Aux. lemma 28 with a finite exceptional set `E` of
prime ends: if every prime end `q ∉ E` has an impression `p` (`f(ζ) → p` as `ζ → q`) which either
lies in `A₂ ∪ ℝ`, has a neighbourhood in which `A₁ ⊆ A₂`, and there `(v₂ + F) ∘ f − 𝔥_C ∘ f → 0`;
or the same with `A₁, v₁` — then `v + F = 𝔥_C = G ∘ φ_C − χ L` on `C`. -/
theorem ae_eqOn_component_union_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    (hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₁ : IsLocalSetMean A₁ h P g₁)
    (hg₂ : IsLocalSetMean A₂ h P g₂) {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∀ K : Set ℂ, Bornology.IsBounded K → ∃ M : ℝ, ∀ z ∈ K ∩ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ (A₁ ω ∪ A₂ ω),
      Bornology.IsBounded (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) →
      ∀ v v₁ v₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd v₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ x, v₁ x * φ x) →
      InnerProductSpace.HarmonicOnNhd v₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ x, v₂ x * φ x) →
      ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ A₂ ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₁ ω ∩ ball p r ⊆ A₂ ω) ∧
            Tendsto (fun ζ => (v₂ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ A₁ ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₂ ω ∩ ball p r ⊆ A₁ ω) ∧
            Tendsto (fun ζ => (v₁ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      ∀ z ∈ connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀,
        v z + F z = G (φc z) - χ * L z := by
  have hAU : Measurable[mΩ, hittingSigma] fun ω => A₁ ω ∪ A₂ ω := measurable_union_hitting hA₁ hA₂
  have hlocU : IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) h P :=
    IsLocalSet.isLocalSet_union hh hA₁ hA₂ hci h₁ h₂
  filter_upwards [ae_eqOn_component_of_tendsto (A := fun ω => A₁ ω ∪ A₂ ω) hh hAU hlocU hg hF hFb
      χ, ae_tendsto_comp_sub_of_union hh hA₁ hA₂ hci h₁ h₂ hunb₂ hg hg₂,
    ae_tendsto_comp_sub_of_union_symm hh hA₁ hA₂ hci h₁ h₂ hunb₁ hg hg₁] with ω hid hc₂ hc₁
    z₀ hz₀ hCb v v₁ v₂ hv hvrep hv₁ hv₁rep hv₂ hv₂rep f φc G L E hf hφc hG hGb hLc hL hE hbd
  refine hid z₀ hz₀ hCb v hv hvrep f φc G L E hf hφc hG hGb hLc hL hE fun q hq hqE => ?_
  have hfC : MapsTo f (ball 0 1) (H \ (A₁ ω ∪ A₂ ω)) :=
    hf.2.mapsTo.mono_right (connectedComponentIn_subset _ _)
  obtain ⟨p, hfq, ⟨hp, hr, hlim⟩ | ⟨hp, hr, hlim⟩⟩ := hbd q hq hqE
  · have hf₂ : MapsTo f (ball 0 1) (H \ A₂ ω) :=
      hfC.mono_right (sdiff_subset_sdiff_right subset_union_right)
    have hd := hc₂ v v₂ hv hvrep hv₂ hv₂rep f q p hf₂ hfq hp hr
    refine tendsto_sub_zero_trans (b := fun ζ => v₂ (f ζ) + F (f ζ)) ?_ hlim
    refine hd.congr fun ζ => ?_
    ring
  · have hf₁ : MapsTo f (ball 0 1) (H \ A₁ ω) :=
      hfC.mono_right (sdiff_subset_sdiff_right subset_union_left)
    have hd := hc₁ v v₁ hv hvrep hv₁ hv₁rep f q p hf₁ hfq hp hr
    refine tendsto_sub_zero_trans (b := fun ζ => v₁ (f ζ) + F (f ζ)) ?_ hlim
    refine hd.congr fun ζ => ?_
    ring

/-- **Proposition 6.1, the Gaussian law on a pocket of the full union** (p. 154 and p. 167):
almost surely, if the test function `φ` is supported in a bounded component `C` of
`ℍ ∖ (A₁ ∪ A₂)` whose mean has been identified as in `ae_eqOn_component_union_of_tendsto`, then
given the germ σ-algebra of `A₁ ∪ A₂` the field `h + F` paired with `φ` has the conditional
characteristic function of `(𝔥_C, φ) + GFF_C(φ)`, `𝔥_C = G ∘ φ_C − χ L`. -/
theorem ae_condExp_exp_eq_of_component_union_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    (hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₁ : IsLocalSetMean A₁ h P g₁)
    (hg₂ : IsLocalSetMean A₂ h P g₂) {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∀ K : Set ℂ, Bornology.IsBounded K → ∃ M : ℝ, ∀ z ∈ K ∩ H, |F z| ≤ M) (χ : ℝ)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ (A₁ ω ∪ A₂ ω),
      Bornology.IsBounded (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) →
      tsupport φ ⊆ connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀ →
      ∀ v v₁ v₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω ψ = ∫ x, v x * ψ x) →
      InnerProductSpace.HarmonicOnNhd v₁ (H \ A₁ ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ A₁ ω → g₁ ω ψ = ∫ x, v₁ x * ψ x) →
      InnerProductSpace.HarmonicOnNhd v₂ (H \ A₂ ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ A₂ ω → g₂ ω ψ = ∫ x, v₂ x * ψ x) →
      ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ A₂ ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₁ ω ∩ ball p r ⊆ A₂ ω) ∧
            Tendsto (fun ζ => (v₂ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ A₁ ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₂ ω ∩ ball p r ⊆ A₁ ω) ∧
            Tendsto (fun ζ => (v₁ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) |
          germSigma (fun ω => A₁ ω ∪ A₂ ω) h] ω =
        cexp (I * ((∫ x, (G (φc x) - χ * L x) * φ x : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
            (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) φ φ) : ℝ) : ℂ) := by
  have hAU : Measurable[mΩ, hittingSigma] fun ω => A₁ ω ∪ A₂ ω := measurable_union_hitting hA₁ hA₂
  have hlocU : IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) h P :=
    IsLocalSet.isLocalSet_union hh hA₁ hA₂ hci h₁ h₂
  have hFc : ContinuousOn F H := fun z hz => (hF z hz).1.continuousAt.continuousWithinAt
  filter_upwards [ae_condExp_exp_eq_of_eqOn_component (A := fun ω => A₁ ω ∪ A₂ ω) hAU
      hh.measurable (hlocU.2.1.mono fun _ h => h.2) hg hFc φ,
    ae_eqOn_component_union_of_tendsto hh hA₁ hA₂ hci h₁ h₂ hunb₁ hunb₂ hg hg₁ hg₂ hF hFb χ]
    with ω hlaw hid z₀ hz₀ hCb hφC v v₁ v₂ hv hvrep hv₁ hv₁rep hv₂ hv₂rep f φc G L E hf hφc hG hGb
      hLc hL hE hbd
  exact hlaw z₀ hz₀ hφC v hv hvrep _ (hid z₀ hz₀ hCb v v₁ v₂ hv hvrep hv₁ hv₁rep hv₂ hv₂rep f φc
    G L E hf hφc hG hGb hLc hL hE hbd)

end Union

section Nested

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {S L : Ω → Set ℂ}

/-- **Proposition 6.1 for a stopped set inside a full one** (p. 168: "Applying Proposition 3.8 to
`A(τ) ⊆ A(∞)` therefore compares the conditional means on each of these local sides"). Let
`S ⊆ L` be local sets of the zero-boundary GFF `h` on `ℍ`, conditionally independent given `h`
(true when both are determined by `h`), with every component of `S ∪ {Im ≤ 0}` unbounded, and
`g_S, g_L` versions of `𝒞_S, 𝒞_L`. Almost surely, for every bounded component `C` of `ℍ ∖ S`,
all harmonic representatives `v` of `g_S` and `v_L` of `g_L`, and every chart with finite
exceptional set `E`: if every prime end `q ∉ E` has an impression `p ∈ S ∪ ℝ` with `L ⊆ S` near `p`
at which `(v_L + F) ∘ f − 𝔥_C ∘ f → 0`, then `v + F = 𝔥_C` on `C`. -/
theorem ae_eqOn_component_of_subset_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hS : Measurable[mΩ, hittingSigma] S) (hL : Measurable[mΩ, hittingSigma] L)
    (hSL : ∀ ω, S ω ⊆ L ω)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap L hittingSigma) (MeasurableSpace.comap S hittingSigma) P)
    (hlS : IsLocalSet S h P) (hlL : IsLocalSet L h P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (S ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (S ω)) z))
    {gS gL : Ω → DistOn upperHalfPlaneOpens} (hgS : IsLocalSetMean S h P gS)
    (hgL : IsLocalSetMean L h P gL) {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∀ K : Set ℂ, Bornology.IsBounded K → ∃ M : ℝ, ∀ z ∈ K ∩ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ S ω, Bornology.IsBounded (connectedComponentIn (H \ S ω) z₀) →
      ∀ v vL : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ S ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ S ω → gS ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd vL (H \ L ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → gL ω φ = ∫ x, vL x * φ x) →
      ∀ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ S ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ S ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn Lc (connectedComponentIn (H \ S ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ S ω) z₀, deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        p ∈ S ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, L ω ∩ ball p r ⊆ S ω) ∧
        Tendsto (fun ζ => (vL (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
          (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ S ω) z₀, v z + F z = G (φc z) - χ * Lc z := by
  have hLS : (fun ω => L ω ∪ S ω) = L := funext fun ω => union_eq_left.2 (hSL ω)
  have hgLS : IsLocalSetMean (fun ω => L ω ∪ S ω) h P gL := by rw [hLS]; exact hgL
  filter_upwards [ae_eqOn_component_of_tendsto hh hS hlS hgS hF hFb χ,
    ae_tendsto_comp_sub_of_union hh hL hS hci hlL hlS hunb hgLS hgS] with ω hid hc
    z₀ hz₀ hCb v vL hv hvrep hvL hvLrep f φc G Lc E hf hφc hG hGb hLc hLd hE hbd
  refine hid z₀ hz₀ hCb v hv hvrep f φc G Lc E hf hφc hG hGb hLc hLd hE fun q hq hqE => ?_
  obtain ⟨p, hfq, hp, hr, hlim⟩ := hbd q hq hqE
  have hfS : MapsTo f (ball 0 1) (H \ S ω) :=
    hf.2.mapsTo.mono_right (connectedComponentIn_subset _ _)
  have hu : L ω ∪ S ω = L ω := union_eq_left.2 (hSL ω)
  have hd := hc vL v (by rw [hu]; exact hvL) (by rw [hu]; exact hvLrep) hv hvrep f q p hfS hfq hp
    hr
  refine tendsto_sub_zero_trans (b := fun ζ => vL (f ζ) + F (f ζ)) ?_ hlim
  have := hd.neg
  rw [neg_zero] at this
  refine this.congr fun ζ => ?_
  ring

/-- **Completed pockets** (p. 168: "every pocket cut off before `τ` is also a component of
`𝒮 ∖ A(∞)`: the future tail does not enter it. The conditional-mean comparison for nested local
sets therefore identifies its mean with the already established full-curve mean"). With the
hypotheses of `ae_eqOn_component_of_subset_of_tendsto`: almost surely, if a bounded component `C`
of `ℍ ∖ S` lies in `ℍ ∖ L`, the mean of `L` is already identified on `C` (`v_L + F = 𝔥_C`), and every
prime end outside a finite set has an impression `p ∈ S ∪ ℝ` near which `L ⊆ S`, then
`v + F = 𝔥_C` on `C`. -/
theorem ae_eqOn_component_of_subset_of_eqOn
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hS : Measurable[mΩ, hittingSigma] S) (hL : Measurable[mΩ, hittingSigma] L)
    (hSL : ∀ ω, S ω ⊆ L ω)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap L hittingSigma) (MeasurableSpace.comap S hittingSigma) P)
    (hlS : IsLocalSet S h P) (hlL : IsLocalSet L h P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (S ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (S ω)) z))
    {gS gL : Ω → DistOn upperHalfPlaneOpens} (hgS : IsLocalSetMean S h P gS)
    (hgL : IsLocalSetMean L h P gL) {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∀ K : Set ℂ, Bornology.IsBounded K → ∃ M : ℝ, ∀ z ∈ K ∩ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ S ω, Bornology.IsBounded (connectedComponentIn (H \ S ω) z₀) →
      connectedComponentIn (H \ S ω) z₀ ⊆ H \ L ω →
      ∀ v vL : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ S ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ S ω → gS ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd vL (H \ L ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → gL ω φ = ∫ x, vL x * φ x) →
      ∀ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ S ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ S ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn Lc (connectedComponentIn (H \ S ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ S ω) z₀, deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) →
      E.Finite →
      (∀ z ∈ connectedComponentIn (H \ S ω) z₀, vL z + F z = G (φc z) - χ * Lc z) →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        p ∈ S ω ∪ {z : ℂ | z.im = 0} ∧ ∃ r > 0, L ω ∩ ball p r ⊆ S ω) →
      ∀ z ∈ connectedComponentIn (H \ S ω) z₀, v z + F z = G (φc z) - χ * Lc z := by
  filter_upwards [ae_eqOn_component_of_subset_of_tendsto hh hS hL hSL hci hlS hlL hunb hgS hgL hF
    hFb χ] with ω hω z₀ hz₀ hCb _ v vL hv hvrep hvL hvLrep f φc G Lc E hf hφc hG hGb hLc hLd hE
    hLid hbd
  refine hω z₀ hz₀ hCb v vL hv hvrep hvL hvLrep f φc G Lc E hf hφc hG hGb hLc hLd hE
    fun q hq hqE => ?_
  obtain ⟨p, hfq, hp, hr⟩ := hbd q hq hqE
  refine ⟨p, hfq, hp, hr, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  rw [hLid (f ζ) (hf.2.mapsTo hζ), sub_self]

end Nested

section Outer

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A₁ A₂ : Ω → Set ℂ}

/-- **The outer components** (p. 167: "Proposition 3.9 implies the same if `(z_k)` converges to a
point on the right side of `η_{θ₁}` … Then this implies that `𝒞_A` agrees with `𝔥_C` if `C` is
either the unbounded connected component which lies to the right of `η_{θ₁}` or to the left of
`η_{θ₂}`"): Proposition 3.9 for the harmonic representatives. Under the hypotheses of
`LocalSets.IsLocalSetMean.ae_eq_on_of_union` (`C` a `σ(A₁)`-measurable union of components of
`ℍ ∖ A₁`, disjoint from `A₂`), almost surely every harmonic representative `v` of `𝒞_{A₁ ∪ A₂}`
agrees on `C` with every harmonic representative `v₁` of `𝒞_{A₁}`; in particular `v + F = 𝔥` on `C`
whenever `v₁ + F = 𝔥` there (the single-set mean). -/
theorem ae_eqOn_of_union_of_components
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap A₁ hittingSigma, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A₁ ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A₁ ω) z ⊆ C ω)
    (hCA₂ : ∀ᵐ ω ∂P, Disjoint (C ω) (A₂ ω))
    {g g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₁ : IsLocalSetMean A₁ h P g₁) :
    ∀ᵐ ω ∂P, ∀ v v₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd v₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ x, v₁ x * φ x) →
      EqOn v v₁ (C ω) := by
  filter_upwards [IsLocalSetMean.ae_eq_on_of_union hh hA₁ hA₂ hci h₁ h₂ hCm hC hCA₂ hg hg₁, hC,
    hCA₂, h₁.2.1] with ω hω ⟨hCs, hCc⟩ hdis ⟨_, ho₁⟩ v v₁ hv hvrep hv₁ hv₁rep
  have hCo : IsOpen (C ω) := by
    have : C ω = ⋃ z ∈ C ω, connectedComponentIn (H \ A₁ ω) z := by
      refine Subset.antisymm (fun z hz => mem_biUnion hz (mem_connectedComponentIn (hCs hz)))
        (iUnion₂_subset fun z hz => hCc z hz)
    rw [this]
    exact isOpen_biUnion fun z _ => ho₁.connectedComponentIn
  have hCU : C ω ⊆ H \ (A₁ ω ∪ A₂ ω) := fun z hz =>
    ⟨(hCs hz).1, fun hz' => hz'.elim (hCs hz).2 (Set.disjoint_left.1 hdis hz)⟩
  refine eqOn_of_integral_mul_eq hCo (hCU.trans sdiff_subset) (fun z hz => hv z (hCU hz))
    (fun z hz => hv₁ z (hCs hz)) fun φ hφ => ?_
  rw [← hvrep φ (hφ.trans hCU), ← hv₁rep φ (hφ.trans hCs), hω φ hφ]

end Outer

end InteractingSLE.Sec6
