/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# Proposition 6.1: nested local-set comparisons read at prime ends

Packet PROVE-SEC6-C (specification §6.1, `source/spec/p145-192.md`, `#prop-6.1-proof`,
pp. 166–168).

The proof of Proposition 6.1 obtains the boundary values of the actual mean `𝒞_A` of a component
`C` from those of a comparison local set through Proposition 3.8: "The local-set comparison then
gives `𝒞_A − 𝔥_C → 0` on `∂C ∖ {x₀, y₀}`" (p. 167); "Applying Proposition 3.8 to
`A(τ) ⊆ A(∞)` therefore compares the conditional means on each of these local sides … These
comparisons use the prime-end compactification" (p. 168). Proposition 3.8 (landed,
`LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union`) gives a limit at a **physical** point `p`
along `ℍ ∖ (A₁ ∪ A₂)`; a prime end `q` of `C` (a point of the unit circle, read through a conformal
`f : 𝔻 → C`) whose impression is the single point `p` (`f(ζ) → p` as `ζ → q`) inherits it. This
file proves that transfer:

* `tendsto_comp_of_tendsto_nhdsWithin` (deterministic): if `u → 0` at `p` along `ℍ ∖ L`, the
  chart `f` maps the disk into `ℍ ∖ S`, `f → p` at `q`, and `L ⊆ S` near `p`, then `u ∘ f → 0` at
  `q`;
* `ae_tendsto_comp_sub_of_union` : for local sets `A₁, A₂` as in Proposition 3.8 and harmonic
  representatives `v` of `𝒞_{A₁ ∪ A₂}` and `v₂` of `𝒞_{A₂}`, almost surely, for every chart `f`
  of a subdomain of `ℍ ∖ A₂` and every prime end `q` with impression `p ∈ A₂ ∪ ℝ` near which
  `A₁ ⊆ A₂`, `v ∘ f − v₂ ∘ f → 0` at `q`. It serves both directions of the source's comparisons:
  a component of `ℍ ∖ (A₁ ∪ A₂)` compared with the smaller set `A₂` (the pockets, p. 167), and a
  component of `ℍ ∖ A₂` compared with the larger set `A₁ ∪ A₂` (`A(τ) ⊆ A(∞)`, p. 168).
* `ae_tendsto_comp_sub_of_union_symm` : the same with the roles of `A₁` and `A₂` exchanged.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Real

namespace InteractingSLE.Sec6

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open LocalSets

/-- Near a prime end `q` with impression `p`, the chart avoids `L` if `L ⊆ S` near `p` and the chart
maps the disk into `ℍ ∖ S`. -/
theorem eventually_mem_diff_of_tendsto {S L : Set ℂ} {f : ℂ → ℂ} {q p : ℂ}
    (hf : MapsTo f (ball 0 1) (H \ S)) (hfq : Tendsto f (𝓝[ball 0 1] q) (𝓝 p))
    (hr : ∃ r > 0, L ∩ ball p r ⊆ S) : ∀ᶠ ζ in 𝓝[ball 0 1] q, f ζ ∈ H \ L := by
  obtain ⟨r, hr0, hrS⟩ := hr
  filter_upwards [hfq (ball_mem_nhds p hr0), self_mem_nhdsWithin] with ζ hζp hζ
  exact ⟨(hf hζ).1, fun hL => (hf hζ).2 (hrS ⟨hL, hζp⟩)⟩

/-- **A physical boundary limit read at a prime end.** If `u → 0` at `p` along `ℍ ∖ L`, `f` maps
the unit disk into `ℍ ∖ S`, `f(ζ) → p` as `ζ → q` in the disk, and `L ∩ B(p, r) ⊆ S` for some
`r > 0`, then `u ∘ f → 0` as `ζ → q` in the disk. -/
theorem tendsto_comp_of_tendsto_nhdsWithin {S L : Set ℂ} {f : ℂ → ℂ} {q p : ℂ} {u : ℂ → ℝ}
    (hf : MapsTo f (ball 0 1) (H \ S)) (hfq : Tendsto f (𝓝[ball 0 1] q) (𝓝 p))
    (hr : ∃ r > 0, L ∩ ball p r ⊆ S) (hu : Tendsto u (𝓝[H \ L] p) (𝓝 0)) :
    Tendsto (u ∘ f) (𝓝[ball 0 1] q) (𝓝 0) :=
  hu.comp (tendsto_nhdsWithin_iff.2 ⟨hfq, eventually_mem_diff_of_tendsto hf hfq hr⟩)

section Compare

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A₁ A₂ : Ω → Set ℂ}

/-- **Proposition 3.8 read at prime ends.** Let `A₁, A₂` be local sets of the zero-boundary GFF `h`
on `ℍ`, conditionally independent given `h`, every component of `A₂ ∪ {Im ≤ 0}` unbounded, and
`g`, `g₂` versions of `𝒞_{A₁ ∪ A₂}`, `𝒞_{A₂}`. Almost surely: for all harmonic representatives `v`
of `g` on `ℍ ∖ (A₁ ∪ A₂)` and `v₂` of `g₂` on `ℍ ∖ A₂`, every `f` mapping the unit disk into
`ℍ ∖ A₂` (a chart of a component of `ℍ ∖ (A₁ ∪ A₂)` or of `ℍ ∖ A₂`), every point `q` and every
`p ∈ A₂ ∪ ℝ` with `f(ζ) → p` as `ζ → q` and `A₁ ⊆ A₂` near `p`, eventually `f(ζ) ∉ A₁ ∪ A₂` and
`v(f ζ) − v₂(f ζ) → 0` as `ζ → q`. -/
theorem ae_tendsto_comp_sub_of_union
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₂ : IsLocalSetMean A₂ h P g₂) :
    ∀ᵐ ω ∂P, ∀ v v₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd v₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ x, v₂ x * φ x) →
      ∀ (f : ℂ → ℂ) (q p : ℂ), MapsTo f (ball 0 1) (H \ A₂ ω) →
        Tendsto f (𝓝[ball 0 1] q) (𝓝 p) → p ∈ A₂ ω ∪ {z : ℂ | z.im = 0} →
        (∃ r > 0, A₁ ω ∩ ball p r ⊆ A₂ ω) →
        Tendsto (fun ζ => v (f ζ) - v₂ (f ζ)) (𝓝[ball 0 1] q) (𝓝 0) := by
  filter_upwards [IsLocalSetMean.ae_tendsto_sub_of_union hh hA₁ hA₂ hci h₁ h₂ hunb hg hg₂,
    h₁.2.1, h₂.2.1] with ω ⟨u, hu, hrep, hlim⟩ ⟨_, ho₁⟩ ⟨_, ho₂⟩ v v₂ hv hvrep hv₂ hv₂rep f q p
    hf hfq hp hr
  have hUeq : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
    ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]; tauto
  have hoU : IsOpen (H \ (A₁ ω ∪ A₂ ω)) := hUeq ▸ ho₁.inter ho₂
  have hUA₂ : H \ (A₁ ω ∪ A₂ ω) ⊆ H \ A₂ ω := sdiff_subset_sdiff_right subset_union_right
  -- `u = v − v₂` on `ℍ ∖ (A₁ ∪ A₂)`
  have hcont : ∀ {U : Set ℂ} {w : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd w U →
      ContinuousOn w U := fun hw z hz => (hw z hz).1.continuousAt.continuousWithinAt
  have huv : EqOn u (fun z => v z - v₂ z) (H \ (A₁ ω ∪ A₂ ω)) := by
    refine eqOn_of_integral_mul_eq hoU sdiff_subset hu
      (hv.sub fun z hz => hv₂ z (hUA₂ hz)) fun φ hφ => ?_
    rw [← hrep φ hφ, hvrep φ hφ, hv₂rep φ (hφ.trans hUA₂),
      ← integral_sub (integrable_mul_test hoU (hcont hv) φ hφ)
        (integrable_mul_test hoU ((hcont hv₂).mono hUA₂) φ hφ)]
    congr 1; funext z; ring
  have hrL : ∃ r > 0, (A₁ ω ∪ A₂ ω) ∩ ball p r ⊆ A₂ ω := by
    obtain ⟨r, hr0, hrS⟩ := hr
    refine ⟨r, hr0, ?_⟩
    rintro z ⟨hz | hz, hzb⟩
    · exact hrS ⟨hz, hzb⟩
    · exact hz
  refine (tendsto_comp_of_tendsto_nhdsWithin hf hfq hrL (hlim p hp hr)).congr' ?_
  filter_upwards [eventually_mem_diff_of_tendsto hf hfq hrL] with ζ hζ
  exact huv hζ

/-- `ae_tendsto_comp_sub_of_union` with the roles of `A₁` and `A₂` exchanged: comparison of
`𝒞_{A₁ ∪ A₂}` with `𝒞_{A₁}` at prime ends with impression `p ∈ A₁ ∪ ℝ` near which `A₂ ⊆ A₁`. -/
theorem ae_tendsto_comp_sub_of_union_symm
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    {g g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₁ : IsLocalSetMean A₁ h P g₁) :
    ∀ᵐ ω ∂P, ∀ v v₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd v₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ x, v₁ x * φ x) →
      ∀ (f : ℂ → ℂ) (q p : ℂ), MapsTo f (ball 0 1) (H \ A₁ ω) →
        Tendsto f (𝓝[ball 0 1] q) (𝓝 p) → p ∈ A₁ ω ∪ {z : ℂ | z.im = 0} →
        (∃ r > 0, A₂ ω ∩ ball p r ⊆ A₁ ω) →
        Tendsto (fun ζ => v (f ζ) - v₁ (f ζ)) (𝓝[ball 0 1] q) (𝓝 0) := by
  have hcomm : (fun ω => A₂ ω ∪ A₁ ω) = fun ω => A₁ ω ∪ A₂ ω := funext fun ω => union_comm _ _
  have hg' : IsLocalSetMean (fun ω => A₂ ω ∪ A₁ ω) h P g := hcomm ▸ hg
  filter_upwards [ae_tendsto_comp_sub_of_union hh hA₂ hA₁ hci.symm h₂ h₁ hunb hg' hg₁] with ω hω
    v v₁ hv hvrep hv₁ hv₁rep f q p hf hfq hp hr
  rw [union_comm (A₁ ω)] at hv hvrep
  exact hω v v₁ hv hvrep hv₁ hv₁rep f q p hf hfq hp hr

end Compare

end InteractingSLE.Sec6
