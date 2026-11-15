/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CertStop
import InteractingSLE.Spec.Sec7.R6RelCert
import InteractingSLE.Spec.Sec7.PocketStopSideFinalComparison

/-!
# R.6's physical germ comparison (`R6Germ`) from a joint walls–hull law

PROVE-R6-CERT. Item 5 of the R.6 certificate (`R6Rel.R6Cert`, PROVE-R6-NESTREL §4.1): the germ comparison
`vI ∘ c_C⁻¹ − v ∘ c_C⁻¹ → 0` at a collar point of the outer chart, for the local-set means of an outer set `E_C` and
an inner set `E_U`. Supplement p. 477: "The all-stop collar argument identifies each local germ with that same ambient
germ in its own chart". The two sets need **not** be read at a common time: it suffices that both are
hitting-measurable for the marks `ℳ` of one history-marked local set `E₀` that they cover (for R.6: the walls–hull
set at the later of the two marked stops, `R6Cert.isHistoryAvoidanceLocal_walls_regHull_markedStop`), and that the
current domains are the complements of the two sets.

* `tendsto_inverse_compl_union`: a shared collar puts the outer inverse approach in the common complement;
* **`ae_r6Germ_of_joint`**: almost surely, uniformly over harmonic representatives, charts, collars and landings,
  local agreement of the two sets at the landing point gives `R6Rel.R6Germ`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Cert

open PocketStopSide LocalSets WholeField

/-- **A shared collar puts the outer inverse approach in the common complement** of the two sets whose complements
are the current domains. -/
theorem tendsto_inverse_compl_union {outer inner : Chart} (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hIncl : (inner.dom : Set ℂ) ⊆ outer.dom) {EC EU : Set ℂ} (hOC : (outer.dom : Set ℂ) = H \ EC)
    (hIU : (inner.dom : Set ℂ) = H \ EU) {ξ r : ℝ} (hr : 0 < r)
    (hCollar : H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ))
    {p : ℂ} (hLanding : Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) :
    Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝[H \ (EC ∪ EU)] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨hLanding, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (ball_mem_nhds (ξ : ℂ) hr)] with z hzH hzball
  have hpI := ((mem_dom_pocketTransitionChart hO hI hIncl).1 (hCollar ⟨hzH, hzball⟩)).2
  have hpO := hIncl hpI
  change outer.2.1 z ∈ (inner.dom : Set ℂ) at hpI
  rw [hOC] at hpO
  rw [hIU] at hpI
  exact ⟨hpO.1, fun h => h.elim hpO.2 hpI.2⟩

variable {Ω : Type*} {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **R.6's germ comparison from a joint law** (item 5 of `R6Rel.R6Cert`): two local sets `EC`, `EU`,
hitting-measurable for the marks of a history-marked local set `E₀` that they cover, with unbounded lower-union
components and local-set means `gC`, `gU`. Almost surely, for all harmonic representatives `v` of `gC` and `vI` of
`gU`, all conformal charts `outer ⊇ inner` with domains `ℍ ∖ EC`, `ℍ ∖ EU`, every collar point `ξ` of the transition
whose outer inverse lands at a point `p` where the two sets agree locally, `vI − v → 0` at `ξ` in outer coordinates. -/
theorem ae_r6Germ_of_joint [IsProbabilityMeasure P] (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {E₀ EC EU : Ω → Set ℂ} (hJoint : WholeField.IsHistoryAvoidanceLocal ℳ E₀ h P)
    (hCℳ : Measurable[ℳ, hittingSigma] EC) (hUℳ : Measurable[ℳ, hittingSigma] EU)
    (hcov : ∀ᵐ ω ∂P, E₀ ω ⊆ EC ω ∪ EU ω)
    (hCm : Measurable[mΩ, hittingSigma] EC) (hUm : Measurable[mΩ, hittingSigma] EU)
    (hCloc : IsLocalSet EC h P) (hUloc : IsLocalSet EU h P)
    (hCunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (EC ω), ¬ IsBounded (connectedComponentIn (lowerUnion (EC ω)) z))
    (hUunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (EU ω), ¬ IsBounded (connectedComponentIn (lowerUnion (EU ω)) z))
    {gC gU : Ω → DistOn upperHalfPlaneOpens} (hgC : IsLocalSetMean EC h P gC)
    (hgU : IsLocalSetMean EU h P gU) :
    ∀ᵐ ω ∂P, ∀ v vI : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ EC ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EC ω → gC ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd vI (H \ EU ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EU ω → gU ω φ = ∫ z, vI z * φ z) →
      ∀ outer inner : Chart, outer.IsConformal → inner.IsConformal → (inner.dom : Set ℂ) ⊆ outer.dom →
        (outer.dom : Set ℂ) = H \ EC ω → (inner.dom : Set ℂ) = H \ EU ω →
        ∀ (p : ℂ) (ξ r : ℝ), p ∈ EC ω ∪ {z : ℂ | z.im = 0} → p ∈ EU ω ∪ {z : ℂ | z.im = 0} →
          (∃ ε > 0, EU ω ∩ ball p ε ⊆ EC ω) → (∃ ε > 0, EC ω ∩ ball p ε ⊆ EU ω) → 0 < r →
          H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ) →
          Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → R6Rel.R6Germ outer v vI ξ := by
  have hpair := isHistoryAvoidanceLocal_pair_of_joint hJoint hCℳ hUℳ hcov
  filter_upwards [ae_tendsto_sub_of_marked_union hh hCm hUm hCloc hUloc hpair hCunb hUunb hgC hgU] with
    ω hω v vI hv hvr hvI hvIr outer inner hO hI hIncl hOC hIU p ξ r hpC hpU hUC hCU hr hCollar hLanding
  have hsub := hω v vI hv hvr hvI hvIr p hpC hpU hUC hCU
  have happ := tendsto_inverse_compl_union hO hI hIncl hOC hIU hr hCollar hLanding
  have hneg := (hsub.comp happ).neg
  simp only [neg_zero] at hneg
  refine hneg.congr fun z => ?_
  simp only [Function.comp_apply, neg_sub]

end InteractingSLE.Sec7.R6Cert
