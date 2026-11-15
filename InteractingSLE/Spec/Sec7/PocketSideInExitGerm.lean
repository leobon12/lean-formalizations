/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInExitLog
import InteractingSLE.Spec.Sec7.PocketSideInRealGerm

/-!
# The current real landing supplies the germ comparison's boundary membership

PROVE-POCKET-SIDEIN. A finite real inverse landing cannot be in the current
open domain. Its nonnegative imaginary part then puts it in the filled set
or on the real line. This removes a physical-point premise from the joint
marked germ comparison.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketUnionPt

/-- Every finite current real inverse landing is a point where the filled
set germ theorem applies: in the filled set or on the real boundary. -/
theorem inverse_real_landing_mem_filled_or_real {c : Chart} (hc : c.IsConformal)
    {C F : Set ℂ} (hDomain : (c.dom : Set ℂ) = C ∩ (H \ F)) {x : ℝ} {p : ℂ}
    (hLanding : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) :
    p ∈ extHullSet C F ∪ {z : ℂ | z.im = 0} := by
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  have hbar : p ∈ Hbar := QuantumZipper.isClosed_Hbar.mem_of_tendsto hLanding
    (eventually_nhdsWithin_of_forall fun _ hz => QuantumZipper.H_subset_Hbar (hc.2.1 hz))
  have hnot : p ∉ (c.dom : Set ℂ) := inverse_real_landing_notMem_dom hc hLanding
  rw [hDomain] at hnot
  by_cases hpH : p ∈ H
  · by_cases hpC : p ∈ C
    · have hpF : p ∈ F := by
        by_contra hpF
        exact hnot ⟨hpC, hpH, hpF⟩
      exact Or.inl ⟨hpH, Or.inr hpF⟩
    · exact Or.inl ⟨hpH, Or.inl hpC⟩
  · exact Or.inr (le_antisymm (le_of_not_gt hpH) hbar)

/-- The marked comparison at a shared neighborhood needs no additional
boundary membership premise for the physical landing. The good event is
still uniform before selection of the charts, access and physical point. -/
theorem ae_current_germ_of_shared_neighborhood_and_landing {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {C U F : Ω → Set ℂ}
    (hCm : Measurable[mΩ, hittingSigma] (fun ω => extHullSet (C ω) (F ω)))
    (hUm : Measurable[mΩ, hittingSigma] (fun ω => extHullSet (U ω) (F ω)))
    (hCloc : IsLocalSet (fun ω => extHullSet (C ω) (F ω)) h P)
    (hUloc : IsLocalSet (fun ω => extHullSet (U ω) (F ω)) h P)
    (hPairMarked : WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (fun ω => extHullSet (C ω) (F ω)) hittingSigma ⊔
        MeasurableSpace.comap (fun ω => extHullSet (U ω) (F ω)) hittingSigma)
      (fun ω => extHullSet (C ω) (F ω) ∪ extHullSet (U ω) (F ω)) h P)
    (hCunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (extHullSet (C ω) (F ω)),
      ¬ IsBounded (connectedComponentIn (lowerUnion (extHullSet (C ω) (F ω))) z))
    (hUunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (extHullSet (U ω) (F ω)),
      ¬ IsBounded (connectedComponentIn (lowerUnion (extHullSet (U ω) (F ω))) z))
    {gC gU : Ω → DistOn upperHalfPlaneOpens}
    (hgC : IsLocalSetMean (fun ω => extHullSet (C ω) (F ω)) h P gC)
    (hgU : IsLocalSetMean (fun ω => extHullSet (U ω) (F ω)) h P gU) :
    ∀ᵐ ω ∂P, ∀ vC vU : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vC (H \ extHullSet (C ω) (F ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ extHullSet (C ω) (F ω) →
        gC ω φ = ∫ z, vC z * φ z) →
      InnerProductSpace.HarmonicOnNhd vU (H \ extHullSet (U ω) (F ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ extHullSet (U ω) (F ω) →
        gU ω φ = ∫ z, vU z * φ z) → ∀ outer inner : Chart,
      outer.IsConformal → inner.IsConformal → (inner.dom : Set ℂ) ⊆ outer.dom →
      (outer.dom : Set ℂ) = C ω ∩ (H \ F ω) →
      (inner.dom : Set ℂ) = U ω ∩ (H \ F ω) → ∀ (p : ℂ) (ξ r : ℝ),
      (∃ ε > 0, C ω ∩ ball p ε = U ω ∩ ball p ε) → 0 < r →
      H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ) →
      Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
      Tendsto (fun z => vU (outer.2.1 z) - vC (outer.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  filter_upwards [ae_current_germ_of_shared_pocket_neighborhood hh hCm hUm hCloc hUloc
    hPairMarked hCunb hUunb hgC hgU] with ω hcompare
  intro vC vU hvC hrepC hvU hrepU outer inner hO hI hIncl hOC hIC p ξ r hLocal hr hCollar hLanding
  exact hcompare vC vU hvC hrepC hvU hrepU outer inner hO hI hIncl hOC hIC p ξ r
    (inverse_real_landing_mem_filled_or_real hO hOC hLanding) hLocal hr hCollar hLanding

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketUnionPt Sec7.PocketStop Sec7.PocketStopField Sec7.PocketTraversal

variable {Ω : Type} [MeasurableSpace Ω]

/-- The canonical actual original-visit landing automatically satisfies
the filled-set-or-real membership needed by the incoming germ comparison. -/
theorem currentVisitLanding_mem_filled_or_real {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) (x : ℝ) :
    j.currentVisitLanding i d ω t x ∈
      extHullSet ((j.target i d).domain ω)
        (QuantumZipper.fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t) ∪ {z : ℂ | z.im = 0} :=
  inverse_real_landing_mem_filled_or_real
    (isDomainChart_relChart_visitCapacity hj hRc hLc hω ht hvisit).1
    (relChart_dom_visitCapacity hj hRc hLc hω ht hvisit)
    (tendsto_currentVisitLanding hj hRc hLc hω ht hvisit x)

end InteractingSLE.Wire.Current.SideTest
