/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainGerm

/-!
# The actual original-time R.5 germ comparison from the ambient coupling

PROVE-POCKET-SIDEIN. This assembly constructs both mean versions and all
marked-law, locality and complementary-component inputs. Its good event is
uniform over charts and accesses. The remaining geometric inputs are the
physical shared initial neighborhood and the current shared collar.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ LocalSets WholeField WangWu

/-- The R.5 physical germ comparison for fixed actual candidates at a fixed
original time, with all its field-law inputs produced internally. -/
theorem exists_original_time_germ_comparison {Ω : Type} [mΩ : MeasurableSpace Ω]
    {outer inner : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hOuter : outer.Ready d) (hInner : inner.Ready d)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ j ω, Continuous (pairWallFamily outer inner d j ω))
    (hStart : ∀ j ω, pairWallFamily outer inner d j ω 0 = 0)
    (hMeas : ∀ j t, Measurable fun ω => pairWallFamily outer inner d j ω t)
    (hDetermined : ∀ j t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily outer inner d j ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j, Sec6.IsEntranceHistoryLocal (pairWallFamily outer inner d j)
      (centredField d.field d.originalMean) d.measure) (q : ℝ≥0) :
    let F := fun ω => regHull d.driver d.lifetime q ω
    let C := (outer.target i d).domain
    let U := (inner.target i d).domain
    let EC := eventFilled outer.event C F
    let EU := eventFilled inner.event U F
    ∃ gC gU : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean EC (centredField d.translatedField d.coupledMean) d.measure gC ∧
      IsLocalSetMean EU (centredField d.translatedField d.coupledMean) d.measure gU ∧
      ∀ᵐ ω ∂d.measure, ω ∈ outer.event → ω ∈ inner.event → ∀ vC vU : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vC (H \ EC ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EC ω →
        gC ω φ = ∫ z, vC z * φ z) →
      InnerProductSpace.HarmonicOnNhd vU (H \ EU ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EU ω →
        gU ω φ = ∫ z, vU z * φ z) → ∀ cC cU : Chart,
      cC.IsConformal → cU.IsConformal → (cU.dom : Set ℂ) ⊆ cC.dom →
      (cC.dom : Set ℂ) = C ω ∩ (H \ F ω) →
      (cU.dom : Set ℂ) = U ω ∩ (H \ F ω) → ∀ (p : ℂ) (ξ r : ℝ),
      (∃ ε > 0, C ω ∩ ball p ε = U ω ∩ ball p ε) → 0 < r →
      H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart cC cU).dom : Set ℂ) →
      Tendsto cC.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
      Tendsto (fun z => vU (cC.2.1 z) - vC (cC.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  let idxO : Fin 3 → Fin 3 := ![0, 1, 1]
  let idxI : Fin 3 → Fin 3 := ![0, 2, 2]
  have hOEq (k : Fin 3) : pairWallFamily outer outer d k =
      pairWallFamily outer inner d (idxO k) := by fin_cases k <;> rfl
  have hIEq (k : Fin 3) : pairWallFamily inner inner d k =
      pairWallFamily outer inner d (idxI k) := by fin_cases k <;> rfl
  have hFactsO := local_facts_at_original_time hOuter hTransport hTranslate hu hh hCoupling hu'
    hKilled hLife
    (by intro k ω; rw [hOEq]; exact hCont _ ω)
    (by intro k ω; rw [hOEq]; exact hStart _ ω)
    (by intro k t; rw [hOEq]; exact hMeas _ t)
    (by intro k t; rw [hOEq]; exact hDetermined _ t)
    (by intro k; rw [hOEq]; exact hLocal _) q
  have hFactsI := local_facts_at_original_time hInner hTransport hTranslate hu hh hCoupling hu'
    hKilled hLife
    (by intro k ω; rw [hIEq]; exact hCont _ ω)
    (by intro k ω; rw [hIEq]; exact hStart _ ω)
    (by intro k t; rw [hIEq]; exact hMeas _ t)
    (by intro k t; rw [hIEq]; exact hDetermined _ t)
    (by intro k; rw [hIEq]; exact hLocal _) q
  obtain ⟨hCm, hCloc, gC, hgC⟩ := hFactsO
  obtain ⟨hUm, hUloc, gU, hgU⟩ := hFactsI
  have hh' : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField d.translatedField d.coupledMean) d.measure :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData
      ⟨hCoupling.2.1, hCoupling.2.2.1⟩ hu'
  have hPair := pair_marked_law_at_original_time hOuter hInner hTransport hTranslate hu hh hCoupling hu'
    hKilled hLife hCont hStart hMeas hDetermined hLocal q
  have hCunb := (ae_eventFilled_unbounded_components hOuter (hCont 0) (hCont 1) hCoupling hLife).mono
    (fun _ hω => hω q)
  have hUunb := (ae_eventFilled_unbounded_components hInner (hCont 0) (hCont 2) hCoupling hLife).mono
    (fun _ hω => hω q)
  exact ⟨gC, gU, hgC, hgU, ae_germ_of_separate_candidate_laws hh' hCm hUm hCloc hUloc
    hPair hCunb hUunb hgC hgU⟩

end InteractingSLE.Wire.Current.SideTest
