/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainActual

/-!
# Actual fixed original-time references are local sets with mean versions

PROVE-POCKET-SIDEIN. Repeating the same fixed candidate in the pair theorem
produces its individual law. The existing regularity equivalence and mean
existence theorem then supply the local-set and mean inputs.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ LocalSets WholeField WangWu

/-- Each candidate retains its own event and normalization. Its individual
locality and a version of its actual conditional mean are conclusions. -/
theorem local_facts_at_original_time {Ω : Type} [mΩ : MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hj : j.Ready d)
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
    (hCont : ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure) (q : ℝ≥0) :
    let E := eventFilled j.event (j.target i d).domain (fun ω => regHull d.driver d.lifetime q ω)
    Measurable[mΩ, hittingSigma] E ∧
      IsLocalSet E (centredField d.translatedField d.coupledMean) d.measure ∧
      ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean E (centredField d.translatedField d.coupledMean) d.measure g := by
  let F : Ω → Set ℂ := fun ω => regHull d.driver d.lifetime q ω
  let E : Ω → Set ℂ := eventFilled j.event (j.target i d).domain F
  have hPair := pair_marked_law_at_original_time hj hj hTransport hTranslate hu hh hCoupling hu'
    hKilled hLife hCont hStart hMeas hDetermined hLocal q
  have hLaw : IsHistoryAvoidanceLocal (MeasurableSpace.comap E hittingSigma) E
      (centredField d.translatedField d.coupledMean) d.measure := by
    simpa only [sup_idem, union_self] using hPair
  have hWalls : (j.target i d).walls ≤ mΩ := by
    rw [target_walls]
    exact wallsSigma_le (hMeas 0) (hMeas 1)
  have hEvent : MeasurableSet j.event := by
    apply hWalls
    rw [target_walls]
    obtain ⟨-, -, -, -, -, -, -, hEvent, -⟩ := hj
    exact hEvent
  have hF : Measurable[mΩ, hittingSigma] F := measurable_regHull hKilled measurable_const
  have hE : Measurable[mΩ, hittingSigma] E :=
    measurable_eventFilled_of_ready hj (hCont 0) (hCont 1) hWalls hEvent
      (by rw [target_event]) hF
  have hh' : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField d.translatedField d.coupledMean) d.measure :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData
      ⟨hCoupling.2.1, hCoupling.2.2.1⟩ hu'
  have hReg : ∀ ω, E ω ⊆ H ∧ IsOpen (H \ E ω) :=
    eventFilled_regular (fun ω hω => isOpen_domain hj ω (by rwa [target_event]))
      (fun ω _ => QuantumZipper.FwdHolo.isOpen_compl_fwdHull
        ((continuous_regDrv d.driver d.lifetime ω).comp continuous_real_toNNReal) q.coe_nonneg)
  have hLoc : IsLocalSet E (centredField d.translatedField d.coupledMean) d.measure :=
    ((isLocalSet_tfae hh' hE (Eventually.of_forall hReg)).out 1 4).1
      (IsHistoryAvoidanceLocal.isAvoidanceLocal hLaw)
  exact ⟨hE, hLoc, IsLocalSet.exists_isLocalSetMean hh' hE hLoc⟩

end InteractingSLE.Wire.Current.SideTest
