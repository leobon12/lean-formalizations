/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainSingle
import InteractingSLE.Spec.Jordan.Coupling

/-!
# Unbounded complementary components of the actual original-time references

PROVE-POCKET-SIDEIN. The ambient Loewner domain is simply connected.
The existing filling theorem passes its complementary-component property
to each initial pocket. All original times share the same good event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Bornology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketStopWallsFin

/-- The actual regularized ambient hull has no bounded complementary
component, simultaneously at every original time. -/
theorem ae_original_hull_unbounded_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hLife : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∀ q : ℝ≥0, ∀ p ∈ lowerUnion (regHull W ζ q ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (regHull W ζ q ω)) p) := by
  filter_upwards [hC.1.2.2.2.2, hLife, ae_regHull_eq hC hLife] with ω hp hl hHull q
  have hc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
  have hUniv : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} = univ := by
    ext s
    simp only [hl, ENNReal.coe_lt_top, mem_ofPred_eq, mem_univ]
  rw [hUniv] at hc
  have hW : Continuous (fun s : ℝ => W s.toNNReal ω) :=
    (continuousOn_univ.1 hc).comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simpa using hp.1
  have hChart := isDomainChart_loewner hW hW0 q.coe_nonneg
  rw [hHull q]
  exact not_isBounded_lowerUnion_of_chart hChart.1 hChart.coe_dom.symm

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWallsFin LocalSets

/-- Both shapes of actual fixed-time pocket reference satisfy the germ
theorem's component hypothesis. No separate unboundedness input remains. -/
theorem ae_eventFilled_unbounded_components {Ω : Type} [mΩ : MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} [IsProbabilityMeasure d.measure]
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤) :
    ∀ᵐ ω ∂d.measure, ∀ q : ℝ≥0,
      ∀ p ∈ lowerUnion (eventFilled j.event (j.target i d).domain
        (fun ω => regHull d.driver d.lifetime q ω) ω),
        ¬ IsBounded (connectedComponentIn
          (lowerUnion (eventFilled j.event (j.target i d).domain
            (fun ω => regHull d.driver d.lifetime q ω) ω)) p) := by
  filter_upwards [ae_original_hull_unbounded_components hC hLife] with ω hHull q
  by_cases hω : ω ∈ j.event
  · rw [eventFilled, ite_eq_left hω]
    have hEvent : ω ∈ (j.target i d).event := by rwa [target_event]
    have hChart := (isPocketChartOn hj hRc hLc).1 ω hEvent
    have hSC : IsSimplyConnected ((j.target i d).domain ω) := by
      rw [← hChart.2.1]
      exact isSimplyConnected_of_isConformalBijection QuantumZipper.isOpen_H
        hChart.1.isConformalBijection isSimplyConnected_H
    exact not_isBounded_lowerUnion_extHullSet (isOpen_domain hj ω hEvent) hSC (hHull q)
  · rw [eventFilled, ite_eq_right hω]
    have hH : lowerUnion H = univ := by
      ext z
      simp only [lowerUnion, H, mem_union, mem_ofPred_eq, mem_univ, iff_true]
      exact lt_or_ge 0 z.im
    rw [hH]
    intro p _
    rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
    exact NormedSpace.unbounded_univ ℝ ℂ

end InteractingSLE.Wire.Current.SideTest
