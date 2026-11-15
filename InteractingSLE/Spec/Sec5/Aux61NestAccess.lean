/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NestGauss
import InteractingSLE.Spec.Sec5.Aux61GInstAccessLocal

/-!
# Nested chart decompositions for the completed-access fibre code

Packet PROVE-AUX61-NEST. Specialize the marked chart construction to GLUEINST's
`accessExitCode`, whose finite landing is completed before taking its window
exit. The field, chart and measurability premises are discharged by the landed
restart-code API.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Nest

open Aux61FibK (codeFiltration)
open Aux61FibData (IsRestartSpec IsMeasChart chartOf)
open Aux61GInst (HasAccessLanding accessExitCode)
open Aux61ChLoc (IsChartGaussAt liveEv liveSet)
open Aux61UnionK (chartHull)
open LocalSets (germSigma)
open WholeField (IsHistoryAvoidanceLocal centredField)

universe u

variable {X : Type u} {ℋ₀ ℋ : MeasurableSpace X} [mX : MeasurableSpace X]
  {β : Type*} [mβ : MeasurableSpace β]

/-- The two nested decompositions for GLUEINST's selected-access restart code.
In addition to the two physical marked local sets, the caller supplies their
recorded inclusion and measurability of the initial set from the initial marks. -/
theorem exists_isChartGaussAt_pair_accessExit
    {μ : Measure X} [IsProbabilityMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) {Er : Set X} {c : X → Chart}
    {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ} {a k : ℝ}
    (hs : IsRestartSpec Er c ρ T) (hVo : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding Er c ρ T V)
    (hinj : ∀ x ∈ Er, InjOn (ρ x) {r | (r : ℝ≥0∞) < T x})
    (hliftc : ∀ x ∈ Er, ContinuousOn (c x).2.2 (c x).dom)
    (hlift : ∀ x ∈ Er, InnerProductSpace.HarmonicOnNhd (c x).2.2 (c x).dom)
    {h : X → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ) (q : ℝ≥0)
    (hℋ : ℋ ≤ mX) (hℋ₀ : ℋ₀ ≤ ℋ) (hZ₀ : mβ.comap Z ≤ ℋ₀)
    (hY₀ : (codeFiltration.{u} 0).comap
      (fun x => ULift.up.{u} (accessExitCode Er c ρ T V a k h x)) ≤ ℋ₀)
    (hYq : (codeFiltration.{u} q).comap
      (fun x => ULift.up.{u} (accessExitCode Er c ρ T V a k h x)) ≤ ℋ)
    (hE₀ : MeasurableSet[ℋ₀] Er) (hc₀ : @IsMeasChart X ℋ₀ c)
    {A₀ A : X → Set ℂ} (hA₀m : Measurable[ℋ₀, hittingSigma] A₀)
    (hAm : Measurable[mX, hittingSigma] A)
    (hA₀c : ∀ x, A₀ x ⊆ H ∧ IsOpen (H \ A₀ x))
    (hAc : ∀ x, A x ⊆ H ∧ IsOpen (H \ A x)) (hAA : ∀ x, A₀ x ⊆ A x)
    (hloc₀ : IsHistoryAvoidanceLocal ℋ₀ A₀ (centredField h u₀) μ)
    (hloc : IsHistoryAvoidanceLocal ℋ A (centredField h u₀) μ)
    (hgeo₀ : ∀ᵐ x ∂μ, Z x ∈ B →
      ((0 : ℝ≥0) : ℝ≥0∞) < (accessExitCode Er c ρ T V a k h x).life →
      H \ A₀ x = (c x).2.1 '' (H \ chartHull (accessExitCode Er c ρ T V a k h) 0 x))
    (hgeo : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (accessExitCode Er c ρ T V a k h x).life →
      H \ A x = (c x).2.1 '' (H \ chartHull (accessExitCode Er c ρ T V a k h) q x)) :
    ∃ h₀ hq : X → DistOn upperHalfPlaneOpens,
      IsChartGaussAt μ Z B (accessExitCode Er c ρ T V a k h) 0
        (germSigma (liveSet (liveEv Z B (accessExitCode Er c ρ T V a k h) 0) A₀)
          (centredField h u₀) ⊔ ℋ₀) h₀ ∧
      IsChartGaussAt μ Z B (accessExitCode Er c ρ T V a k h) q
        (germSigma (liveSet (liveEv Z B (accessExitCode Er c ρ T V a k h) q) A)
          (centredField h u₀) ⊔
          (ℋ ⊔ germSigma (liveSet (liveEv Z B (accessExitCode Er c ρ T V a k h) 0) A₀)
            (centredField h u₀))) hq ∧
      germSigma (liveSet (liveEv Z B (accessExitCode Er c ρ T V a k h) 0) A₀)
          (centredField h u₀) ⊔ ℋ₀ ≤
        germSigma (liveSet (liveEv Z B (accessExitCode Er c ρ T V a k h) q) A)
          (centredField h u₀) ⊔
          (ℋ ⊔ germSigma (liveSet (liveEv Z B (accessExitCode Er c ρ T V a k h) 0) A₀)
            (centredField h u₀)) := by
  have hcm := @IsMeasChart.chartOf X ℋ₀ Er hE₀ c hc₀
  refine exists_isChartGaussAt_pair_of_marked hB
    (Aux61GInst.measurable_accessExitCode hs hVo hV0 hland hinj hliftc hhm) q hhm hu₀ hh0
    (Aux61FibData.isConformal_chartOf hs.conf) a k
    (fun x _ hq => Aux61GInst.accessExitCode_field_eq hs.conf
      (Aux61GInst.mem_exitEv_of_lt_accessLife hq)) hℋ hℋ₀ hZ₀ hY₀ hYq
    (@IsMeasChart.dom X ℋ₀ _ hcm) (@IsMeasChart.fwd X ℋ₀ _ hcm)
    (@IsMeasChart.lift X ℋ₀ _ hcm) (Aux61ChLoc.continuousOn_lift_chartOf hliftc)
    (Aux61ChLoc.harmonicOnNhd_lift_chartOf hlift) hA₀m hAm hA₀c hAc hAA hloc₀ hloc ?_ ?_
  · filter_upwards [hgeo₀] with x hx hxB hxq
    rw [Aux61FibData.chartOf_of_mem (Aux61GInst.mem_exitEv_of_lt_accessLife hxq).1.1]
    exact hx hxB hxq
  · filter_upwards [hgeo] with x hx hxB hxq
    rw [Aux61FibData.chartOf_of_mem (Aux61GInst.mem_exitEv_of_lt_accessLife hxq).1.1]
    exact hx hxB hxq

end InteractingSLE.Sec5.Aux61Nest
