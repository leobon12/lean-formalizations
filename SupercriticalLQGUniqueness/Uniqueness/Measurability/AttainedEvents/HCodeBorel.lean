import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.PathDiameter
import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.EndpointLoopBorel




 


set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

abbrev HInput := (LSCMetric × LSCMetric) × ((Measurability.GeodesicCodes.Path × (ℂ × ℂ)) × ℝ)

private def hGeoMap (swap : Bool) (p : HInput) : Measurability.GeodesicCodes.GeoInput :=
  (if swap then p.1.2 else p.1.1, p.2.1)

private theorem hGeoMap_measurable (swap : Bool) : Measurable (hGeoMap swap) := by
  have hD : Measurable (fun p : HInput => if swap then p.1.2 else p.1.1) := by
    cases swap with
    | false => exact measurable_fst.comp measurable_fst
    | true => exact measurable_snd.comp measurable_fst
  have hw : Measurable (fun p : HInput => p.2.1) :=
    measurable_fst.comp measurable_snd
  exact hD.prodMk hw

private theorem hPath_measurable : Measurable (fun p : HInput => p.2.1.1) :=
  measurable_fst.comp (measurable_fst.comp measurable_snd)

private theorem hU_measurable : Measurable (fun p : HInput => p.2.1.2.1) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_fst.comp measurable_snd))

private theorem hV_measurable : Measurable (fun p : HInput => p.2.1.2.2) :=
  measurable_snd.comp (measurable_snd.comp
    (measurable_fst.comp measurable_snd))

private theorem hC_measurable : Measurable (fun p : HInput => p.2.2) :=
  measurable_snd.comp measurable_snd

private def hPairMap (swap : Bool) (p : HInput) : LSCMetric × (ℂ × ℂ) :=
  (if swap then p.1.2 else p.1.1, (p.2.1.2.1, p.2.1.2.2))

private theorem hPairMap_measurable (swap : Bool) : Measurable (hPairMap swap) := by
  have hD : Measurable (fun p : HInput => if swap then p.1.2 else p.1.1) := by
    cases swap with
    | false => exact measurable_fst.comp measurable_fst
    | true => exact measurable_snd.comp measurable_fst
  exact hD.prodMk (hU_measurable.prodMk hV_measurable)

private theorem hDistance_measurable (swap : Bool) :
    Measurable (fun p : HInput =>
      (if swap then p.1.2 else p.1.1) (p.2.1.2.1, p.2.1.2.2)) := by
  let f : LSCMetric × (ℂ × ℂ) → ENNReal := fun q => q.1 q.2
  have hf : Measurable f := TwoScale.S36Events.jointEval_lsc.measurable
  have hc : Measurable (hPairMap swap) := hPairMap_measurable swap
  have hcomp : Measurable (f ∘ hPairMap swap) := hf.comp hc
  exact hcomp

private def hLoopMap (swap atV : Bool) (p : HInput) : LoopGeoInput :=
  (if swap then p.1.2 else p.1.1,
    ((p.2.1.2.1, p.2.1.2.2), if atV then p.2.1.2.2 else p.2.1.2.1))

private theorem hLoopMap_measurable (swap atV : Bool) :
    Measurable (hLoopMap swap atV) := by
  have hD : Measurable (fun p : HInput => if swap then p.1.2 else p.1.1) := by
    cases swap with
    | false => exact measurable_fst.comp measurable_fst
    | true => exact measurable_snd.comp measurable_fst
  have hx : Measurable (fun p : HInput =>
      if atV then p.2.1.2.2 else p.2.1.2.1) := by
    cases atV with
    | false => exact hU_measurable
    | true => exact hV_measurable
  exact hD.prodMk ((hU_measurable.prodMk hV_measurable).prodMk hx)

private theorem hGeoTrace_measurable (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (swap : Bool) :
    MeasurableSet {p : HInput | Measurability.GeodesicCodes.GeoCode (hGeoMap swap p) ∧
      MapsTo p.2.1.1 Set.univ
        (Metric.closedBall (0 : ℂ) (r : ℝ) \ Metric.ball 0 ((a : ℝ) * r)) ∧
      p.2.1.2.1 ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * r) ∧
      p.2.1.2.2 ∈ Metric.sphere (0 : ℂ) (r : ℝ)} := by
  have hK : IsClosed (Metric.closedBall (0 : ℂ) (r : ℝ) \
      Metric.ball 0 ((a : ℝ) * r)) :=
    Metric.isClosed_closedBall.inter Metric.isOpen_ball.isClosed_compl
  exact (Measurability.GeodesicCodes.geoTraceCode_borel hK Metric.isClosed_sphere Metric.isClosed_sphere).preimage
    (hGeoMap_measurable swap)

private theorem hDiameter_measurable (r : Set.Ioi (0 : ℝ)) :
    MeasurableSet {p : HInput |
      Metric.diam (Set.range p.2.1.1) ≤ (r : ℝ) / 100} := by
  have hr : 0 ≤ (r : ℝ) / 100 := le_of_lt (div_pos r.property (by norm_num))
  exact (pathDiameter_measurable ((r : ℝ) / 100) hr).preimage
    hPath_measurable

private theorem hComparison_measurable (C : Set.Ioi (0 : ℝ)) (swap : Bool) :
    MeasurableSet {p : HInput |
      if swap then
        p.1.2 (p.2.1.2.1, p.2.1.2.2) ≤
          ENNReal.ofReal (C : ℝ) * p.1.1 (p.2.1.2.1, p.2.1.2.2)
      else
        ENNReal.ofReal (C : ℝ) * p.1.1 (p.2.1.2.1, p.2.1.2.2) ≤
          p.1.2 (p.2.1.2.1, p.2.1.2.2)} := by
  cases swap with
  | false =>
      exact measurableSet_le (measurable_const.mul (hDistance_measurable false))
        (hDistance_measurable true)
  | true =>
      exact measurableSet_le (hDistance_measurable true)
        (measurable_const.mul (hDistance_measurable false))

private theorem hCircleBound_measurable (ξ Q : ℝ)
    (r : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1) (swap : Bool) :
    MeasurableSet {p : HInput |
      (if swap then p.1.2 else p.1.1) (p.2.1.2.1, p.2.1.2.2) ≤
        ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) *
          Real.exp (ξ * p.2.2))} := by
  have hleft := hDistance_measurable swap
  have hr : Measurable (fun p : HInput =>
      (1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * p.2.2)) := by
    fun_prop
  exact measurableSet_le hleft (ENNReal.measurable_ofReal.comp hr)

private theorem hLoops_measurable (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ))
    (swap : Bool) :
    MeasurableSet {p : HInput |
      (if swap then p.1.2 else p.1.1) (p.2.1.2.1, p.2.1.2.2) ≠ ⊤ ∧
      OptimalConstants.Ratios.EndpointLoop (if swap then p.1.2 else p.1.1) r a θ
        p.2.1.2.1 p.2.1.2.2 p.2.1.2.1 ∧
      OptimalConstants.Ratios.EndpointLoop (if swap then p.1.2 else p.1.1) r a θ
        p.2.1.2.1 p.2.1.2.2 p.2.1.2.2} := by
  have hu := (endpointLoopFinite_measurable r a θ).preimage
    (hLoopMap_measurable swap false)
  have hv := (endpointLoopFinite_measurable r a θ).preimage
    (hLoopMap_measurable swap true)
  convert hu.inter hv using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
    hLoopMap, ite_true]
  tauto

def HCode (ξ Q : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ))
    (swap : Bool) (p : HInput) : Prop :=
  Measurability.GeodesicCodes.GeoCode (hGeoMap swap p) ∧
    MapsTo p.2.1.1 Set.univ
      (Metric.closedBall (0 : ℂ) (r : ℝ) \ Metric.ball 0 ((a : ℝ) * r)) ∧
    p.2.1.2.1 ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * r) ∧
    p.2.1.2.2 ∈ Metric.sphere (0 : ℂ) (r : ℝ) ∧
    Metric.diam (Set.range p.2.1.1) ≤ (r : ℝ) / 100 ∧
    (if swap then
        p.1.2 (p.2.1.2.1, p.2.1.2.2) ≤
          ENNReal.ofReal (C : ℝ) * p.1.1 (p.2.1.2.1, p.2.1.2.2)
      else
        ENNReal.ofReal (C : ℝ) * p.1.1 (p.2.1.2.1, p.2.1.2.2) ≤
          p.1.2 (p.2.1.2.1, p.2.1.2.2)) ∧
    (if swap then p.1.2 else p.1.1) (p.2.1.2.1, p.2.1.2.2) ≤
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) *
        Real.exp (ξ * p.2.2)) ∧
    (if swap then p.1.2 else p.1.1) (p.2.1.2.1, p.2.1.2.2) ≠ ⊤ ∧
    OptimalConstants.Ratios.EndpointLoop (if swap then p.1.2 else p.1.1) r a θ
      p.2.1.2.1 p.2.1.2.2 p.2.1.2.1 ∧
    OptimalConstants.Ratios.EndpointLoop (if swap then p.1.2 else p.1.1) r a θ
      p.2.1.2.1 p.2.1.2.2 p.2.1.2.2

theorem hCode_measurable (ξ Q : ℝ) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (C θ : Set.Ioi (0 : ℝ))
    (swap : Bool) :
    MeasurableSet {p : HInput | HCode ξ Q r a C θ swap p} := by
  have hgeo := hGeoTrace_measurable r a swap
  have hdiam := hDiameter_measurable r
  have hcomp := hComparison_measurable C swap
  have hbound := hCircleBound_measurable ξ Q r a swap
  have hloops := hLoops_measurable r a θ swap
  convert (((hgeo.inter hdiam).inter hcomp).inter hbound).inter hloops using 1
  ext p
  simp only [HCode, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
