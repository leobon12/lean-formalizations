import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.E5LoopScalar
import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.PathDiameter




 


set_option autoImplicit false
noncomputable section

open Set
open SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

abbrev E5Input := (LSCMetric × LSCMetric) × ((Measurability.GeodesicCodes.Path × (ℂ × ℂ)) × ℝ)

def e5Region (z : ℂ) (r a : ℝ) : Set ℂ :=
  Metric.closedBall z r \ Metric.ball z (a * r)

theorem e5Region_closed (z : ℂ) (r a : ℝ) :
    IsClosed (e5Region z r a) := by
  unfold e5Region
  exact Metric.isClosed_closedBall.sdiff Metric.isOpen_ball

 

def E5BadCode (ξ Qpar : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (C θ : Ioi (0 : ℝ)) (Cminus Cplus : ℝ) (p : E5Input) : Prop :=
  let D := p.1.1
  let D' := p.1.2
  let P := p.2.1.1
  let u := p.2.1.2.1
  let v := p.2.1.2.2
  let c := p.2.2
  u ∈ Metric.sphere z ((a : ℝ) * r) ∧
  v ∈ Metric.sphere z r ∧
  dist u v ≤ (q : ℝ) * r ∧
  TwoScale.Consolidated.loopF D v r q ≤ ENNReal.ofReal (Cminus / (2 * Cplus)) *
    OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) ∧
  Measurability.GeodesicCodes.GeoCode (D, (P, (u, v))) ∧
  (∀ t, P t ∈ e5Region z r a) ∧
  Metric.diam (Set.range P) ≤ (r : ℝ) / 100 ∧
  D (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Qpar) *
    Real.exp (ξ * c)) ∧
  TwoScale.S36Events.EndpointLoopAt D r a θ u v u ∧
  TwoScale.S36Events.EndpointLoopAt D r a θ u v v ∧
  ENNReal.ofReal (C : ℝ) * D (u, v) < D' (u, v)

attribute [local irreducible] E5BadCode

 

theorem e5BadCode_measurable (ξ Qpar : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (C θ : Ioi (0 : ℝ)) (Cminus Cplus : ℝ) :
    MeasurableSet {p : E5Input |
      E5BadCode ξ Qpar z r q a C θ Cminus Cplus p} := by
  let T := E5Input
  have hD : Measurable (fun p : T => p.1.1) := measurable_fst.comp measurable_fst
  have hD' : Measurable (fun p : T => p.1.2) := measurable_snd.comp measurable_fst
  have hP : Measurable (fun p : T => p.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hu : Measurable (fun p : T => p.2.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hv : Measurable (fun p : T => p.2.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hc : Measurable (fun p : T => p.2.2) := measurable_snd.comp measurable_snd
  have hPair : Measurable (fun p : T => (p.2.1.2.1, p.2.1.2.2)) := hu.prodMk hv
  have hCost : Measurable (fun p : T => p.1.1 (p.2.1.2.1, p.2.1.2.2)) :=
    TwoScale.S36Events.jointEval_lsc.measurable.comp (hD.prodMk hPair)
  have hCost' : Measurable (fun p : T => p.1.2 (p.2.1.2.1, p.2.1.2.2)) :=
    TwoScale.S36Events.jointEval_lsc.measurable.comp (hD'.prodMk hPair)
  have hSphereU : MeasurableSet {p : T | p.2.1.2.1 ∈ Metric.sphere z ((a : ℝ) * r)} :=
    Metric.isClosed_sphere.measurableSet.preimage hu
  have hSphereV : MeasurableSet {p : T | p.2.1.2.2 ∈ Metric.sphere z r} :=
    Metric.isClosed_sphere.measurableSet.preimage hv
  have hNear : MeasurableSet {p : T |
      dist p.2.1.2.1 p.2.1.2.2 ≤ (q : ℝ) * r} :=
    measurableSet_le (hu.dist hv) measurable_const
  let f : T → (LSCMetric × ℂ) := fun p => (p.1.1, p.2.1.2.2)
  have hf : Measurable f := hD.prodMk hv
  have hLoop : MeasurableSet {p : T |
      TwoScale.Consolidated.loopF p.1.1 p.2.1.2.2 r q ≤
        ENNReal.ofReal (Cminus / (2 * Cplus)) *
          OptimalConstants.Ratios.setDist p.1.1 (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)} :=
    by
      have hc := (e5AnnulusCondition_measurable z r q Cminus Cplus).preimage hf
      exact hc
  have hGeo : MeasurableSet {p : T |
      Measurability.GeodesicCodes.GeoCode (p.1.1, (p.2.1.1, (p.2.1.2.1, p.2.1.2.2)))} :=
    Measurability.GeodesicCodes.geoCode_borel.preimage (hD.prodMk (hP.prodMk hPair))
  have hTraceSet : MeasurableSet {P : Measurability.GeodesicCodes.Path |
      ∀ t, P t ∈ e5Region z r a} := by
    have h := ContinuousMap.isClosed_setOfPred_mapsTo
      (e5Region_closed z r a) (Set.univ : Set unitInterval)
    simpa only [Set.MapsTo, Set.mem_univ, true_implies] using h.measurableSet
  have hTrace : MeasurableSet {p : T |
      ∀ t, p.2.1.1 t ∈ e5Region z r a} := hTraceSet.preimage hP
  have hDiam : MeasurableSet {p : T |
      Metric.diam (Set.range p.2.1.1) ≤ (r : ℝ) / 100} :=
    (pathDiameter_measurable ((r : ℝ) / 100) (by exact div_nonneg (le_of_lt (show 0 < (r : ℝ) from r.property)) (by norm_num))).preimage hP
  have hUpper : Measurable (fun p : T =>
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Qpar) *
        Real.exp (ξ * p.2.2))) := by
    have hReal : Continuous (fun c : ℝ =>
        (1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Qpar) * Real.exp (ξ * c)) := by fun_prop
    exact (ENNReal.continuous_ofReal.comp hReal).measurable.comp hc
  have hCostUpper : MeasurableSet {p : T |
      p.1.1 (p.2.1.2.1, p.2.1.2.2) ≤
        ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Qpar) *
          Real.exp (ξ * p.2.2))} := measurableSet_le hCost hUpper
  have hLoopU : MeasurableSet {p : T |
      p.1.1 (p.2.1.2.1, p.2.1.2.2) ≠ ⊤ ∧
      TwoScale.S36Events.EndpointLoopAt p.1.1 r a θ p.2.1.2.1 p.2.1.2.2 p.2.1.2.1} :=
    (endpointLoopAtFinite_measurable r q a θ).preimage
      (hD.prodMk (hPair.prodMk hu))
  have hLoopV : MeasurableSet {p : T |
      p.1.1 (p.2.1.2.1, p.2.1.2.2) ≠ ⊤ ∧
      TwoScale.S36Events.EndpointLoopAt p.1.1 r a θ p.2.1.2.1 p.2.1.2.2 p.2.1.2.2} :=
    (endpointLoopAtFinite_measurable r q a θ).preimage
      (hD.prodMk (hPair.prodMk hv))
  have hBad : MeasurableSet {p : T |
      ENNReal.ofReal (C : ℝ) * p.1.1 (p.2.1.2.1, p.2.1.2.2) <
        p.1.2 (p.2.1.2.1, p.2.1.2.2)} :=
    measurableSet_lt (measurable_const.mul hCost) hCost'
  have hAll := (((((((((hSphereU.inter hSphereV).inter hNear).inter hLoop).inter
    hGeo).inter hTrace).inter hDiam).inter hCostUpper).inter hLoopU).inter hLoopV).inter hBad
  have hEq : {p : T | E5BadCode ξ Qpar z r q a C θ Cminus Cplus p} =
      (((((((((({p : T | p.2.1.2.1 ∈ Metric.sphere z ((a : ℝ) * r)} ∩
        {p : T | p.2.1.2.2 ∈ Metric.sphere z r}) ∩
        {p : T | dist p.2.1.2.1 p.2.1.2.2 ≤ (q : ℝ) * r}) ∩
        {p : T | TwoScale.Consolidated.loopF p.1.1 p.2.1.2.2 r q ≤
          ENNReal.ofReal (Cminus / (2 * Cplus)) *
            OptimalConstants.Ratios.setDist p.1.1 (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)}) ∩
        {p : T | Measurability.GeodesicCodes.GeoCode (p.1.1, (p.2.1.1, (p.2.1.2.1, p.2.1.2.2)))}) ∩
        {p : T | ∀ t, p.2.1.1 t ∈ e5Region z r a}) ∩
        {p : T | Metric.diam (Set.range p.2.1.1) ≤ (r : ℝ) / 100}) ∩
        {p : T | p.1.1 (p.2.1.2.1, p.2.1.2.2) ≤
          ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Qpar) *
            Real.exp (ξ * p.2.2))}) ∩
        {p : T | p.1.1 (p.2.1.2.1, p.2.1.2.2) ≠ ⊤ ∧
          TwoScale.S36Events.EndpointLoopAt p.1.1 r a θ p.2.1.2.1 p.2.1.2.2 p.2.1.2.1}) ∩
        {p : T | p.1.1 (p.2.1.2.1, p.2.1.2.2) ≠ ⊤ ∧
          TwoScale.S36Events.EndpointLoopAt p.1.1 r a θ p.2.1.2.1 p.2.1.2.2 p.2.1.2.2}) ∩
        {p : T | ENNReal.ofReal (C : ℝ) *
          p.1.1 (p.2.1.2.1, p.2.1.2.2) <
            p.1.2 (p.2.1.2.1, p.2.1.2.2)}) := by
    ext p
    simp only [E5BadCode, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hu', hv', hn, hl, hg, ht, hd, hc', hlu, hlv, hb⟩
      have hf : p.1.1 (p.2.1.2.1, p.2.1.2.2) ≠ ⊤ := hg.2.2.1.ne
      simp only [and_assoc]
      exact ⟨hu', hv', hn, hl, hg, ht, hd, hc', hf, hlu, hf, hlv, hb⟩
    · intro h
      simp only [and_assoc] at h
      rcases h with ⟨hu', hv', hn, hl, hg, ht, hd, hc', _, hlu, _, hlv, hb⟩
      exact ⟨hu', hv', hn, hl, hg, ht, hd, hc', hlu, hlv, hb⟩
  rw [hEq]
  exact hAll

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
