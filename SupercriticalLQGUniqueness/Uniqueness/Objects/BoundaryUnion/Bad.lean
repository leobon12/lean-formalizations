import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnion.Meas
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Low
import Mathlib.MeasureTheory.Integral.Prod




 




set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnion

 
theorem measurable_nrm (ξ Q : ℝ) (s : ℝ) (c : ℂ) :
    Measurable (fun g : LQGMetric.DistC => Objects.AnnulusTails.nrm ξ Q g s c) := by
  have hH : Measurable (fun g : LQGMetric.DistC => LQGMetric.circleAvg g s c) :=
    LQGMetric.measurable_circleAvg_left s c
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Real.measurable_exp.comp (hH.const_mul ξ)))

 

theorem measurableSet_bad_boundary_relation
    (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    (c : ℂ) (s R : ℝ) (hs : 0 ≤ s) :
    MeasurableSet {p : LQGMetric.DistC × ℝ |
      ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q p.1 s c <
        (D p.1).internal (Metric.closedBall c s)
          (⟨circleMap c s p.2, circleMap_mem_closedBall c hs p.2⟩,
           ⟨c, Metric.mem_closedBall_self hs⟩)} := by
  have hN : Measurable (fun p : LQGMetric.DistC × ℝ =>
      ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q p.1 s c) :=
    measurable_const.mul ((measurable_nrm ξ Q s c).comp measurable_fst)
  exact measurableSet_lt hN (measurable_ball_boundary_cost D hD c s hs)

 
def badBoundaryRelation (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (c : ℂ) (s R : ℝ) (hs : 0 ≤ s) : Set (LQGMetric.DistC × ℝ) :=
  {p | ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q p.1 s c <
    (D p.1).internal (Metric.closedBall c s)
      (⟨circleMap c s p.2, circleMap_mem_closedBall c hs p.2⟩,
       ⟨c, Metric.mem_closedBall_self hs⟩)}

 
def badPointIndicator (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (c : ℂ) (s R : ℝ) (hs : 0 ≤ s) (p : LQGMetric.DistC × ℝ) : ℝ≥0∞ :=
  by
    classical
    exact if p ∈ badBoundaryRelation ξ Q D c s R hs then 1 else 0

 
theorem measurable_bad_angle_mass
    (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    (c : ℂ) (s R : ℝ) (hs : 0 ≤ s) :
    Measurable (fun g : LQGMetric.DistC =>
      MeasureTheory.lintegral
        (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))
        (fun θ => badPointIndicator ξ Q D c s R hs (g, θ))) := by
  classical
  have hE : MeasurableSet (badBoundaryRelation ξ Q D c s R hs) :=
    measurableSet_bad_boundary_relation ξ Q D hD c s R hs
  have hf : Measurable (badPointIndicator ξ Q D c s R hs) := by
    unfold badPointIndicator
    exact Measurable.ite hE measurable_const measurable_const
  exact hf.lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnion
