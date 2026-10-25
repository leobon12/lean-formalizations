import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.PointLoopBorel
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.LoopCover
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3




 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

private theorem pointSphere_eq_setDist (D : LSCMetric) (x : ℂ) (R : ℝ) :
    TwoScale.S36Events.pointSphereDist D x R = OptimalConstants.Ratios.setDist D {x} (Metric.sphere x R) := by
  simp only [TwoScale.S36Events.pointSphereDist, TwoScale.S36Events.spherePairInf, OptimalConstants.Ratios.setDist,
    Metric.sphere_zero, iInf_singleton]

private theorem loopRadius_bounds (a : Set.Ioo (3 / 4 : ℝ) 1) :
    0 < (1 - (a : ℝ)) ^ 2 ∧ (1 - (a : ℝ)) ^ 2 ≤ 1 / 16 := by
  have h1 : (3 / 4 : ℝ) < a := a.property.1
  have h2 : (a : ℝ) < 1 := a.property.2
  constructor
  · have : 0 < 1 - (a : ℝ) := by linarith
    positivity
  · have h3 : 0 < 1 - (a : ℝ) := by linarith
    have h4 : 1 - (a : ℝ) < 1 / 4 := by linarith
    nlinarith

private theorem aroundLoop_measurable (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ)) :
    MeasurableSet {p : LoopInput | p.2.2 ≠ ⊤ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ (1 - (a : ℝ)) ^ 2 →
        TwoScale.Consolidated.loopF p.1 p.2.1 r δ ≤
          ENNReal.ofReal (δ ^ (θ : ℝ)) * p.2.2} := by
  have hb := TwoScale.Consolidated.measurableSet_loopClause r.property θ.property
    (loopRadius_bounds a).1 (loopRadius_bounds a).2
  convert hb using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_Ioc, and_imp]

theorem endpointLoopParts_measurable (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ)) :
    MeasurableSet {p : LoopInput | p.2.2 ≠ ⊤ ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ (1 - (a : ℝ)) ^ 2 →
        OptimalConstants.Ratios.setDist p.1 {p.2.1} (Metric.sphere p.2.1 (δ * r)) ≤
          ENNReal.ofReal (δ ^ (θ : ℝ)) * p.2.2) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ (1 - (a : ℝ)) ^ 2 →
        TwoScale.Consolidated.loopF p.1 p.2.1 r δ ≤
          ENNReal.ofReal (δ ^ (θ : ℝ)) * p.2.2)} := by
  have hp := pointLoopClause_measurable (r : ℝ) (θ : ℝ)
    ((1 - (a : ℝ)) ^ 2) θ.property
  have ha := aroundLoop_measurable r a θ
  have hparts := hp.inter ha
  convert hparts using 1
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hfin, hpt, har⟩
    refine ⟨⟨hfin, ?_⟩, hfin, har⟩
    intro δ h0 hδ
    rw [pointSphere_eq_setDist]
    exact hpt δ h0 hδ
  · rintro ⟨⟨hfin, hpt⟩, _, har⟩
    refine ⟨hfin, ?_, har⟩
    intro δ h0 hδ
    rw [← pointSphere_eq_setDist]
    exact hpt δ h0 hδ

theorem endpointLoop_iff_parts (D : LSCMetric) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ)) (u v x : ℂ) :
    OptimalConstants.Ratios.EndpointLoop D r a θ u v x ↔
      (∀ δ : ℝ, 0 < δ → δ ≤ (1 - (a : ℝ)) ^ 2 →
        OptimalConstants.Ratios.setDist D {x} (Metric.sphere x (δ * r)) ≤
          ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ (1 - (a : ℝ)) ^ 2 →
        TwoScale.Consolidated.loopF D x r δ ≤
          ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v)) := by
  have hr : (0 : ℝ) < r := r.property
  have hδ₀ := loopRadius_bounds a
  constructor
  · intro hL
    constructor
    · intro δ hδ hδle
      have hδ1 : δ < 1 := by linarith [hδ₀.2]
      obtain ⟨A, hc, hi, ho, hmax⟩ := hL δ hδ hδle
      have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hδ hδ1
      have hA : A = ⟨(x, (δ * r, Real.sqrt δ * r)), hvalid⟩ := by
        apply Subtype.ext
        have hc' : A.1.1 = x := hc
        have hi' : A.1.2.1 = δ * r := hi
        have ho' : A.1.2.2 = Real.sqrt δ * r := ho
        exact Prod.ext hc' (Prod.ext hi' ho')
      exact (max_le_iff.mp hmax).1
    · intro δ hδ hδle
      have hδ1 : δ < 1 := by linarith [hδ₀.2]
      obtain ⟨A, hc, hi, ho, hmax⟩ := hL δ hδ hδle
      have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hδ hδ1
      have hA : A = ⟨(x, (δ * r, Real.sqrt δ * r)), hvalid⟩ := by
        apply Subtype.ext
        have hc' : A.1.1 = x := hc
        have hi' : A.1.2.1 = δ * r := hi
        have ho' : A.1.2.2 = Real.sqrt δ * r := ho
        exact Prod.ext hc' (Prod.ext hi' ho')
      have hF : TwoScale.Consolidated.loopF D x r δ = aroundDist D A := by
        rw [hA]
        exact TwoScale.Consolidated.aroundAt_eq D x _ _ hvalid
      exact hF ▸ (max_le_iff.mp hmax).2
  · rintro ⟨hpoint, haround⟩ δ hδ hδle
    have hδ1 : δ < 1 := by linarith [hδ₀.2]
    have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hδ hδ1
    refine ⟨⟨(x, (δ * r, Real.sqrt δ * r)), hvalid⟩, rfl, rfl, rfl, ?_⟩
    rw [max_le_iff]
    refine ⟨hpoint δ hδ hδle, ?_⟩
    have hF : TwoScale.Consolidated.loopF D x r δ =
        aroundDist D ⟨(x, (δ * r, Real.sqrt δ * r)), hvalid⟩ :=
      TwoScale.Consolidated.aroundAt_eq D x _ _ hvalid
    exact hF ▸ haround δ hδ hδle

abbrev LoopGeoInput := LSCMetric × ((ℂ × ℂ) × ℂ)

private def endpointCostMap (p : LoopGeoInput) : LSCMetric × (ℂ × ℂ) :=
  (p.1, p.2.1)

private theorem endpointCostMap_measurable : Measurable endpointCostMap := by
  have hend : Measurable (fun p : LoopGeoInput => p.2.1) :=
    measurable_fst.comp measurable_snd
  exact measurable_fst.prodMk hend

private theorem endpointDistance_measurable :
    Measurable (fun p : LoopGeoInput => p.1 p.2.1) := by
  let f : LSCMetric × (ℂ × ℂ) → ENNReal := fun p => p.1 p.2
  have hf : Measurable f := TwoScale.S36Events.jointEval_lsc.measurable
  have hcomp : Measurable (f ∘ endpointCostMap) :=
    hf.comp endpointCostMap_measurable
  exact hcomp

private def loopInputMap (p : LoopGeoInput) : LoopInput :=
  (p.1, (p.2.2, p.1 p.2.1))

private theorem loopInputMap_measurable : Measurable loopInputMap := by
  have hx : Measurable (fun p : LoopGeoInput => p.2.2) :=
    measurable_snd.comp measurable_snd
  exact measurable_fst.prodMk (hx.prodMk endpointDistance_measurable)

 

theorem endpointLoopFinite_measurable (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ)) :
    MeasurableSet {p : LoopGeoInput | p.1 p.2.1 ≠ ⊤ ∧
      OptimalConstants.Ratios.EndpointLoop p.1 r a θ p.2.1.1 p.2.1.2 p.2.2} := by
  have hpre := (endpointLoopParts_measurable r a θ).preimage
    loopInputMap_measurable
  convert hpre using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  exact and_congr Iff.rfl
    (endpointLoop_iff_parts p.1 r a θ p.2.1.1 p.2.1.2 p.2.2)

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
