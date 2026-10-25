import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.LoopCover
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3




 








set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.LoopFit

 
theorem loopRadius_bounds (a : Set.Ioo (3 / 4 : ℝ) 1) :
    0 < (1 - (a : ℝ)) ^ 2 ∧ (1 - (a : ℝ)) ^ 2 ≤ 1 / 16 := by
  have h1 : (3 / 4 : ℝ) < a := a.property.1
  have h2 : (a : ℝ) < 1 := a.property.2
  constructor
  · have : 0 < 1 - (a : ℝ) := by linarith
    positivity
  · have h3 : 0 < 1 - (a : ℝ) := by linarith
    have h4 : 1 - (a : ℝ) < 1 / 4 := by linarith
    nlinarith

 
theorem endpointLoop_iff_loopF (D : LSCMetric) (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ)) (u v x : ℂ) :
    OptimalConstants.Ratios.EndpointLoop D r a θ u v x ↔
      ∀ δ ∈ Ioc (0 : ℝ) ((1 - (a : ℝ)) ^ 2),
        OptimalConstants.Ratios.setDist D {x} (Metric.sphere x (δ * r)) ≤
            ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v) ∧
          TwoScale.Consolidated.loopF D x r δ ≤ ENNReal.ofReal (δ ^ (θ : ℝ)) * D (u, v) := by
  have hr : (0 : ℝ) < r := r.property
  have hδ₀ := loopRadius_bounds a
  constructor
  · intro hL δ hδ
    have hδ1 : δ < 1 := by linarith [hδ.2, hδ₀.2]
    obtain ⟨A, hc, hi, ho, hmax⟩ := hL δ hδ.1 hδ.2
    have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hδ.1 hδ1
    have hA : A = ⟨(x, (δ * r, Real.sqrt δ * r)), hvalid⟩ := by
      apply Subtype.ext
      have hc' : A.1.1 = x := hc
      have hi' : A.1.2.1 = δ * r := hi
      have ho' : A.1.2.2 = Real.sqrt δ * r := ho
      exact Prod.ext hc' (Prod.ext hi' ho')
    have hF : TwoScale.Consolidated.loopF D x r δ = aroundDist D A := by
      rw [hA]
      exact TwoScale.Consolidated.aroundAt_eq D x _ _ hvalid
    rw [max_le_iff] at hmax
    exact ⟨hmax.1, hF ▸ hmax.2⟩
  · intro hR δ hδ0 hδle
    have hδ1 : δ < 1 := by linarith [hδ₀.2]
    have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hδ0 hδ1
    obtain ⟨h1, h2⟩ := hR δ ⟨hδ0, hδle⟩
    refine ⟨⟨(x, (δ * r, Real.sqrt δ * r)), hvalid⟩, rfl, rfl, rfl, ?_⟩
    rw [max_le_iff]
    refine ⟨h1, ?_⟩
    have hF : TwoScale.Consolidated.loopF D x r δ =
        aroundDist D ⟨(x, (δ * r, Real.sqrt δ * r)), hvalid⟩ :=
      TwoScale.Consolidated.aroundAt_eq D x _ _ hvalid
    exact hF ▸ h2

 

theorem measurableSet_endpointLoop_around (r : Set.Ioi (0 : ℝ))
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ)) :
    MeasurableSet {p : LSCMetric × ℂ × ℝ≥0∞ | p.2.2 ≠ ⊤ ∧
      ∀ δ ∈ Ioc 0 ((1 - (a : ℝ)) ^ 2),
        TwoScale.Consolidated.loopF p.1 p.2.1 r δ ≤ ENNReal.ofReal (δ ^ (θ : ℝ)) * p.2.2} :=
  TwoScale.Consolidated.measurableSet_loopClause r.property θ.property (loopRadius_bounds a).1
    (loopRadius_bounds a).2


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.LoopFit
