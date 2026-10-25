import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent

 



set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness

open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont addFun)

namespace IsWeakLQGMetric

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

theorem measurable (h : IsWeakLQGMetric ξ Q D) :
    Measurable D := h.1

theorem length (h : IsWeakLQGMetric ξ Q D) :
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace) := h.2.1

theorem locality (h : IsWeakLQGMetric ξ Q D) :
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
      ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞), Measurable F ∧
        ∀ᵐ ω ∂P, (D (h ω)).internal (U : Set ℂ) = F (restrictTo U (h ω))) := h.2.2.1

theorem weyl (h : IsWeakLQGMetric ξ Q D) :
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), weylScale (ξ : ℝ) f (D (h ω)) = (D (addFun (h ω) f)).1) := h.2.2.2.1

theorem translation (h : IsWeakLQGMetric ξ Q D) :
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (translateDist z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z)) := h.2.2.2.2.1

theorem tightness (h : IsWeakLQGMetric ξ Q D) :
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ a : Set.Ioi (0 : ℝ) → Ω → ℝ,
      (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) →
      ∀ A : EuclideanAnnulus,
        IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
          ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
            acrossDist (D (h ω)) (A.dilate r r.2)) ∧
        IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
          ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
            aroundDist (D (h ω)) (A.dilate r r.2))) := h.2.2.2.2.2

end IsWeakLQGMetric

end SupercriticalLQGUniqueness
