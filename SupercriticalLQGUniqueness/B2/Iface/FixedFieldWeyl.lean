import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Stochastic

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.Iface

 


def FixedFieldWeylAllBounded (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (Φ : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ δ, IsHeatSmoothing P h δ (X δ)) →
      ∀ᵐ ω ∂P, ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M),
        ∃ E : LSCMetric, (∀ p, E p = weylScale (ξ : ℝ) f (Φ (h ω)) p) ∧
          Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n))
            (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' f M hM))
            atTop (𝓝 E)

end SupercriticalLQGUniqueness.B2.Iface
