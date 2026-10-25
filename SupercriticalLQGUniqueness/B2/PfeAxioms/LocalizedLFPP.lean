import SupercriticalLQGUniqueness.B2.PfeAxioms.InternalRadius
import SupercriticalLQGUniqueness.B2.LscTop.LFPP
import LQGMetric.Papers.DFGPS.L2_1
import LQGMetric.Papers.DFGPS.L2_1RadialMain
import LQGMetric.Papers.DFGPS.L2_17CoreB

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

abbrev localizedLFPP (ξ ε : Set.Ioi (0 : ℝ)) (h : DistC) (U : Set ℂ)
    (z w : ℂ) : ℝ≥0∞ :=
  lfppLocOn (ξ : ℝ) (ε : ℝ) ε.property h U z w

 



theorem localizedLFPP_congr (ξ ε : Set.Ioi (0 : ℝ)) (U : Set ℂ)
    (O : TopologicalSpace.Opens ℂ)
    (hU : ∀ z ∈ U, Metric.closedBall z (Real.sqrt (ε : ℝ)) ⊆ O)
    {g g' : DistC} (he : restrictTo O g = restrictTo O g') (z w : ℂ) :
    localizedLFPP ξ ε g U z w = localizedLFPP ξ ε g' U z w := by
  unfold localizedLFPP lfppLocOn
  apply lfppDOn_congr
  intro x hx
  unfold locMollify
  exact LQGMetric.DFGPS.L217.apply_eq_of_restrictTo_eq he _
    ((tsupport_locTest_subset (ε : ℝ) ε.property x).trans (hU x hx))

 


theorem localizedLFPP_compare {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    {U : Set ℂ} (hU : Bornology.IsBounded U) (ξ : Set.Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P,
      (∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε,
        ∀ z ∈ closure U,
          |heatMollify ε (h ω) z - locMollify ε hε (h ω) z| ≤ δ) ∧
      ∀ c : ℝ, 1 < c → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε,
        ∀ z w : ℂ,
          lfppLocOn (ξ : ℝ) ε hε (h ω) U z w ≤
            ENNReal.ofReal c * lfppDOn (ξ : ℝ) (heatMollify ε (h ω)) U z w ∧
          lfppDOn (ξ : ℝ) (heatMollify ε (h ω)) U z w ≤
            ENNReal.ofReal c * lfppLocOn (ξ : ℝ) ε hε (h ω) U z w := by
  filter_upwards [LQGMetric.DFGPS.lem2_1 LQGMetric.DFGPS.lem2_1GffApprox hh hU (ξ : ℝ)]
    with ω hω
  exact ⟨hω.2.1, hω.2.2⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
