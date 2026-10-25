import LQGMetric.Papers.DFGPS.L2_1RadialMain
import LQGMetric.Papers.DFGPS.L2_8FinCmp
import SupercriticalLQGUniqueness.B2.Iface.Statements

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_gff_localized_approx
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    {U : Set ℂ} (hU : Bornology.IsBounded U) (ξ : ℝ) :
    ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × ℂ => if hp : 0 < p.1 then
        locMollify p.1 hp (h ω) p.2 else 0) (Ioi 0 ×ˢ univ) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε,
        ∀ z ∈ closure U,
          |heatMollify ε (h ω) z - locMollify ε hε (h ω) z| ≤ δ) ∧
      ∀ c : ℝ, 1 < c → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε,
        ∀ z w : ℂ,
          lfppLocOn ξ ε hε (h ω) U z w ≤
            ENNReal.ofReal c * lfppDOn ξ (heatMollify ε (h ω)) U z w ∧
          lfppDOn ξ (heatMollify ε (h ω)) U z w ≤
            ENNReal.ofReal c * lfppLocOn ξ ε hε (h ω) U z w := by
  exact lem2_1_uncond (isGFFPlusBddCont_of_wp hh.1) hU ξ

end SupercriticalLQGUniqueness.B2.DG20Pt
