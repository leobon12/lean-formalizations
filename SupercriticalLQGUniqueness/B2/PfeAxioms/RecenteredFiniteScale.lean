import SupercriticalLQGUniqueness.B2.PfeAxioms.FiniteConstantScale
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionBdd
import SupercriticalLQGUniqueness.B2.PfeAxioms.RecenteredGeometrySB
import LQGMetric.Papers.DFGPS.L2_6

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem ae_recentered_finiteLFPP_scale
    (ξ : ℝ) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (r : ℝ) (z : ℂ)
    (hY : ∀ δ, IsHeatSmoothing P
      (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) δ (Y δ)) :
    ∀ᵐ ω ∂P, ∀ n, ∀ p : ℂ × ℂ,
      PfeWeyl.normalizedLFPPMetric ξ (m (ε n)) (Y (ε n) ω) p =
        ENNReal.ofReal (Real.exp (ξ * -circleAvg (h ω) r z)) *
          PfeWeyl.normalizedLFPPMetric ξ (m (ε n)) (X (ε n) ω) p := by
  have hg := isGFFPlusBddCont_recentered hh r z
  have hb := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1
  rw [ae_all_iff]
  intro n
  have hXeq := ae_heatVersion_eq_heatMollify_bdd hb (ε n) (X (ε n)) (hX (ε n))
  have hYeq := ae_heatVersion_eq_heatMollify_bdd hg (ε n) (Y (ε n)) (hY (ε n))
  have hconv := hh.1.ae_tendstoLocallyUniformly_heatMollify
    (ε n : ℝ) (ε n).property.ne'
  filter_upwards [hXeq, hYeq, hconv] with ω hXω hYω hc p
  apply normalizedLFPPMetric_add_const ξ (m (ε n))
    (X (ε n) ω) (Y (ε n) ω)
    (-circleAvg (h ω) r z) _ p
  intro u
  rw [hYω u, hXω u,
    heatMollify_addConst_of_tendsto (ε n).property.ne'
      ((tendstoLocallyUniformlyOn_univ.2 hc.1).tendsto_at (mem_univ u))]

end SupercriticalLQGUniqueness.B2.PfeAxioms
