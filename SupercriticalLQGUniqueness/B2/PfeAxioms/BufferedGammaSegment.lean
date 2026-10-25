import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaLower
import SupercriticalLQGUniqueness.B2.PfeAxioms.RadiusBall
import SupercriticalLQGUniqueness.B2.PfeWeyl.GammaCompact

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem buffered_short_segment_recovery
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    {V K : Set ℂ} (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (x y : ℕ → V) (hxK : ∀ᶠ n in atTop, (x n : ℂ) ∈ K)
    {r R : ℝ≥0∞} (hrR : r < R)
    (hR : R < ⨅ p ∈ K ×ˢ frontier V, D p)
    (hrfin : r < ∞)
    {d : ℝ≥0∞}
    (hxy : Tendsto (fun n => (G n) ((x n : ℂ), (y n : ℂ))) atTop (𝓝 d))
    (hdr : d < r) :
    Tendsto (fun n => (G n).internal V (x n, y n)) atTop (𝓝 d) := by
  have hbarrier := PfeWeyl.eventually_lower_on_compact hG
    (hK.prod hfront) hR
  have hcost : ∀ᶠ n in atTop,
      (G n) ((x n : ℂ), (y n : ℂ)) < r :=
    hxy.eventually (isOpen_Iio.mem_nhds hdr)
  have heq : (fun n => (G n).internal V (x n, y n)) =ᶠ[atTop]
      (fun n => (G n) ((x n : ℂ), (y n : ℂ))) := by
    filter_upwards [hxK, hbarrier, hcost] with n hxn hbn hcn
    have hRfront : R ≤ ⨅ b ∈ frontier V, (G n) ((x n : ℂ), b) := by
      refine le_iInf fun b => le_iInf fun hb => ?_
      exact hbn _ ⟨hxn, hb⟩
    exact internal_eq_of_lt_frontier_distance (G n) (hLen n) (hPath n)
      hV (x n).property (y n).property hrfin (hrR.trans_le hRfront) hcn
  exact hxy.congr' heq.symm

end SupercriticalLQGUniqueness.B2.PfeAxioms
