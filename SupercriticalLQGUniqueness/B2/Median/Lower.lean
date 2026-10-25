import SupercriticalLQGUniqueness.B2.Median.LFPPMetric
import LQGMetric.Papers.GM.S1.NoGap
import LQGMetric.Papers.DFGPS.L2_8GffSq

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal
open LQGMetric (leftSide rightSide)

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Toolkit.CompactPathInfimum

private theorem isCompact_unitSquare : IsCompact unitSquare := by
  change IsCompact LQGMetric.Blueprint.closedUnitSquare
  exact LQGMetric.DFGPS.isCompact_closedUnitSquare

theorem crossingInf_le_liminf {G : ℕ → LSCMetric} {d : LSCMetric}
    (hG : Tendsto G atTop (𝓝 d)) :
    crossingInf d ≤ liminf (fun n => crossingInf (G n)) atTop :=
  compactPathInf_seq_liminf hG isCompact_unitSquare
    LQGMetric.GM.isCompact_leftSide LQGMetric.GM.isCompact_rightSide

theorem crossing_le_liminf (ξ : ℝ) (m : ℕ → Set.Ioi (0 : ℝ))
    (φ : ℕ → C(ℂ, ℝ)) (d : LSCMetric)
    (hG : LSCTendsto (fun n => rescaledLFPP ξ (m n) (φ n))
      d.toLSCFun.1) :
    crossingInf d ≤
      liminf (fun n => ENNReal.ofReal (((m n : Set.Ioi (0 : ℝ)) : ℝ)⁻¹) *
        lfppCrossingLength ξ (φ n)) atTop := by
  let G : ℕ → LSCMetric := fun n => lfppMetric ξ (m n) (φ n)
  have hLSC : LSCTendsto (fun n => (G n).toLSCFun.1) d.toLSCFun.1 := by
    simpa only [G, lfppMetric_toLSCFun] using hG
  have hT : Tendsto G atTop (𝓝 d) :=
    LSCMetric.tendsto_iff.mpr (LSCMetric.lscTendsto_toLSCFun_iff.mp hLSC)
  exact (crossingInf_le_liminf hT).trans
    (liminf_le_liminf (Eventually.of_forall fun n =>
      crossingInf_lfppMetric_le ξ (m n) (φ n)))

end SupercriticalLQGUniqueness.B2.Median
