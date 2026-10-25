import SupercriticalLQGUniqueness.B2.DG20Lim.Recovery
import SupercriticalLQGUniqueness.Frozen.LSCFun
import Mathlib.Topology.Instances.EReal.Lemmas

 

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

def RData.toLSCFun (R : RData) : LSCFun :=
  ⟨fun p => (R.DfromR p.1 p.2 : EReal),
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      R.lowerSemicontinuous_DfromR
      (fun _ _ h => EReal.coe_ennreal_strictMono.monotone h)⟩

 

theorem RData.lscTendsto_of_circleDist (R : RData)
    (D : ℕ → LQGMetric.ContMetric) (hlen : ∀ n, (D n).IsLength)
    (hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
        atTop (nhds (R.across O P))) :
    LSCTendsto
      (fun n p => (ENNReal.ofReal ((D n).1 p) : EReal)) R.toLSCFun.1 := by
  constructor
  · intro p q hp
    have hzn : Tendsto (fun n => (p n).1) atTop (nhds q.1) :=
      (continuous_fst.tendsto q).comp hp
    have hwn : Tendsto (fun n => (p n).2) atTop (nhds q.2) :=
      (continuous_snd.tendsto q).comp hp
    have hlim := R.le_liminf_pointDist D hlen hcircle
      (fun n => (p n).1) (fun n => (p n).2) hzn hwn
    have hmap := (EReal.coe_ennreal_strictMono.monotone).map_liminf_of_continuousAt
      (F := atTop) (fun n => ENNReal.ofReal ((D n).1 (p n)))
      continuous_coe_ennreal_ereal.continuousAt
    change (R.DfromR q.1 q.2 : EReal) ≤
      liminf (fun n => (ENNReal.ofReal ((D n).1 (p n)) : EReal)) atTop
    calc
      (R.DfromR q.1 q.2 : EReal) ≤
          ((liminf (fun n => ENNReal.ofReal ((D n).1 (p n))) atTop : ℝ≥0∞) : EReal) :=
        EReal.coe_ennreal_strictMono.monotone hlim
      _ = liminf (fun n => (ENNReal.ofReal ((D n).1 (p n)) : EReal)) atTop := by
        simpa only [Function.comp_def] using hmap
  · intro q
    obtain ⟨zn, wn, hzn, hwn, hdist⟩ :=
      R.exists_pointDist_recovery D hcircle q.1 q.2
    refine ⟨fun n => (zn n, wn n), ?_, ?_⟩
    · have hq : q = (q.1, q.2) := by cases q; rfl
      rw [hq, nhds_prod_eq]
      exact hzn.prodMk hwn
    change Tendsto (fun n => (ENNReal.ofReal ((D n).1 (zn n, wn n)) : EReal))
      atTop (nhds (R.DfromR q.1 q.2 : EReal))
    exact (continuous_coe_ennreal_ereal.tendsto _).comp hdist

end SupercriticalLQGUniqueness.B2.DG20Lim
