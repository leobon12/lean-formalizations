import SupercriticalLQGUniqueness.B2.DG20Lim.LSCConvergence
import SupercriticalLQGUniqueness.Frozen.LSCMetricToLSCFun

 


set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def RData.toLSCMetric (R : RData)
    (htri : ∀ x y z : ℂ,
      R.DfromR x z ≤ R.DfromR x y + R.DfromR y z) : LSCMetric :=
  ⟨fun p => R.DfromR p.1 p.2,
    ⟨R.DfromR_self,
      (fun x y h => (R.DfromR_eq_zero_iff x y).mp h),
      R.DfromR_symm,
      htri⟩,
    R.lowerSemicontinuous_DfromR⟩

@[simp] theorem RData.toLSCMetric_apply (R : RData)
    (htri : ∀ x y z : ℂ,
      R.DfromR x z ≤ R.DfromR x y + R.DfromR y z)
    (x y : ℂ) : R.toLSCMetric htri (x, y) = R.DfromR x y := rfl

theorem RData.lscTendsto_toLSCMetric_of_circleDist (R : RData)
    (htri : ∀ x y z : ℂ,
      R.DfromR x z ≤ R.DfromR x y + R.DfromR y z)
    (D : ℕ → LQGMetric.ContMetric)
    (hlen : ∀ n, (D n).IsLength)
    (hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
        atTop (nhds (R.across O P))) :
    LSCTendsto
      (fun n p => (ENNReal.ofReal ((D n).1 p) : EReal))
      (R.toLSCMetric htri).toLSCFun.1 := by
  exact R.lscTendsto_of_circleDist D hlen hcircle

end SupercriticalLQGUniqueness.B2.DG20Lim
