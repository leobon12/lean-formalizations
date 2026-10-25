import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import LQGMetric.Prob.PolishContinuousMap




 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes

abbrev Path := C(unitInterval, ℂ)

example : PolishSpace Path := inferInstance
example : StandardBorelSpace Path := inferInstance

def pathReal (P : Path) (t : ℝ) : ℂ :=
  P (projIcc 0 1 zero_le_one t)

theorem length_joint_lsc :
    LowerSemicontinuous (fun p : LSCMetric × Path => p.1.len (pathReal p.2) 0 1) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G p hG
  have hm : Tendsto (fun n => (G n).1) atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hG
  have hp : Tendsto (fun n => (G n).2) atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hG
  apply Toolkit.CompactPathInfimum.joint_len_le_liminf hm
  intro t ht
  have he : Continuous fun P : Path => P (projIcc 0 1 zero_le_one t) :=
    continuous_eval_const _
  exact (he.tendsto p.2).comp hp

theorem length_joint_borel :
    @Measurable (LSCMetric × Path) ENNReal (borel _) inferInstance
      (fun p => p.1.len (pathReal p.2) 0 1) := by
  letI : MeasurableSpace (LSCMetric × Path) := borel _
  letI : OpensMeasurableSpace (LSCMetric × Path) := ⟨le_rfl⟩
  exact length_joint_lsc.measurable

theorem length_joint_measurable :
    Measurable (fun p : LSCMetric × Path => p.1.len (pathReal p.2) 0 1) :=
  length_joint_lsc.measurable

 

def FiniteTraceRelation (K : Set ℂ) (p : LSCMetric × Path) : Prop :=
  p.1.len (pathReal p.2) 0 1 < ∞ ∧ MapsTo p.2 Set.univ K

theorem finiteTraceRelation_borel {K : Set ℂ} (hK : IsClosed K) :
    MeasurableSet {p : LSCMetric × Path | FiniteTraceRelation K p} := by
  have htrace : MeasurableSet {P : Path | MapsTo P Set.univ K} :=
    (ContinuousMap.isClosed_setOfPred_mapsTo hK Set.univ).measurableSet
  exact (measurableSet_lt length_joint_measurable measurable_const).inter
    (htrace.preimage measurable_snd)


end SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes
