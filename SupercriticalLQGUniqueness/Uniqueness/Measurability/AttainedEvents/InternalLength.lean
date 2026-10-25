import SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.PathLength
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.JointCompactPort




 




set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

abbrev InternalPath (K : Set ℂ) := C(unitInterval, K)

private def stepMap (K : Set ℂ) (s t : unitInterval)
    (p : LSCMetric × InternalPath K) : LSCMetric × (K × K) :=
  (p.1, (p.2 s, p.2 t))

private theorem stepMap_continuous {K : Set ℂ} (s t : unitInterval) :
    Continuous (stepMap K s t) := by
  have hs : Continuous (fun p : LSCMetric × InternalPath K => p.2 s) :=
    (continuous_eval_const s).comp continuous_snd
  have ht : Continuous (fun p : LSCMetric × InternalPath K => p.2 t) :=
    (continuous_eval_const t).comp continuous_snd
  exact continuous_fst.prodMk (hs.prodMk ht)

private theorem internal_step_lsc {K : Set ℂ} (hK : IsCompact K)
    (s t : unitInterval) :
    LowerSemicontinuous (fun p : LSCMetric × InternalPath K =>
      p.1.internal K (p.2 s, p.2 t)) := by
  let f : LSCMetric × (K × K) → ENNReal :=
    fun q => q.1.internal K (q.2.1, q.2.2)
  have hf : LowerSemicontinuous f := TwoScale.S36Events.internal_compact_joint_lsc hK
  have hc : Continuous (stepMap K s t) := stepMap_continuous s t
  have hcomp : LowerSemicontinuous (f ∘ stepMap K s t) := hf.comp hc
  exact hcomp

private def internalPartitionSum (K : Set ℂ) (n : ℕ)
    (t : ℕ → unitInterval) (p : LSCMetric × InternalPath K) : ENNReal :=
  ∑ i ∈ Finset.range n,
    p.1.internal K (p.2 (t (i + 1)), p.2 (t i))

private theorem internalPartitionSum_lsc {K : Set ℂ} (hK : IsCompact K)
    (n : ℕ) (t : ℕ → unitInterval) :
    LowerSemicontinuous (internalPartitionSum K n t) := by
  unfold internalPartitionSum
  apply lowerSemicontinuous_sum
  intro i hi
  exact internal_step_lsc hK (t (i + 1)) (t i)

 
def internalPathLength (K : Set ℂ)
    (p : LSCMetric × InternalPath K) : ENNReal :=
  ⨆ (n : ℕ) (t : ℕ → unitInterval)
      (_ : StrictMonoOn (fun i => (t i : ℝ)) (Iic n))
      (_ : t 0 = 0) (_ : t n = 1),
    internalPartitionSum K n t p

theorem internalPathLength_joint_lsc {K : Set ℂ} (hK : IsCompact K) :
    LowerSemicontinuous
      (fun p : LSCMetric × InternalPath K => internalPathLength K p) := by
  unfold internalPathLength
  apply lowerSemicontinuous_iSup
  intro n
  apply lowerSemicontinuous_iSup
  intro t
  apply lowerSemicontinuous_iSup
  intro ht
  apply lowerSemicontinuous_iSup
  intro h0
  apply lowerSemicontinuous_iSup
  intro hn
  exact internalPartitionSum_lsc hK n t

theorem internalPathLength_joint_measurable {K : Set ℂ} (hK : IsCompact K) :
    Measurable (fun p : LSCMetric × InternalPath K => internalPathLength K p) :=
  (internalPathLength_joint_lsc hK).measurable

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
