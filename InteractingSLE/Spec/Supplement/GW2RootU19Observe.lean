/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootR18Path
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# Observable live tips read from GW2's actual stopped records

Packet PROVE-T14-GW2ROOT2. LP11 reconstructs a trace including a finite
endpoint. The availability gate distinguishes a successful cutoff from
death at the same recorded time. All readers are Borel on the full record
space and are measurable in the actual retained stage sigma-algebra.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootU19

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

/-- The whole frozen trace reconstructed from a stopped record. LP11
includes its finite endpoint, even when the record's death flag is true. -/
def recordTrace (r : RecData) : ℝ≥0 → ℂ :=
  (LP.drivingTrace (r.2.1, fun t : ℝ≥0 => rdrv r t)).2

/-- A recorded time is available when it precedes death and is no later
than the prescribed cutoff. Equality with a successful cutoff is allowed. -/
def recordAvailable (t : ℝ≥0) (r : RecData) : Prop :=
  (t : ℝ≥0∞) ≤ r.2.1 ∧ ((t : ℝ≥0∞) < r.2.1 ∨ r.2.2 = false)

/-- The live own-chart driver and tip, read solely from a stopped record. -/
def recordObservation (t : ℝ≥0) (r : RecData) : ℝ × ℂ :=
  open scoped Classical in
  if recordAvailable t r then (rdrv r t, recordTrace r t) else (0, 0)

theorem measurable_recordTrace : Measurable recordTrace :=
  (measurable_snd.comp LP.measurable_drivingTrace).comp
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_pi_iff.2 fun t => measurable_rdrv_apply (t : ℝ)))

theorem measurableSet_recordAvailable (t : ℝ≥0) : MeasurableSet {r | recordAvailable t r} :=
  (measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).inter
    ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).union
      ((measurable_snd.comp measurable_snd) (measurableSet_singleton false)))

theorem measurable_recordObservation (t : ℝ≥0) : Measurable (recordObservation t) :=
  Measurable.ite (measurableSet_recordAvailable t)
    ((measurable_rdrv_apply (t : ℝ)).prodMk
      ((measurable_pi_apply t).comp measurable_recordTrace)) measurable_const

/-- The death flag gives precisely the original strict availability test. -/
theorem recordAvailable_recOf_iff (t : ℝ≥0) (T : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    recordAvailable t (recOf T e) ↔ (t : ℝ≥0∞) ≤ T ∧ (t : ℝ≥0∞) < e.2 := by
  change ((t : ℝ≥0∞) ≤ min T e.2 ∧
    ((t : ℝ≥0∞) < min T e.2 ∨ decide (e.2 ≤ T) = false)) ↔ _
  simp only [le_min_iff, lt_min_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨htT, hte⟩, hlt | hnot⟩
    · exact ⟨htT, hlt.2⟩
    · exact ⟨htT, htT.trans_lt (not_le.mp hnot)⟩
  · rintro ⟨htT, hte⟩
    refine ⟨⟨htT, hte.le⟩, ?_⟩
    by_cases hT : e.2 ≤ T
    · exact Or.inl ⟨hte.trans_le hT, hte⟩
    · exact Or.inr hT

/-- The trace reader returns the original trace through the full recorded
interval. Only the original generating trace and driver regularity are inputs. -/
theorem recordTrace_recOf_eq {T : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) (hfin : min T e.2 ≠ ⊤)
    (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ min T e.2})
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace e.1 (min T e.2) γ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ min T e.2) :
    recordTrace (recOf T e) t = γ t := by
  have hg := isDrvGood_of_continuousOn_le he hfin hc
  have heq := LP.drivingTrace_eq hγ
    (hc.mono fun q (hq : (q : ℝ≥0∞) < min T e.2) => hq.le) he.2.1
    (w' := fun q : ℝ≥0 => rdrv (recOf T e) q) (fun q hq => by
      simp only [rdrv, Real.toNNReal_coe]
      rw [histDrv_recHist he hg]
      change e.1 (min (q : ℝ≥0∞) (min T e.2)).toNNReal = e.1 q
      rw [min_eq_left hq.le, ENNReal.toNNReal_coe])
  have htip := congrFun (congrArg Prod.snd heq) t
  change recordTrace (recOf T e) t = γ (min (t : ℝ≥0∞) (min T e.2)).toNNReal at htip
  simpa only [min_eq_left ht, ENNReal.toNNReal_coe] using htip

/-- On the source live event the record observation is the actual driver
and generating-trace tip, including the prescribed cutoff itself. -/
theorem recordObservation_recOf_eq {T : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) (hfin : min T e.2 ≠ ⊤)
    (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ min T e.2})
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace e.1 (min T e.2) γ)
    {t : ℝ≥0} (htT : (t : ℝ≥0∞) ≤ T) (hte : (t : ℝ≥0∞) < e.2) :
    recordObservation t (recOf T e) = (e.1 t, γ t) := by
  have ht : (t : ℝ≥0∞) ≤ min T e.2 := le_min htT hte.le
  have hg := isDrvGood_of_continuousOn_le he hfin hc
  rw [recordObservation, ite_eq_left ((recordAvailable_recOf_iff t T e).2 ⟨htT, hte⟩),
    recordTrace_recOf_eq he hfin hc hγ ht]
  congr 1
  simp only [rdrv, Real.toNNReal_coe]
  rw [histDrv_recHist he hg]
  change e.1 (min (t : ℝ≥0∞) (min T e.2)).toNNReal = e.1 t
  rw [min_eq_left ht, ENNReal.toNNReal_coe]

section Stage

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord)
  {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens)
  (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ)

/-- Every stopped piece record is measurable in the actual stage sigma-algebra. -/
theorem measurable_stageSigma_stopRec (j : Fin n) :
    Measurable[stageSigma hκ h12p βA c₀ h s W' ζ' spec n]
      (stopRec hκ h12p βA c₀ h spec j) :=
  ((measurable_pi_apply j).comp measurable_snd).comp
    (comap_measurable (stageMap hκ h12p βA c₀ h s W' ζ' spec n))

/-- The driver/tip observation at any own time is known from the actual
stopped stage records; no continuation after their cutoff is conditioned on. -/
theorem measurable_stageSigma_recordObservation (j : Fin n) (t : ℝ≥0) :
    Measurable[stageSigma hκ h12p βA c₀ h s W' ζ' spec n]
      (fun ω => recordObservation t (stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_recordObservation t).comp
    (measurable_stageSigma_stopRec hκ h12p βA c₀ h s W' ζ' spec n j)

end Stage

end InteractingSLE.Theorem14.GW2TipSystem.RootU19
