/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Sigma
import InteractingSLE.Spec.Sec5.Prop513ScheduleTrace
import InteractingSLE.Spec.Restart.StagedEntranceStripPast

/-!
# A continuous driver for a complete finite switched record

Packet PROVE-T14-GW2ROOT2. Reuse the finite concatenation from Proposition
5.13. Its input is the actual retained vector, including every old piece.
No generating trace or source probability property is assumed to define it.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist Staged StagedLaw Restart GW2Schedule RootC24
open Sec5.Prop513TreeExtract Sec5.Prop513Schedule

/-- Extend a finite vector by the zero continuous driver. -/
def recordDriver {n : ℕ} (R : Fin n → RecData) (j : ℕ) : ℝ≥0 → ℝ :=
  if hj : j < n then fun t => rdrv (R ⟨j, hj⟩) t else fun _ => 0

theorem measurable_recordDriver {n : ℕ} (j : ℕ) :
    Measurable (fun R : Fin n → RecData => recordDriver R j) := by
  classical
  by_cases hj : j < n
  · simp only [recordDriver, hj, ↓reduceDIte]
    exact measurable_pi_iff.mpr fun t =>
      (measurable_rdrv_apply t).comp (measurable_pi_apply (⟨j, hj⟩ : Fin n))
  · simp only [recordDriver, hj, ↓reduceDIte]
    exact measurable_const

theorem continuous_recordDriver {n : ℕ} (R : Fin n → RecData) (j : ℕ) :
    Continuous (recordDriver R j) := by
  classical
  by_cases hj : j < n
  · simp only [recordDriver, hj, ↓reduceDIte]
    exact (continuous_rdrv _).comp NNReal.continuous_coe
  · simp only [recordDriver, hj, ↓reduceDIte]
    exact continuous_const

theorem recordDriver_zero {n : ℕ} (R : Fin n → RecData) (j : ℕ) :
    recordDriver R j 0 = 0 := by
  classical
  by_cases hj : j < n
  · simp only [recordDriver, hj, ↓reduceDIte, NNReal.coe_zero, rdrv_zero]
  · simp only [recordDriver, hj, ↓reduceDIte]

/-- Concatenate the continuous stopped drivers at their prescribed own times. -/
def joinedRead (L : List (ℝ × ℝ≥0)) (R : Fin L.length → RecData) : ℝ≥0 → ℝ :=
  joinedDriver (fun j (R : Fin L.length → RecData) => (recordDriver R j, ⊤)) 0 0 L R

theorem measurable_joinedRead (L : List (ℝ × ℝ≥0)) : Measurable (joinedRead L) :=
  measurable_joinedDriver (fun j => (measurable_recordDriver j).prodMk measurable_const) _ _ _

theorem continuous_joinedRead (L : List (ℝ × ℝ≥0)) (R : Fin L.length → RecData) :
    Continuous (joinedRead L R) ∧ joinedRead L R 0 = 0 :=
  joinedDriver_continuous _ R 0 0 L
    (fun j _ _ => ⟨continuous_recordDriver R j, recordDriver_zero R j⟩)

/-- One record of the entire concatenation, with its actual finite time cap. -/
def joinedRecord (L : List (ℝ × ℝ≥0)) (R : Fin L.length → RecData) : RecData :=
  StagedEntrance.Strip.recOfDriver (lastTime 0 L) (joinedRead L R)

theorem measurable_joinedRecord (L : List (ℝ × ℝ≥0)) : Measurable (joinedRecord L) :=
  (StagedEntrance.Strip.measurable_recOfDriver _).comp (measurable_joinedRead L)

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The entire literal retained vector for the selected physical program. -/
def programRecords (c : SourceData Ω) (x : ℝ) (L : List (ℝ × ℝ≥0)) (ω : Ω) :
    Fin L.length → RecData := fun j =>
  stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) j ω

/-- The concatenated own driver and its cap are Borel in exactly this program's
retained sigma algebra, before taking an almost-sure source event. -/
theorem measurable_programJoinedRecord (c : SourceData Ω) (x : ℝ)
    (L : List (ℝ × ℝ≥0)) :
    Measurable[stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec x L) L.length] (fun ω => joinedRecord L (programRecords c x L ω)) :=
  (measurable_joinedRecord L).comp (measurable_snd.comp
    (comap_measurable (stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec x L) L.length)))

/-- Ambient measurability uses the source's canonical measurable family. -/
theorem measurable_programJoinedRecord_ambient (c : SourceData Ω) (x : ℝ)
    (L : List (ℝ × ℝ≥0)) :
    Measurable fun ω => joinedRecord L (programRecords c x L ω) :=
  Measurable.mono (measurable_programJoinedRecord c x L)
    (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _) le_rfl

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
