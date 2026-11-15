/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TfAgree

/-!
# The schedule's records and explored path are read off the field; the capped candidate is regular

Packet PROVE-GW2-RELDET (`GW2TcCurve.SchedPhysCurveStatement`, time-ordered case).

* `measurable_stopRec_field`, `measurableSet_oldSuccess_field`, **`measurable_schedW_field`**: the piece records, the
  success event and the explored driver are measurable for `σ(c.h)`. The marks built from them are therefore
  field-determined (`comap_le_aeSigma_centred_of_field`).
* **`ae_continuousOn_capped`**: almost surely, if the history succeeded, the candidate's driver of the program capped at
  own time `d` is continuous up to and including its stop `min(d, ζ)` (Theorem 1.3's piece regularity,
  `stagedPiecesRegular_of_regular`). Also every record of the capped program is good.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 Sec5.Prop513TreeExtract Sec5.Prop513Schedule

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

theorem measurable_stopRec_field (c : SourceData Ω) (spec : ExplSpec) (j : ℕ) :
    @Measurable Ω RecData (MeasurableSpace.comap c.h inferInstance) _
      (stopRec c.hκ c.h12p c.βA c.c₀ c.h spec j) :=
  (measurable_comp_const_left (F := fun Δ' f => canonRec c.hκ c.h12p c.βA c.c₀ spec.1 (specAngle spec) Δ' f j)
    (measurable_canonRec c.hκ c.h12p c.βA c.c₀ spec.1 (specAngle spec) c.hβA.1 j) (specDelta spec)
    measurable_id).comp (comap_measurable c.h)

theorem measurableSet_oldSuccess_field (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    @MeasurableSet Ω (MeasurableSpace.comap c.h inferInstance) {ω | RootJ31.oldSuccess c r l ω} := by
  have hm : ∀ j : Fin (RootJ31.historyProgram c r l).length,
      @MeasurableSet Ω (MeasurableSpace.comap c.h inferInstance)
        {ω | (stopRec c.hκ c.h12p c.βA c.c₀ c.h
          (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l)) j ω).2.2 = false} :=
    fun j => ((measurable_snd.comp measurable_snd).comp (measurable_stopRec_field c _ j))
      (measurableSet_singleton false)
  have e : {ω | RootJ31.oldSuccess c r l ω} = ⋂ j : Fin (RootJ31.historyProgram c r l).length,
      {ω | (stopRec c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l)) j ω).2.2 = false} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    rfl
  rw [e]
  exact @MeasurableSet.iInter Ω _ (MeasurableSpace.comap c.h inferInstance) _ _ hm

/-- **The explored driver is read off the field.** -/
theorem measurable_schedW_field (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (t : ℝ≥0) :
    @Measurable Ω ℝ (MeasurableSpace.comap c.h inferInstance) _ (GW2Rd.schedW c r l a t) := by
  classical
  have hR : @Measurable Ω _ (MeasurableSpace.comap c.h inferInstance) _
      (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a)) :=
    (@measurable_pi_iff _ _ _ (MeasurableSpace.comap c.h inferInstance) _ _).mpr
      fun j => measurable_stopRec_field c _ j
  have hfj : @Measurable Ω ℝ (MeasurableSpace.comap c.h inferInstance) _
      fun ω => futureJoined c r l a ω t :=
    ((measurable_pi_apply t).comp (RootJ31.measurable_joinedRead _)).comp hR
  exact Measurable.ite (measurableSet_oldSuccess_field c r l) hfj measurable_const

/-- Field-measurable maps generate field-determined marks. -/
theorem comap_le_aeSigma_centred_of_field (c : SourceData Ω) (u₀ : ℂ → ℝ) {X : Type*} [MeasurableSpace X]
    {g : Ω → X} (hg : @Measurable Ω X (MeasurableSpace.comap c.h inferInstance) _ g) :
    MeasurableSpace.comap g inferInstance ≤
      LocalSets.aeSigma (MeasurableSpace.comap (WholeField.centredField c.h u₀) inferInstance) c.P := by
  rw [GW2Rd.comap_centredField]
  exact hg.comap_le.trans (LocalSets.le_aeSigma _ _)

variable [StandardBorelSpace Ω]

/-- **The capped candidate is regular up to its stop, and the capped records are good, almost surely.** -/
theorem ae_continuousOn_capped (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (d : ℝ≥0) :
    ∀ᵐ ω ∂c.P, RootJ31.oldSuccess c r l ω →
      ContinuousOn (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (cappedProgram c r l a d))
          (RootJ31.historyProgram c r l).length ω).1
        {s | (s : ℝ≥0∞) ≤ min (specDelta (schedSpec (rootPt r.1) (cappedProgram c r l a d))
            (RootJ31.historyProgram c r l).length)
          (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (cappedProgram c r l a d))
            (RootJ31.historyProgram c r l).length ω).2} ∧
      ∀ (j : ℕ) (hj : j < (cappedProgram c r l a d).length), LocalExt.IsDrvGood
        (recHist (RootJ31.programRecords c (rootPt r.1) (cappedProgram c r l a d) ω ⟨j, hj⟩)) := by
  set x := rootPt r.1
  set L := cappedProgram c r l a d
  have hS := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle (schedSpec x L)) (specDelta (schedSpec x L))
    h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := schedSpec x L) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS
    (fun k ω => isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x
      (specAngle (schedSpec x L)) (specDelta (schedSpec x L)) (c.h ω) k)
  filter_upwards [hR.ae_pieceRegular] with ω hω hold
  have hsm := allSucc_capped_of_oldSuccess c r l a d ω hold
  have hlenL : L.length = (RootJ31.historyProgram c r l).length + 1 := length_cappedProgram c r l a d
  -- the regularity of a launched piece `k ≤ m`
  have hreg : ∀ k < L.length, ContinuousOn (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) k ω).1
      {s | (s : ℝ≥0∞) ≤ min (specDelta (schedSpec x L) k)
        (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) k ω).2} := by
    intro k hk
    have hs : AllSucc (specDelta (schedSpec x L))
        (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) j ω) k := hsm.mono (by omega)
    have hlen : k < (schedSpec x L).2.2.length := by
      simpa only [schedSpec, GW2Schedule.length_scheduleProgram] using hk
    have hl := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := schedSpec x L)
      rfl (isFlowProg_spec x true L) (specDelta_ne_top _)
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) j ω) hlen).1 hs
    obtain ⟨-, hW, -⟩ := hω k _ _ hl
    have hT := RootU19.instrTime_sched_ne_top x L hk
    have hd : specDelta (schedSpec x L) k = instrTime (schedSpec x L) k := by
      simp only [specDelta, hT, ↓reduceIte]
    rw [← hd] at hW
    exact hW
  refine ⟨hreg _ (by omega), fun j hj => ?_⟩
  have he : IsRegularDriver (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) j ω) :=
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) j
  exact isDrvGood_of_continuousOn_le he
    (ne_top_of_le_ne_top (specDelta_ne_top _ j) (min_le_left _ _)) (hreg j hj)

end InteractingSLE.Theorem14.GW2TipSystem.Gm
