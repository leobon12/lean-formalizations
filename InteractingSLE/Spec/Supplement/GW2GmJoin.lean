/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmBack
import InteractingSLE.Spec.Supplement.GW2RootJ31Construction
import InteractingSLE.Spec.Supplement.GW2RootY20Regular

/-!
# The joined future driver of J31 generates a trace, almost surely

Packet PROVE-GW2-GEOM2 (step R3). For the concrete construction `RootJ31.constructionFamily`, the
future record of a candidate `a` after a retained history `l` is the joined record of the future
program (`RootJ31.futurePair`). Almost surely, at every history whose old pieces all succeeded
(`RootJ31.oldSuccess`), every piece of the future program is launched, Theorem 1.3
(`StagedPiecesRegular`) makes it a continuous curve up to its stop, and the joined driver
`RootJ31.joinedRead` generates a trace on `[0, ∞)` (boundary hits allowed):

* `allSucc_future_of_oldSuccess`: the old pieces of the future program succeed;
* `ae_launched_rdrv_trace`: for a fixed schedule, every launched piece decodes to a trace-generating driver;
* **`ae_futureJoined_trace`**: the statement above for all histories and candidates at once.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The joined future driver of candidate `a` after history `l`. -/
def futureJoined (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (ω : Ω) : ℝ≥0 → ℝ :=
  RootJ31.joinedRead (RootJ31.futureProgram c r l a)
    (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω)

theorem continuous_futureJoined (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    Continuous (futureJoined c r l a ω) ∧ futureJoined c r l a ω 0 = 0 :=
  RootJ31.continuous_joinedRead _ _

/-- The future record is the record of the joined future driver at the program's last time. -/
theorem futurePair_snd (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (RootJ31.futurePair c r l a ω).2 = StagedEntrance.Strip.recOfDriver
      (Sec5.Prop513Schedule.lastTime 0 (RootJ31.futureProgram c r l a)) (futureJoined c r l a ω) :=
  rfl

/-- The old pieces of every future program succeed when the retained history did. -/
theorem allSucc_future_of_oldSuccess (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (hold : RootJ31.oldSuccess c r l ω) :
    AllSucc (specDelta (schedSpec (rootPt r.1) (RootJ31.futureProgram c r l a)))
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (RootJ31.futureProgram c r l a)) j ω)
      (RootJ31.historyProgram c r l).length := by
  intro j hj
  apply (RootCv.recOf_flag_eq_false_iff _ _).mp
  change (stopRec c.hκ c.h12p c.βA c.c₀ c.h
    (schedSpec (rootPt r.1) (RootJ31.futureProgram c r l a)) j ω).2.2 = false
  rw [RootJ31.futureProgram, stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hj ω]
  exact hold ⟨j, hj⟩

variable [StandardBorelSpace Ω]

/-- **Every launched canonical piece of a fixed schedule decodes, almost surely, to a driver generating a
trace on `[0, ∞)`** (Theorem 1.3 through `StagedPiecesRegular`; the stop may be the lifetime). -/
theorem ae_launched_rdrv_trace (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (x : ℝ)
    (L : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂c.P, ∀ k < L.length,
      AllSucc (specDelta (schedSpec x L))
        (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) j ω) k →
      LocalExt.IsDrvGood (recHist (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) k ω)) ∧
      ∃ η, IsGeneratingTrace
        (fun t : ℝ≥0 => rdrv (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) k ω) t) ⊤ η := by
  have hS := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle (schedSpec x L)) (specDelta (schedSpec x L))
    h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := schedSpec x L) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS
    (fun k ω => isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x
      (specAngle (schedSpec x L)) (specDelta (schedSpec x L)) (c.h ω) k)
  filter_upwards [hR.ae_pieceRegular] with ω hω k hk hs
  have hlen : k < (schedSpec x L).2.2.length := by
    simpa only [schedSpec, length_scheduleProgram] using hk
  have hl := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := schedSpec x L)
    rfl (isFlowProg_spec x true L) (specDelta_ne_top _)
    (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) j ω) hlen).1 hs
  obtain ⟨hW0, hW, η, hη, _⟩ := hω k _ _ hl
  have hT := RootU19.instrTime_sched_ne_top x L hk
  have hd : specDelta (schedSpec x L) k = instrTime (schedSpec x L) k := by
    simp only [specDelta, hT, ↓reduceIte]
  set e := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) k ω with he_def
  have he : IsRegularDriver e :=
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) k
  have hfin : min (specDelta (schedSpec x L) k) e.2 ≠ ⊤ :=
    ne_top_of_le_ne_top (specDelta_ne_top _ k) (min_le_left _ _)
  rw [← hd] at hW hη
  obtain ⟨η', hη', -⟩ := exists_isGeneratingTrace_rdrv_recOf he hfin hW hη
  exact ⟨isDrvGood_of_continuousOn_le he hfin hW, η', hη'⟩

/-- **The joined future driver generates a trace on `[0, ∞)`, almost surely, for every history whose
old pieces succeeded and every candidate.** -/
theorem ae_futureJoined_trace (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), RootJ31.oldSuccess c r l ω →
      (∀ (j : ℕ) (hj : j < (RootJ31.futureProgram c r l a).length), LocalExt.IsDrvGood (recHist
        (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω ⟨j, hj⟩))) ∧
      ∃ γ, IsGeneratingTrace (futureJoined c r l a ω) ⊤ γ := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  rw [ae_all_iff]
  intro l
  rw [ae_all_iff]
  intro a
  filter_upwards [ae_launched_rdrv_trace h13 c (rootPt r.1) (RootJ31.futureProgram c r l a)]
    with ω hω hold
  have hlen : (RootJ31.futureProgram c r l a).length =
      (RootJ31.historyProgram c r l).length + 1 := by
    simp only [RootJ31.futureProgram, List.length_append, List.length_singleton]
  have hall : ∀ (i : ℕ) (hi : i < (RootJ31.futureProgram c r l a).length),
      LocalExt.IsDrvGood (recHist (stopRec c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (RootJ31.futureProgram c r l a)) i ω)) ∧
      ∃ η, IsGeneratingTrace (fun t : ℝ≥0 => rdrv (stopRec c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (RootJ31.futureProgram c r l a)) i ω) t) ⊤ η :=
    fun i hi => hω i hi ((allSucc_future_of_oldSuccess c r l a ω hold).mono (by omega))
  exact ⟨fun j hj => (hall j hj).1,
    exists_isGeneratingTrace_joinedRead _ _ fun i hi => (hall i hi).2⟩

end InteractingSLE.Theorem14.GW2TipSystem.Gm
