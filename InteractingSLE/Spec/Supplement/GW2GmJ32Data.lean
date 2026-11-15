/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Read
import InteractingSLE.Spec.Supplement.GW2RootJ31Alive
import InteractingSLE.Spec.Supplement.GW2GmCap

/-!
# J32's construction data and its structural facts

Packet PROVE-GW2-GEOM2 (ruling R110). The construction `RootJ32.constructionFamily` is J31's with the stage
driver, sample, entry, observation and tip read through J32's running-maximum inverse clock
(`GW2GmJ32Read`). The angle, bands, failure (buffer), clock, increments, reach and slow sets, the drift bound
and the protected root event are J31's, literally.

* `experimentData`, `experiment`, `construction`, **`constructionFamily`**, `rootCoverStatement`;
* the sharing identities with J31 (`sourceSample_fst`, `failure_eq`, `clock_eq`, …, all `rfl`);
* the entry/failure facts and the alive-history facts (old success, launch, time order, admissibility),
  as for J31;
* the fields `band_open`, `reach_measurable`, `record_read`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ32

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootK3 RootD25 RootV7

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- J32's experiments: J31's with the readers of `GW2GmJ32Read`. -/
def experimentData (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    StageModelData Ω c.Θ c.Q DriverRecord (c.sigma r) where
  ang := RootJ31.candidateAngle c r
  X := sourceX c r
  γ := sourceTip c r
  S := sourceEntry c r
  F := RootJ31.sourceFailure c r
  I := fun _ _ => Ioo (7 / 4) (9 / 4)
  sample := sourceSample c r
  kernel := fun l a => Kernel.mapOfMeasurable (condExpKernel c.P (c.sigma r l))
    (sourceSample c r l a) (measurable_sourceSample c r l a)
  reach := fun _ _ => reachSet
  slow := fun _ _ => slowSet
  p₀ := 1

def experiment (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) : Experiment c r where
  data := experimentData c r
  sampleMeas := measurable_sourceSample c r
  driftBound := RootJ31.sourceDriftBound c r
  Y := sourceDriver c r
  clock := fun l a q => RootJ31.sourceClock c r l a q

def construction (c : SourceData Ω) : Construction c where
  G := RootCv.coverEvent c
  experiment := experiment c

/-- **The successor construction J32** (ruling R110). -/
def constructionFamily : ConstructionFamily.{u} := fun _ _ _ c => construction c

theorem withCover_constructionFamily :
    RootCv.withCover constructionFamily.{u} = constructionFamily.{u} := rfl

theorem rootCoverStatement (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) : RootCoverStatement constructionFamily.{u} :=
  RootCv.rootCoverStatement_of_G_eq h13 h13₀ constructionFamily fun _ _ _ _ => rfl

/-! ### Sharing with J31 -/

omit [StandardBorelSpace Ω] in
/-- J32's sample has J31's lifetime. -/
theorem sourceSample_fst (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (sourceSample c r l a ω).1 = (RootJ31.sourceSample c r l a ω).1 := rfl

theorem failure_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    (experiment c r).data.F = RootJ31.sourceFailure c r :=
  (rfl : RootJ31.sourceFailure c r = RootJ31.sourceFailure c r)

theorem clock_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    (experiment c r).clock = fun l a (q : c.Q) => RootJ31.sourceClock c r l a (q : ℝ≥0) :=
  (rfl : (fun l a (q : c.Q) => RootJ31.sourceClock c r l a (q : ℝ≥0)) = _)

theorem ang_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    (experiment c r).data.ang = RootJ31.candidateAngle c r :=
  (rfl : RootJ31.candidateAngle c r = RootJ31.candidateAngle c r)

theorem G_eq (c : SourceData Ω) : (construction c).G = RootCv.coverEvent c :=
  (rfl : RootCv.coverEvent c = RootCv.coverEvent c)

theorem driftBound_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    (experiment c r).driftBound = RootJ31.sourceDriftBound c r :=
  (rfl : RootJ31.sourceDriftBound c r = RootJ31.sourceDriftBound c r)

theorem reach_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    (experiment c r).data.reach = fun _ _ => reachSet :=
  (rfl : (fun (_ : List (EntryIdx c.Θ c.Q)) (_ : ℕ) => reachSet) = _)

/-! ### Entry and failure -/

omit [StandardBorelSpace Ω] in
theorem sourceEntry_ge_historyTime (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (RootJ31.historyTime c r l : ℝ) ≤ sourceEntry c r l a ω :=
  NNReal.coe_le_coe.mpr (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ _))

theorem switchedEntry_le_buffer (a : ℝ≥0) (ε x : ℝ) (s v v₀ T F : ℝ≥0) (p : RecData × RecData) :
    switchedEntry a ε x s v v₀ T F p ≤ F := by
  classical
  unfold switchedEntry
  split_ifs
  · unfold invClock
    apply ciSup_le
    intro q
    split_ifs with hq
    · exact ENNReal.coe_le_coe.mp hq.2.1
    · exact zero_le
  · exact le_rfl

omit [StandardBorelSpace Ω] in
theorem sourceEntry_le_failure (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    sourceEntry c r l a ω ≤ RootJ31.sourceFailure c r l a ω :=
  NNReal.coe_le_coe.mpr (add_le_add le_rfl (switchedEntry_le_buffer _ _ _ _ _ _ _ _ _))

omit [StandardBorelSpace Ω] in
theorem sourceEntry_eq_failure_of_not_reach (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (hf : sourceSample c r l a ω ∉ reachSet) :
    sourceEntry c r l a ω = RootJ31.sourceFailure c r l a ω := by
  unfold sourceEntry RootJ31.sourceFailure
  rw [show switchedEntry _ _ _ _ _ _ _ _ _ = _ from ite_eq_right hf]

omit [StandardBorelSpace Ω] in
theorem entry_lt_failure_imp_reach (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hSF : sourceEntry c r l a ω < RootJ31.sourceFailure c r l a ω) :
    sourceSample c r l a ω ∈ reachSet := by
  by_contra hf
  exact (ne_of_lt hSF) (sourceEntry_eq_failure_of_not_reach c r l a ω hf)

omit [StandardBorelSpace Ω] in
/-- An active J32 window has a live sample (J31's sample lifetime). -/
theorem live_of_entry_lt_failure (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hSF : sourceEntry c r l a ω < RootJ31.sourceFailure c r l a ω) :
    0 < (RootJ31.sourceSample c r l a ω).1 :=
  lt_of_le_of_lt bot_le (entry_lt_failure_imp_reach c r l a ω hSF)

/-! ### Alive histories -/

theorem oldSuccess_of_test (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) (ω : Ω)
    (ht : ω ∈ (experiment c r).data.tests l a q) : RootJ31.oldSuccess c r l ω :=
  (RootK32.sourceSample_live_geometry c r l a ω
    (live_of_entry_lt_failure c r l a ω (ht.1.trans ht.2.1))).2.1

theorem next_piece_live_of_test (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) (ω : Ω)
    (ht : ω ∈ (experiment c r).data.tests l a q) :
    let spec := schedSpec (rootPt r.1)
      (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])
    specDelta spec (RootJ31.historyProgram c r l).length <
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec (RootJ31.historyProgram c r l).length ω).2 := by
  have hTq : RootJ31.historyTime c r l < (q : ℝ≥0) :=
    NNReal.coe_lt_coe.mp ((sourceEntry_ge_historyTime c r l a ω).trans_lt ht.1)
  have hqF : ((q : ℝ≥0) : ℝ) <
      (RootJ31.historyTime c r l : ℝ) + RootJ31.sourceBuffer c r l a ω := by
    simpa only [experiment, experimentData, RootJ31.sourceFailure, NNReal.coe_add] using ht.2.1
  have hδ : (q : ℝ≥0) - RootJ31.historyTime c r l < RootJ31.sourceBuffer c r l a ω := by
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_sub hTq.le]
    linarith
  have hlt := (ENNReal.coe_lt_coe.mpr hδ).trans_le
    (RootJ31.sourceBuffer_coe_le_next_lifetime c r l a ω)
  have he := RootH29.canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h
    (rootPt r.1) (RootJ31.candidateAngle c r a) (RootJ31.historyProgram c r l)
    (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) q ω
  change _ < (canonSpecFam _ _ _ _ _
    (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
      [((RootJ31.candidateAngle c r a : ℝ),
        RootJ31.historyTime c r l + RootJ31.candidateCap c r a)]))
        (RootJ31.historyProgram c r l).length ω).2 at hlt
  rw [he] at hlt
  simpa only [RootH29.specDelta_last, RootJ31.historyTime] using hlt

theorem oldSuccess_cons_of_test (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) (ω : Ω)
    (ht : ω ∈ (experiment c r).data.tests l a q) :
    RootJ31.oldSuccess c r ((RootJ31.candidateAngle c r a, q) :: l) ω := by
  have hold := oldSuccess_of_test c r l a q ω ht
  have hnext := next_piece_live_of_test c r l a q ω ht
  rintro ⟨j, hj'⟩
  have hj : j < (RootJ31.historyProgram c r l).length + 1 := by
    simpa only [RootJ31.historyProgram_cons, List.length_append, List.length_singleton] using hj'
  change (stopRec c.hκ c.h12p c.βA c.c₀ c.h
    (schedSpec (rootPt r.1) (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q) :: l)))
      j ω).2.2 = false
  rw [RootJ31.historyProgram_cons]
  by_cases hjold : j < (RootJ31.historyProgram c r l).length
  · rw [stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hjold ω]
    exact hold ⟨j, hjold⟩
  · have hje : j = (RootJ31.historyProgram c r l).length := by omega
    rw [hje]
    exact (RootCv.recOf_flag_eq_false_iff _ _).mpr hnext

/-- Every J32-alive history is a successful physical history. -/
theorem oldSuccess_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    RootJ31.oldSuccess c r l ω := by
  cases l with
  | nil => exact RootJ31.oldSuccess_nil_of_cover c r ω ha
  | cons x l =>
    obtain ⟨_, htest⟩ := ha
    obtain ⟨a, htest⟩ := mem_iUnion.mp htest
    obtain ⟨hang, ht⟩ := mem_iUnion.mp htest
    have he : (RootJ31.candidateAngle c r a, x.2) = x := Prod.ext hang rfl
    rw [← he]
    exact oldSuccess_cons_of_test c r l a x.2 ω ht

/-- J32-alive histories are strictly time-ordered. -/
theorem pairwise_lt_historyProgram_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ (l : List (EntryIdx c.Θ c.Q)) (ω : Ω),
      ω ∈ (experiment c r).data.alive ((construction c).G r) l →
      (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2)
  | [], _, _ => by
    simp only [RootJ31.historyProgram, entryList, List.map_nil, schedOf, List.reverse_nil,
      List.pairwise_singleton]
  | x :: l, ω, ha => by
    obtain ⟨hprev, htest⟩ := ha
    obtain ⟨a, htest⟩ := mem_iUnion.mp htest
    obtain ⟨hang, ht⟩ := mem_iUnion.mp htest
    have ih := pairwise_lt_historyProgram_of_alive c r l ω hprev
    have hT : RootJ31.historyTime c r l < (x.2 : ℝ≥0) :=
      NNReal.coe_lt_coe.mp ((sourceEntry_ge_historyTime c r l a ω).trans_lt ht.1)
    have hTl : RootJ31.historyTime c r l =
        Sec5.Prop513Schedule.lastTime 0 (RootJ31.historyProgram c r l) :=
      Gm.schedTime_length_eq_lastTime _
    rw [RootJ31.historyProgram_cons]
    refine List.pairwise_append.2 ⟨ih, List.pairwise_singleton _ _, fun p hp q hq => ?_⟩
    rw [List.mem_singleton.1 hq]
    exact ((Gm.le_lastTime_of_mem (Gm.timeOrdered_of_pairwise_lt ih) p hp).trans
      hTl.symm.le).trans_lt hT

theorem timeOrdered_historyProgram_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l) :=
  Gm.timeOrdered_of_pairwise_lt (pairwise_lt_historyProgram_of_alive c r l ω ha)

theorem schedAdm_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l)
    (hseed : RootCv.RootSeedOK c r.1) :
    SchedAdm c.b c.jumps c.Θ c.Q (κ := c.κ) (rootPt r.1) (rootEntry r.1) (entryList l) := by
  refine ⟨(RootI30.schedAdm_nil_of_seedOK c r hseed).1, ?_,
    pairwise_lt_historyProgram_of_alive c r l ω ha⟩
  intro p hp
  simp only [schedOf, entryList, List.mem_cons, List.mem_reverse, List.mem_map] at hp
  rcases hp with rfl | ⟨y, -, rfl⟩
  · exact ⟨r.1.2.1.property, r.1.2.2.property⟩
  · exact ⟨y.1.property, y.2.property⟩

/-! ### Three fields -/

theorem experiment_band_open (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : IsOpen ((experiment c r).data.I l a) :=
  isOpen_Ioo

theorem experiment_reach_measurable (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    MeasurableSet ((experiment c r).data.reach l a) := measurableSet_reachSet

theorem experiment_record_read (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (experiment c r).data.alive ((construction c).G r) l →
      ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ((experiment c r).data.sample l a ω).1 →
        ((experiment c r).data.sample l a ω).2 q = (experiment c r).Y l a ω q :=
  Eventually.of_forall fun ω _ _ hq => sourceSample_read c r l a ω hq

end InteractingSLE.Theorem14.GW2TipSystem.RootJ32
