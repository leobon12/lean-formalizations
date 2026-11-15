/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TfField

/-!
# The physical curve of the schedule is a marked local set inside the explored trace (time-ordered histories)

Packet PROVE-GW2-RELDET. The time-ordered case of `GW2TcCurve.SchedPhysCurveStatement`, proved outright from Theorems
1.2–1.3. The statement as stated is false for unordered histories (handoff round 20); this case is common to every
option for that decision.

At a root `x`, a time-ordered history `l`, a candidate `a` and a time `q ≥ T` (`T` the history time):
* **the capped program**: the history followed by the candidate run for own time `d = min(q − T, cap)` (`capOwn`).
* **the marks** (`capMarks`): the retained past of the capped program, the history records, the explored path on
  `[0, q]` and the null sets. They are field-determined.
* **the physical curve**: a measurable version of the capped program's stage set on `oldSuccess`, `ℍ` off it.
* **locality**: round 10's stage-set locality (`SB.Lcd.stageSet_markedLocal_of_thm12_thm13`) for the retained past,
  carried to the marks by `isHistoryAvoidanceLocal_ite_H_trace`. On `oldSuccess` every mark agrees a.s. with a retained
  event, because there:
  - the records are the retained past (`pastMap_of_allSucc_pred`);
  - the explored path up to `q` is the capped program's joined read of it (`Gm.futureJoined_eq_cappedRead`).
* **inclusion**: the stage set lies in the physical set, which lies in the joined trace on `[0, T + d]`
  (`Gm.prefixSet_capped_subset`, also after the candidate's death). That trace lies in the trace on `[0, q]`.

**`exists_schedPhysCurveX_of_timeOrdered`**: the same at any root `x`, with the curve inside `x + (explored trace)`
(nothing in the proof reads the root, except the final translate). **`exists_schedPhysCurve_of_timeOrdered`**: the
conclusion of `SchedPhysCurveStatement` at every such instance (root `0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec5.Prop513Schedule LocalSets WholeField

section Defs

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The candidate's own time in the program capped at `q`. -/
def capOwn (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0) : ℝ≥0 :=
  min (q - historyTime c r l) (candidateCap c r a)

/-- The program capped at `q`. -/
abbrev capProg (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0) :
    List (ℝ × ℝ≥0) :=
  Gm.cappedProgram c r l a (capOwn c r l a q)

/-- The retained past of the program capped at `q`. -/
@[instance_reducible]
def capPast (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0) :
    MeasurableSpace Ω :=
  pastSigma c.κ c.b c.jumps (schedSpec (rootPt r.1) (capProg c r l a q))
    (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (capProg c r l a q))) (capProg c r l a q).length

/-- **The marks of the capped schedule.** -/
@[instance_reducible]
def capMarks (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0) :
    MeasurableSpace Ω :=
  capPast c r l a q ⊔
    (⨆ j : Fin ((entryList l).length + 1),
      MeasurableSpace.comap (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j) inferInstance) ⊔
    (⨆ t : ℝ≥0, ⨆ (_ : t ≤ q), MeasurableSpace.comap (schedW c r l a t) inferInstance) ⊔ Ito.nullSets c.P

end Defs

theorem nullSets_le_aeSigma {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (P : Measure Ω) :
    Ito.nullSets P ≤ aeSigma m P := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨-, hs⟩
  exact ⟨∅, @MeasurableSet.empty _ m, ae_eq_empty.2 hs⟩

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The physical curve of the schedule is a marked local set inside the explored trace, translated to the root**
(time-ordered histories, any root `x`: the physical explored curve is `x + schedTr`). -/
theorem exists_schedPhysCurveX_of_timeOrdered (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hord : TimeOrdered 0 (historyProgram c r l)) (u₀ : ℂ → ℝ) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    (q : ℝ≥0) (hq : historyTime c r l ≤ q) :
    ∃ 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets c.P ≤ 𝓜.1 ∧
      (∀ t ≤ q, Measurable[𝓜.1] (schedW c r l a t)) ∧
      (∀ j : Fin ((entryList l).length + 1),
        Measurable[𝓜.1] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) ∧
      𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P ∧
      ∃ S : Ω → Set ℂ, (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (S ω) U}) ∧
        IsHistoryAvoidanceLocal 𝓜.1 S (centredField c.h u₀) c.P ∧
        ∀ᵐ ω ∂c.P, oldSuccess c r l ω →
          S ω ∩ H ⊆ (fun s => (rootPt r.1 : ℂ) + schedTr c r l a ω s) '' Icc 0 q := by
  classical
  set x := rootPt r.1 with hx
  set T := historyTime c r l with hT
  set d := capOwn c r l a q with hd
  have hdcap : d ≤ candidateCap c r a := min_le_right _ _
  have hdq : T + d ≤ q := by
    calc T + d ≤ T + (q - T) := add_le_add le_rfl (min_le_left _ _)
      _ = q := add_tsub_cancel_of_le hq
  set L := Gm.cappedProgram c r l a d with hL
  set spec := schedSpec x L with hspec
  set E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec with hEdef
  set n := L.length with hn
  set m := (historyProgram c r l).length with hm
  have hnm : n = m + 1 := Gm.length_cappedProgram c r l a d
  have hlenspec : spec.2.2.length = n := GW2Schedule.length_scheduleProgram 0 L
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x (specAngle spec) (specDelta spec) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  obtain ⟨hSm0, hSo, hSloc⟩ := SB.Lcd.stageSet_markedLocal_of_thm12_thm13 c.h12p h13 c.hκ c.hκ4 c.hb c.hh hS hreg hu₀ n
  obtain ⟨f, hf, hp⟩ := StagedDet.exists_pastMap_eq_comp_field c.h12p h13 c.hκ c.hκ4 c.hb c.hh hS hR n
  have hℋ₀d : capPast c r l a q ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P :=
    WalkLaw.pastSigma_le_aeSigma_centred hf hp u₀
  obtain ⟨A', -, hA'ae, hA'm⟩ := WalkLaw.exists_version_of_aeSigma (𝒢 := capPast c r l a q)
    (fun ω => WalkLaw.stageSet_subset_H (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) (E := E) n ω) hSo hSm0
  have hA'loc : IsHistoryAvoidanceLocal (capPast c r l a q) A' (centredField c.h u₀) c.P :=
    WalkLaw.isHistoryAvoidanceLocal_congr_ae (hA'ae.mono fun ω h => h.symm) hSloc
  have hhm := measurable_centredField c.hh.1 u₀
  have hpm : @Measurable Ω _ (capPast c r l a q) _ (pastMap c.κ c.b c.jumps spec E n) := comap_measurable _
  -- `oldSuccess` is the success of the capped program's history pieces
  have hsucc : ∀ ω, oldSuccess c r l ω ↔ AllSucc (specDelta spec) (fun j => E j ω) m := by
    intro ω
    rw [oldSuccess_iff_allSucc c r l ω]
    have hΔ : ∀ j < m, specDelta spec j = specDelta (schedSpec x (historyProgram c r l)) j :=
      fun j hj => specDelta_schedSpec_append x _ hj
    have hE' : ∀ j < m, E j ω = canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x (historyProgram c r l)) j ω :=
      fun j hj => RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
    constructor
    · intro h j hj
      show specDelta spec j < (E j ω).2
      rw [hΔ j hj, hE' j hj]
      exact h j hj
    · intro h j hj
      have h1 : specDelta spec j < (E j ω).2 := h j hj
      rw [hΔ j hj, hE' j hj] at h1
      exact h1
  have hE0 : @MeasurableSet Ω (capPast c r l a q) {ω | oldSuccess c r l ω} := by
    have hmle : m ≤ spec.2.2.length := by omega
    have e : {ω | oldSuccess c r l ω} =
        ⋂ i : Fin m, {ω | (pastMap c.κ c.b c.jumps spec E m ω i).2.2 = false} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter]
      rw [hsucc ω]
      exact allSucc_iff_flags rfl (isFlowProg_spec x true L) (specDelta_ne_top _) E hmle ω
    rw [e]
    have hmono := pastSigma_mono (κ := c.κ) (b := c.b) (jumps := c.jumps) spec E (show m ≤ n by omega)
    refine @MeasurableSet.iInter Ω _ (capPast c r l a q) _ _ fun i => hmono _ ?_
    exact ((measurable_snd.comp measurable_snd).comp ((measurable_pi_apply i).comp
      (comap_measurable (pastMap c.κ c.b c.jumps spec E m)))) (measurableSet_singleton false)
  -- on `oldSuccess` the retained past is the record sequence
  have hpast : ∀ ω, oldSuccess c r l ω →
      pastMap c.κ c.b c.jumps spec E n ω = programRecords c x L ω := by
    intro ω hω
    have hs : AllSucc (specDelta spec) (fun j => E j ω) (n - 1) := by
      rw [hnm, Nat.add_sub_cancel]
      exact (hsucc ω).1 hω
    rw [pastMap_of_allSucc_pred rfl (isFlowProg_spec x true L) (specDelta_ne_top _) E hlenspec.ge hs]
    rfl
  -- the marks agree with retained events on `oldSuccess`
  have htrace : capMarks c r l a q ≤ traceSigma c.P {ω | oldSuccess c r l ω} (capPast c r l a q) := by
    refine sup_le (sup_le (sup_le (le_traceSigma _ _) ?_) ?_) (nullSets_le_traceSigma _ _)
    · refine iSup_le fun j => ?_
      have hjm : (j : ℕ) < m := by
        have : m = (entryList l).length + 1 := by
          simp only [hm, historyProgram, schedOf, List.length_cons, List.length_reverse]
        omega
      have hjn : (j : ℕ) < n := by omega
      refine comap_le_traceSigma c.P _ hpm (measurable_pi_apply (⟨j, hjn⟩ : Fin n))
        (Eventually.of_forall fun ω hω => ?_)
      rw [hpast ω hω]
      exact (stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h x _ hjm ω).symm
    · refine iSup₂_le fun t ht => ?_
      refine comap_le_traceSigma c.P _ hpm
        ((measurable_pi_apply t).comp (measurable_joinedRead L)) ?_
      filter_upwards [Gm.ae_futureJoined_trace h13 c r, Gm.ae_continuousOn_capped h13 c r l a d] with ω hfut hcap hωE
      change schedW c r l a t ω = joinedRead L (pastMap c.κ c.b c.jumps spec E n ω) t
      rw [hpast ω hωE]
      have h1 : schedW c r l a t ω = Gm.futureJoined c r l a ω t :=
        congrFun (schedW_of_oldSuccess c r l a hωE) t
      rw [h1]
      by_cases htd : t ≤ T + d
      · exact Gm.futureJoined_eq_cappedRead c r l a hdcap ω hord hωE (hfut l a hωE).1 (hcap hωE).2 htd
      · -- beyond `T + d` the capped program is the whole future program
        have hdc : d = candidateCap c r a := by
          rcases min_choice (q - T) (candidateCap c r a) with h | h
          · exfalso
            apply htd
            have : T + d = q := by
              change T + min (q - T) (candidateCap c r a) = q
              rw [h]
              exact add_tsub_cancel_of_le hq
            rw [this]
            exact ht
          · exact h
        have hLf : L = futureProgram c r l a := by rw [hL, hdc]; rfl
        change Gm.futureJoined c r l a ω t = joinedRead L (programRecords c x L ω) t
        rw [hLf]
        rfl
  -- the marks are field-determined and ambient
  have hMd : capMarks c r l a q ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P := by
    refine sup_le (sup_le (sup_le hℋ₀d ?_) ?_) (nullSets_le_aeSigma _)
    · exact iSup_le fun j => Gm.comap_le_aeSigma_centred_of_field c u₀ (Gm.measurable_stopRec_field c _ j)
    · exact iSup₂_le fun t _ => Gm.comap_le_aeSigma_centred_of_field c u₀ (Gm.measurable_schedW_field c r l a t)
  have hMle : capMarks c r l a q ≤ mΩ := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) (Ito.nullSets_le c.P)
    · exact (measurable_pastMap_of_isStagedHistory hS n).comap_le
    · exact iSup_le fun j => (measurable_stopRec c.hβA.1 c.hh.1 _ j).comap_le
    · exact iSup₂_le fun t _ => (measurable_schedW c r l a t).comap_le
  have hpastle : capPast c r l a q ≤ capMarks c r l a q := le_sup_left.trans (le_sup_left.trans le_sup_left)
  obtain ⟨hAm, -⟩ := isHistoryAvoidanceLocal_ite_H hhm hA'loc hA'm hℋ₀d hE0
  refine ⟨⟨capMarks c r l a q, hMle⟩, le_sup_right, fun t ht => ?_, fun j => ?_, hMd,
    fun ω => if ω ∈ {ω | oldSuccess c r l ω} then A' ω else H, fun U hUH => hpastle _ (hAm U hUH),
    isHistoryAvoidanceLocal_ite_H_trace hhm hA'loc hA'm hℋ₀d hMd hE0 fun F hF => htrace F hF, ?_⟩
  · exact Measurable.of_comap_le ((le_iSup₂ (f := fun t (_ : t ≤ q) =>
      MeasurableSpace.comap (schedW c r l a t) inferInstance) t ht).trans (le_sup_right.trans le_sup_left))
  · exact Measurable.of_comap_le ((le_iSup (fun j : Fin ((entryList l).length + 1) =>
      MeasurableSpace.comap (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j) inferInstance) j).trans
      (le_sup_right.trans (le_sup_left.trans le_sup_left)))
  · -- the inclusion
    filter_upwards [hA'ae, Gm.ae_futureJoined_trace h13 c r, Gm.ae_continuousOn_capped h13 c r l a d,
      ae_schedW_trace c r l a h13] with ω hA hfut hcap htr hωE
    have hS1 : (if oldSuccess c r l ω then A' ω else H) = A' ω := by simp only [hωE, ↓reduceIte]
    rw [hS1, hA]
    have hγ : IsGeneratingTrace (Gm.futureJoined c r l a ω) ⊤ (schedTr c r l a ω) := by
      rw [← schedW_of_oldSuccess c r l a hωE]
      exact htr.1
    have hsub := Gm.prefixSet_capped_subset c r l a ω hord hωE (hfut l a hωE).1 hγ hdcap (hcap hωE).1
    intro z hz
    have hzP : z ∈ prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x L ω := by
      change z ∈ ExplState.physSet c.κ c.b c.jumps spec (fun k => E k ω)
      unfold ExplState.physSet
      simp only []
      rw [hlenspec]
      exact Or.inl (Or.inr hz.1.1)
    obtain ⟨w, ⟨s, hs, rfl⟩, rfl⟩ := hsub hzP
    exact ⟨s, ⟨hs.1, hs.2.trans hdq⟩, rfl⟩

/-- **The physical curve of the schedule is a marked local set inside the explored trace** (time-ordered histories,
root `0`). -/
theorem exists_schedPhysCurve_of_timeOrdered (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : TimeOrdered 0 (historyProgram c r l)) (u₀ : ℂ → ℝ) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    (q : ℝ≥0) (hq : historyTime c r l ≤ q) :
    ∃ 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets c.P ≤ 𝓜.1 ∧
      (∀ t ≤ q, Measurable[𝓜.1] (schedW c r l a t)) ∧
      (∀ j : Fin ((entryList l).length + 1),
        Measurable[𝓜.1] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) ∧
      𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P ∧
      ∃ S : Ω → Set ℂ, (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (S ω) U}) ∧
        IsHistoryAvoidanceLocal 𝓜.1 S (centredField c.h u₀) c.P ∧
        ∀ᵐ ω ∂c.P, oldSuccess c r l ω → S ω ∩ H ⊆ schedTr c r l a ω '' Icc 0 q := by
  obtain ⟨𝓜, h1, h2, h3, h4, S, h5, h6, h7⟩ := exists_schedPhysCurveX_of_timeOrdered h13 c r l a hord u₀ hu₀ q hq
  refine ⟨𝓜, h1, h2, h3, h4, S, h5, h6, ?_⟩
  filter_upwards [h7] with ω hω hωE z hz
  obtain ⟨s, hs, hzs⟩ := hω hωE hz
  refine ⟨s, hs, ?_⟩
  rw [← hzs, hr0, Complex.ofReal_zero]
  exact (zero_add _).symm

end InteractingSLE.Theorem14.GW2Rd
