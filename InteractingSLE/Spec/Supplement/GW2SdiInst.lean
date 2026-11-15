/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdiBuf
import InteractingSLE.Spec.Supplement.GW2SzLoc

/-!
# GW2's schedule instance with `ℍ` off the history's success (RELDET round 17's correction)

Packet PROVE-GW2-SDE (round 6). PROVE-GW2-RELDET (round 17) found the following defect.
* Off `RootJ31.oldSuccess` the explored driver `GW2Rd.schedW` is the zero driver, so the explored hull is a
  deterministic slit, which is not marked local.
* The corrected stage union is therefore `ℍ` off `oldSuccess`, as GB6's `retOfRec` does for the retained set.
* SDE's shape field must then use the physical union only on the live event.

This file restates round 5's schedule instance accordingly:

* `succSet`, **`succRec c r l`**: the stage records whose encoded history succeeded (`c.sigma r l` is
  `comap stageEncRec`, and `oldSuccess` is retained, `RootJ31.measurableSet_oldSuccess_rootSigma`);
  **`augRec_mem_succRec_iff`**;
* **`schedUnionS`**: the physical union on `oldSuccess`, `ℍ` off it. `schedUnionS_eq` gives RELDET's form
  `invHull ∪ (if oldSuccess then fwdHull schedW (T + t) else ℍ)`. **`schedUnionS_subset_isOpen`** and
  **`measurable_schedUnionS`** (from RELDET's `GW2Rd.schedUnion_subset_isOpen`, `GW2Rd.measurable_schedUnion`)
  discharge `sets_open` and `sets_meas`;
* `SchedChoice.succ` (`E₀ ∩ succRec`), **`schedInstS`** (round 5's instance with `B := schedUnionS` and
  `E := (E₀ ∩ succRec) ∩ aliveRec`);
* **`OpenLinesS`** (the open lines inputs without `sets_meas`, `sets_open`), `openLines_of_S`;
* **`schedInstS_good`**: `StageInst.Good` from the same inputs as round 5, with the shape transferred from the
  physical union on the live event (live records are successful records);
* `PkgFamily.withSchedS`, **`RootPairInputsSchedLBS`**, **`retainedComparisonsLossy_rootJ32B_schedS`** (the lossy J32
  pair with BUF's slow half and the corrected instances).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Sdi

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Rd GW2Sde GW2Sdf GW2Sdh Restart.DomainMarkov Restart.FCDet Sec7.PocketTraversal Supp8.RelSafeS
  GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 LocalSets WholeField

/-! ### The successful stage records -/

section Succ

variable {Ω : Type u} [MeasurableSpace Ω]

theorem exists_succSet (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∃ O : Set RecData, MeasurableSet O ∧ stageEncRec c r l ⁻¹' O = {ω | oldSuccess c r l ω} := by
  have h := measurableSet_oldSuccess_rootSigma c r l
  rw [← comap_stageEncRec_sigma c r l] at h
  exact MeasurableSpace.measurableSet_comap.1 h

/-- The encoded histories that succeeded. -/
def succSet (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Set RecData :=
  (exists_succSet c r l).choose

/-- **The stage records whose encoded history succeeded.** -/
def succRec (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Set RecData :=
  {z | (pairEnc.symm z).1 ∈ succSet c r l}

theorem measurableSet_succRec (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    MeasurableSet (succRec c r l) :=
  (measurable_fst.comp pairEnc.symm.measurable) (exists_succSet c r l).choose_spec.1

/-- **A stage record is successful exactly when the history succeeded.** -/
theorem augRec_mem_succRec_iff (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (y : Ω → RecData) (ω : Ω) : augRec (stageEncRec c r l) y ω ∈ succRec c r l ↔ oldSuccess c r l ω := by
  have he := (exists_succSet c r l).choose_spec.2
  have h : stageEncRec c r l ω ∈ succSet c r l ↔ oldSuccess c r l ω := by
    change ω ∈ stageEncRec c r l ⁻¹' succSet c r l ↔ ω ∈ {ω | oldSuccess c r l ω}
    unfold succSet
    rw [he]
  simp only [succRec, augRec, mem_ofPred_eq, MeasurableEquiv.symm_apply_apply]
  exact h

end Succ

/-! ### The corrected stage union -/

section Union

variable {Ω : Type u} [MeasurableSpace Ω]

open Classical in
/-- **The corrected stage union**: the physical union on the history's success, `ℍ` off it. -/
def schedUnionS (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (t : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  if oldSuccess c r l ω then schedPhysUnion c r l a t ω else H

open Classical in
/-- RELDET's form of the corrected union: the retained set together with the explored hull, or `ℍ`. -/
theorem schedUnionS_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (t : ℝ≥0) (ω : Ω) :
    schedUnionS c r l a t ω = Supp8.Q3Rel.invHull (rdrv (gb6Rec c.s c.W c.ζ ω)) c.s ∪
      (if oldSuccess c r l ω then schedHull c r l a (historyTime c r l + t) ω else H) := by
  unfold schedUnionS
  split_ifs
  · rfl
  · exact (union_eq_right.2 (GW2Shr.invHull_subset_H (continuous_rdrv _) c.s.coe_nonneg)).symm

/-- **The corrected union lies in `ℍ` and has an open complement**, at every sample. -/
theorem schedUnionS_subset_isOpen (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (t : ℝ≥0) (ω : Ω) : schedUnionS c r l a t ω ⊆ H ∧ IsOpen (H \ schedUnionS c r l a t ω) := by
  unfold schedUnionS
  split_ifs
  · exact schedUnion_subset_isOpen c r l a (historyTime c r l) t ω
  · exact ⟨subset_rfl, by rw [sdiff_self]; exact isOpen_empty⟩

/-- **The corrected union is hitting-measurable.** -/
theorem measurable_schedUnionS (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (t : ℝ≥0) : Measurable[_, hittingSigma] (schedUnionS c r l a t) := by
  classical
  have hS : MeasurableSet {ω | oldSuccess c r l ω} :=
    stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _ _ (measurableSet_oldSuccess_rootSigma c r l)
  exact Measurable.ite hS (measurable_schedUnion c r l a (historyTime c r l) t) measurable_const

end Union

/-! ### The corrected instance -/

section Inst

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The record event restricted to successful stage records. -/
def _root_.InteractingSLE.Theorem14.GW2Sdh.SchedChoice.succ (ch : SchedChoice Ω) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : SchedChoice Ω :=
  { ch with E₀ := ch.E₀ ∩ succRec c r l }

/-- **The corrected schedule instance**: round 5's instance on successful records with the union `schedUnionS`. -/
def schedInstS (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (ch : SchedChoice Ω) :
    StageInst Ω :=
  { schedInst c r l a GT hA (ch.succ c r l) with B := schedUnionS c r l a }

end Inst

/-- **The open lines inputs of the corrected instance** (`sets_meas` and `sets_open` are discharged). -/
structure OpenLinesS {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (I : StageInst Ω)
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hWm : ∀ t, Measurable (I.W t)) :
    Prop where
  sets_le : ∀ t, stgFilt (physFilt (measurable_gb6Rec_src c) hWm c.P) I.T (GW2Sde.measurable_stageEncRec c r l) t ≤
    I.ℋ t
  sets_amb : ∀ t, I.ℋ t ≤ mΩ
  loc : ∀ t, IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (centredField c.h I.u₀) c.P
  mean : ∀ (w : WordType) (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
    IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
    ∀ᵐ ω ∂c.P, GW2Stl.stageMeanAt I c r l w t ψ ω (g ω)
  noThreshold : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → ∀ u : ℝ≥0, (u : ℝ≥0∞) < I.cap c ω →
    ¬ ForceWord.ThresholdCondition
      (flowLineRhoL c.κ (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 0)
      (flowLineRhoR c.κ (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 0)
      (I.drv c u ω)
      (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -I.drv c v.toNNReal ω)
        (-flowLineXL (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 i) u)
      (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => I.drv c v.toNNReal ω)
        (flowLineXR (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 j) u)
  condGFF : ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : ℝ), Measurable[𝒢.1] (I.srec c r l) ∧ 0 ≤ M ∧
    (∀ y ∈ I.E, ∀ x ∉ (I.β y).jumps, |(I.β y).fn x| ≤ M) ∧
    ∀ᵐ ω₀ ∂c.P, I.srec c r l ω₀ ∈ I.E →
      IsGFFWithBoundaryData (condExpKernel c.P 𝒢.1 ω₀) I.Hr (I.β (I.srec c r l ω₀)).fn (I.β (I.srec c r l ω₀)).jumps

section Good

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- `OpenLines` of the corrected instance from `OpenLinesS`. -/
theorem openLines_of_S (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (ch : SchedChoice Ω)
    (h : OpenLinesS (schedInstS c r l a GT hA ch) c r l (measurable_schedW c r l a)) :
    OpenLines (schedInstS c r l a GT hA ch) c r l (measurable_schedW c r l a) where
  sets_le := h.sets_le
  sets_amb := h.sets_amb
  sets_meas := measurable_schedUnionS c r l a
  sets_open := schedUnionS_subset_isOpen c r l a
  loc := h.loc
  mean := h.mean
  noThreshold := h.noThreshold
  condGFF := h.condGFF

/-- **`StageInst.Good` for the corrected schedule instance** (as `GW2Sdh.schedInst_good`; the shape of the corrected
union is the physical union's on the live event, whose records are successful). -/
theorem schedInstS_good (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGood c.s (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (hV : ∀ ω, V ω ≠ ⊤)
    (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hopen : OpenLinesS (schedInstS c r l a GT hA ch) c r l (measurable_schedW c r l a)) :
    (schedInstS c r l a GT hA ch).Good c r l := by
  set I := schedInstS c r l a GT hA ch with hI
  set I₀ := schedInst c r l a GT hA (ch.succ c r l) with hI₀
  have hopen' := openLines_of_S c r l a GT hA ch hopen
  have hWm : ∀ t, Measurable (I.W t) := measurable_schedW c r l a
  have hver : IsGB6RelVersionR c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V := hA.1
  have hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hρs := hA.2.choose_spec
  have hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R) :=
    measurable_stgPreRec_amb hGT.1 (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2 hver I.T
  have hE : MeasurableSet I.E :=
    (hE₀.inter (measurableSet_succRec c r l)).inter (measurableSet_aliveRec _ c.s hρ.1)
  have hfin : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := GW2Sdf.StageInst.E_good_of_record I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hHr : Measurable I.Hr := measurable_stgField_inst I hv hpre
  have hzb := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  obtain ⟨𝒢, M, hrec, hM0, hM, hgff⟩ := hopen.condGFF
  have hshape : ∀ (w : WordType) (t : ℝ≥0), ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) →
      min (physClock c.s I.W c.W c.ζ I.GT (I.T + t) ω) (I.V ω) < I.V ω →
      H \ I.B t ω = (relChart (gb6Rec c.s c.W c.ζ ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun u => I.R u ω)
          (min (physClock c.s I.W c.W c.ζ I.GT (I.T + t) ω) (I.V ω)).toNNReal) := by
    intro w t
    filter_upwards [StageInst.shape_of_physUnion (I := I₀) (c := c) (r := r) (l := l) hGT.1 hver hGT.2.2
      (hEgood.mono fun _ h hm => (h hm).1) (fun _ _ => rfl) w t] with ω h hlive hlt
    have hsucc : oldSuccess c r l ω := (augRec_mem_succRec_iff c r l _ ω).1 hlive.1.1.2
    have hB : I.B t ω = I₀.B t ω := by
      change schedUnionS c r l a t ω = schedPhysUnion c r l a t ω
      unfold schedUnionS
      exact ite_eq_left hsucc
    rw [hB]
    exact h hlive hlt
  exact
    { physGood := hGT.1
      measurable_W := hWm
      measurableSet_GT := hGT.2.1
      GT_ae := hGT.2.2
      version := hv
      measurable_ρ := hρ.1
      isPathRule_ρ := hρ.2.1
      V_eq := hρ.2.2
      measurable_ρs := hρs.1
      isPathRule_ρs := hρs.2.1
      ρs_ne_top := hρs.2.2.1
      ρs_mono := hρs.2.2.2.1
      announce := hρs.2.2.2.2
      prefix_retained := StageInst.prefix_retained_of_path I hGT.1 hWm hGT.2.1 hGT.2.2 hver
        fun t ht => (comap_schedW_le_sigma c r l a ht).trans (LocalSets.le_aeSigma _ _)
      measurable_β := hβ.1
      measurableSet_E := hE
      countable_wordType := hβ.2.1
      isSorted := fun y _ => hβ.2.2 y
      E_good := hEgood
      measurable_Hr := hHr
      lines := fun w => GW2Stl.StageInst.linesLocal_of I hv hpre hβ.1 hE hHr hWm w
        (Eventually.of_forall fun _ _ hc => chartTransport_eq_stgField hc) hu₀.1 hzb hopen'.sets_le
        hopen'.sets_amb hopen'.sets_meas hopen'.sets_open hopen'.loc (hshape w)
        (hopen'.mean w) hopen'.noThreshold 𝒢.2 hrec hM0 hM hgff }

/-- **`StageInst.Good` for the corrected schedule instance with RELDET's good set.** -/
theorem schedInstS_good_of_reldet (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (hV : ∀ ω, V ω ≠ ⊤)
    (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hopen : OpenLinesS (schedInstS c r l a (schedGT h13 c r l a) hA ch) c r l (measurable_schedW c r l a)) :
    (schedInstS c r l a (schedGT h13 c r l a) hA ch).Good c r l :=
  schedInstS_good c r l a (schedGT_spec h13 c r l a) hA hV ch hβ hE₀ hu₀ hopen

end Good

/-! ### The lossy J32 pair with the corrected instances -/

/-- The package with the corrected schedule instances. -/
def _root_.InteractingSLE.Theorem14.GW2Sde.PkgFamily.withSchedS (K : PkgFamily.{u})
    (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) : PkgFamily.{u} :=
  fun Ω _ _ c r =>
    { K Ω c r with
      inst := fun l a => schedInstS c r l a (schedGT h13 c r l a) (ver Ω c r l a).isA (ch Ω c r l a) }

/-- **The remaining inputs of the lossy R11 pair for J32 with the corrected schedule instances and BUF's slow
half.** -/
structure RootPairInputsSchedLBS (Kb : ℕ → PkgFamily.{u}) (h13 : Exist.Theorem13Statement.{u})
    (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) : Prop where
  word : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
    Measurable (ch Ω c r l a).β ∧ (range fun y => wordType c.κ ((ch Ω c r l a).β y)).Countable ∧
      ∀ y, ((ch Ω c r l a).β y).IsSorted
  measurableSet_E₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), MeasurableSet (ch Ω c r l a).E₀
  u₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), IsBoundedHarmonicExtension c.b c.jumps (ch Ω c r l a).u₀
  openLines : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
    OpenLinesS (schedInstS c r l a (schedGT h13 c r l a) (ver Ω c r l a).isA (ch Ω c r l a)) c r l
      (measurable_schedW c r l a)
  nearStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      (((Kb k).withSchedS h13 ver ch Ω c r).nearStop l n m a).Good
        (((Kb k).withSchedS h13 ver ch Ω c r).inst l a) c r l
  slowStop : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k' : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k' + 4 → ∀ a : ℕ,
      (((Kb k).withSchedS h13 ver ch Ω c r).slowStop l a).Good (((Kb k).withSchedS h13 ver ch Ω c r).inst l a) c r l
  words : ∀ k : ℕ,
    FrameNWordStatement RootJ32.constructionFamily (((Kb k).withSchedS h13 ver ch).rootFrameN nearLam)
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    RootNearImg32L ((Kb k).withSchedS h13 ver ch) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      GW2Bf.J32DriverId ((Kb 0).withSchedS h13 ver ch) Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      GW2Sdg.RootStopCovers ((Kb 0).withSchedS h13 ver ch) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      GW2Bf.J32ShellChoice ((Kb 0).withSchedS h13 ver ch) Ω c r l a

theorem rootPairInputs32LB_of_schedS {Kb : ℕ → PkgFamily.{u}} {h13 : Exist.Theorem13Statement.{u}}
    {ver : SchedVerFamily.{u}} {ch : SchedChoiceFamily.{u}} (hK : RootPairInputsSchedLBS Kb h13 ver ch) :
    RootPairInputs32LB (fun k => (Kb k).withSchedS h13 ver ch) nearLam where
  lam_ne := nearLam_ne
  inst _ Ω _ _ c r l a := schedInstS_good_of_reldet h13 c r l a (ver Ω c r l a).isA (ver Ω c r l a).V_ne_top
    (ch Ω c r l a) (hK.word Ω c r l a) (hK.measurableSet_E₀ Ω c r l a) (hK.u₀ Ω c r l a) (hK.openLines Ω c r l a)
  nearStop := hK.nearStop
  slowStop := hK.slowStop
  words := hK.words
  nearImg := hK.nearImg
  driverId := hK.driverId
  stopCovers := hK.stopCovers
  shell := hK.shell

/-- **Both C24 binders for J32 with the corrected schedule instances, the lossy near binder and BUF's slow half**
(R114; Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossy_rootJ32B_schedS (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (Kb : ℕ → PkgFamily.{u})
    (ver : SchedVerFamily.{u}) (ch : SchedChoiceFamily.{u}) (hK : RootPairInputsSchedLBS Kb h13 ver ch) :
    RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u} :=
  retainedComparisonsLossy_rootJ32B h12p₀ h13₀ h13 _ nearLam (rootPairInputs32LB_of_schedS hK)

end InteractingSLE.Theorem14.GW2Sdi
