/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdfAlive
import InteractingSLE.Spec.Supplement.GW2SyVer
import InteractingSLE.Spec.Supplement.GW2StlMean

/-!
# GW2's stage instance at the actual schedule: `StageInst.Good` from RELDET's and STAGEMEAN's pieces

Packet PROVE-GW2-SDE (round 5). The first field of `RootPairInputs32` asks `StageInst.Good` for the instance of every
history `l` and candidate `a`. This file builds the instance at the ACTUAL schedule from RELDET's round-15 bundle
(explored driver `GW2Rd.schedW`, trace `GW2Rd.schedTr`, good set `GW2Rd.exists_goodSet_sched`, announced versions
`GW2Rd.exists_schedVersionsA*`). It proves `StageInst.Good` with STAGEMEAN's lines constructor
(`GW2Stl.StageInst.linesLocal_of`), leaving only the genuinely open lines inputs:

* `schedPhysUnion` (the physical stage union `invHull ∪ fwdHull schedW (T + t)`), `schedChart` (the stage chart of a
  version); `SchedChoice` (the free choices: word map `β`, record event `E₀`, chart constants, `u₀`, marks `ℋ`);
* **`schedInst c r l a GT hA ch`**: the instance with stage start `historyTime c r l`, any GB6 good set `GT`, any
  announced version `hA` (its path rules chosen from `hA`), the record event `E₀ ∩ aliveRec` (live stage records,
  round 3) and the canonical stage field `stgField`;
* **`OpenLines I c r l`**: the open lines inputs: RELDET's union locality (`sets_le`, `sets_amb`, `sets_meas`,
  `sets_open`, `loc`) and STAGEMEAN's mean, no-threshold and conditional GFF inputs;
* **`schedInst_good`**: `StageInst.Good` from a good set, an announced version with finite stops, a word map with
  STAGEMEAN's three word properties (`GW2Stl.stageWordMap_targets` gives them for raised stage word maps), a
  measurable `E₀`, a bounded harmonic extension `u₀` of the boundary data, and `OpenLines`;
* `schedGT` (RELDET's good set, chosen) and `schedGT_spec`.

What `schedInst_good` DISCHARGES: the good set, measurability of the explored driver, the version and its announced
path rules, part (II) (`prefix_retained`, from `GW2Rd.comap_schedW_le_sigma`), `measurableSet_E`, `E_good`, the
stage field's measurability and transport, `harmonic`/`zbgff` (from `u₀`), the shape of the physical union, and the
threshold and integrability fields (STAGEMEAN's `lines_thr`, `lines_int`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Sdh

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Rd GW2Sde GW2Sdf Restart.DomainMarkov Restart.FCDet Sec7.PocketTraversal Supp8.RelSafeS
  GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 LocalSets WholeField

section Defs

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The physical stage union** at the schedule: the retained counterflow hull and the explored hull at `T + t`. -/
def schedPhysUnion (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (t : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  Supp8.Q3Rel.invHull (rdrv (gb6Rec c.s c.W c.ζ ω)) c.s ∪
    fwdHull (fun s : ℝ => schedW c r l a s.toNNReal ω) ((historyTime c r l + t : ℝ≥0) : ℝ)

/-- The stage chart of a version at the schedule. -/
def schedChart (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (ω : Ω) : Chart :=
  stgChart (relChart (gb6Rec c.s c.W c.ζ ω)) (fun t => R t ω)
    (stgStart c.s (schedW c r l a) c.W c.ζ GT V (historyTime c r l) ω)

/-- **The free choices of a stage instance** beyond RELDET's bundle. -/
structure SchedChoice (Ω : Type u) where
  β : RecData → BoundaryWord
  E₀ : Set RecData
  σa : ℝ
  kc : ℝ
  u₀ : ℂ → ℝ
  ℋ : ℝ≥0 → MeasurableSpace Ω

/-- **The stage instance at the actual schedule** for a good set `GT` and an announced GB6 version `hA`. -/
def schedInst (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (ch : SchedChoice Ω) :
    StageInst Ω where
  W := schedW c r l a
  γ := schedTr c r l a
  GT := GT
  R := R
  V := V
  ρ := hA.1.2.choose
  ρs := hA.2.choose
  T := historyTime c r l
  β := ch.β
  E := ch.E₀ ∩ aliveRec ((entryList l).length + 1) c.s hA.1.2.choose
  Hr := stgField ch.σa ch.kc c.h (schedChart c r l a GT R V)
  σa := ch.σa
  kc := ch.kc
  u₀ := ch.u₀
  ℋ := ch.ℋ
  B := schedPhysUnion c r l a

end Defs

/-- **The open lines inputs of an instance** (RELDET: the union's marks, measurability, openness and locality;
STAGEMEAN: the union mean for every local-set mean, the no-threshold statement along the stage driver, and the
conditional GFF law of the stage field given a σ-algebra making the stage record measurable). -/
structure OpenLines {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (I : StageInst Ω) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hWm : ∀ t, Measurable (I.W t)) : Prop where
  sets_le : ∀ t, stgFilt (physFilt (measurable_gb6Rec_src c) hWm c.P) I.T (GW2Sde.measurable_stageEncRec c r l) t ≤
    I.ℋ t
  sets_amb : ∀ t, I.ℋ t ≤ mΩ
  sets_meas : ∀ t, Measurable[mΩ, hittingSigma] (I.B t)
  sets_open : ∀ t ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω)
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

/-- **`StageInst.Good` at the actual schedule** from a good set, an announced version with finite stops, the word
map's three properties, a measurable record event, a bounded harmonic extension of the boundary data, and the open
lines inputs. -/
theorem schedInst_good (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGood c.s (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (hV : ∀ ω, V ω ≠ ⊤)
    (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hopen : OpenLines (schedInst c r l a GT hA ch) c r l (measurable_schedW c r l a)) :
    (schedInst c r l a GT hA ch).Good c r l := by
  set I := schedInst c r l a GT hA ch with hI
  have hWm : ∀ t, Measurable (I.W t) := measurable_schedW c r l a
  have hver : IsGB6RelVersionR c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V := hA.1
  have hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hρs := hA.2.choose_spec
  have hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R) :=
    measurable_stgPreRec_amb hGT.1 (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2 hver I.T
  have hE : MeasurableSet I.E := hE₀.inter (measurableSet_aliveRec _ c.s hρ.1)
  have hfin : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → stgStartM c.s I.W c.W c.ζ I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := GW2Sdf.StageInst.E_good_of_record I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hHr : Measurable I.Hr := measurable_stgField_inst I hv hpre
  have hzb := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  obtain ⟨𝒢, M, hrec, hM0, hM, hgff⟩ := hopen.condGFF
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
        (Eventually.of_forall fun _ _ hc => chartTransport_eq_stgField hc) hu₀.1 hzb hopen.sets_le
        hopen.sets_amb hopen.sets_meas hopen.sets_open hopen.loc
        (StageInst.shape_of_physUnion hGT.1 hver hGT.2.2 (hEgood.mono fun _ h hm => (h hm).1)
          (fun _ _ => rfl) w)
        (hopen.mean w) hopen.noThreshold 𝒢.2 hrec hM0 hM hgff }

end Good

/-! ### RELDET's good set, chosen -/

section Chosen

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **RELDET's GB6 good set at the schedule instance**, chosen. -/
def schedGT (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Set Ω :=
  (exists_goodSet_sched h13 c r l a).choose

theorem schedGT_spec (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (∀ ω ∈ schedGT h13 c r l a, PhysGood c.s (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α ω) ∧
      MeasurableSet (schedGT h13 c r l a) ∧
      (∀ᵐ ω ∂c.P, ω ∈ schedGT h13 c r l a ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s) :=
  (exists_goodSet_sched h13 c r l a).choose_spec

/-- **`StageInst.Good` at the actual schedule with RELDET's good set.** -/
theorem schedInst_good_of_reldet (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (hV : ∀ ω, V ω ≠ ⊤)
    (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hopen : OpenLines (schedInst c r l a (schedGT h13 c r l a) hA ch) c r l (measurable_schedW c r l a)) :
    (schedInst c r l a (schedGT h13 c r l a) hA ch).Good c r l :=
  schedInst_good c r l a (schedGT_spec h13 c r l a) hA hV ch hβ hE₀ hu₀ hopen

end Chosen

end InteractingSLE.Theorem14.GW2Sdh
