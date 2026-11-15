/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdiInst
import InteractingSLE.Spec.Supplement.GW2TbSets

/-!
# GW2's corrected schedule instance: RELDET's set-level lines fields wired in (root `0`)

Packet PROVE-GW2-SDE (round 7). PROVE-GW2-RELDET (round 18) asked SDE to do two things at root `0`:
* use the corrected union `GW2Rd.schedUnionL c r l a I.T` with `GW2Rd.exists_schedLinesLocal_setsL`;
* use a shape variant on the live event.
Round 6's `GW2Sdi.schedInstS_good` already has the shape on the live event. This file wires RELDET's lemma in:

* **`schedUnionS_eq_schedUnionL`**: round 6's `schedUnionS` IS RELDET's `schedUnionL` at the history time;
* `OpenLinesMean`: the STAGEMEAN part of `GW2Sdi.OpenLinesS` (`mean`, `noThreshold`, `condGFF`);
* **`schedInstS_good'`**: `GW2Sdi.schedInstS_good` with `u₀` given through the two facts the proof uses
  (harmonic, zero-boundary GFF for the centred field) instead of `IsBoundedHarmonicExtension`;
* **`exists_schedChoice_lines`**: at root `0`, from RELDET's `GW2Rd.SchedHullLocalStatementL` (Theorems 1.2–1.3),
  there are `u₀` and marks `ℋ` such that for every good set, version, word map, record event and chart constants,
  the instance's `OpenLinesS` reduces to STAGEMEAN's `OpenLinesMean`, and `StageInst.Good` holds
  (**`schedInstS_good_of_lines`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Sdj

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Rd GW2Sde GW2Sdf GW2Sdh GW2Sdi Restart.DomainMarkov Restart.FCDet Sec7.PocketTraversal Supp8.RelSafeS
  GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 LocalSets WholeField

/-- **Round 6's corrected union is RELDET's `schedUnionL` at the history time.** -/
theorem schedUnionS_eq_schedUnionL {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (t : ℝ≥0) :
    schedUnionS c r l a t = schedUnionL c r l a (historyTime c r l) t := by
  funext ω
  rw [schedUnionS_eq]
  unfold schedUnionL schedHullL
  congr 1

/-- **The STAGEMEAN part of the open lines inputs** (`GW2Sdi.OpenLinesS` without the set-level fields). -/
structure OpenLinesMean {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (I : StageInst Ω)
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Prop where
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

/-- **`StageInst.Good` for the corrected schedule instance**, with `u₀` given through harmonicity and the
zero-boundary GFF of the centred field (the two facts `GW2Sdi.schedInstS_good` draws from
`IsBoundedHarmonicExtension`). -/
theorem schedInstS_good' (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGood c.s (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (hV : ∀ ω, V ω ≠ ⊤)
    (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀) (hharm : InnerProductSpace.HarmonicOnNhd ch.u₀ H)
    (hzb : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h ch.u₀) c.P)
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
        (Eventually.of_forall fun _ _ hc => chartTransport_eq_stgField hc) hharm hzb hopen'.sets_le
        hopen'.sets_amb hopen'.sets_meas hopen'.sets_open hopen'.loc (hshape w)
        (hopen'.mean w) hopen'.noThreshold 𝒢.2 hrec hM0 hM hgff }

/-- **RELDET's set-level lines fields for the corrected instance** (root `0`; Theorems 1.2–1.3 and RELDET's
`SchedHullLocalStatementL`): there are a harmonic `u₀` with a zero-boundary GFF centred field and marks `ℋ` such that,
for every good set, version and remaining choice, the instance's open lines inputs are STAGEMEAN's alone, and
`StageInst.Good` holds from them. -/
theorem exists_schedChoice_lines (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hS : SchedHullLocalStatementL.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0) :
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω), InnerProductSpace.HarmonicOnNhd u₀ H ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P ∧
      ∀ (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
        (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V)
        (β : RecData → BoundaryWord) (E₀ : Set RecData) (σa kc : ℝ),
        OpenLinesMean (schedInstS c r l a GT hA ⟨β, E₀, σa, kc, u₀, ℋ⟩) c r l →
        OpenLinesS (schedInstS c r l a GT hA ⟨β, E₀, σa, kc, u₀, ℋ⟩) c r l (measurable_schedW c r l a) := by
  obtain ⟨u₀, ℋ, hharm, hzb, hle, hamb, -, -, hloc⟩ :=
    exists_schedLinesLocal_setsL c r l a h12 h13 hS hr0 (le_refl (historyTime c r l))
  refine ⟨u₀, ℋ, hharm, hzb, fun GT R V hA β E₀ σa kc hm => ⟨hle, hamb, fun t => ?_, hm.mean, hm.noThreshold,
    hm.condGFF⟩⟩
  change IsHistoryAvoidanceLocal (ℋ t) (schedUnionS c r l a t) (centredField c.h u₀) c.P
  rw [schedUnionS_eq_schedUnionL]
  exact hloc t

/-- **`StageInst.Good` for the corrected instance at root `0` from STAGEMEAN's part alone** (Theorems 1.2–1.3 and
RELDET's `SchedHullLocalStatementL`; good set, version, word map and record event as before). -/
theorem schedInstS_good_of_lines (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hS : SchedHullLocalStatementL.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0) :
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω),
      ∀ {GT : Set Ω} (_hGT : (∀ ω ∈ GT, PhysGood c.s (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α ω) ∧
        MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s))
        {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
        (hA : IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) (_hV : ∀ ω, V ω ≠ ⊤)
        (β : RecData → BoundaryWord) (E₀ : Set RecData) (σa kc : ℝ)
        (_hβ : Measurable β ∧ (range fun y => wordType c.κ (β y)).Countable ∧ ∀ y, (β y).IsSorted)
        (_hE₀ : MeasurableSet E₀),
        OpenLinesMean (schedInstS c r l a GT hA ⟨β, E₀, σa, kc, u₀, ℋ⟩) c r l →
        (schedInstS c r l a GT hA ⟨β, E₀, σa, kc, u₀, ℋ⟩).Good c r l := by
  obtain ⟨u₀, ℋ, hharm, hzb, h⟩ := exists_schedChoice_lines h12 h13 hS c r l a hr0
  exact ⟨u₀, ℋ, fun {GT} hGT {R} {V} hA hV β E₀ σa kc hβ hE₀ hm =>
    schedInstS_good' c r l a hGT hA hV ⟨β, E₀, σa, kc, u₀, ℋ⟩ hβ hE₀ hharm hzb (h _ hA β E₀ σa kc hm)⟩

end Good

end InteractingSLE.Theorem14.GW2Sdj
