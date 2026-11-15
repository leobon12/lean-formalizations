/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMarkedLocalGlue
import InteractingSLE.Spec.Supplement.WalkPastLaw
import InteractingSLE.Spec.Supplement.CondDriverBridge
import InteractingSLE.Spec.Supplement.GW1PieceRun
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# Theorem 1.4: the past of a boundary walk is a marked local set (Part D.2), stage by stage

Packet PROVE-T14-WALKLAW2. The named input `WalkLaw.WalkMarkedLocalRegStatement θ right` of the union law of the two
walks (PROVE-T14-WALKLAW) is reduced here to two stage-wise statements, following the follow-up note's Part D.2
(`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L771–L832: "Given the old marked datum, a new ordinary stage
is the canonical finite-word flow of that conditional field. […] Iterating the conditional Gaussian identities proves
the asserted full joined-history law"):

* `stageSet … k`: the explored set in `ℍ` after the first `k` instructions (the pieces recorded so far; connectors are
  real); `pieceSet … k`: the piece launched by instruction `k`, in `ℍ` (empty if none);
  `stageSet_succ`: `stageSet (k + 1) = stageSet k ∪ pieceSet k`; `walkSet_eq_stageSet`;
* **`WalkStageKernelLocalStatement θ right`** (named input, the per-stage content of D.2): under almost every regular
  conditional law given the retained past `pastSigma k`, the new piece is a history-marked local set of the centred
  field for the marks `pastSigma (k + 1)`, on the open sets off the explored set (Aux. lemma 56 for the flow line of the
  conditional field, read in the physical domain);
* **`WalkStageAvoidMeasStatement θ right`** (named input, D.5's measurability in the past): the avoidance events of the
  explored set after `k` instructions are events of `pastSigma k`;
* **`walkMarkedLocalRegStatement_of_stages`**: `PastDetRegStatement` (proved, `WalkPastDet`) and the two inputs give
  `WalkMarkedLocalRegStatement θ right`, through the iteration `isHistoryAvoidanceLocal_of_stages`
  (`WalkMarkedLocalGlue`). The openness clause is proved here (`ae_isOpen_H_diff_walkSet`: GW1P's closed pieces).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

open LocalSets Exist.StagedLaw

/-! ### The explored set stage by stage -/

section Sets

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (spec : ExplSpec)
  (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)

/-- The explored set in `ℍ` after the first `k` instructions: the physical points in `ℍ` of the ordinary pieces recorded
so far (the root and the connectors are real). -/
def stageSet (k : ℕ) (ω : Ω) : Set ℂ :=
  (⋃ p ∈ (ExplState.run κ b jumps spec (fun j => E j ω) k).1, p.1.tipSet p.2.1 p.2.2) ∩ H

/-- The piece launched by instruction `k`, in `ℍ`: the physical points in `ℍ` of its trace read through the chart of
the current domain, run to its stop `min t_k ζ_k`; empty if instruction `k` launches no piece. -/
def pieceSet (k : ℕ) (ω : Ω) : Set ℂ :=
  if (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none then ∅ else
    ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.tipSet
      (fun r : ℝ≥0 => (E k ω).1 (min (r : ℝ≥0∞) (min (instrTime spec k) (E k ω).2)).toNNReal)
      (min (instrTime spec k) (E k ω).2)) ∩ H

theorem stageSet_zero (ω : Ω) : stageSet κ b jumps spec E 0 ω = ∅ := by
  simp [stageSet, ExplState.run, ExplState.init]

/-- **One instruction adds its piece.** -/
theorem stageSet_succ (k : ℕ) (ω : Ω) :
    stageSet κ b jumps spec E (k + 1) ω = stageSet κ b jumps spec E k ω ∪ pieceSet κ b jumps spec E k ω := by
  rcases hl : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k with _ | ⟨c, θ⟩
  · have e := GW1P.pieces_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hl
    simp only [stageSet, pieceSet, hl, ↓reduceIte, union_empty, e]
  · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hl
    have hne : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [hl]; exact Option.some_ne_none _
    have hp : pieceSet κ b jumps spec E k ω = ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.tipSet
        (fun r : ℝ≥0 => (E k ω).1 (min (r : ℝ≥0∞) (min (instrTime spec k) (E k ω).2)).toNNReal)
        (min (instrTime spec k) (E k ω).2)) ∩ H := by
      simp only [pieceSet, hne, ↓reduceIte]
    rw [hp, stageSet, stageSet, he, CounterflowRange.pieces_launch]
    ext z
    simp only [mem_inter_iff, mem_iUnion, mem_union, exists_prop, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨⟨p, hp | rfl, hz⟩, hzH⟩
      · exact Or.inl ⟨⟨p, hp, hz⟩, hzH⟩
      · exact Or.inr ⟨hz, hzH⟩
    · rintro (⟨⟨p, hp, hz⟩, hzH⟩ | ⟨hz, hzH⟩)
      · exact ⟨⟨p, Or.inl hp, hz⟩, hzH⟩
      · exact ⟨⟨_, Or.inr rfl, hz⟩, hzH⟩

theorem stageSet_subset_succ (k : ℕ) (ω : Ω) :
    stageSet κ b jumps spec E k ω ⊆ stageSet κ b jumps spec E (k + 1) ω := by
  rw [stageSet_succ]; exact subset_union_left

theorem stageSet_subset_H (k : ℕ) (ω : Ω) : stageSet κ b jumps spec E k ω ⊆ H := inter_subset_right

/-- The range of a completed history in `ℍ` is its explored set after all its instructions. -/
theorem walkSet_eq_stageSet (ω : Ω) :
    walkSet κ b jumps spec E ω = stageSet κ b jumps spec E spec.2.2.length ω := by
  ext z
  simp only [walkSet, stageSet, ExplState.physSet, mem_inter_iff, mem_union, mem_singleton_iff, mem_iUnion,
    mem_image, exists_prop]
  constructor
  · rintro ⟨(⟨rfl | h⟩ | ⟨a, -, x, -, rfl⟩), hzH⟩
    · exact absurd hzH (by simp [QuantumZipper.H])
    · exact ⟨h, hzH⟩
    · exact absurd hzH (by simp [QuantumZipper.H])
  · rintro ⟨h, hzH⟩
    exact ⟨Or.inl (Or.inr h), hzH⟩

end Sets

/-! ### The first stage and the openness clause -/

section Base

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
/-- Before any instruction the retained past is trivial. -/
theorem pastSigma_zero_trivial (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ F, MeasurableSet[pastSigma κ b jumps spec E 0] F → F = ∅ ∨ F = univ := by
  rintro _ ⟨s, -, rfl⟩
  by_cases hne : ∃ ω, (fun ω (i : Fin 0) =>
      let r := (ExplState.run κ b jumps spec (fun j => E j ω) 0).2.2.1 i
      ((fun q : ℚ => r.1 (q : ℝ).toNNReal), r.2.1, r.2.2)) ω ∈ s
  · right
    obtain ⟨ω₀, h₀⟩ := hne
    ext ω
    simp only [mem_preimage, mem_univ, iff_true]
    convert h₀ using 1
  · left
    ext ω
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    exact fun h => hne ⟨ω, h⟩

/-- The empty set is a marked local set for trivial marks. -/
theorem isHistoryAvoidanceLocal_empty_of_trivial [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h) (htriv : ∀ F, MeasurableSet[ℋ] F → F = ∅ ∨ F = univ) :
    WholeField.IsHistoryAvoidanceLocal ℋ (fun _ => (∅ : Set ℂ)) h P := by
  intro U G _ _ _ F hF
  have hm : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  rcases htriv F hF with rfl | rfl
  · refine ⟨fun _ => 0, measurable_const, ?_⟩
    simp only [inter_empty, indicator_empty]
    have e0 : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
    rw [e0, condExp_zero]
  · refine ⟨fun _ => 1, measurable_const, ?_⟩
    have e : {ω | Disjoint (∅ : Set ℂ) U} ∩ univ = (univ : Set Ω) := by
      ext ω; simp
    rw [e, indicator_univ, condExp_const hm]

end Base

section Open

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The complement in `ℍ` of a completed history is almost surely open** (GW1P: every recorded piece of a run with
regular launched pieces is closed). -/
theorem ae_isOpen_H_diff_walkSet {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) :
    ∀ᵐ ω ∂P, IsOpen (H \ walkSet κ b jumps spec E ω) := by
  filter_upwards [hR.ae_pieceRegular] with ω hω
  have hcl := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hω
    spec.2.2.length).2
  set l := (ExplState.run κ b jumps spec (fun j => E j ω) spec.2.2.length).1 with hl
  have hS : IsClosed (⋃ p ∈ l, p.1.tipSet p.2.1 p.2.2) :=
    (List.finite_toSet l).isClosed_biUnion fun p hp => hcl p hp
  have e : H \ walkSet κ b jumps spec E ω = H \ ⋃ p ∈ l, p.1.tipSet p.2.1 p.2.2 := by
    rw [walkSet_eq_stageSet, stageSet]
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  rw [e]
  exact QuantumZipper.isOpen_H.sdiff hS

end Open

/-! ### The two stage inputs and the reduction -/

/-- **Named input: each new piece of a boundary walk is, conditionally on the retained past, a marked local set of
the field** (Part D.2, L788–L832: "Given the old marked datum, a new ordinary stage is the canonical finite-word flow
of that conditional field"; its locality is Aux. lemma 56 — `WholeField.retainedRangeEntranceStatement` — for that
flow line, read in the physical domain through the launch chart). For the setting of `WalkMarkedLocalRegStatement`,
the walk `w = boundaryWalkSpec b jumps θ right` and every instruction `k`: for almost every `ω₀`, under the regular
conditional law given the retained past `pastSigma k` at `ω₀`, the piece launched by instruction `k` (in `ℍ`)
satisfies the history-marked avoidance criterion for the centred field and the marks `pastSigma (k + 1)`, for every
open `U ⊆ ℍ` disjoint from the explored set `stageSet k ω₀` and every Markov decomposition along `U` under that law. -/
def WalkStageKernelLocalStatement (θ : ℝ) (right : Bool) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ → ∀ k : ℕ,
      ∀ᵐ ω₀ ∂P, IsHistoryAvoidanceLocalOff
        (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) (k + 1))
        (stageSet κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) k ω₀)
        (pieceSet κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) k)
        (WholeField.centredField h u₀)
        (condExpKernel P
          (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) k) ω₀)

/-- **Named input: the explored set of a boundary walk is recorded by its retained past** (Part D.5, L866–L901: "the
classified word is measurable in the past history"; the physical pieces are Borel functions of the records through
the launch charts). For the setting of `WalkMarkedLocalRegStatement` (drivers regular at every sample), every
instruction count `k` and open `U ⊆ ℍ`, the avoidance event of the explored set after `k` instructions is an event of
`pastSigma k`. -/
def WalkStageAvoidMeasStatement (θ : ℝ) (right : Bool) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
    ∀ (k : ℕ) (U : Opens ℂ), (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) k]
        {ω | Disjoint (stageSet κ b jumps (boundaryWalkSpec b jumps θ right)
          (E (boundaryWalkSpec b jumps θ right)) k ω) U}

/-- **The past of a boundary walk is a marked local set (Part D.2), from the stage inputs.** For an angle in
`[−π/2, π/2]`, the determination of the retained past (`PastDetRegStatement`, proved in `WalkPastDet` from Theorems
1.2–1.3), the measurability of the explored sets in the past and the conditional locality of each new piece give
`WalkMarkedLocalRegStatement θ right`. -/
theorem walkMarkedLocalRegStatement_of_stages {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool}
    (hdet : PastDetRegStatement.{u}) (hmeas : WalkStageAvoidMeasStatement.{u} θ right)
    (hker : WalkStageKernelLocalStatement.{u} θ right) : WalkMarkedLocalRegStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg u₀ hu₀
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps θ right).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hEw := hE w hw
  have hRw := hR w hw
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hmeas' := hmeas κ hκ hκ4 b jumps hb P h hh E hE hR hreg
  refine ⟨fun U hU => ?_, ae_isOpen_H_diff_walkSet hRw, ?_⟩
  · have e : {ω | Disjoint (walkSet κ b jumps w (E w) ω) U} =
        {ω | Disjoint (stageSet κ b jumps w (E w) w.2.2.length ω) U} := by
      ext ω; rw [mem_ofPred_eq, mem_ofPred_eq, walkSet_eq_stageSet]
    rw [e]
    exact hmeas' _ U hU
  · have hall := isHistoryAvoidanceLocal_of_stages (P := P) (𝒢 := fun k => pastSigma κ b jumps w (E w) k)
      (A := fun k => stageSet κ b jumps w (E w) k) hh0 (fun k => hEw.2.1 k)
      (fun k => pastSigma_mono (κ := κ) (b := b) (jumps := jumps) w (E w) (Nat.le_succ k))
      (fun k ω => stageSet_subset_succ κ b jumps w (E w) k ω) hmeas'
      (fun k => by
        obtain ⟨f, hf, hp⟩ := hdet κ hκ hκ4 b jumps hb P h hh w (E w) hEw hRw k
        exact pastSigma_le_aeSigma_centred hf hp u₀)
      (by
        have e : (fun ω => stageSet κ b jumps w (E w) 0 ω) = fun _ => (∅ : Set ℂ) :=
          funext fun ω => stageSet_zero κ b jumps w (E w) ω
        simp only [e]
        exact isHistoryAvoidanceLocal_empty_of_trivial (WholeField.measurable_centredField hh.1 u₀)
          (pastSigma_zero_trivial κ b jumps w (E w)))
      (fun k => by
        filter_upwards [hker κ hκ hκ4 b jumps hb P h hh E hE hR hreg u₀ hu₀ k,
          CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) w
            (fun j _ ω => hreg w j ω) (hEw.2.1 k) le_rfl] with ω₀ hω₀ hfr
        have hfr' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) k) ω₀),
            stageSet κ b jumps w (E w) k ω = stageSet κ b jumps w (E w) k ω₀ := by
          filter_upwards [hfr] with ω hω
          simp only [stageSet, hω]
        have := hω₀.union_frozen hfr'
        have e : (fun ω => stageSet κ b jumps w (E w) k ω ∪ pieceSet κ b jumps w (E w) k ω) =
            stageSet κ b jumps w (E w) (k + 1) :=
          funext fun ω => (stageSet_succ κ b jumps w (E w) k ω).symm
        rw [e] at this
        exact this)
    have e : walkSet κ b jumps w (E w) = stageSet κ b jumps w (E w) w.2.2.length :=
      funext fun ω => walkSet_eq_stageSet κ b jumps w (E w) ω
    rw [e]
    exact hall w.2.2.length

/-- The right walk (`θ = −π/2`). -/
theorem walkMarkedLocalRegStatement_right (hdet : PastDetRegStatement.{u})
    (hmeas : WalkStageAvoidMeasStatement.{u} (-(Real.pi / 2)) true)
    (hker : WalkStageKernelLocalStatement.{u} (-(Real.pi / 2)) true) :
    WalkMarkedLocalRegStatement.{u} (-(Real.pi / 2)) true :=
  walkMarkedLocalRegStatement_of_stages ⟨le_rfl, by linarith [Real.pi_pos]⟩ hdet hmeas hker

/-- The left walk (`θ = π/2`). -/
theorem walkMarkedLocalRegStatement_left (hdet : PastDetRegStatement.{u})
    (hmeas : WalkStageAvoidMeasStatement.{u} (Real.pi / 2) false)
    (hker : WalkStageKernelLocalStatement.{u} (Real.pi / 2) false) :
    WalkMarkedLocalRegStatement.{u} (Real.pi / 2) false :=
  walkMarkedLocalRegStatement_of_stages ⟨by linarith [Real.pi_pos], le_rfl⟩ hdet hmeas hker

end WalkLaw

end Theorem14

end InteractingSLE
