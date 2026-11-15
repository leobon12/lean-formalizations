/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkStageLocalAE

/-!
# Theorem 1.4: the per-stage kernel input of the walk law, reduced to launched pieces with their own records

Packet PROVE-T14-WALKLAW3. The per-stage input `WalkLaw.WalkStageKernelLocalStatement θ right` (Part D.2: under almost
every regular conditional law `ν` given the retained past `pastSigma k`, the piece of instruction `k` is a marked local
set of the centred field for the marks `pastSigma (k + 1)`, off the explored set) is reduced here to its genuine
content, the launched pieces with the marks of their own retained record:

* under `ν` the run before instruction `k` is that of `ω₀` (`CondDriverBridge.ae_ae_run_eq_of_le`), hence so is the
  launch decision of instruction `k` (`launches_run_succ_of_run_eq`) and every earlier record;
* **no launch**: the piece is empty and every mark of `pastSigma (k + 1)` is `ν`-trivial, so the criterion holds with
  a constant function (`isHistoryAvoidanceLocalOff_of_trivial`);
* **launch**: every mark of `pastSigma (k + 1)` agrees `ν`-almost surely with an event of the new record
  `recOf (instrTime w k) (E w k ·)` (the stopped driver at rational times, the stop and the threshold flag), so the
  marks may be replaced by those of the record (`isHistoryAvoidanceLocalOff_of_le_aeSigma`).

The remaining named input is **`WalkStageLaunchLocalStatement θ right`**: for a launched piece, under `ν`, the marked
criterion off the explored set with the marks of the piece's own record; and
**`walkStageKernelLocalStatement_of_launch`** derives `WalkStageKernelLocalStatement θ right` from it.
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

open LocalSets Exist.Staged Exist.StagedLaw

/-! ### Two generic forms of the criterion off a set -/

section Generic

variable {Ω : Type*} {ℋ ℋ' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **Marks may be replaced by almost surely equal ones.** -/
theorem isHistoryAvoidanceLocalOff_of_le_aeSigma {K : Set ℂ} {B : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    {Q : Measure Ω} (hle : ℋ ≤ aeSigma ℋ' Q) (hoff : IsHistoryAvoidanceLocalOff ℋ' K B h Q) :
    IsHistoryAvoidanceLocalOff ℋ K B h Q := by
  intro U G hUH hKU hG hd F hF
  obtain ⟨F', hF', hFF'⟩ := hle F hF
  obtain ⟨g, hg, hge⟩ := hoff U G hUH hKU hG hd F' hF'
  refine ⟨g, hg, Filter.EventuallyEq.trans ?_ hge⟩
  refine condExp_congr_ae (indicator_ae_eq_of_ae_eq_set ?_)
  filter_upwards [hFF'] with ω hω
  change (ω ∈ {ω | Disjoint (B ω) U} ∧ ω ∈ F) = (ω ∈ {ω | Disjoint (B ω) U} ∧ ω ∈ F')
  rw [hω]

/-- **An almost surely empty new set with almost surely trivial marks satisfies the criterion.** -/
theorem isHistoryAvoidanceLocalOff_of_trivial {K : Set ℂ} {B : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    {Q : Measure Ω} [IsFiniteMeasure Q] (hhm : Measurable h) (hB : ∀ᵐ ω ∂Q, B ω = ∅)
    (htriv : ∀ F, MeasurableSet[ℋ] F → (∀ᵐ ω ∂Q, ω ∈ F) ∨ ∀ᵐ ω ∂Q, ω ∉ F) :
    IsHistoryAvoidanceLocalOff ℋ K B h Q := by
  intro U G _ _ _ _ F hF
  have hm : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  rcases htriv F hF with hFa | hFa
  · refine ⟨fun _ => 1, measurable_const, ?_⟩
    have e : ({ω | Disjoint (B ω) U} ∩ F).indicator (fun _ => (1 : ℝ)) =ᵐ[Q] fun _ => (1 : ℝ) := by
      filter_upwards [hB, hFa] with ω hω hωF
      have hmem : ω ∈ {ω | Disjoint (B ω) U} ∩ F := ⟨by simp [mem_ofPred_eq, hω], hωF⟩
      simp only [Set.indicator_of_mem hmem]
    refine (condExp_congr_ae e).trans ?_
    rw [condExp_const hm]
  · refine ⟨fun _ => 0, measurable_const, ?_⟩
    have e : ({ω | Disjoint (B ω) U} ∩ F).indicator (fun _ => (1 : ℝ)) =ᵐ[Q] (0 : Ω → ℝ) := by
      filter_upwards [hFa] with ω hωF
      have hnm : ω ∉ {ω | Disjoint (B ω) U} ∩ F := fun h' => hωF h'.2
      simp only [Set.indicator_of_notMem hnm, Pi.zero_apply]
    refine (condExp_congr_ae e).trans ?_
    rw [condExp_zero]
    rfl

end Generic

/-! ### The past after one more instruction under the kernel -/

section Past

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}

/-- The retained past after instruction `k`, from the run before it and the new record. -/
def pastSucc {k : ℕ} (p : PastData k) (x : RecData) : PastData (k + 1) :=
  fun i => if hi : (i : ℕ) < k then p ⟨i, hi⟩ else x

theorem measurable_pastSucc {k : ℕ} (p : PastData k) : Measurable (pastSucc p) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : (i : ℕ) < k
  · simp only [pastSucc, hi, ↓reduceDIte]
    exact measurable_const
  · simp only [pastSucc, hi, ↓reduceDIte]
    exact measurable_id

/-- **The retained past after instruction `k`**: the records before `k` are those of the run before `k`, the new one is
the launched piece's record or the initial record. -/
theorem pastMap_succ_eq (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω : Ω) :
    pastMap κ b jumps spec E (k + 1) ω = pastSucc (pastMap κ b jumps spec E k ω)
      (if (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none then
        readRec (fun _ => 0, 0, false) else recOf (instrTime spec k) (E k ω)) := by
  funext i
  by_cases hi : (i : ℕ) < k
  · simp only [pastSucc, hi, ↓reduceDIte]
    change readRec ((ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.1 i) =
      readRec ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.1 i)
    rw [retained_run_succ_of_lt spec _ hi]
  · have hik : (i : ℕ) = k := le_antisymm (Nat.lt_succ_iff.1 i.2) (not_lt.1 hi)
    simp only [pastSucc, hi, ↓reduceDIte]
    change readRec ((ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.1 i) = _
    rw [show ((ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.1 i) =
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.1 k from by rw [hik],
      retained_run_succ_self spec _ k]
    split_ifs <;> rfl

end Past

/-! ### The reduction -/

/-- **Named input: a launched piece of a boundary walk, under the regular conditional law given the past, satisfies the
marked criterion off the explored set for the marks of its own record** (Part D.2, L788–L832: "Given the old marked
datum, a new ordinary stage is the canonical finite-word flow of that conditional field"; Aux. lemma 56 for that flow
line, read in the physical domain through the launch chart). For the setting of `WalkStageKernelLocalStatement`, every
instruction `k` and almost every `ω₀` at which instruction `k` launches a piece: under `ν = condExpKernel P (pastSigma
k) ω₀`, the piece (in `ℍ`) satisfies the history-marked criterion for the centred field and the marks generated by its
record `recOf (instrTime w k) (E w k ·)` (stopped driver at rational times, stop, threshold flag), for every open
`U ⊆ ℍ` disjoint from the explored set `stageSet k ω₀` and every Markov decomposition along `U` under `ν`. -/
def WalkStageLaunchLocalStatement (θ : ℝ) (right : Bool) : Prop :=
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
      ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω₀) (k + 1)).2.2.2.1 k ≠ none →
        IsHistoryAvoidanceLocalOff
          (MeasurableSpace.comap
            (fun ω => recOf (instrTime (boundaryWalkSpec b jumps θ right) k)
              (E (boundaryWalkSpec b jumps θ right) k ω)) inferInstance)
          (stageSet κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) k ω₀)
          (pieceSet κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) k)
          (WholeField.centredField h u₀)
          (condExpKernel P
            (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) (E (boundaryWalkSpec b jumps θ right)) k) ω₀)

/-- **The per-stage kernel input from the launched pieces.** For an angle in `[−π/2, π/2]`,
`WalkStageLaunchLocalStatement θ right` gives `WalkStageKernelLocalStatement θ right`. -/
theorem walkStageKernelLocalStatement_of_launch {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {right : Bool} (hL : WalkStageLaunchLocalStatement.{u} θ right) : WalkStageKernelLocalStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg u₀ hu₀ k
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps θ right).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hEw := hE w hw
  filter_upwards [hL κ hκ hκ4 b jumps hb P h hh E hE hR hreg u₀ hu₀ k,
    CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) w
      (fun j _ ω => hreg w j ω) (hEw.2.1 k) le_rfl] with ω₀ hLω hfr
  -- under the kernel, the launch decision of instruction `k` is that of `ω₀`
  have hlaunch : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) k) ω₀),
      (ExplState.run κ b jumps w (fun j => E w j ω) (k + 1)).2.2.2.1 k =
        (ExplState.run κ b jumps w (fun j => E w j ω₀) (k + 1)).2.2.2.1 k := by
    filter_upwards [hfr] with ω hω
    rw [launches_run_succ_of_run_eq w hω]
  have hpast : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) k) ω₀),
      pastMap κ b jumps w (E w) k ω = pastMap κ b jumps w (E w) k ω₀ := by
    filter_upwards [hfr] with ω hω
    unfold pastMap
    rw [hω]
  by_cases hl : (ExplState.run κ b jumps w (fun j => E w j ω₀) (k + 1)).2.2.2.1 k = none
  · -- no launch: the piece is empty and the marks are trivial
    refine isHistoryAvoidanceLocalOff_of_trivial (WholeField.measurable_centredField hh.1 u₀) ?_ ?_
    · filter_upwards [hlaunch] with ω hω
      simp only [pieceSet, hω, hl, ↓reduceIte]
    · rintro _ ⟨T, -, rfl⟩
      have hconst : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) k) ω₀),
          pastMap κ b jumps w (E w) (k + 1) ω = pastMap κ b jumps w (E w) (k + 1) ω₀ := by
        filter_upwards [hlaunch, hpast] with ω h1 h2
        rw [pastMap_succ_eq, pastMap_succ_eq, h1, h2]
        simp only [hl, ↓reduceIte]
      by_cases hT : pastMap κ b jumps w (E w) (k + 1) ω₀ ∈ T
      · left
        filter_upwards [hconst] with ω hω
        show pastMap κ b jumps w (E w) (k + 1) ω ∈ T
        rw [hω]
        exact hT
      · right
        filter_upwards [hconst] with ω hω
        show pastMap κ b jumps w (E w) (k + 1) ω ∉ T
        rw [hω]
        exact hT
  · -- launch: the marks are those of the new record
    refine isHistoryAvoidanceLocalOff_of_le_aeSigma ?_ (hLω hl)
    rintro _ ⟨T, hT, rfl⟩
    refine ⟨(fun ω => recOf (instrTime w k) (E w k ω)) ⁻¹'
      (pastSucc (pastMap κ b jumps w (E w) k ω₀) ⁻¹' T), ⟨_, measurable_pastSucc _ hT, rfl⟩, ?_⟩
    filter_upwards [hlaunch, hpast] with ω h1 h2
    have e : pastMap κ b jumps w (E w) (k + 1) ω =
        pastSucc (pastMap κ b jumps w (E w) k ω₀) (recOf (instrTime w k) (E w k ω)) := by
      rw [pastMap_succ_eq, h1, h2]
      simp only [hl, ↓reduceIte]
    change (pastMap κ b jumps w (E w) (k + 1) ω ∈ T) =
      (pastSucc (pastMap κ b jumps w (E w) k ω₀) (recOf (instrTime w k) (E w k ω)) ∈ T)
    rw [e]

/-- The right walk. -/
theorem walkStageKernelLocalStatement_right_of_launch
    (hL : WalkStageLaunchLocalStatement.{u} (-(Real.pi / 2)) true) :
    WalkStageKernelLocalStatement.{u} (-(Real.pi / 2)) true :=
  walkStageKernelLocalStatement_of_launch ⟨le_rfl, by linarith [Real.pi_pos]⟩ hL

/-- The left walk. -/
theorem walkStageKernelLocalStatement_left_of_launch
    (hL : WalkStageLaunchLocalStatement.{u} (Real.pi / 2) false) :
    WalkStageKernelLocalStatement.{u} (Real.pi / 2) false :=
  walkStageKernelLocalStatement_of_launch ⟨by linarith [Real.pi_pos], le_rfl⟩ hL

end WalkLaw

end Theorem14

end InteractingSLE
