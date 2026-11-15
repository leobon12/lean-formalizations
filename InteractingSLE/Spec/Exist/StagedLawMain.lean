/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLawStep
import InteractingSLE.Spec.Restart.R1Glue

/-!
# The staged conditional law (`Staged.StagedCondLawStatement`) from the single-stage law

Packet PROVE-STAGEDLAW. Lemma GW1 (specification p. 618–620): "The iterated optional Gaussian law is the full
joined-history kernel; there is no step which conditions only on the newest range and forgets an older piece." The
staged history is conditioned one launched piece at a time:

* a launch at instruction `k > 0` has a last launch `ℓ < k` (`exists_last_launch`); between them the history only moves
  along the original boundary, which recentres the chart (`a ℓ`) and adds no new field reveal;
* the conditional law given the retained past before `ℓ + 1` of the field read right after piece `ℓ` is the single-stage
  law (`post_stage`); on the event of the last launch `ℓ` the retained past before `k` carries no more information
  (`Restart.ae_condExp_eq_of_trace`), so the same law holds given the retained past before `k`;
* the regular conditional law then makes that field a GFF (`ae_isGFFWithBoundaryData_condExpKernel`), and recentring
  translates its data (`isGFFWithBoundaryData_shiftW`).

## Main results

* **`stageLaw_succ`**, **`stageLaw`**: the invariant `StageLaw k` for every `k` (strong induction);
* **`stagedCondLawStatement_of_inputs`**: `Staged.StagedCondLawStatement` from `StopLawStatement`, `RunMeasStatement`
  and `WordMeasStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open LQGMetric Restart Staged

/-! ### Deterministic facts about the last launch -/

section Det

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- Launch records of earlier instructions are never changed. -/
theorem launches_run_of_lt (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {i : ℕ} :
    ∀ {n : ℕ}, i < n → (ExplState.run κ b jumps spec D n).2.2.2.1 i =
      (ExplState.run κ b jumps spec D (i + 1)).2.2.2.1 i
  | 0, h => absurd h (Nat.not_lt_zero i)
  | n + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · rw [run_succ]
      cases spec.2.2[n]? with
      | none => exact launches_run_of_lt spec D h
      | some a =>
        rw [launches_step_of_ne _ _ _ _ (Nat.ne_of_gt h)]
        exact launches_run_of_lt spec D h
    · rw [h]

/-- **The last launch is unique.** -/
theorem eq_of_last_launch {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k ℓ ℓ' : ℕ} (hℓ : ℓ < k) (hℓ' : ℓ' < k)
    (hl : (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hl' : (ExplState.run κ b jumps spec D (ℓ' + 1)).2.2.2.1 ℓ' ≠ none)
    (hn : ∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = none)
    (hn' : ∀ j, ℓ' < j → j < k → (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = none) : ℓ = ℓ' := by
  rcases lt_trichotomy ℓ ℓ' with h | h | h
  · exact absurd (hn ℓ' h hℓ') hl'
  · exact h
  · exact absurd (hn' ℓ h hℓ) hl

/-- The retained past before `k` is the retained past before `ℓ + 1`, padded with initial records, when no
instruction between them launches. -/
theorem pastMap_eq_pad (spec : ExplSpec) {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {ℓ k : ℕ} (hℓk : ℓ + 1 ≤ k)
    {ω : Ω} (hn : ∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none) :
    pastMap κ b jumps spec E k ω = fun i : Fin k =>
      if hi : (i : ℕ) < ℓ + 1 then pastMap κ b jumps spec E (ℓ + 1) ω ⟨i, hi⟩
      else readRec (fun _ => 0, 0, false) := by
  funext i
  split_ifs with hi
  · exact (pastMap_castLE spec E hℓk ω ⟨i, hi⟩).symm
  · change readRec ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.1 i) = _
    rw [retained_run_of_lt spec _ i.2, retained_run_succ_self]
    simp only [hn i (by omega) i.2, ↓reduceIte]

/-- **At the last launch `ℓ` before a launch at `k`**: the piece `ℓ` stopped at a finite time, and the chart at `k` is
the chart after piece `ℓ`, recentred. -/
theorem last_launch_props {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k ℓ : ℕ} (hℓ : ℓ < k)
    (hk : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k ≠ none)
    (hl : (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hn : ∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = none) :
    min (instrTime spec ℓ) (D ℓ).2 ≠ ⊤ ∧ ∃ a : ℝ, (ExplState.run κ b jumps spec D k).2.2.2.2.1 =
      (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.2.1.recenter a := by
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hk
  obtain ⟨ℓ', hℓ', ⟨c', θ', hl'⟩, hstop, hn', ha⟩ := exists_last_launch spec D (lt_of_le_of_lt (Nat.zero_le ℓ) hℓ) hcθ
  have e : ℓ = ℓ' := eq_of_last_launch hℓ hℓ' hl (by rw [hl']; simp) hn hn'
  subst e
  exact ⟨hstop, ha⟩

/-- Running on from equal states without launching keeps the states equal. -/
theorem run_eq_of_noLaunch_after (spec : ExplSpec) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ k : ℕ}
    (h : ExplState.run κ b jumps spec D (ℓ + 1) = ExplState.run κ b jumps spec D' (ℓ + 1))
    (hn : ∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = none) :
    ∀ n, ℓ + 1 + n ≤ k → ExplState.run κ b jumps spec D (ℓ + 1 + n) = ExplState.run κ b jumps spec D' (ℓ + 1 + n)
  | 0, _ => h
  | n + 1, hn' => by
    have ih := run_eq_of_noLaunch_after spec h hn n (by omega)
    rw [show ℓ + 1 + (n + 1) = ℓ + 1 + n + 1 by ring]
    exact run_succ_eq_of_noLaunch spec ih (hn _ (by omega) (by omega))

end Det

/-! ### The induction step -/

section Step

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit mΩ [StandardBorelSpace Ω] in
/-- Equal retained pasts before `k` give equal states at every `j ≤ k`. -/
theorem run_eq_of_pastMap_eq_of_le {k : ℕ} (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) {ω ω' : Ω}
    (he : pastMap κ b jumps spec E k ω = pastMap κ b jumps spec E k ω') {j : ℕ} (hj : j ≤ k) :
    ExplState.run κ b jumps spec (fun i => E i ω) j = ExplState.run κ b jumps spec (fun i => E i ω') j := by
  refine run_eq_of_pastMap_eq spec (fun i hi => hreg i (lt_of_lt_of_le hi hj)) ?_
  funext i
  rw [pastMap_castLE spec E hj ω i, pastMap_castLE spec E hj ω' i, he]

/-- Maps determined by the states up to `k` are measurable for the retained past before `k`. -/
theorem measurable_pastSigma_of_runs (hB : RunMeasStatement.{u}) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {k : ℕ} (hEm : ∀ j < k, Measurable (E j)) (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) {Y : Type*}
    [MeasurableSpace Y] {g : Ω → Y} (hg : Measurable g)
    (hsat : ∀ ω ω', (∀ j ≤ k, ExplState.run κ b jumps spec (fun i => E i ω) j =
      ExplState.run κ b jumps spec (fun i => E i ω') j) → g ω = g ω') :
    Measurable[pastSigma κ b jumps spec E k] g := by
  rw [pastSigma_eq_comap]
  exact measurable_comap_of_saturated (measurable_pastMap hB hb spec hEm hreg k le_rfl) hg
    fun ω ω' he => hsat ω ω' fun j hj => run_eq_of_pastMap_eq_of_le hreg he hj

theorem measurableSet_pastSigma_of_runs (hB : RunMeasStatement.{u}) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {k : ℕ} (hEm : ∀ j < k, Measurable (E j)) (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) {S : Set Ω}
    (hS : MeasurableSet S)
    (hsat : ∀ ω ω', (∀ j ≤ k, ExplState.run κ b jumps spec (fun i => E i ω) j =
      ExplState.run κ b jumps spec (fun i => E i ω') j) → ω ∈ S → ω' ∈ S) :
    MeasurableSet[pastSigma κ b jumps spec E k] S := by
  rw [pastSigma_eq_comap]
  exact measurableSet_comap_of_saturated (measurable_pastMap hB hb spec hEm hreg k le_rfl) hS
    fun ω ω' he => hsat ω ω' fun j hj => run_eq_of_pastMap_eq_of_le hreg he hj

omit [StandardBorelSpace Ω] in
/-- The launch event of instruction `k` is measurable when the drivers before `k` are. -/
theorem measurableSet_launch_self (hB : RunMeasStatement.{u}) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {k : ℕ} (hEm : ∀ j < k, Measurable (E j)) (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) :
    MeasurableSet {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} := by
  have h := (hB κ b jumps hb spec (truncE k E) (measurable_truncE hEm) (isRegularDriver_truncE hreg) k).1
  convert h using 3 with ω
  rw [launches_run_succ_congr spec (D := fun j => E j ω) (D' := fun j => truncE k E j ω)
    fun j hj => by rw [truncE_of_lt E hj]]

omit mΩ [StandardBorelSpace Ω] in
/-- The record of a launched piece in the retained past. -/
theorem pastMap_last_of_launch {ℓ : ℕ} {ω : Ω}
    (hω : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ) = recOf (instrTime spec ℓ) (E ℓ ω) := by
  rw [pastMap_succ, Fin.snoc_last, readRec_retained_succ]
  simp only [hω, ↓reduceIte]

/-- The witnesses of the invariant `StageLaw`. -/
def IsStageWitness (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  Measurable[pastSigma κ b jumps spec E k] β ∧ Measurable Y ∧
    (∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ω)) ∧
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) Y (β ω₀).fn (β ω₀).jumps

theorem stageLaw_iff {k : ℕ} : StageLaw κ b jumps P h spec E k ↔
    ∃ β Y, IsStageWitness κ b jumps P h spec E k β Y := Iff.rfl

/-- **The induction step.** -/
theorem stageLaw_succ {βA : BoundaryWord × ℝ × RecData → BoundaryWord} (hβA : IsStopLaw.{u} κ βA)
    (hB : RunMeasStatement.{u}) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {k : ℕ} (hk : 0 < k)
    (hEm : ∀ j < k, Measurable (E j)) (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω))
    (hok : ∀ j < k, StageOK κ b jumps P h spec E j)
    (hprev : ∀ ℓ < k, StageLaw κ b jumps P h spec E ℓ) : StageLaw κ b jumps P h spec E k := by
  classical
  have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens), ℓ < k →
      IsStageWitness κ b jumps P h spec E ℓ β Y := by
    intro ℓ
    by_cases hℓ : ℓ < k
    · obtain ⟨β, Y, hW⟩ := hprev ℓ hℓ
      exact ⟨β, Y, fun _ => hW⟩
    · exact ⟨fun _ => default, fun _ => 0, fun h' => absurd h' hℓ⟩
  choose β Y hW using H
  have hEm' : ∀ ℓ < k, ∀ j < ℓ + 1, Measurable (E j) := fun ℓ hℓ j hj => hEm j (by omega)
  have hreg' : ∀ ℓ < k, ∀ j < ℓ + 1, ∀ ω, IsRegularDriver (E j ω) := fun ℓ hℓ j hj => hreg j (by omega)
  have hpost := fun ℓ (hℓ : ℓ < k) => post_stage hβA hB hκ hb hh (hEm' ℓ hℓ) (hreg' ℓ hℓ) (hok ℓ hℓ)
    (hW ℓ hℓ).1 (hW ℓ hℓ).2.1 (hW ℓ hℓ).2.2.1 (hW ℓ hℓ).2.2.2
  have h𝒢k : pastSigma κ b jumps spec E k ≤ mΩ := by
    rw [pastSigma_eq_comap]; exact (measurable_pastMap hB hb spec hEm hreg k le_rfl).comap_le
  -- the event of the last launch `ℓ`
  set A : ℕ → Set Ω := fun ℓ => {ω | ℓ < k ∧
    (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none ∧
    (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
    ∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none} with hAdef
  -- the recentring after piece `ℓ`
  set a : ℕ → Ω → ℝ := fun ℓ ω => ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.1 0 -
    (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 0).re with hadef
  -- the field and the word right after piece `ℓ`
  set Zr : ℕ → Ω → DistOn upperHalfPlaneOpens := fun ℓ ω =>
    recField κ (pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ)) (Y ℓ ω) with hZrdef
  set γr : ℕ → Ω → BoundaryWord := fun ℓ ω =>
    βA (β ℓ ω, instrAngle spec ℓ, pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ)) with hγrdef
  set βk : Ω → BoundaryWord := finPw A (fun ℓ ω => BoundaryWord.shiftW (a ℓ ω) (γr ℓ ω)) (fun _ => default) k
    with hβkdef
  set Yk : Ω → DistOn upperHalfPlaneOpens := finPw A (fun ℓ ω => flowField (a ℓ ω) 0 (Zr ℓ ω)) (fun _ => 0) k
    with hYkdef
  -- the last launch is unique
  have hdisj : ∀ ℓ ω, ω ∈ A ℓ → ∀ j, j ≠ ℓ → ω ∉ A j := by
    rintro ℓ ω ⟨hℓ, -, hl, hn⟩ j hj ⟨hj', -, hl', hn'⟩
    exact hj (eq_of_last_launch hℓ hj' hl hl' hn hn').symm
  have hcover : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → ∃ ℓ, ω ∈ A ℓ := by
    intro ω hω
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω
    obtain ⟨ℓ, hℓ, ⟨c', θ', hl'⟩, -, hn', -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
    exact ⟨ℓ, hℓ, hω, by rw [hl']; simp, hn'⟩
  have hβk : ∀ ℓ ω, ω ∈ A ℓ → βk ω = BoundaryWord.shiftW (a ℓ ω) (γr ℓ ω) := fun ℓ ω hω =>
    finPw_eq hω (hdisj ℓ ω hω) k hω.1
  have hYk : ∀ ℓ ω, ω ∈ A ℓ → Yk ω = flowField (a ℓ ω) 0 (Zr ℓ ω) := fun ℓ ω hω =>
    finPw_eq hω (hdisj ℓ ω hω) k hω.1
  -- measurability
  have hAm : ∀ ℓ < k, MeasurableSet (A ℓ) := by
    intro ℓ hℓ
    have hset : A ℓ = {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} ∩
        ({ω | (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} ∩
          ⋂ j ∈ (Finset.range k).filter (ℓ < ·),
            {ω | (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none}ᶜ) := by
      ext ω
      simp only [hAdef, mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_filter, Finset.mem_range, mem_compl_iff,
        not_not, hℓ, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun j hj => h3 j hj.2 hj.1⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun j hj hjk => h3 j ⟨hjk, hj⟩⟩
    rw [hset]
    refine (measurableSet_launch_self hB hb hEm hreg).inter ((measurableSet_launch hB hb spec hEm hreg hℓ).inter ?_)
    refine Finset.measurableSet_biInter _ fun j hj => (measurableSet_launch hB hb spec hEm hreg ?_).compl
    exact (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
  -- `A ℓ` is an event of the retained past before `k` and before `ℓ + 1`
  have hA𝒢 : ∀ ℓ < k, MeasurableSet[pastSigma κ b jumps spec E k] (A ℓ) := by
    intro ℓ hℓ
    refine measurableSet_pastSigma_of_runs hB hb hEm hreg (hAm ℓ hℓ) fun ω ω' he hω => ?_
    obtain ⟨-, hlk, hl, hn⟩ := hω
    refine ⟨hℓ, ?_, ?_, fun j hj hjk => ?_⟩
    · rw [← launches_run_succ_of_run_eq spec (he k le_rfl)]; exact hlk
    · rw [← launches_run_of_lt spec _ hℓ, ← he k le_rfl, launches_run_of_lt spec _ hℓ]; exact hl
    · rw [← launches_run_of_lt spec _ hjk, ← he k le_rfl, launches_run_of_lt spec _ hjk]; exact hn j hj hjk
  have hA𝒢ℓ : ∀ ℓ < k, MeasurableSet[pastSigma κ b jumps spec E (ℓ + 1)] (A ℓ) := by
    intro ℓ hℓ
    refine measurableSet_pastSigma_of_runs hB hb (hEm' ℓ hℓ) (hreg' ℓ hℓ) (hAm ℓ hℓ) fun ω ω' he hω => ?_
    obtain ⟨-, hlk, hl, hn⟩ := hω
    have hrun := run_eq_of_noLaunch_after spec (he (ℓ + 1) le_rfl) hn
    have hrunk : ExplState.run κ b jumps spec (fun j => E j ω) k =
        ExplState.run κ b jumps spec (fun j => E j ω') k := by
      have := hrun (k - (ℓ + 1)) (by omega)
      rwa [show ℓ + 1 + (k - (ℓ + 1)) = k by omega] at this
    refine ⟨hℓ, ?_, ?_, fun j hj hjk => ?_⟩
    · rw [← launches_run_succ_of_run_eq spec hrunk]; exact hlk
    · rw [← he (ℓ + 1) le_rfl]; exact hl
    · have hrj := hrun (j - ℓ) (by omega)
      rw [show ℓ + 1 + (j - ℓ) = j + 1 by omega] at hrj
      rw [← hrj]; exact hn j hj hjk
  have ham : ∀ ℓ < k, Measurable (a ℓ) := fun ℓ hℓ =>
    Complex.measurable_re.comp ((measurable_chart_apply hB hb spec hEm hreg (by omega) 0).sub
      (measurable_chart_apply hB hb spec hEm hreg le_rfl 0))
  have ha𝒢 : ∀ ℓ < k, Measurable[pastSigma κ b jumps spec E k] (a ℓ) := fun ℓ hℓ =>
    measurable_pastSigma_of_runs hB hb hEm hreg (ham ℓ hℓ) fun ω ω' he => by
      simp only [hadef, he (ℓ + 1) (by omega), he k le_rfl]
  have hlast𝒢 : ∀ ℓ < k, Measurable[pastSigma κ b jumps spec E k]
      fun ω => pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ) := by
    intro ℓ hℓ
    have h1 : Measurable[pastSigma κ b jumps spec E (ℓ + 1)]
        fun ω => pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ) := by
      rw [pastSigma_eq_comap]
      exact (measurable_pi_apply (X := fun _ : Fin (ℓ + 1) => RecData) (Fin.last ℓ)).comp
        (comap_measurable (pastMap κ b jumps spec E (ℓ + 1)))
    exact h1.mono (pastSigma_mono spec E (by omega)) le_rfl
  have hγ𝒢 : ∀ ℓ < k, Measurable[pastSigma κ b jumps spec E k] (γr ℓ) := by
    intro ℓ hℓ
    have hβ' : Measurable[pastSigma κ b jumps spec E k] (β ℓ) :=
      (hW ℓ hℓ).1.mono (pastSigma_mono spec E hℓ.le) le_rfl
    exact hβA.1.comp (hβ'.prodMk (measurable_const.prodMk (hlast𝒢 ℓ hℓ)))
  have hlastm : ∀ ℓ < k, Measurable fun ω => pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ) := fun ℓ hℓ =>
    (measurable_pi_apply (X := fun _ : Fin (ℓ + 1) => RecData) (Fin.last ℓ)).comp
      (measurable_pastMap hB hb spec hEm hreg (ℓ + 1) (by omega))
  have hZm : ∀ ℓ < k, Measurable (Zr ℓ) := fun ℓ hℓ => measurable_recField_comp κ (hlastm ℓ hℓ) (hW ℓ hℓ).2.1
  have hβkm : Measurable[pastSigma κ b jumps spec E k] βk :=
    measurable_finPw (mα := pastSigma κ b jumps spec E k) measurable_const k hA𝒢 fun ℓ hℓ =>
      BoundaryWord.measurable_shiftW.comp ((ha𝒢 ℓ hℓ).prodMk (hγ𝒢 ℓ hℓ))
  have hYkm : Measurable Yk := by
    refine measurable_finPw measurable_const k hAm fun ℓ hℓ => ?_
    have h1 := measurable_flowField_uncurry.comp ((ham ℓ hℓ).prodMk (hZm ℓ hℓ))
    exact h1
  -- the earlier stages, almost surely for all of them
  have hpathAll : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ℓ ω) := by
    refine ae_all_iff.2 fun ℓ => ?_
    by_cases hℓ : ℓ < k
    · exact (hW ℓ hℓ).2.2.1.mono fun ω hω _ => hω
    · exact Eventually.of_forall fun ω h' => absurd h' hℓ
  have hgoodAll : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (E ℓ ω))) := by
    refine ae_all_iff.2 fun ℓ => ?_
    by_cases hℓ : ℓ < k
    · exact (hpost ℓ hℓ).1.mono fun ω hω _ => hω
    · exact Eventually.of_forall fun ω h' => absurd h' hℓ
  -- the chart right after piece `ℓ`, on the event of the last launch `ℓ`
  have hafter : ∀ ω, (∀ ℓ, ℓ < k →
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ℓ ω)) → (∀ ℓ, ℓ < k →
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (E ℓ ω)))) →
      ∀ ℓ, ω ∈ A ℓ → (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.IsConformal ∧
        ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2
          ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
        IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
          (h ω) (Yk ω) := by
    intro ω hp hg ℓ hωA
    obtain ⟨hℓ, hlk, hl, hn⟩ := hωA
    obtain ⟨hstop, a₀, ha₀⟩ := last_launch_props hℓ hlk hl hn
    obtain ⟨hconf, hlift, hT⟩ := hp ℓ hℓ hl
    have hgood := hg ℓ hℓ hl hstop
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨-, hrun, -⟩ := eq_launch_of_launches spec _ hcθ
    have hregℓ := hreg ℓ hℓ ω
    have hWc : Continuous fun x : ℝ => (retOf (instrTime spec ℓ) (E ℓ ω)).1 x.toNNReal :=
      (continuous_retOf hregℓ hgood).comp continuous_real_toNNReal
    have hW0 : (fun x : ℝ => (retOf (instrTime spec ℓ) (E ℓ ω)).1 x.toNNReal) 0 = 0 := by
      change (E ℓ ω).1 (min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min (instrTime spec ℓ) (E ℓ ω).2)).toNNReal = 0
      rw [Real.toNNReal_zero, ENNReal.coe_zero, min_eq_left (zero_le (a := min (instrTime spec ℓ) (E ℓ ω).2)),
        ENNReal.toNNReal_zero]
      exact hregℓ.2.1
    have hchart1 : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1 =
        (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.loewner
          (fun x : ℝ => (retOf (instrTime spec ℓ) (E ℓ ω)).1 x.toNNReal)
          ((min (instrTime spec ℓ) (E ℓ ω).2).toNNReal : ℝ) := by
      rw [hrun]
      exact chart_launch _ _ _ _ _ hstop
    have hconf1 : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.IsConformal := by
      rw [hchart1]; exact hconf.loewner hWc hW0 (NNReal.coe_nonneg _)
    have hlift1 : ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1.2.1 w)) QuantumZipper.H := by
      rw [hchart1]; exact hconf.continuousOn_loewner_lift hlift hWc hW0 (NNReal.coe_nonneg _)
    have hT1 : IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.2.1 1 0
        (QuantumZipper.chiC κ) (h ω) (Zr ℓ ω) := by
      rw [hchart1, InteractingSLE.Chart.loewner_eq_trans, ← recChart_eq_loewner hregℓ hgood]
      have hZ : Zr ℓ ω = recField κ (recOf (instrTime spec ℓ) (E ℓ ω)) (Y ℓ ω) := by
        simp only [hZrdef, pastMap_last_of_launch hl]
      rw [hZ]
      exact IsChartTransport.trans hconf (isConformal_recChart _) hlift (continuousOn_recChart_lift _) hT
        (isChartTransport_recField κ _ _)
    have haω : a ℓ ω = a₀ := by
      simp only [hadef, ha₀, InteractingSLE.Chart.recenter, sub_sub_cancel, Complex.ofReal_re]
    rw [ha₀]
    refine ⟨hconf1.recenter a₀, Chart.continuousOn_recenter_lift hlift1, ?_⟩
    rw [hYk ℓ ω ⟨hℓ, hlk, hl, hn⟩, haω, Chart.recenter_eq_trans]
    exact IsChartTransport.trans hconf1 (isConformal_shiftChart a₀) hlift1 (continuousOn_shiftChart_lift a₀) hT1
      (isChartTransport_shiftChart a₀ _ _)
  refine ⟨βk, Yk, hβkm, hYkm, ?_, ?_⟩
  · filter_upwards [hpathAll, hgoodAll] with ω hp hg hω
    obtain ⟨ℓ, hωA⟩ := hcover ω hω
    exact hafter ω hp hg ℓ hωA
  · have hkerℓ : ∀ ℓ, ∀ᵐ ω₀ ∂P, ω₀ ∈ A ℓ → IsGFFWithBoundaryData
        (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) Yk (βk ω₀).fn (βk ω₀).jumps := by
      intro ℓ
      by_cases hℓ : ℓ < k
      swap
      · exact Eventually.of_forall fun ω₀ hω₀ => absurd hω₀.1 hℓ
      -- the conditional characteristic functional given the retained past before `k`, on `A ℓ`
      have hCF : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ A ℓ →
          P[fun ω' => Complex.exp (Complex.I * (Zr ℓ ω' φ : ℂ)) | pastSigma κ b jumps spec E k] ω =
            gaussCF (γr ℓ ω) φ := by
        intro φ
        have hXi : Integrable (fun ω' => Complex.exp (Complex.I * (Zr ℓ ω' φ : ℂ))) P :=
          GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp (hZm ℓ hℓ))
        have htr : ∀ B, MeasurableSet[pastSigma κ b jumps spec E k] B →
            MeasurableSet[LocalSets.aeSigma (pastSigma κ b jumps spec E (ℓ + 1)) P] (B ∩ A ℓ) := by
          intro B hB
          refine ⟨B ∩ A ℓ, ?_, EventuallyEq.rfl⟩
          rw [pastSigma_eq_comap] at hB
          obtain ⟨C, hC, rfl⟩ := hB
          set pad : PastData (ℓ + 1) → PastData k := fun u i =>
            if hi : (i : ℕ) < ℓ + 1 then u ⟨i, hi⟩ else readRec (fun _ => 0, 0, false) with hpad
          have hpadm : Measurable pad := measurable_pi_iff.2 fun i => by
            by_cases hi : (i : ℕ) < ℓ + 1
            · simp only [hpad, hi, ↓reduceDIte]; exact measurable_pi_apply _
            · simp only [hpad, hi, ↓reduceDIte]; exact measurable_const
          have hset : pastMap κ b jumps spec E k ⁻¹' C ∩ A ℓ =
              pastMap κ b jumps spec E (ℓ + 1) ⁻¹' (pad ⁻¹' C) ∩ A ℓ := by
            ext ω
            simp only [mem_inter_iff, mem_preimage]
            constructor
            · rintro ⟨h1, h2⟩
              refine ⟨?_, h2⟩
              have key := pastMap_eq_pad (κ := κ) spec E (show ℓ + 1 ≤ k by omega) h2.2.2.2
              rw [key] at h1
              exact h1
            · rintro ⟨h1, h2⟩
              refine ⟨?_, h2⟩
              have key := pastMap_eq_pad (κ := κ) spec E (show ℓ + 1 ≤ k by omega) h2.2.2.2
              rw [key]
              exact h1
          rw [hset]
          refine MeasurableSet.inter ?_ (hA𝒢ℓ ℓ hℓ)
          rw [pastSigma_eq_comap]
          exact ⟨pad ⁻¹' C, hpadm hC, rfl⟩
        have htrace := Restart.ae_condExp_eq_of_trace (pastSigma_mono spec E (show ℓ + 1 ≤ k by omega)) h𝒢k
          htr hXi
        filter_upwards [htrace, (hpost ℓ hℓ).2 φ] with ω h1 h2 hω
        rw [h1 hω]
        obtain ⟨-, hlk, hl, hn⟩ := hω
        exact h2 hl (last_launch_props hℓ hlk hl hn).1
      have hK := ae_isGFFWithBoundaryData_condExpKernel h𝒢k (M := A ℓ) (β := γr ℓ)
        (Eventually.of_forall fun ω _ => hβA.2.1 _) (hZm ℓ hℓ) hCF
      filter_upwards [hK, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢k (hA𝒢 ℓ hℓ),
        Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢k (ha𝒢 ℓ hℓ)] with ω₀ hG hmem haK hω₀
      have hYe : (fun ω => flowField (a ℓ ω₀) 0 (Zr ℓ ω))
          =ᵐ[condExpKernel P (pastSigma κ b jumps spec E k) ω₀] Yk := by
        filter_upwards [hmem hω₀, haK] with ω hω ha
        rw [hYk ℓ ω hω, ha]
      rw [hβk ℓ ω₀ hω₀]
      exact isGFFWithBoundaryData_congr_ae (isGFFWithBoundaryData_shiftW (a ℓ ω₀) (hG hω₀)) hYkm hYe
    filter_upwards [ae_all_iff.2 hkerℓ] with ω₀ hk' hω₀
    obtain ⟨ℓ, hωA⟩ := hcover ω₀ hω₀
    exact hk' ℓ hωA

/-- **The invariant at every instruction** (strong induction on `k`). -/
theorem stageLaw {βA : BoundaryWord × ℝ × RecData → BoundaryWord} (hβA : IsStopLaw.{u} κ βA)
    (hB : RunMeasStatement.{u}) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) : ∀ k : ℕ, (∀ j < k, Measurable (E j)) →
      (∀ j < k, ∀ ω, IsRegularDriver (E j ω)) → (∀ j < k, StageOK κ b jumps P h spec E j) →
      StageLaw κ b jumps P h spec E k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hEm hreg hok
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact stageLaw_zero hb hh spec E
    · exact stageLaw_succ hβA hB hκ hb hh hk hEm hreg hok fun ℓ hℓ =>
        ih ℓ hℓ (fun j hj => hEm j (hj.trans hℓ)) (fun j hj => hreg j (hj.trans hℓ))
          (fun j hj => hok j (hj.trans hℓ))

end Step

/-! ### The staged conditional law -/

/-- **`Staged.StagedCondLawStatement` from the single-stage law and the two deterministic measurability inputs.** -/
theorem stagedCondLawStatement_of_inputs (hA : StopLawStatement.{u}) (hB : RunMeasStatement.{u})
    (hC : WordMeasStatement) : StagedCondLawStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh spec _ k E hEm hreg hok
  obtain ⟨βA, hβA⟩ := hA κ hκ hκ4
  obtain ⟨β, Y, hβ, hY, hpath, hker⟩ := stageLaw hβA hB hκ hb hh k hEm hreg hok
  have hpm := measurable_pastMap (κ := κ) hB hb spec hEm hreg k le_rfl
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm.comap_le
  obtain ⟨W, hWm, hβW⟩ : ∃ W : PastData k → BoundaryWord, Measurable W ∧ β = W ∘ pastMap κ b jumps spec E k := by
    rw [pastSigma_eq_comap] at hβ
    exact hβ.exists_eq_measurable_comp
  have h1 : Measurable fun x : PastData k => flowLineNL (W x).fn (W x).jumps 0 := by
    have := hC.1.comp hWm; exact this
  have h2 : Measurable fun x : PastData k => flowLineNR (W x).fn (W x).jumps 0 := by
    have := hC.2.1.comp hWm; exact this
  have h3 : ∀ θ : ℝ, Measurable fun x : PastData k => padFL κ θ (W x).fn (W x).jumps := fun θ => by
    have := (hC.2.2 κ θ).comp hWm; exact this
  refine ⟨hpm, fun x => ((W x).fn, (W x).jumps), Y, h1, h2, h3, hY, ?_⟩
  filter_upwards [hpath, hker, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hpath,
    ae_ae_run_eq hB hb spec hEm hreg (P := P)] with ω₀ hp₀ hk₀ hpK hrunK c θ hcθ
  have hl : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hcθ]; simp
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches spec _ hcθ
  obtain ⟨hconf, hlift, -⟩ := hp₀ hl
  rw [← hc] at hconf hlift
  have hgT : ∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω)
      (Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hYe : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
      Y ω = Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) := by
    filter_upwards [hpK, hrunK] with ω hpω hrω
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq spec hrω]; exact hl
    obtain ⟨-, -, hT⟩ := hpω hlω
    rw [hrω, ← hc] at hT
    exact hT.unique hconf (hgT ω)
  refine ⟨(W (pastMap κ b jumps spec E k ω₀)).isPiecewiseConstantBoundaryData,
    fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω), hgT, hYe, ?_⟩
  have hG := hk₀ hl
  rw [hβW] at hG
  exact isGFFWithBoundaryData_congr_ae hG ((Chart.measurable_chartTransport hconf 1 0 _).comp hh.1) hYe

/-- **Theorem 1.4's companion construction from the parametric Theorem 1.2, Theorem 1.3, the single-stage law and the
two deterministic measurability inputs** (PROVE-STAGED's assembly with the staged conditional law proved here). -/
theorem stagedHistoryConstructionStatement_of_stopLaw (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hA : StopLawStatement.{u}) (hB : RunMeasStatement.{u})
    (hC : WordMeasStatement) : Theorem14.StagedHistoryConstructionStatement.{u} :=
  stagedHistoryConstructionStatement_of_inputs h12p h13 (stagedCondLawStatement_of_inputs hA hB hC)

/-- The same, with drivers regular at every sample. -/
theorem regularStagedHistoryConstructionStatement_of_stopLaw (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hA : StopLawStatement.{u}) (hB : RunMeasStatement.{u})
    (hC : WordMeasStatement) : RegularStagedHistoryConstructionStatement.{u} :=
  regularStagedHistoryConstructionStatement_of_inputs h12p h13 (stagedCondLawStatement_of_inputs hA hB hC)

end StagedLaw

end Exist

end InteractingSLE
