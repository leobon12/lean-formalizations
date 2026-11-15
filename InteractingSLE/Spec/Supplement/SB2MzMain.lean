/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzId
import InteractingSLE.Spec.Supplement.SB2JqStage

/-!
# The code match at a tail relative stage under the upper kernel

Packet PROVE-SB2-LCMEAN, round 15 (item 4: transfer to the upper kernel, identification with `EL`, gluing). At a fixed
upper-past sample `ω₀`, under `Q = condExpKernel P (upper past) ω₀`, the relative stage `j ≥ 2` of `EL` lifts B's
stage `j + relOff`. **`ae_codeMatch_tail_Q`** assembles the code match against every witness of the relative stage law.
Its inputs, given under `Q`:

* SB2LIFT's per-stage correspondence (`Mn.StageChainAtR2`, `Mq.StageChainAtP`, `Mq.StageChainAtZ`);
* the frozen upper prefix, and the regular launches of B and of `EL`;
* `R` in B's physical set;
* the tail canonical objects of every B-stage: laws given `marksQ n` under `Q`, and pathwise clauses;
* the offset events as events of the marks;
* the root record.

The proof:

* glues the canonical objects along the stopped index of the offset (`Mz.exists_stopIdx`, `Mz.ae_codeMatch_of_glued`);
* identifies `EL`'s stages with the canonical drivers (`Mz.ident_rel_stage`);
* matches the records of the relative past (`Mz.pastSigma_le_aeSigma_of_rec`);
* reads the field through the relative run chart (`Mz.isChartTransport_run_of_phys`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mz

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mx Restart

/-- The zero driver. -/
abbrev zeroDrv : (ℝ≥0 → ℝ) × ℝ≥0∞ := (fun _ => 0, 0)

theorem isRegularDriver_zeroDrv : IsRegularDriver zeroDrv := by
  refine ⟨?_, rfl, fun t _ => rfl, fun h0 hpos => absurd hpos (lt_irrefl 0)⟩
  intro t ht
  exact continuousWithinAt_const

/-- Offset events of different offsets are disjoint. -/
theorem relOffEvent_disjoint (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) {Ω : Type*}
    (D : Ω → ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    Pairwise (Disjoint on fun o => {ω | relOffEvent κ θ b₁ J₁ R (D ω) o}) := by
  intro o o' hne
  refine Set.disjoint_left.2 fun ω h h' => hne ?_
  exact h.1.symm.trans h'.1

/-- The offset event at the offset, when `R` lies in the walk's physical set. -/
theorem relOffEvent_of_mem_physSet (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) {R : ℝ}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : (R : ℂ) ∈ ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D) :
    relOffEvent κ θ b₁ J₁ R D (relOff κ θ b₁ J₁ R D) := by
  classical
  have hex := Lk.exists_mem_statePhysicalSet_succ hR
  obtain ⟨hin, -⟩ := entryStage_spec κ θ b₁ J₁ hex
  refine ⟨rfl, entryStage κ θ b₁ J₁ R D, ?_, hin⟩
  have h1 : entryStage κ θ b₁ J₁ R D ≤ startOff κ θ b₁ J₁ R D + 1 := by unfold startOff; omega
  have h2 : startOff κ θ b₁ J₁ R D ≤ relOff κ θ b₁ J₁ R D := by
    unfold relOff; split_ifs <;> omega
  omega

/-- A family indexed by `ℕ` with a default at `0` and `f n` at `n + 1` (the stopped index's shift). -/
def shiftFam {α : Sort*} (d : α) (f : ℕ → α) : ℕ → α
  | 0 => d
  | n + 1 => f n

@[simp] theorem shiftFam_zero {α : Sort*} (d : α) (f : ℕ → α) : shiftFam d f 0 = d := rfl
@[simp] theorem shiftFam_succ {α : Sort*} (d : α) (f : ℕ → α) (n : ℕ) : shiftFam d f (n + 1) = f n := rfl

theorem isRegularDriver_driverOf (h12p : Theorem12ParamStatement) {κ : ℝ} (hκ : 0 < κ) (ψ : ℝ)
    (q : BoundaryWord × DistOn upperHalfPlaneOpens) : IsRegularDriver (driverOf h12p hκ ψ q) := by
  obtain ⟨c, f⟩ := q
  rw [driverOf_mk]
  exact drvOf_regular _

theorem stageMarks_mono {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} :
    Monotone (Ms.stageMarks κ b jumps E u l k) := fun _ _ hmn => sup_le_sup le_rfl (pastSigma_mono _ _ hmn)

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The code match at a tail relative stage under the upper kernel.** -/
theorem ae_codeMatch_tail_Q (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ}
    (hEu : IsStagedHistory κ b jumps P h (upperSpec u l) (E (upperSpec u l)))
    (hEl : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    {ω₀ : Ω} {c : Chart} (hcN : WalkIntCanon.IsNormalized c) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {h' : Ω → DistOn upperHalfPlaneOpens}
    (hT' : ∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) (hh'm : Measurable h') {m : ℝ}
    {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hELm : ∀ j, Measurable (EL j)) (hELr : ∀ j ω, IsRegularDriver (EL j ω))
    (hRP : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      Mn.StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω ∧ Mq.StageChainAtP κ b jumps E u l k ω₀ c b' J' m EL ω ∧
        Mq.StageChainAtZ κ b' J' m EL ω)
    (hup : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      upperPrefix κ b jumps E u l k ω = upperPrefix κ b jumps E u l k ω₀ ∧ ω ∈ upperLaunchSet κ b jumps E u l k)
    (hBreg : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      SB.LuM.RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω))
    (hELreg : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      SB.LuM.RegLaunches κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω))
    (hRmem : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ((realMax (upperPrefix κ b jumps E u l k ω₀) : ℝ) : ℂ) ∈
        ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω))
    {G : ℕ → Set Ω} {cw : ℕ → Ω → BoundaryWord} {K : ℕ → Ω → Set ℂ} {x₀ : ℕ → Ω → ℝ}
    {Dr : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hKc : ∀ n ω, IsCompact (K n ω))
    (hKp : ∀ n ω, IsPreconnected (K n ω ∪ Restart.lowerHalf))
    (hcm : ∀ n, Measurable[Ms.stageMarks κ b jumps E u l k n] (cw n))
    (hKm : ∀ n, @IsDyadicHitMeasurable Ω (Ms.stageMarks κ b jumps E u l k n) (K n))
    (hx₀m : ∀ n, Measurable[Ms.stageMarks κ b jumps E u l k n] (x₀ n))
    (hDrm : ∀ n, Measurable[Ms.stageMarks κ b jumps E u l k (n + 1)] (Dr n))
    (hDrr : ∀ n ω, IsRegularDriver (Dr n ω))
    (hlawQ : ∀ n, ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ω₁ ∈ G n → IsGFFWithBoundaryData (condExpKernel (condExpKernel P
        (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) (marksQ κ b jumps E u l k n) ω₁)
        (fun ω => Chart.chartTransport (Mu.isConformal_canon (x₀ n) (hKc n) (hKp n) ω) 1 0 (chiC κ) (h ω))
        (cw n ω₁).fn (cw n ω₁).jumps)
    (hcover : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀), ∀ n,
      ω ∈ upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
        (n + 1)).2.2.2.1 n ≠ none →
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (lowerD b jumps E ω) + 2 ≤ n →
      (lowerD b jumps E ω n).2 ≠ 0 → ω ∈ G n)
    (hident : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀), ∀ n,
      ω ∈ G n → fillH (K n ω) = fillH (retY (κ := κ) b jumps E u l k n ω) ∧
        ChainFor (Mn.stageRetained (Mn.walkStageChart κ b jumps E n ω) (retY (κ := κ) b jumps E u l k n ω))
          (stageChartOf (Mn.walkStageChart κ b jumps E n ω) (Mo.hullChart (fillH (K n ω)) (x₀ n ω)))
          (SB.LuM.trOf (lowerD b jumps E ω n)) (lowerD b jumps E ω n).2
          (driverOf h12p hκ (-(Real.pi / 2))
            (cw n ω, Chart.chartTransport (Mu.isConformal_canon (x₀ n) (hKc n) (hKp n) ω) 1 0 (chiC κ) (h ω))) ∧
        (driverOf h12p hκ (-(Real.pi / 2))
          (cw n ω, Chart.chartTransport (Mu.isConformal_canon (x₀ n) (hKc n) (hKp n) ω) 1 0 (chiC κ) (h ω))).2 ≠ 0 ∧
        recOf ⊤ (Dr n ω) = recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
          (cw n ω, Chart.chartTransport (Mu.isConformal_canon (x₀ n) (hKc n) (hKp n) ω) 1 0 (chiC κ) (h ω))))
    (hoff : ∀ o, ∃ A : Set Ω, MeasurableSet[marksQ κ b jumps E u l k (o + 2)] A ∧
      A =ᵐ[condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀]
        {ω | relOffEvent κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (lowerD b jumps E ω) o})
    {Dr₀ : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDr₀m : ∀ n, Measurable[Ms.stageMarks κ b jumps E u l k (n + 1)] (Dr₀ n))
    (hDr₀r : ∀ n ω, IsRegularDriver (Dr₀ n ω))
    (hroot : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      recOf ⊤ (EL 0 ω) = recOf ⊤ (Dr₀ (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (lowerD b jumps E ω)) ω))
    {j : ℕ} (hj : 2 ≤ j) {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL j β Y) :
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
        (j + 1)).2.2.2.1 j ≠ none →
      IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β ω, Y ω)) (fun t => (EL j ω).1 t) (EL j ω).2 := by
  classical
  have hMQ : ∀ n, marksQ κ b jumps E u l k n ≤ mΩ := marksQ_le hb hEu hEl
  have hSM : ∀ n, Ms.stageMarks κ b jumps E u l k n ≤ marksQ κ b jumps E u l k n := stageMarks_le_marksQ
  -- the stopped index of the offset
  obtain ⟨N, hN, hNS⟩ := exists_stopIdx (μ := condExpKernel P
      (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) hMQ marksQ_mono
    (relOffEvent_disjoint κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
      (lowerD b jumps E)) j (fun o => by
        obtain ⟨A, hA, he⟩ := hoff o
        exact ⟨A, marksQ_mono (by omega : o + 2 ≤ o + j) _ hA, he⟩)
  have hNω : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      N ω = relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω) +
        j + 1 := by
    filter_upwards [hNS, hRmem] with ω h1 h2
    exact h1 _ (relOffEvent_of_mem_physSet _ _ _ _ h2)
  -- the glued families
  set Kg : ℕ → Ω → Set ℂ := shiftFam (fun _ => (∅ : Set ℂ)) K with hKg
  set x₀g : ℕ → Ω → ℝ := shiftFam (fun _ => (0 : ℝ)) x₀ with hx₀g
  set cg : ℕ → Ω → BoundaryWord := shiftFam (fun _ => (default : BoundaryWord)) cw with hcg
  set Gg : ℕ → Set Ω := shiftFam ∅ G with hGg
  have hKcg : ∀ n ω, IsCompact (Kg n ω) := by
    intro n ω
    cases n with
    | zero => exact isCompact_empty
    | succ n => exact hKc n ω
  have hKpg : ∀ n ω, IsPreconnected (Kg n ω ∪ Restart.lowerHalf) := by
    intro n ω
    cases n with
    | zero =>
      show IsPreconnected (∅ ∪ Restart.lowerHalf)
      rw [empty_union]
      exact InteractingSLE.isPreconnected_lowerHalf
    | succ n => exact hKp n ω
  have hKmg : ∀ n, @IsDyadicHitMeasurable Ω (stopFam (marksQ κ b jumps E u l k) n) (Kg n) := by
    intro n
    cases n with
    | zero =>
      intro a q
      have e : {ω | (dyadicSquare a q ∩ Kg 0 ω).Nonempty} = ∅ := by
        ext ω
        simp only [hKg, shiftFam_zero, inter_empty, Set.not_nonempty_empty, mem_ofPred_eq,
          mem_empty_iff_false]
      rw [e]
      exact MeasurableSet.empty
    | succ n => exact fun a q => hSM n _ (hKm n a q)
  have hx₀mg : ∀ n, Measurable[stopFam (marksQ κ b jumps E u l k) n] (x₀g n) := by
    intro n
    cases n with
    | zero => exact measurable_const
    | succ n => exact (hx₀m n).mono (hSM n) le_rfl
  have hcmg : ∀ n, Measurable[stopFam (marksQ κ b jumps E u l k) n] (cg n) := by
    intro n
    cases n with
    | zero => exact measurable_const
    | succ n => exact (hcm n).mono (hSM n) le_rfl
  have hlawg : ∀ n, ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ω₁ ∈ Gg n → N ω₁ = n → IsGFFWithBoundaryData (condExpKernel (condExpKernel P
        (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) (stopFam (marksQ κ b jumps E u l k) n) ω₁)
        (fun ω => Chart.chartTransport (Mu.isConformal_canon (x₀g n) (hKcg n) (hKpg n) ω) 1 0 (chiC κ) (h ω))
        (cg n ω₁).fn (cg n ω₁).jumps := by
    intro n
    cases n with
    | zero => exact Eventually.of_forall fun ω₁ hG => absurd hG (by simp [hGg])
    | succ n =>
      filter_upwards [hlawQ n] with ω₁ h1 hG _
      exact h1 hG
  -- the identification at every launched relative stage `i ≥ 1`
  have hid : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ (i : ℕ) (c₁ : Chart) (θ' : ℝ), 1 ≤ i →
      (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
        (i + 1)).2.2.2.1 i = some (c₁, θ') →
      ω ∈ G (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (lowerD b jumps E ω)) ∧
      (EL i ω).2 = (driverOf h12p hκ (-(Real.pi / 2)) (cw (i + relOff κ (-(Real.pi / 2)) b jumps
        (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω,
          Chart.chartTransport (Mu.isConformal_canon (x₀ (i + relOff κ (-(Real.pi / 2)) b jumps
            (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)))
            (hKc (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (lowerD b jumps E ω)))
            (hKp (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (lowerD b jumps E ω))) ω) 1 0 (chiC κ)
            (h ω))).2 ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < (EL i ω).2 → (EL i ω).1 t = (driverOf h12p hκ (-(Real.pi / 2))
        (cw (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (lowerD b jumps E ω)) ω,
          Chart.chartTransport (Mu.isConformal_canon (x₀ (i + relOff κ (-(Real.pi / 2)) b jumps
            (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)))
            (hKc (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (lowerD b jumps E ω)))
            (hKp (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (lowerD b jumps E ω))) ω) 1 0 (chiC κ)
            (h ω))).1 t) ∧
      EqOn (Mo.hullChart (fillH (K (i + relOff κ (-(Real.pi / 2)) b jumps
          (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω))
          (x₀ (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (lowerD b jumps E ω)) ω)).1 (Mo.physRelChart c c₁ m).1
        (H \ fillH (K (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (lowerD b jumps E ω)) ω)) ∧
      EqOn (Mo.hullChart (fillH (K (i + relOff κ (-(Real.pi / 2)) b jumps
          (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω))
          (x₀ (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (lowerD b jumps E ω)) ω)).2.2 (Mo.physRelChart c c₁ m).2.2
        (H \ fillH (K (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (lowerD b jumps E ω)) ω)) ∧
      IsDomainChart (H \ fillH (K (i + relOff κ (-(Real.pi / 2)) b jumps
          (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω)) (Mo.physRelChart c c₁ m) ∧
      WalkIntCanon.IsNormalized c₁ ∧
      recOf ⊤ (EL i ω) = recOf ⊤ (Dr (i + relOff κ (-(Real.pi / 2)) b jumps
        (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω) := by
    filter_upwards [hRP, hup, hBreg, hELreg, hcover, hident] with ω hRPω hupω hBω hELω hcovω hidω
    intro i c₁ θ' hi hl
    have hl' : (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
        (i + 1)).2.2.2.1 i ≠ none := by rw [hl]; simp
    have hz : (EL i ω).2 ≠ 0 := hRPω.2.2 i c₁ θ' hi hl
    obtain ⟨hBl, -, tL, γ, -, -, hlife⟩ := hRPω.1 i c₁ θ' hl hz
    obtain ⟨S₀, hS₀, -⟩ := exists_pos_of_chainFor hlife (pos_iff_ne_zero.2 hz)
    have hBL : (lowerD b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps
        (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω))).2 ≠ 0 :=
      ne_bot_of_gt hS₀
    have hev := (GW1W.even_of_launches_walk hl').1
    have hG : ω ∈ G (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (lowerD b jumps E ω)) := by
      refine hcovω _ hupω.2 hBl ?_ hBL
      rw [hupω.1]
      omega
    obtain ⟨hfill, hC, hD, hrec⟩ := hidω _ hG
    have hK : IsHPHull (fillH (K (i + relOff κ (-(Real.pi / 2)) b jumps
        (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω)) :=
      Mo.isHPHull_fillH (hKc _) (hKp _) ω
    have hc₁N := isNormalized_launchChart _ hELω hl
    obtain ⟨hl1, hl2, hfwd, hlift⟩ := ident_rel_stage hRPω.1 hRPω.2.1 hupω.1 hl hz hcN hc₁N
      (isNormalized_walkStageChart hBω _) hK hfill hC hD
    have hPd : IsDomainChart (H \ fillH (K (i + relOff κ (-(Real.pi / 2)) b jumps
        (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω)) (Mo.physRelChart c c₁ m) := by
      have h1 := hRPω.2.1 i c₁ θ' hl hz
      have hY : retY (κ := κ) b jumps E u l k (i + relOff κ (-(Real.pi / 2)) b jumps
          (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω =
          upperPrefix κ b jumps E u l k ω₀ ∪ SB.prefixPhysSet κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
            (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (lowerD b jumps E ω)) := by
        show upperPrefix κ b jumps E u l k ω ∪ _ = _
        rw [hupω.1]
      rw [hfill, hY]
      exact h1
    have hcont : ContinuousOn (EL i ω).1 {s | (s : ℝ≥0∞) ≤ min ⊤ (EL i ω).2} := by
      have hpr := hELω i c₁ θ' hl
      have hit : instrTime (relLowerSpec b' J' m) i = ⊤ := GW1W.instrTime_walk hl'
      rw [hit] at hpr
      exact hpr.2.1
    refine ⟨hG, hl1, hl2, hfwd, hlift, hPd, hc₁N, ?_⟩
    rw [recOf_eq_of_ident (hELr i ω) (isRegularDriver_driverOf h12p hκ _ _) hcont hl1 hl2, hrec]
  -- the record matching
  set gl : ℕ → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => shiftFam (fun _ => zeroDrv) (fun n ω =>
    if j ≤ n then (if i = 0 then Dr₀ (n - j) ω else if i < j then Dr (i + (n - j)) ω else zeroDrv) else zeroDrv)
    with hgl
  have hglm : ∀ i n, Measurable[stopFam (marksQ κ b jumps E u l k) n] (gl i n) := by
    intro i n
    cases n with
    | zero => exact measurable_const
    | succ n =>
      show Measurable[marksQ κ b jumps E u l k n] (fun ω =>
        if j ≤ n then (if i = 0 then Dr₀ (n - j) ω else if i < j then Dr (i + (n - j)) ω else zeroDrv) else zeroDrv)
      by_cases hjn : j ≤ n
      · simp only [hjn, ↓reduceIte]
        by_cases hi0 : i = 0
        · simp only [hi0, ↓reduceIte]
          exact (hDr₀m (n - j)).mono ((stageMarks_mono (by omega : n - j + 1 ≤ n)).trans (hSM n)) le_rfl
        · simp only [hi0, ↓reduceIte]
          by_cases hij : i < j
          · simp only [hij, ↓reduceIte]
            exact (hDrm (i + (n - j))).mono
              ((stageMarks_mono (by omega : i + (n - j) + 1 ≤ n)).trans (hSM n)) le_rfl
          · simp only [hij, ↓reduceIte]
            exact measurable_const
      · simp only [hjn, ↓reduceIte]
        exact measurable_const
  have hglr : ∀ i n ω, IsRegularDriver (gl i n ω) := by
    intro i n ω
    cases n with
    | zero => exact isRegularDriver_zeroDrv
    | succ n =>
      show IsRegularDriver (if j ≤ n then (if i = 0 then Dr₀ (n - j) ω else if i < j then Dr (i + (n - j)) ω
        else zeroDrv) else zeroDrv)
      split_ifs
      · exact hDr₀r _ ω
      · exact hDrr _ ω
      · exact isRegularDriver_zeroDrv
      · exact isRegularDriver_zeroDrv
  have hpast := pastSigma_le_aeSigma_of_rec (μ := condExpKernel P
      (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) (k := j)
    (isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb') (relLowerSpec b' J' m) hELr
    (E' := fun i ω => gl i (N ω) ω) (fun i => measurable_stopSigma_glue (hN := hN) (hglm i))
    (fun i ω => hglr i (N ω) ω) (by
      filter_upwards [hid, hNω, hroot] with ω hidω hNω hrootω
      intro i hi hl'
      have hit : instrTime (relLowerSpec b' J' m) i = ⊤ := GW1W.instrTime_walk hl'
      rw [hit, hNω]
      have hjn : j ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (lowerD b jumps E ω) + j := by omega
      have hsub : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (lowerD b jumps E ω) + j - j = relOff κ (-(Real.pi / 2)) b jumps
            (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω) := by omega
      simp only [hgl, shiftFam_succ, hjn, ↓reduceIte, hsub]
      by_cases hi0 : i = 0
      · subst hi0
        simp only [↓reduceIte]
        exact hrootω
      · simp only [hi0, hi, ↓reduceIte]
        obtain ⟨⟨c₁, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hl'
        exact (hidω i c₁ θ' (by omega) hl).2.2.2.2.2.2.2)
  -- the code match at `j` with the canonical code, through the identification
  have hcode : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
        (j + 1)).2.2.2.1 j ≠ none →
      ω ∈ Gg (N ω) ∧ IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (cg (N ω) ω,
        Chart.chartTransport (Mu.isConformal_canon (x₀g (N ω)) (hKcg (N ω)) (hKpg (N ω)) ω) 1 0 (chiC κ) (h ω)))
        (fun t => (EL j ω).1 t) (EL j ω).2 := by
    filter_upwards [hid, hNω] with ω hidω hNω hl'
    obtain ⟨⟨c₁, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hl'
    obtain ⟨hG, hl1, hl2, -⟩ := hidω j c₁ θ' (by omega) hl
    have key : ∀ n, n = j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (lowerD b jumps E ω) + 1 → ω ∈ Gg n ∧
        IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (cg n ω,
          Chart.chartTransport (Mu.isConformal_canon (x₀g n) (hKcg n) (hKpg n) ω) 1 0 (chiC κ) (h ω)))
          (fun t => (EL j ω).1 t) (EL j ω).2 := by
      rintro n rfl
      refine ⟨hG, isDriverCodeMatch_congr (Mu.isDriverCodeMatch_driverOf h12p hκ _ _) hl1 ?_
        fun t ht => hl2 t (hl1 ▸ ht)⟩
      rw [(hELr j ω).2.1, (isRegularDriver_driverOf h12p hκ _ _).2.1]
    exact key (N ω) (by rw [hNω]; omega)
  -- the run chart reads the relative field as the canonical chart reads the physical one
  have htr : ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω₁)
        (j + 1)).2.2.2.1 j ≠ none →
      ∀ ω, IsChartTransport (Cond.runChart κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j ω₁)
        1 0 (chiC κ) (affField m one_pos (h' ω))
        (Chart.chartTransport (Mu.isConformal_canon (x₀g (N ω₁)) (hKcg (N ω₁)) (hKpg (N ω₁)) ω₁) 1 0 (chiC κ)
          (h ω)) := by
    filter_upwards [hid, hNω] with ω₁ hidω hNω hl' ω
    obtain ⟨⟨c₁, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hl'
    obtain ⟨-, -, -, hfwd, hlift, hPd, hc₁N, -⟩ := hidω j c₁ θ' (by omega) hl
    have hrun : Cond.runChart κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j ω₁ = c₁ :=
      ((eq_launch_of_launches _ _ hl).2.2).symm
    have key : ∀ n, n = j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (lowerD b jumps E ω₁) + 1 →
        IsChartTransport (Cond.runChart κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j ω₁)
          1 0 (chiC κ) (affField m one_pos (h' ω))
          (Chart.chartTransport (Mu.isConformal_canon (x₀g n) (hKcg n) (hKpg n) ω₁) 1 0 (chiC κ) (h ω)) := by
      rintro n rfl
      rw [hrun]
      exact isChartTransport_run_of_phys hcN.conformal hc₁N.conformal (continuousOn_lift_inv_of_normalized hcN)
        (continuousOn_lift_inv_of_normalized hc₁N)
        (Mo.isDomainChart_hullChart (Mo.isHPHull_fillH (hKc _) (hKp _) ω₁) _) hPd hfwd hlift (hT' ω)
    exact key (N ω₁) (by rw [hNω]; omega)
  exact ae_codeMatch_of_glued h12p h13 hκ (-(Real.pi / 2))
    (isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb')
    hELm hELr ((measurable_affField one_pos).comp hh'm) (𝓜 := stopFam (marksQ κ b jumps E u l k))
    (stopFam_le hMQ) hN hpast hKmg hKcg hKpg hx₀mg hhm hcmg hlawg hcode htr hW

end Main

end InteractingSLE.Theorem14.SB.Mz
