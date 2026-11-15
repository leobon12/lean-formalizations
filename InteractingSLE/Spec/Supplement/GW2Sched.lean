/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aPiece
import InteractingSLE.Spec.Supplement.GW2aMulti
import InteractingSLE.Spec.Supplement.BR6ProofArc
import InteractingSLE.Spec.Supplement.GW2ScheduleRun

/-!
# Lemma GW2's schedule containments: the first piece of every schedule, and the reduction to the later pieces

Packet PROVE-T14-BR5. The two schedule containments of Lemma GW2 (`GW2Cone.GW2ScheduleContainmentStatement`, from
the root `0`, and `GW2Cone.GW2ArcScheduleContainmentStatement`, from the roots `v` of the first low right arc;
supplement p. 621: "For a boundary root `v`, BR6 forces the whole initial arc `[x, v]` and BR4a gives the full
conditional pair targeted at `v`. […] GB6 places each available prefix in this conditional counterflow range in
reverse first-visit order. […] Ordinary-root schedules use GB6 directly"). A GW2 schedule is a program of ordinary
instructions (`GW2aMulti.isFlowProgram_scheduleProgram`), so its physical set is its root and its launched pieces
(`GW2aMulti.ae_physSet_subset_of_launches`).

* **The first piece of every schedule** is proved: from the root `0` by `GW2aSingle.ae_tipSet_first_subset`, from a
  root `v ∈ lowerArcRoots` by `GW2aPiece.ae_tipSet_first_subset_of_root` (BR4a's pair targeted at `v`, GB6, GW0,
  Theorem 1.3), with `v` a physical counterflow point by `GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13`.
* **The later pieces** (instructions `k ≥ 1`, launched at the interior tip of the previous piece) are the named
  remainder `GW2LaterPieceStatement`: GW2a's inductive step in the conditional world of the retained past (the
  conditional counterflow pair targeted at the current tip, GW1's induction datum (b), is not yet available; see
  `planning/handoffs/PROVE-T14-BR5.md`).
* **`gw2ScheduleContainmentStatement_of_later`**, **`gw2ArcScheduleContainmentStatement_of_later`**: both schedule
  containments from the later pieces; **`gw2LaterPieceStatement_of_length_le_one`**-type results: one-entry schedules
  need nothing more (`ae_physSet_subset_root_zero_of_length_le_one`, `ae_physSet_subset_root_arc_of_length_le_one`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Sched

open GW2aMulti CounterflowRange

/-! ### Schedule programs -/

/-- The angles of a schedule program are those of the schedule. -/
theorem isBoundaryContinuedProgram_scheduleProgram {l : List (ℝ × ℝ≥0)}
    (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (τ₀ : ℝ≥0) :
    IsBoundaryContinuedProgram (scheduleProgram τ₀ l) := by
  induction l generalizing τ₀ with
  | nil =>
    intro θ t h
    simp [scheduleProgram] at h
  | cons p l ih =>
    intro θ t h
    obtain ⟨θ₀, τ⟩ := p
    simp only [scheduleProgram, List.mem_cons] at h
    rcases h with h | h
    · simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      rw [h.1]
      exact hl (θ₀, τ) (List.mem_cons.2 (Or.inl rfl))
    · exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) τ θ t h

/-- The own time of the first instruction of a program starting with a flow. -/
theorem instrTime_zero_of_cons {spec : ExplSpec} {θ : ℝ} {t : ℝ≥0∞} {rest : List Instr}
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) : Exist.StagedLaw.instrTime spec 0 = t := by
  unfold Exist.StagedLaw.instrTime
  rw [hp]
  rfl

/-- No piece is launched by an instruction beyond the program. -/
theorem launches_run_succ_of_length_le (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : spec.2.2.length ≤ k) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none := by
  rw [Exist.Staged.run_succ, List.getElem?_eq_none hk]
  exact Exist.Staged.launches_run_of_le spec D le_rfl

/-- The roots of the first low right arc are positive. -/
theorem pos_of_mem_lowerArcRoots {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {v : ℝ}
    (hv : v ∈ lowerArcRoots κ b jumps) : 0 < v := by
  unfold lowerArcRoots at hv
  split_ifs at hv with h
  · exact hv.2.1
  · exact absurd hv (notMem_empty v)

/-! ### The first piece -/

/-- **The first launched piece, in `GW2aMulti`'s form**, from the containment of the first piece in its root chart. -/
theorem ae_launch_zero_subset (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {spec : ExplSpec} {θ : ℝ} {t : ℝ≥0∞}
    {rest : List Instr} (hp : spec.2.2 = Sum.inl (θ, t) :: rest) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {R : Ω → Set ℂ}
    (h0 : ∀ᵐ ω ∂P, (Chart.id.recenter spec.1).tipSet
      (fun r : ℝ≥0 => (E 0 ω).1 (min (r : ℝ≥0∞) (min t (E 0 ω).2)).toNNReal) (min t (E 0 ω).2) ⊆ R ω) :
    ∀ᵐ ω ∂P, ∀ (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω) (0 + 1)).2.2.2.1 0 = some (c, θ') →
      c.tipSet (stoppedDriver spec (fun j => E j ω) 0) (pieceStop spec (fun j => E j ω) 0) ⊆ R ω := by
  filter_upwards [h0] with ω hω c θ' hl
  rw [GW1.launches_run_one_of_cons κ b jumps spec hp] at hl
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl)
  unfold stoppedDriver pieceStop
  rw [instrTime_zero_of_cons hp]
  exact hω

/-- **The first piece of a GW2 schedule from `0`** lies in the completed counterflow range (GB6, GW0, Theorem 1.3). -/
theorem ae_launch_zero_subset_root_zero (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hW' : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {l : List (ℝ × ℝ≥0)} (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h ⟨0, true, scheduleProgram 0 l⟩ E) :
    ∀ᵐ ω ∂P, ∀ (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps ⟨0, true, scheduleProgram 0 l⟩ (fun j => E j ω) (0 + 1)).2.2.2.1 0 = some (c, θ') →
      c.tipSet (stoppedDriver ⟨0, true, scheduleProgram 0 l⟩ (fun j => E j ω) 0)
          (pieceStop ⟨0, true, scheduleProgram 0 l⟩ (fun j => E j ω) 0) ⊆
        counterflowCompletedRange (fun s => W' s ω) := by
  rcases l with _ | ⟨⟨θ, τ⟩, l'⟩
  · refine Eventually.of_forall fun ω c θ' hl0 => ?_
    rw [launches_run_succ_of_length_le κ b jumps _ _ (by simp [scheduleProgram])] at hl0
    exact absurd hl0 (by simp)
  · have hp : (⟨0, true, scheduleProgram 0 ((θ, τ) :: l')⟩ : ExplSpec).2.2 =
        Sum.inl (θ, (((τ - 0 : ℝ≥0)) : ℝ≥0∞)) :: scheduleProgram τ l' := rfl
    exact ae_launch_zero_subset κ b jumps hp (GW2aSingle.ae_tipSet_first_subset hGB6 hGW0 hT13 hκ hκ4 hb hh hW'
      hζ' hS rfl (hl (θ, τ) (List.mem_cons.2 (Or.inl rfl))) hp)

/-- **The first piece of a GW2 schedule from a root `v` of the first low right arc** lies in the completed
counterflow range (BR4a, GB6, GW0, Theorem 1.3). -/
theorem ae_launch_zero_subset_root_arc (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hW' : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {v : ℝ}
    (hv : v ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)}
    (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h ⟨v, true, scheduleProgram 0 l⟩ E) :
    ∀ᵐ ω ∂P, ∀ (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun j => E j ω) (0 + 1)).2.2.2.1 0 = some (c, θ') →
      c.tipSet (stoppedDriver ⟨v, true, scheduleProgram 0 l⟩ (fun j => E j ω) 0)
          (pieceStop ⟨v, true, scheduleProgram 0 l⟩ (fun j => E j ω) 0) ⊆
        counterflowCompletedRange (fun s => W' s ω) := by
  have hv0 := pos_of_mem_lowerArcRoots hv
  have hvR : ∀ᵐ ω ∂P, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤ := by
    filter_upwards [GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4 hb hh hW' hζ' hv hv0
      le_rfl] with ω hω
    rcases hω with hω | hω
    · exact hω
    · exact absurd (Complex.ofReal_eq_zero.1 (mem_singleton_iff.1 hω)) hv0.ne'
  rcases l with _ | ⟨⟨θ, τ⟩, l'⟩
  · refine Eventually.of_forall fun ω c θ' hl0 => ?_
    rw [launches_run_succ_of_length_le κ b jumps _ _ (by simp [scheduleProgram])] at hl0
    exact absurd hl0 (by simp)
  · have hp : (⟨v, true, scheduleProgram 0 ((θ, τ) :: l')⟩ : ExplSpec).2.2 =
        Sum.inl (θ, (((τ - 0 : ℝ≥0)) : ℝ≥0∞)) :: scheduleProgram τ l' := rfl
    exact ae_launch_zero_subset κ b jumps hp (GW2aPiece.ae_tipSet_first_subset_of_root hBR4a hGB6 hGW0 hT13 hκ
      hκ4 hb hh hW' hζ' hS hv0.ne' hvR (hl (θ, τ) (List.mem_cons.2 (Or.inl rfl))) hp)


/-! ### The later pieces and the two schedule containments -/

/-- **Named remainder: the later pieces of the GW2 schedules** (GW2a's inductive step, p. 623: "In the already
established complete conditional counterflow pair targeted at the current incoming tip, GB6 and BW1 apply to the next
ordinary piece"). In the setting of `GW2Cone.GW2ScheduleContainmentStatement`, for a root `x ∈ {0} ∪ lowerArcRoots`
and every schedule `l` with angles in `[−π/2, π/2]` and increasing times, every piece launched by an instruction
`k ≥ 1` (necessarily at the interior tip of the previous piece, GW2 convention) almost surely lies in the completed
counterflow range. This is the part of the two schedule containments that is not proved here: its proof needs the
conditional counterflow pair at the current tip given the retained past (GW1's induction datum (b)) — see
`planning/handoffs/PROVE-T14-BR5.md`. -/
def GW2LaterPieceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) → ∀ l : List (ℝ × ℝ≥0),
        (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) → l.Pairwise (fun p q => p.2 < q.2) →
        ∀ k : ℕ, 1 ≤ k → ∀ᵐ ω ∂P, ∀ (c : Chart) (θ : ℝ),
          (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
            (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
          c.tipSet (stoppedDriver ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k)
              (pieceStop ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) ⊆
            counterflowCompletedRange (fun t => W' t ω)

/-- **GW2's containment for the schedules from `0`** (`GW2Cone.GW2ScheduleContainmentStatement`) from the later
pieces (conditional helper): the root `0` is the terminal point of the range, the first piece is
`ae_launch_zero_subset_root_zero`. Named inputs: GB6's conditional-law half, Theorem 1.3 (at the universe of the
space and at `0`, the latter for GW0), and `GW2LaterPieceStatement`. -/
theorem gw2ScheduleContainmentStatement_of_later (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hL : GW2LaterPieceStatement.{u}) : GW2Cone.GW2ScheduleContainmentStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE l hlθ hlt
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hS := hE ⟨0, true, scheduleProgram 0 l⟩ (isBoundaryContinuedProgram_scheduleProgram hlθ 0)
  refine ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l)
    (E := fun j ω => E ⟨0, true, scheduleProgram 0 l⟩ j ω) (Eventually.of_forall fun ω => Or.inr rfl) fun k => ?_
  rcases k with _ | k
  · exact ae_launch_zero_subset_root_zero hGB6 hGW0 hT13 hκ hκ4 hb hh hcf hζ' hlθ hS
  · exact hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE 0 (Or.inl rfl) l hlθ hlt (k + 1) (by omega)

/-- **GW2's containment for the schedules from the boundary roots** (`GW2Cone.GW2ArcScheduleContainmentStatement`)
from the later pieces (conditional helper): the root `v` is a physical counterflow point
(`GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13`), the first piece is `ae_launch_zero_subset_root_arc`. Named
inputs: Corollary BR4a, GB6's conditional-law half, Theorem 1.3 and `GW2LaterPieceStatement`. -/
theorem gw2ArcScheduleContainmentStatement_of_later (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hL : GW2LaterPieceStatement.{u}) :
    GW2Cone.GW2ArcScheduleContainmentStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE v hv l hlθ hlt
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hS := hE ⟨v, true, scheduleProgram 0 l⟩ (isBoundaryContinuedProgram_scheduleProgram hlθ 0)
  refine ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l)
    (E := fun j ω => E ⟨v, true, scheduleProgram 0 l⟩ j ω) ?_ fun k => ?_
  · exact GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4 hb hh hcf hζ' hv
      (pos_of_mem_lowerArcRoots hv) le_rfl
  rcases k with _ | k
  · exact ae_launch_zero_subset_root_arc hBR4a hGB6 hGW0 hT13 hκ hκ4 hb hh hcf hζ' hv hlθ hS
  · exact hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE v (Or.inr hv) l hlθ hlt (k + 1) (by omega)

/-! ### One-entry schedules -/

/-- **The later pieces of a schedule with at most one entry** do not exist. -/
theorem later_piece_of_length_le_one (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ) {l : List (ℝ × ℝ≥0)}
    (hl : l.length ≤ 1) {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hk : 1 ≤ k) :
    (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D (k + 1)).2.2.2.1 k = none := by
  refine launches_run_succ_of_length_le κ b jumps _ D ?_
  change (scheduleProgram 0 l).length ≤ k
  rw [GW2Schedule.length_scheduleProgram]
  omega

/-- **GW2's containment for the one-entry schedules from `0`** (named inputs GB6, Theorem 1.3). -/
theorem ae_physSet_subset_root_zero_of_length_le_one (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hW' : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {l : List (ℝ × ℝ≥0)} (hl1 : l.length ≤ 1) (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h ⟨0, true, scheduleProgram 0 l⟩ E) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩ (fun j => E j ω) ⊆
      counterflowCompletedRange (fun t => W' t ω) := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  refine ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l) (E := E)
    (Eventually.of_forall fun ω => Or.inr rfl) fun k => ?_
  rcases k with _ | k
  · exact ae_launch_zero_subset_root_zero hGB6 hGW0 hT13 hκ hκ4 hb hh hW' hζ' hl hS
  · refine Eventually.of_forall fun ω c θ hlk => ?_
    rw [later_piece_of_length_le_one κ b jumps 0 hl1 (by omega)] at hlk
    exact absurd hlk (by simp)

/-- **GW2's containment for the one-entry schedules from a boundary root** (named inputs BR4a, GB6,
Theorem 1.3). -/
theorem ae_physSet_subset_root_arc_of_length_le_one (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hW' : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {v : ℝ}
    (hv : v ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)} (hl1 : l.length ≤ 1)
    (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h ⟨v, true, scheduleProgram 0 l⟩ E) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun j => E j ω) ⊆
      counterflowCompletedRange (fun t => W' t ω) := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  refine ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l) (E := E) ?_ fun k => ?_
  · exact GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4 hb hh hW' hζ' hv
      (pos_of_mem_lowerArcRoots hv) le_rfl
  rcases k with _ | k
  · exact ae_launch_zero_subset_root_arc hBR4a hGB6 hGW0 hT13 hκ hκ4 hb hh hW' hζ' hv hl hS
  · refine Eventually.of_forall fun ω c θ hlk => ?_
    rw [later_piece_of_length_le_one κ b jumps v hl1 (by omega)] at hlk
    exact absurd hlk (by simp)

end GW2Sched

end Theorem14

end InteractingSLE
