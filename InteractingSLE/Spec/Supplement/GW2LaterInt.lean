/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2LaterPass

/-!
# GW2a's later pieces at interior switching tips, from GB6 for the retained staged prefix

Packet PROVE-T14-BR6. Proposition GB6 (supplement p. 518) is stated for "a simple incoming flow prefix `α` from `x`,
stopped at a finite own stopping time `σ` before its continuation threshold, with `p = α(σ) ∈ D`", with "its canonical
finite-piece own marked law", angles in `[−π/2, π/2]`: "Conditional on the marked prefix, the portion of `η` before
its first contact with `α[0, σ]`, in the chart of `U` taking `(y, p)` to `(0, ∞)`, is the complete canonical
counterflow of the conditional component field. Its relative lifetime is infinite." For the retained prefix of a GW2
schedule (GB7: simple; switches at interior tips) this is exactly GW1's induction datum 2 at the next launch,
`HasLaunchPair` (GW2a p. 623: "In the already established complete conditional counterflow pair targeted at the current
incoming tip").

* `IsInteriorStop`, `SwitchTipsInterior`: the tips of the retained pieces at their stops are interior (GB6's `p ∈ D`;
  GW2, p. 621: "all switching and terminal tips of successful schedules are interior").
* **`GB6StagedPairStatement`** (named input): GB6's conclusion for the retained prefix of a GW2 schedule, at every
  launch `k ≥ 1` whose switching tips are interior.
* **`ae_later_piece_subset`**: the piece launched at `k ≥ 1` lies in the completed counterflow range, almost surely,
  when the switching tips are almost surely interior (from `GW2Later.ae_piece_subset_of_pair_flow`).
* **`ae_physSet_subset_of_interior`**: the physical set of a GW2 schedule from `0` or from a root of the first low right
  arc lies in the completed counterflow range when its switching tips are almost surely interior (the first piece is
  PROVE-T14-BR5's).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Later

open CounterflowRange GW2Schedule GW2aMulti GW2Sched

/-- The tip of a piece with driver `w`, stopped at `S`, is an interior point (in the coordinate of its launch chart). -/
def IsInteriorStop (w : ℝ≥0 → ℝ) (S : ℝ≥0∞) : Prop :=
  ∃ p ∈ H, Chart.id.tipAt (fun r : ℝ≥0 => w (min (r : ℝ≥0∞) S).toNNReal) S.toNNReal p

/-- The tips of the pieces launched before instruction `k`, at their stops, are interior. -/
def SwitchTipsInterior (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : Prop :=
  ∀ j < k, IsInteriorStop (D j).1 (pieceStop spec D j)

/-- **Named input: Proposition GB6 for the retained prefix of a GW2 schedule** (supplement p. 518; GW1's induction
datum 2, p. 618; GW2a, p. 623). For a GW2 schedule from the root `0` or from a root `v` of the first low right arc, and
a staged history whose pieces are regular (ruling R51), at almost every sample whose switching tips before the launch of
instruction `k ≥ 1` are interior, the conditional counterflow pair targeted at the current tip is available
(`HasLaunchPair`): under the conditional law given the retained past, the field read in the launch chart has a centred
counterflow with infinite relative lifetime whose tips are physical points of the original completed counterflow
range. -/
def GB6StagedPairStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) → ∀ l : List (ℝ × ℝ≥0),
        (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) → l.Pairwise (fun p q => p.2 < q.2) →
        ∀ k : ℕ, 1 ≤ k → ∀ᵐ ω₀ ∂P,
          SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω₀) k →
          HasLaunchPair κ b jumps P h W' ⟨x, true, scheduleProgram 0 l⟩ (E ⟨x, true, scheduleProgram 0 l⟩) k ω₀

/-- The angles of a schedule lie in `[−π/2, π/2]`. -/
theorem schedAngle_mem_Icc {l : List (ℝ × ℝ≥0)} (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {k : ℕ} (hk : k < l.length) : schedAngle l k ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  unfold schedAngle
  rw [List.getD_eq_getElem _ _ hk]
  exact hl _ (List.getElem_mem hk)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **GW2a's later pieces at interior switching tips.** For a GW2 schedule from `0` or a root `v` of the first low right
arc, a staged history with regular pieces, and `k ≥ 1`: if almost surely the switching tips before `k` are interior
whenever the first `k` pieces were successful, the piece launched at `k` lies in the completed counterflow range almost
surely. Named inputs: `GB6StagedPairStatement`, GB6's restart law, Theorem 1.3 (also at `0`, for GW0). -/
theorem ae_later_piece_subset (hG : GB6StagedPairStatement.{u}) (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {x : ℝ} (hx : x = 0 ∨ x ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)}
    (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hlt : l.Pairwise (fun p q => p.2 < q.2))
    {k : ℕ} (hk1 : 1 ≤ k)
    (hint : ∀ᵐ ω ∂P, AllSucc (schedDelta 0 l) (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k →
      SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) :
    ∀ᵐ ω ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
      c.tipSet (stoppedDriver ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k)
          (pieceStop ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) ⊆
        counterflowCompletedRange (fun t => W' t ω) := by
  set spec : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩ with hspec
  have hBC : IsBoundaryContinuedProgram spec.2.2 := isBoundaryContinuedProgram_scheduleProgram hl 0
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  by_cases hk : k < spec.2.2.length
  · have hprog : IsFlowProg spec.2.2 (schedAngle l) (schedDelta 0 l) := isFlowProg_scheduleProgram 0 l
    have hklen : k < l.length := by
      have := length_scheduleProgram 0 l
      simp only [hspec] at hk
      omega
    have hpair := hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER x hx l hl hlt k hk1
    have hpair' : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω | AllSucc (schedDelta 0 l) (fun j => E spec j ω) k} →
        HasLaunchPair κ b jumps P h W' spec (E spec) k ω₀ := by
      filter_upwards [hpair, hint] with ω₀ hp hi hω₀
      exact hp (hi hω₀)
    have hres := ae_piece_subset_of_pair_flow hGB6 hGW0 hT13 hκ hκ4 hcf hζ' (spec := spec) rfl hprog
      (schedDelta_ne_top 0 l) (hE spec hBC) (hER spec hBC) hk (schedAngle_mem_Icc hl hklen)
      (measurableSet_allSucc rfl hprog (schedDelta_ne_top 0 l) (E spec) hk.le) hpair'
    filter_upwards [hres] with ω hω c θ hlk
    have hs : AllSucc (schedDelta 0 l) (fun j => E spec j ω) k := by
      by_contra hns
      rw [(launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := spec) rfl hprog (schedDelta_ne_top 0 l)
        (fun j => E spec j ω) hk).2 hns] at hlk
      exact absurd hlk (by simp)
    exact hω hs c θ hlk
  · refine Eventually.of_forall fun ω c θ hlk => ?_
    rw [launches_run_succ_of_length_le κ b jumps spec _ (not_lt.1 hk)] at hlk
    exact absurd hlk (by simp)

/-- **GW2's schedule containment at interior switching tips** (Lemma GW2, p. 621: "Intersect these countably many events
before taking the closure"). For a GW2 schedule from `0` or from a root `v` of the first low right arc and a staged
history with regular pieces whose switching tips are almost surely interior (at every launch, whenever the earlier
pieces were successful), the physical set lies in the completed counterflow range almost surely. The first piece is
PROVE-T14-BR5's (`GW2Sched.ae_launch_zero_subset_root_zero`, `ae_launch_zero_subset_root_arc`); the root `v` is a
physical counterflow point (`GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13`). Named inputs:
`GB6StagedPairStatement`, Corollary BR4a (boundary roots), GB6's restart law, Theorem 1.3. -/
theorem ae_physSet_subset_of_interior (hG : GB6StagedPairStatement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {x : ℝ} (hx : x = 0 ∨ x ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)}
    (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hlt : l.Pairwise (fun p q => p.2 < q.2))
    (hint : ∀ k, ∀ᵐ ω ∂P, AllSucc (schedDelta 0 l) (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k →
      SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun k => E ⟨x, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hS := hE ⟨x, true, scheduleProgram 0 l⟩ (isBoundaryContinuedProgram_scheduleProgram hl 0)
  rcases hx with rfl | hv
  · refine ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l)
      (E := fun j ω => E ⟨0, true, scheduleProgram 0 l⟩ j ω) (Eventually.of_forall fun ω => Or.inr rfl)
      fun k => ?_
    rcases k with _ | k
    · exact ae_launch_zero_subset_root_zero hGB6 hGW0 hT13 hκ hκ4 hb hh hcf hζ' hl hS
    · exact ae_later_piece_subset hG hGB6 hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hE hER (Or.inl rfl) hl hlt
        (by omega) (hint (k + 1))
  · refine ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l)
      (E := fun j ω => E ⟨x, true, scheduleProgram 0 l⟩ j ω) ?_ fun k => ?_
    · exact GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4 hb hh hcf hζ' hv
        (pos_of_mem_lowerArcRoots hv) le_rfl
    rcases k with _ | k
    · exact ae_launch_zero_subset_root_arc hBR4a hGB6 hGW0 hT13 hκ hκ4 hb hh hcf hζ' hv hl hS
    · exact ae_later_piece_subset hG hGB6 hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hE hER (Or.inr hv) hl hlt
        (by omega) (hint (k + 1))

end GW2Later

end Theorem14

end InteractingSLE
