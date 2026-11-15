/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem14
import InteractingSLE.Frozen.Spec.ExplState_run

/-!
# Corollary GW6 from Lemma GW2a and the end of the first walk piece

Packet PROVE-T14-IN. Corollary GW6's proof (`source/spec/p625-671.md` L337, p. 643): "Every nontrivial connector of
either walk is an original boundary interval contained in the counterflow range, by GW1. Hence no connector can
occur on the specified event. The finite walk algorithm then consists of just its first complete ordinary piece on
each side. An initial bad seed or a later finite threshold would create a nontrivial low connector, so neither is
possible there."

On the frozen carriers this is a reduction of the named input `Theorem14.GW6Statement` of PROVE-SEC7-D2 to

* `Theorem14.GW2aContainmentStatement` (already a named input: the walks lie in the counterflow range), and
* `Theorem14.GW1FirstThresholdStatement` (new, narrower): the first ordinary piece of an extreme walk, if its lifetime
  is finite, ends at a continuation threshold: a new original record, or its seed with a bad side (Lemma GW0, p. 617:
  "An inadmissible seed gives zero available lifetime"; Lemma GW1, pp. 618–619: "Every finite threshold of a nonempty
  ordinary stage consequently has physical value `q_j > w_j`, and is a new original right record").

The proof is deterministic bookkeeping of the frozen staged-history semantics (`ExplState.run`): steps never forget a
recorded connector (`mem_arcs_step`), and at a threshold the boundary continuation records a connector with nonempty
interior (`exists_mem_arcs_contStep`). Main result: `gw6Statement_of_gw2a`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

/-! ### Steps keep the recorded connectors -/

theorem arcs_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k D θ t).2.1 = s.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  simp only [ExplState.launch]
  split_ifs <;> (try split) <;> rfl

theorem arcs_flowStep (κ : ℝ) (b : ℝ → ℝ) (gw2 : Bool) (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (θ : ℝ) (t : ℝ≥0∞) : (ExplState.flowStep κ b gw2 s k D θ t).2.1 = s.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  simp only [ExplState.flowStep]
  split <;> (try split_ifs) <;> simp only [arcs_launch]

theorem arcs_moveAlong (s : ExplState) (right : Bool) (x : ℝ) (atMark : Bool) :
    (ExplState.moveAlong s right x atMark).2.1 =
      s.2.1 ++ [if right then Icc s.2.2.2.2.2.2.1 x else Icc x s.2.2.2.2.2.2.1] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  rfl

theorem arcs_moveToEnd (s : ExplState) (right : Bool) :
    (ExplState.moveToEnd s right).2.1 =
      s.2.1 ++ [if right then Ici s.2.2.2.2.2.2.1 else Iic s.2.2.2.2.2.2.1] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  rfl

theorem subset_arcs_contStep (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (vStop : Option ℝ)
    (pref : Bool) {A : Set ℝ} (hA : A ∈ s.2.1) : A ∈ (ExplState.contStep κ b jumps s vStop pref).2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  simp only [ExplState.contStep]
  split <;> (try split_ifs) <;> (try split) <;> (try split_ifs) <;>
    simp only [arcs_moveAlong, arcs_moveToEnd, List.mem_append] <;> (try exact Or.inl hA) <;> exact hA

theorem mem_arcs_step (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (gw2 : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (s : ExplState) (ik : Instr × ℕ) {A : Set ℝ} (hA : A ∈ s.2.1) :
    A ∈ (ExplState.step κ b jumps gw2 D s ik).2.1 := by
  obtain ⟨i, k⟩ := ik
  rcases i with ⟨θ, t⟩ | pref | ⟨v, pref⟩
  · simp only [ExplState.step, arcs_flowStep]; exact hA
  · exact subset_arcs_contStep κ b jumps s none pref hA
  · exact subset_arcs_contStep κ b jumps s (some v) pref hA

theorem mem_arcs_foldl (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (gw2 : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (l : List (Instr × ℕ)) (s : ExplState) {A : Set ℝ} (hA : A ∈ s.2.1) :
    A ∈ (l.foldl (ExplState.step κ b jumps gw2 D) s).2.1 := by
  induction l generalizing s with
  | nil => exact hA
  | cons ik l ih => exact ih _ (mem_arcs_step κ b jumps gw2 D s ik hA)

/-! ### A threshold forces a nontrivial connector -/

/-- The state at the end of the first piece of a walk is **a continuation threshold with a bad side**: a new right
or left original record (status *thr* `some _`), or the seed with a bad seed side (status *thr* `none` and the seed
not admissible for the current angle). -/
def IsThresholdEnd (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) : Prop :=
  s.2.2.2.2.2.1 = (Sum.inr (Sum.inr (Sum.inl (some true))) : ExplStatus) ∨
    s.2.2.2.2.2.1 = (Sum.inr (Sum.inr (Sum.inl (some false))) : ExplStatus) ∨
    (s.2.2.2.2.2.1 = (Sum.inr (Sum.inr (Sum.inl none)) : ExplStatus) ∧
      ¬ ExplState.IsAdmissibleSeed κ (PiecewiseConstantBoundaryData.leftLim b s.2.2.2.2.2.2.1)
        (PiecewiseConstantBoundaryData.rightLim b s.2.2.2.2.2.2.1) s.2.2.2.2.2.2.2.1)

theorem nonempty_interior_Icc {a b : ℝ} (h : a < b) : (interior (Icc a b)).Nonempty := by
  rw [interior_Icc]; exact nonempty_Ioo.2 h

theorem nonempty_interior_Ici (a : ℝ) : (interior (Ici a)).Nonempty := by
  rw [interior_Ici]; exact nonempty_Ioi

theorem nonempty_interior_Iic (a : ℝ) : (interior (Iic a)).Nonempty := by
  rw [interior_Iic]; exact nonempty_Iio

/-- **At a continuation threshold the boundary continuation records a connector with nonempty interior.** -/
theorem exists_mem_arcs_contStep (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (pref : Bool)
    (hs : IsThresholdEnd κ b s) :
    ∃ A ∈ (ExplState.contStep κ b jumps s none pref).2.1, (interior A).Nonempty := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  simp only [IsThresholdEnd] at hs
  rcases hs with h | h | ⟨h, hadm⟩ <;> subst h
  · simp only [ExplState.contStep]
    split_ifs with hC
    · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      have hm := (Finset.mem_filter.1 (Finset.min'_mem _ hC)).2.1
      simp only [ite_true]
      exact nonempty_interior_Icc hm
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by
        simp only [ite_true]; exact nonempty_interior_Ici _⟩
  · simp only [ExplState.contStep]
    split_ifs with hC
    · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      have hm := (Finset.mem_filter.1 (Finset.max'_mem _ hC)).2.1
      simp only [Bool.false_eq_true, ite_false]
      exact nonempty_interior_Icc hm
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by
        simp only [Bool.false_eq_true, ite_false]; exact nonempty_interior_Iic _⟩
  · simp only [ExplState.IsAdmissibleSeed, not_and_or, not_lt] at hadm
    simp only [ExplState.contStep]
    -- the boundary continuation to the right, resp. left, records a connector with nonempty interior
    have hright : ∃ A ∈ (if hC : ((PiecewiseConstantBoundaryData.jumpSet b jumps).filter fun x => pt < x ∧
          -sleLambda κ < PiecewiseConstantBoundaryData.rightLim b x + θ' * QuantumZipper.chiC κ).Nonempty then
          ExplState.moveAlong (pieces, arcs, retained, launches, chart, Sum.inr (Sum.inr (Sum.inl none)), pt, θ',
            recR, recL) true (Finset.min' _ hC) true
        else ExplState.moveToEnd (pieces, arcs, retained, launches, chart, Sum.inr (Sum.inr (Sum.inl none)), pt, θ',
            recR, recL) true).2.1, (interior A).Nonempty := by
      split_ifs with hC
      · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        have hm := (Finset.mem_filter.1 (Finset.min'_mem _ hC)).2.1
        simp only [ite_true]
        exact nonempty_interior_Icc hm
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by
          simp only [ite_true]; exact nonempty_interior_Ici _⟩
    have hleft : ∃ A ∈ (if hC : ((PiecewiseConstantBoundaryData.jumpSet b jumps).filter fun x => x < pt ∧
          PiecewiseConstantBoundaryData.leftLim b x + θ' * QuantumZipper.chiC κ < sleLambda κ).Nonempty then
          ExplState.moveAlong (pieces, arcs, retained, launches, chart, Sum.inr (Sum.inr (Sum.inl none)), pt, θ',
            recR, recL) false (Finset.max' _ hC) true
        else ExplState.moveToEnd (pieces, arcs, retained, launches, chart, Sum.inr (Sum.inr (Sum.inl none)), pt, θ',
            recR, recL) false).2.1, (interior A).Nonempty := by
      split_ifs with hC
      · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        have hm := (Finset.mem_filter.1 (Finset.max'_mem _ hC)).2.1
        simp only [Bool.false_eq_true, ite_false]
        exact nonempty_interior_Icc hm
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by
          simp only [Bool.false_eq_true, ite_false]; exact nonempty_interior_Iic _⟩
    by_cases h1 : PiecewiseConstantBoundaryData.rightLim b pt + θ' * QuantumZipper.chiC κ ≤ -sleLambda κ ∧
        sleLambda κ ≤ PiecewiseConstantBoundaryData.leftLim b pt + θ' * QuantumZipper.chiC κ
    · rw [ite_eq_left h1]
      cases pref
      · exact hleft
      · exact hright
    · rw [ite_eq_right h1]
      by_cases h2 : PiecewiseConstantBoundaryData.rightLim b pt + θ' * QuantumZipper.chiC κ ≤ -sleLambda κ
      · rw [ite_eq_left h2]
        exact hright
      · rw [ite_eq_right h2, ite_eq_left (hadm.resolve_right h2)]
        exact hleft

/-! ### The first two instructions of a walk -/

/-- The walk program starts with its first ordinary piece and its first boundary continuation. -/
theorem zipIdx_take_boundaryWalkSpec (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) :
    ∃ rest : List (Instr × ℕ),
      (boundaryWalkSpec b jumps θ right).2.2.zipIdx.take (boundaryWalkSpec b jumps θ right).2.2.length =
        (Sum.inl (θ, ⊤), 0) :: (Sum.inr (Sum.inl right), 1) :: rest := by
  refine ⟨((List.replicate (PiecewiseConstantBoundaryData.jumpSet b jumps).card
    [(Sum.inl (θ, ⊤) : Instr), Sum.inr (Sum.inl right)]).flatten).zipIdx 2, ?_⟩
  rw [List.take_of_length_le (by rw [List.length_zipIdx])]
  simp only [boundaryWalkSpec, List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append,
    List.zipIdx_cons]

/-- **A threshold at the end of the first piece puts a connector with nonempty interior into the walk.** -/
theorem exists_mem_arcs_run_boundaryWalkSpec (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hthr : IsThresholdEnd κ b (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤)) :
    ∃ A ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (boundaryWalkSpec b jumps θ right).2.2.length).2.1, (interior A).Nonempty := by
  obtain ⟨rest, hrest⟩ := zipIdx_take_boundaryWalkSpec b jumps θ right
  have h1 : ExplState.step κ b jumps false D (ExplState.init 0) (Sum.inl (θ, ⊤), 0) =
      ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤ := rfl
  obtain ⟨A, hA, hAi⟩ := exists_mem_arcs_contStep κ b jumps _ right hthr
  refine ⟨A, ?_, hAi⟩
  unfold ExplState.run
  rw [hrest, List.foldl_cons, List.foldl_cons]
  refine mem_arcs_foldl κ b jumps _ D rest _ ?_
  show A ∈ (ExplState.step κ b jumps false D
    (ExplState.step κ b jumps false D (ExplState.init 0) (Sum.inl (θ, ⊤), 0)) (Sum.inr (Sum.inl right), 1)).2.1
  rw [h1]
  exact hA

/-- A recorded connector lies in the physical set of the history. -/
theorem image_subset_physSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {A : Set ℝ}
    (hA : A ∈ (ExplState.run κ b jumps spec D spec.2.2.length).2.1) :
    ((↑) : ℝ → ℂ) '' A ⊆ ExplState.physSet κ b jumps spec D := fun _ hz =>
  Or.inr (Set.mem_biUnion hA hz)

/-! ### The named input and the reduction -/

/-- **Named input: the end of the first piece of an extreme walk** (Lemma GW0, p. 617: "An inadmissible seed gives
zero available lifetime", with the maximal lifetime of an integrated evolution; Lemma GW1, pp. 618–619: "Every finite
threshold of a nonempty ordinary stage consequently has physical value `q_j > w_j`, and is a new original right
record"): almost surely, if the first ordinary piece of the right walk (angle `−π/2`) or of the left walk (angle
`π/2`) has finite lifetime, the state after it is a continuation threshold with a bad side (`IsThresholdEnd`): a new
original record, or the seed with a bad seed side. The setting is that of `GW6Statement`. -/
def GW1FirstThresholdStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ (θ : ℝ) (right : Bool), (θ = -(Real.pi / 2) ∧ right = true) ∨ (θ = Real.pi / 2 ∧ right = false) →
        ∀ᵐ ω ∂P, (E (boundaryWalkSpec b jumps θ right) 0 ω).2 ≠ ⊤ →
          IsThresholdEnd κ b
            (ExplState.launch (ExplState.init 0) 0 (E (boundaryWalkSpec b jumps θ right) 0 ω) θ ⊤)

/-- **Corollary GW6 (the nowhere-boundary-filling clause) from Lemma GW2a and the end of the first walk piece**
(GW6's proof, p. 643: "Every nontrivial connector of either walk is an original boundary interval contained in the
counterflow range … An initial bad seed or a later finite threshold would create a nontrivial low connector"). -/
theorem gw6Statement_of_gw2a (hGW2a : GW2aContainmentStatement.{u})
    (hthr : GW1FirstThresholdStatement.{u}) : GW6Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE
  have hpi := Real.pi_pos
  have hR := hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
      ⟨le_rfl, by linarith⟩ true)
  have hL := hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2)
      ⟨by linarith, le_rfl⟩ false)
  have tR := hthr κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE (-(Real.pi / 2)) true
    (Or.inl ⟨rfl, rfl⟩)
  have tL := hthr κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE (Real.pi / 2) false
    (Or.inr ⟨rfl, rfl⟩)
  filter_upwards [hR, hL, tR, tL] with ω h1 h2 h3 h4 hint
  have key : ∀ (θ : ℝ) (right : Bool),
      ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right)
          (fun k => E (boundaryWalkSpec b jumps θ right) k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) →
      ((E (boundaryWalkSpec b jumps θ right) 0 ω).2 ≠ ⊤ →
        IsThresholdEnd κ b
          (ExplState.launch (ExplState.init 0) 0 (E (boundaryWalkSpec b jumps θ right) 0 ω) θ ⊤)) →
      (E (boundaryWalkSpec b jumps θ right) 0 ω).2 = ⊤ := by
    intro θ right hsub hthr'
    by_contra hne
    obtain ⟨A, hA, hAi⟩ := exists_mem_arcs_run_boundaryWalkSpec κ b jumps θ right
      (fun k => E (boundaryWalkSpec b jumps θ right) k ω) (hthr' hne)
    have hAsub : A ⊆ ((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω) := fun x hx =>
      hsub (image_subset_physSet κ b jumps _ _ hA (mem_image_of_mem _ hx))
    obtain ⟨x, hx⟩ := hAi
    have := interior_mono hAsub hx
    rw [hint] at this
    exact this
  exact ⟨key _ _ h1 h3, key _ _ h2 h4⟩

end Theorem14

end InteractingSLE
