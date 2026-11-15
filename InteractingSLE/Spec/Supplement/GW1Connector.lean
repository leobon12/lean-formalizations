/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedRun
import InteractingSLE.Frozen.Spec.boundaryWalkSpec

/-!
# Lemma GW1: the connectors of an extreme boundary walk lie on its own side (the deterministic part)

Packet PROVE-T14-GW6. Lemma GW1 (`source/spec/p577-624.md` L931–L932, p. 618): "Every nontrivial real connector is
rightward, every restart uses a previously unpassed original right mark"; "Reflection gives the left boundary walk
`L`". The named input `Theorem14.GW3Word.WalkConnectorSideStatement` asks that almost surely every connector recorded
by the right walk lies in `[0, ∞)` and every one of the left walk in `(−∞, 0]`.

This file is the bookkeeping of the frozen state machine (`ExplState.run`) for the two walk programs
`boundaryWalkSpec b jumps θ right` (alternating ordinary pieces `flow θ ⊤` and boundary continuations `cont right`).
A connector on the wrong side can only arise in two ways:

* a piece ends at a threshold on the wrong side (status *thr* `some false` for the right walk), or
* a piece has zero lifetime (status *thr* `none`) and the left seed height is bad for the current angle.

The second case is excluded deterministically: a piece is launched from a boundary point only when its seed is
admissible for the walk's angle (`ExplState.flowStep`), and from the root only under a seed bound that the main
theorem gets from the ambient admissibility (GW0). So the connectors are on the right side as soon as no piece ends at
a wrong-side record.

## Main results

* `getElem?_boundaryWalkSpec`: the instruction list of a walk program;
* `RFlowInv`, `RContInv` (and the mirrors `LFlowInv`, `LContInv`): the invariants before a flow and before a
  continuation instruction, preserved by the steps (`rFlowInv_flowStep`, `rContInv_contStep`, …);
* **`arcs_subset_Ici_of_forall_ne`**: if the root seed bound holds and no instruction ends at status *thr*
  `some false`, every connector recorded by the right walk lies in `[0, ∞)`;
* **`arcs_subset_Iic_of_forall_ne`**: the mirror statement for the left walk.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW1Conn

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### The walk program -/

/-- The `k`-th entry of a list of `m` copies of a pair `[x, y]`, flattened. -/
theorem getElem?_flatten_replicate_pair {α : Type*} (x y : α) (m k : ℕ) :
    (List.replicate m [x, y]).flatten[k]? =
      if k < 2 * m then some (if k % 2 = 0 then x else y) else none := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons]
    rcases k with _ | _ | k
    · simp
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
      have h1 : 1 < 2 * (m + 1) := by omega
      simp [h1]
    · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
      rw [ih k]
      have h1 : (k + 1 + 1 < 2 * (m + 1)) ↔ k < 2 * m := by omega
      have h2 : (k + 1 + 1) % 2 = k % 2 := by omega
      simp only [h1, h2]

/-- **The instructions of a walk program**: ordinary pieces `flow θ ⊤` at the even indices and boundary
continuations `cont right` at the odd indices, `2 (n + 1)` instructions in all (`n` genuine jumps). -/
theorem getElem?_boundaryWalkSpec (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) (k : ℕ) :
    (boundaryWalkSpec b jumps θ right).2.2[k]? =
      if k < (boundaryWalkSpec b jumps θ right).2.2.length then
        some (if k % 2 = 0 then (Sum.inl (θ, ⊤) : Instr) else Sum.inr (Sum.inl right))
      else none := by
  have hlen : (boundaryWalkSpec b jumps θ right).2.2.length = 2 * ((jumpSet b jumps).card + 1) := by
    simp only [boundaryWalkSpec, List.length_flatten, List.map_replicate, List.sum_replicate,
      List.length_cons, List.length_nil, smul_eq_mul]
    ring
  rw [hlen]
  exact getElem?_flatten_replicate_pair _ _ _ k

/-- The root of a walk program is `0`. -/
theorem boundaryWalkSpec_fst (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) :
    (boundaryWalkSpec b jumps θ right).1 = 0 := rfl

/-- A walk program is not a GW2 program. -/
theorem boundaryWalkSpec_gw2 (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) :
    (boundaryWalkSpec b jumps θ right).2.1 = false := rfl

/-! ### The statuses -/

/-- The status *root*. -/
abbrev stRoot : ExplStatus := Sum.inl ()

/-- The status *tip*. -/
abbrev stTip : ExplStatus := Sum.inr (Sum.inl ())

/-- The status *threshold* (`some true`: a new right record; `some false`: a new left record; `none`: the seed). -/
abbrev stThr (o : Option Bool) : ExplStatus := Sum.inr (Sum.inr (Sum.inl o))

/-- The status *on an arc* (direction, at a mark). -/
abbrev stArc (r m : Bool) : ExplStatus := Sum.inr (Sum.inr (Sum.inr (Sum.inl (r, m))))

/-- The status *done*. -/
abbrev stDone : ExplStatus := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))

/-- The status *dead*. -/
abbrev stDead : ExplStatus := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))

/-! ### Records -/

/-- A supremum of a set containing a nonnegative number is nonnegative (`sSup` of an unbounded set is `0`). -/
theorem zero_le_sSup_insert {a : ℝ} (ha : 0 ≤ a) (S : Set ℝ) : 0 ≤ sSup (insert a S) := by
  by_cases hb : BddAbove (insert a S)
  · exact ha.trans (le_csSup hb (mem_insert a S))
  · rw [Real.sSup_of_not_bddAbove hb]

/-- An infimum of a set containing a nonpositive number is nonpositive (`sInf` of an unbounded set is `0`). -/
theorem sInf_insert_nonpos {a : ℝ} (ha : a ≤ 0) (S : Set ℝ) : sInf (insert a S) ≤ 0 := by
  by_cases hb : BddBelow (insert a S)
  · exact (csInf_le hb (mem_insert a S)).trans ha
  · rw [Real.sInf_of_not_bddBelow hb]

/-! ### One launch with an infinite budget -/

/-- **A launch with an infinite budget, right-walk view.** From a state that is not at a tip, with nonnegative current
point and right record, a launch `flow θ ⊤` keeps the connectors, sets the angle to `θ`, keeps the current point and
right record nonnegative, and ends at a right record, at the seed (status *thr* `none`, same point), done or dead —
unless it ends at a new left record. -/
theorem launch_top_right (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (hst : s.2.2.2.2.2.1 ≠ stTip) (hp : 0 ≤ s.2.2.2.2.2.2.1) (hR : 0 ≤ s.2.2.2.2.2.2.2.2.1)
    (hno : (ExplState.launch s k D θ ⊤).2.2.2.2.2.1 ≠ stThr (some false)) :
    (ExplState.launch s k D θ ⊤).2.1 = s.2.1 ∧ 0 ≤ (ExplState.launch s k D θ ⊤).2.2.2.2.2.2.1 ∧
      0 ≤ (ExplState.launch s k D θ ⊤).2.2.2.2.2.2.2.2.1 ∧
      (ExplState.launch s k D θ ⊤).2.2.2.2.2.2.2.1 = θ ∧
      ((ExplState.launch s k D θ ⊤).2.2.2.2.2.1 = stThr (some true) ∨
        ((ExplState.launch s k D θ ⊤).2.2.2.2.2.1 = stThr none ∧
          (ExplState.launch s k D θ ⊤).2.2.2.2.2.2.1 = s.2.2.2.2.2.2.1) ∨
        (ExplState.launch s k D θ ⊤).2.2.2.2.2.1 = stDone ∨
        (ExplState.launch s k D θ ⊤).2.2.2.2.2.1 = stDead) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  simp only at hst hp hR
  have hstop : min (⊤ : ℝ≥0∞) D.2 = D.2 := min_eq_right le_top
  simp only [ExplState.launch, hstop] at hno ⊢
  split_ifs at hno ⊢ with h1 h2 h3 h4 h5 <;> first
    | exact absurd h2 not_top_lt
    | exact absurd rfl hno
    | exact absurd rfl hst
    | exact ⟨rfl, hp, hR, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    | exact ⟨rfl, hp, zero_le_sSup_insert hR _, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | exact ⟨rfl, zero_le_sSup_insert hR _, zero_le_sSup_insert hR _, rfl, Or.inl rfl⟩
    | exact ⟨rfl, hp, zero_le_sSup_insert hR _, rfl, Or.inr (Or.inr (Or.inr rfl))⟩

/-- **A launch with an infinite budget, left-walk view** (mirror of `launch_top_right`). -/
theorem launch_top_left (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (hst : s.2.2.2.2.2.1 ≠ stTip) (hp : s.2.2.2.2.2.2.1 ≤ 0) (hL : s.2.2.2.2.2.2.2.2.2 ≤ 0)
    (hno : (ExplState.launch s k D θ ⊤).2.2.2.2.2.1 ≠ stThr (some true)) :
    (ExplState.launch s k D θ ⊤).2.1 = s.2.1 ∧ (ExplState.launch s k D θ ⊤).2.2.2.2.2.2.1 ≤ 0 ∧
      (ExplState.launch s k D θ ⊤).2.2.2.2.2.2.2.2.2 ≤ 0 ∧
      (ExplState.launch s k D θ ⊤).2.2.2.2.2.2.2.1 = θ ∧
      ((ExplState.launch s k D θ ⊤).2.2.2.2.2.1 = stThr (some false) ∨
        ((ExplState.launch s k D θ ⊤).2.2.2.2.2.1 = stThr none ∧
          (ExplState.launch s k D θ ⊤).2.2.2.2.2.2.1 = s.2.2.2.2.2.2.1) ∨
        (ExplState.launch s k D θ ⊤).2.2.2.2.2.1 = stDone ∨
        (ExplState.launch s k D θ ⊤).2.2.2.2.2.1 = stDead) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  simp only at hst hp hL
  have hstop : min (⊤ : ℝ≥0∞) D.2 = D.2 := min_eq_right le_top
  simp only [ExplState.launch, hstop] at hno ⊢
  split_ifs at hno ⊢ with h1 h2 h3 h4 h5 <;> first
    | exact absurd h2 not_top_lt
    | exact absurd rfl hno
    | exact absurd rfl hst
    | exact ⟨rfl, hp, hL, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    | exact ⟨rfl, hp, sInf_insert_nonpos hL _, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | exact ⟨rfl, sInf_insert_nonpos hL _, sInf_insert_nonpos hL _, rfl, Or.inl rfl⟩
    | exact ⟨rfl, hp, sInf_insert_nonpos hL _, rfl, Or.inr (Or.inr (Or.inr rfl))⟩

/-! ### The invariants of the right walk -/

/-- **The right walk before an ordinary-piece instruction**: every connector lies in `[0, ∞)`, the current point and
the right record are nonnegative, and the status is the root (with the root seed bound for the angle `θ`), on a
right arc at a mark, done or dead. -/
def RFlowInv (κ : ℝ) (b : ℝ → ℝ) (θ : ℝ) (s : ExplState) : Prop :=
  (∀ a ∈ s.2.1, a ⊆ Ici (0 : ℝ)) ∧ 0 ≤ s.2.2.2.2.2.2.1 ∧ 0 ≤ s.2.2.2.2.2.2.2.2.1 ∧
    ((s.2.2.2.2.2.1 = stRoot ∧ leftLim b s.2.2.2.2.2.2.1 + θ * QuantumZipper.chiC κ < sleLambda κ) ∨
      s.2.2.2.2.2.1 = stArc true true ∨ s.2.2.2.2.2.1 = stDone ∨ s.2.2.2.2.2.1 = stDead)

/-- **The right walk before a boundary-continuation instruction**: every connector lies in `[0, ∞)`, the current
point and the right record are nonnegative, and the status is a right record, the seed with an admissible left side
for the current angle, a right arc at a mark, done or dead. -/
def RContInv (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) : Prop :=
  (∀ a ∈ s.2.1, a ⊆ Ici (0 : ℝ)) ∧ 0 ≤ s.2.2.2.2.2.2.1 ∧ 0 ≤ s.2.2.2.2.2.2.2.2.1 ∧
    (s.2.2.2.2.2.1 = stThr (some true) ∨
      (s.2.2.2.2.2.1 = stThr none ∧
        leftLim b s.2.2.2.2.2.2.1 + s.2.2.2.2.2.2.2.1 * QuantumZipper.chiC κ < sleLambda κ) ∨
      s.2.2.2.2.2.1 = stArc true true ∨ s.2.2.2.2.2.1 = stDone ∨ s.2.2.2.2.2.1 = stDead)

/-- **An ordinary-piece instruction of the right walk preserves the invariant**, unless it ends at a new left
record. -/
theorem rContInv_flowStep {κ : ℝ} {b : ℝ → ℝ} {θ : ℝ} {s : ExplState} (hs : RFlowInv κ b θ s) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hno : (ExplState.flowStep κ b false s k D θ ⊤).2.2.2.2.2.1 ≠ stThr (some false)) :
    RContInv κ b (ExplState.flowStep κ b false s k D θ ⊤) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  obtain ⟨harcs, hp, hR, hst⟩ := hs
  simp only at harcs hp hR hst
  -- the launch case
  have hlaunch : st ≠ stTip → (leftLim b pt + θ * QuantumZipper.chiC κ < sleLambda κ) →
      (ExplState.launch (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) k D θ ⊤).2.2.2.2.2.1 ≠
        stThr (some false) →
      RContInv κ b (ExplState.launch (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) k D θ ⊤) := by
    intro htip hseed hno'
    obtain ⟨ha, hp', hR', hang, hcase⟩ := launch_top_right _ k D θ htip hp hR hno'
    have ha' : (ExplState.launch (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) k D θ ⊤).2.1 = arcs := ha
    refine ⟨fun a hmem => harcs a (by rw [ha'] at hmem; exact hmem), hp', hR', ?_⟩
    rcases hcase with h | ⟨h, hpt⟩ | h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨h, ?_⟩)
      rw [hpt, hang]
      exact hseed
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  rcases hst with ⟨rfl, hseed⟩ | rfl | rfl | rfl
  · exact hlaunch (by simp) hseed hno
  · simp only [ExplState.flowStep, Bool.false_eq_true, ↓reduceIte] at hno ⊢
    split_ifs at hno ⊢ with hadm
    · exact hlaunch (by simp) (by simpa [ExplState.heights] using hadm.1) hno
    · exact ⟨harcs, hp, hR, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨harcs, hp, hR, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · exact ⟨harcs, hp, hR, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

/-- The rightward move of a boundary continuation keeps the right-walk invariant. -/
theorem rFlowInv_moveRight {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (θ : ℝ)
    (pieces : List (Chart × (ℝ≥0 → ℝ) × ℝ≥0∞)) (arcs : List (Set ℝ)) (ret : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ × Bool)
    (lau : ℕ → Option (Chart × ℝ)) (chart : Chart) (st : ExplStatus) (pt ang rR rL : ℝ)
    (harcs : ∀ a ∈ arcs, a ⊆ Ici (0 : ℝ)) (hp : 0 ≤ pt) (hR : 0 ≤ rR) :
    RFlowInv κ b θ
      (let C := (jumpSet b jumps).filter
          (fun x => pt < x ∧ -sleLambda κ < rightLim b x + ang * QuantumZipper.chiC κ)
        if hC : C.Nonempty then
          ExplState.moveAlong (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) true (C.min' hC) true
        else ExplState.moveToEnd (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) true) := by
  dsimp only
  split_ifs with hC
  · have hx : pt < _ := (Finset.mem_filter.1 (Finset.min'_mem _ hC)).2.1
    simp only [ExplState.moveAlong, ↓reduceIte]
    refine ⟨fun a ha => ?_, hp.trans hx.le, le_max_of_le_left hR, Or.inr (Or.inl rfl)⟩
    rcases List.mem_append.1 ha with h | h
    · exact harcs a h
    · rw [List.mem_singleton.1 h]
      exact Icc_subset_Ici_self.trans (Ici_subset_Ici.2 hp)
  · simp only [ExplState.moveToEnd, ↓reduceIte]
    refine ⟨fun a ha => ?_, hp, hR, Or.inr (Or.inr (Or.inl rfl))⟩
    rcases List.mem_append.1 ha with h | h
    · exact harcs a h
    · rw [List.mem_singleton.1 h]
      exact Ici_subset_Ici.2 hp

/-- **A boundary-continuation instruction of the right walk restores the invariant before the next piece.** -/
theorem rFlowInv_contStep {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {s : ExplState} (hs : RContInv κ b s) (θ : ℝ) :
    RFlowInv κ b θ (ExplState.contStep κ b jumps s none true) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  obtain ⟨harcs, hp, hR, hst⟩ := hs
  simp only at harcs hp hR hst
  rcases hst with rfl | ⟨rfl, hseed⟩ | rfl | rfl | rfl
  · exact rFlowInv_moveRight θ pieces arcs ret lau chart _ pt ang rR rL harcs hp hR
  · have hn : ¬ sleLambda κ ≤ leftLim b pt + ang * QuantumZipper.chiC κ := not_le.2 hseed
    by_cases h2 : rightLim b pt + ang * QuantumZipper.chiC κ ≤ -sleLambda κ
    · simp only [ExplState.contStep, hn, h2, and_false, ↓reduceIte]
      exact rFlowInv_moveRight θ pieces arcs ret lau chart _ pt ang rR rL harcs hp hR
    · simp only [ExplState.contStep, hn, h2, and_false, ↓reduceIte]
      exact ⟨harcs, hp, hR, Or.inr (Or.inr (Or.inr rfl))⟩
  · simp only [ExplState.contStep]
    exact ⟨harcs, hp, hR, Or.inr (Or.inl rfl)⟩
  · simp only [ExplState.contStep]
    exact ⟨harcs, hp, hR, Or.inr (Or.inr (Or.inl rfl))⟩
  · simp only [ExplState.contStep]
    exact ⟨harcs, hp, hR, Or.inr (Or.inr (Or.inr rfl))⟩

/-! ### The invariants of the left walk -/

/-- **The left walk before an ordinary-piece instruction** (mirror of `RFlowInv`). -/
def LFlowInv (κ : ℝ) (b : ℝ → ℝ) (θ : ℝ) (s : ExplState) : Prop :=
  (∀ a ∈ s.2.1, a ⊆ Iic (0 : ℝ)) ∧ s.2.2.2.2.2.2.1 ≤ 0 ∧ s.2.2.2.2.2.2.2.2.2 ≤ 0 ∧
    ((s.2.2.2.2.2.1 = stRoot ∧ -sleLambda κ < rightLim b s.2.2.2.2.2.2.1 + θ * QuantumZipper.chiC κ) ∨
      s.2.2.2.2.2.1 = stArc false true ∨ s.2.2.2.2.2.1 = stDone ∨ s.2.2.2.2.2.1 = stDead)

/-- **The left walk before a boundary-continuation instruction** (mirror of `RContInv`). -/
def LContInv (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) : Prop :=
  (∀ a ∈ s.2.1, a ⊆ Iic (0 : ℝ)) ∧ s.2.2.2.2.2.2.1 ≤ 0 ∧ s.2.2.2.2.2.2.2.2.2 ≤ 0 ∧
    (s.2.2.2.2.2.1 = stThr (some false) ∨
      (s.2.2.2.2.2.1 = stThr none ∧
        -sleLambda κ < rightLim b s.2.2.2.2.2.2.1 + s.2.2.2.2.2.2.2.1 * QuantumZipper.chiC κ) ∨
      s.2.2.2.2.2.1 = stArc false true ∨ s.2.2.2.2.2.1 = stDone ∨ s.2.2.2.2.2.1 = stDead)

/-- **An ordinary-piece instruction of the left walk preserves the invariant**, unless it ends at a new right
record. -/
theorem lContInv_flowStep {κ : ℝ} {b : ℝ → ℝ} {θ : ℝ} {s : ExplState} (hs : LFlowInv κ b θ s) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hno : (ExplState.flowStep κ b false s k D θ ⊤).2.2.2.2.2.1 ≠ stThr (some true)) :
    LContInv κ b (ExplState.flowStep κ b false s k D θ ⊤) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  obtain ⟨harcs, hp, hL, hst⟩ := hs
  simp only at harcs hp hL hst
  have hlaunch : st ≠ stTip → (-sleLambda κ < rightLim b pt + θ * QuantumZipper.chiC κ) →
      (ExplState.launch (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) k D θ ⊤).2.2.2.2.2.1 ≠
        stThr (some true) →
      LContInv κ b (ExplState.launch (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) k D θ ⊤) := by
    intro htip hseed hno'
    obtain ⟨ha, hp', hL', hang, hcase⟩ := launch_top_left _ k D θ htip hp hL hno'
    have ha' : (ExplState.launch (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) k D θ ⊤).2.1 = arcs := ha
    refine ⟨fun a hmem => harcs a (by rw [ha'] at hmem; exact hmem), hp', hL', ?_⟩
    rcases hcase with h | ⟨h, hpt⟩ | h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨h, ?_⟩)
      rw [hpt, hang]
      exact hseed
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  rcases hst with ⟨rfl, hseed⟩ | rfl | rfl | rfl
  · exact hlaunch (by simp) hseed hno
  · simp only [ExplState.flowStep, Bool.false_eq_true, ↓reduceIte] at hno ⊢
    split_ifs at hno ⊢ with hadm
    · exact hlaunch (by simp) (by simpa [ExplState.heights] using hadm.2) hno
    · exact ⟨harcs, hp, hL, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨harcs, hp, hL, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · exact ⟨harcs, hp, hL, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

/-- The leftward move of a boundary continuation keeps the left-walk invariant. -/
theorem lFlowInv_moveLeft {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (θ : ℝ)
    (pieces : List (Chart × (ℝ≥0 → ℝ) × ℝ≥0∞)) (arcs : List (Set ℝ)) (ret : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ × Bool)
    (lau : ℕ → Option (Chart × ℝ)) (chart : Chart) (st : ExplStatus) (pt ang rR rL : ℝ)
    (harcs : ∀ a ∈ arcs, a ⊆ Iic (0 : ℝ)) (hp : pt ≤ 0) (hL : rL ≤ 0) :
    LFlowInv κ b θ
      (let C := (jumpSet b jumps).filter
          (fun x => x < pt ∧ leftLim b x + ang * QuantumZipper.chiC κ < sleLambda κ)
        if hC : C.Nonempty then
          ExplState.moveAlong (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) false (C.max' hC) true
        else ExplState.moveToEnd (pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL) false) := by
  dsimp only
  split_ifs with hC
  · have hx : _ < pt := (Finset.mem_filter.1 (Finset.max'_mem _ hC)).2.1
    simp only [ExplState.moveAlong, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun a ha => ?_, hx.le.trans hp, min_le_of_left_le hL, Or.inr (Or.inl rfl)⟩
    rcases List.mem_append.1 ha with h | h
    · exact harcs a h
    · rw [List.mem_singleton.1 h]
      exact Icc_subset_Iic_self.trans (Iic_subset_Iic.2 hp)
  · simp only [ExplState.moveToEnd, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun a ha => ?_, hp, hL, Or.inr (Or.inr (Or.inl rfl))⟩
    rcases List.mem_append.1 ha with h | h
    · exact harcs a h
    · rw [List.mem_singleton.1 h]
      exact Iic_subset_Iic.2 hp

/-- **A boundary-continuation instruction of the left walk restores the invariant before the next piece.** -/
theorem lFlowInv_contStep {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {s : ExplState} (hs : LContInv κ b s) (θ : ℝ) :
    LFlowInv κ b θ (ExplState.contStep κ b jumps s none false) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  obtain ⟨harcs, hp, hL, hst⟩ := hs
  simp only at harcs hp hL hst
  rcases hst with rfl | ⟨rfl, hseed⟩ | rfl | rfl | rfl
  · exact lFlowInv_moveLeft θ pieces arcs ret lau chart _ pt ang rR rL harcs hp hL
  · have hn : ¬ rightLim b pt + ang * QuantumZipper.chiC κ ≤ -sleLambda κ := not_le.2 hseed
    by_cases h3 : sleLambda κ ≤ leftLim b pt + ang * QuantumZipper.chiC κ
    · simp only [ExplState.contStep, hn, h3, false_and, ↓reduceIte]
      exact lFlowInv_moveLeft θ pieces arcs ret lau chart _ pt ang rR rL harcs hp hL
    · simp only [ExplState.contStep, hn, h3, false_and, ↓reduceIte]
      exact ⟨harcs, hp, hL, Or.inr (Or.inr (Or.inr rfl))⟩
  · simp only [ExplState.contStep]
    exact ⟨harcs, hp, hL, Or.inr (Or.inl rfl)⟩
  · simp only [ExplState.contStep]
    exact ⟨harcs, hp, hL, Or.inr (Or.inr (Or.inl rfl))⟩
  · simp only [ExplState.contStep]
    exact ⟨harcs, hp, hL, Or.inr (Or.inr (Or.inr rfl))⟩

/-! ### The runs of the two walks -/

/-- The run of a program before its first instruction is the initial state at its root. -/
theorem run_zero (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b jumps spec D 0 = ExplState.init spec.1 := rfl

/-- **The invariants along the right walk.** -/
theorem rInv_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ}
    (hroot : leftLim b 0 + θ * QuantumZipper.chiC κ < sleLambda κ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hno : ∀ k, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.2.2.1 ≠
      stThr (some false)) (k : ℕ) (hk : k ≤ (boundaryWalkSpec b jumps θ true).2.2.length) :
    (k % 2 = 0 → RFlowInv κ b θ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) ∧
      (k % 2 = 1 → RContInv κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) := by
  induction k with
  | zero =>
    refine ⟨fun _ => ?_, fun h => absurd h (by norm_num)⟩
    rw [run_zero]
    exact ⟨fun a ha => by simp [ExplState.init] at ha, le_rfl, le_rfl, Or.inl ⟨rfl, hroot⟩⟩
  | succ k ih =>
    have hk' : k < (boundaryWalkSpec b jumps θ true).2.2.length := hk
    obtain ⟨ih0, ih1⟩ := ih hk'.le
    have hrun := Exist.Staged.run_succ (κ := κ) (b := b) (jumps := jumps) (boundaryWalkSpec b jumps θ true) D k
    rw [getElem?_boundaryWalkSpec, ite_eq_left hk'] at hrun
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
    · rw [ite_eq_left h0] at hrun
      have hno' := hno k
      rw [hrun] at hno' ⊢
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      exact rContInv_flowStep (ih0 h0) k (D k) hno'
    · rw [ite_eq_right (by omega)] at hrun
      rw [hrun]
      refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
      exact rFlowInv_contStep (ih1 h1) θ

/-- **The connectors of the right walk lie in `[0, ∞)`** (deterministic): if the root seed bound holds for the
walk's angle and no instruction ends at a new left record, every connector recorded by the right walk lies in
`[0, ∞)`. -/
theorem arcs_subset_Ici_of_forall_ne {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ}
    (hroot : leftLim b 0 + θ * QuantumZipper.chiC κ < sleLambda κ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hno : ∀ k, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.2.2.1 ≠
      stThr (some false)) :
    ∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
      (boundaryWalkSpec b jumps θ true).2.2.length).2.1, a ⊆ Ici 0 := by
  obtain ⟨h0, h1⟩ := rInv_run hroot D hno _ le_rfl
  rcases Nat.mod_two_eq_zero_or_one (boundaryWalkSpec b jumps θ true).2.2.length with h | h
  · exact (h0 h).1
  · exact (h1 h).1

/-- **The invariants along the left walk.** -/
theorem lInv_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ}
    (hroot : -sleLambda κ < rightLim b 0 + θ * QuantumZipper.chiC κ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hno : ∀ k, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (k + 1)).2.2.2.2.2.1 ≠
      stThr (some true)) (k : ℕ) (hk : k ≤ (boundaryWalkSpec b jumps θ false).2.2.length) :
    (k % 2 = 0 → LFlowInv κ b θ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k)) ∧
      (k % 2 = 1 → LContInv κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k)) := by
  induction k with
  | zero =>
    refine ⟨fun _ => ?_, fun h => absurd h (by norm_num)⟩
    rw [run_zero]
    exact ⟨fun a ha => by simp [ExplState.init] at ha, le_rfl, le_rfl, Or.inl ⟨rfl, hroot⟩⟩
  | succ k ih =>
    have hk' : k < (boundaryWalkSpec b jumps θ false).2.2.length := hk
    obtain ⟨ih0, ih1⟩ := ih hk'.le
    have hrun := Exist.Staged.run_succ (κ := κ) (b := b) (jumps := jumps) (boundaryWalkSpec b jumps θ false) D k
    rw [getElem?_boundaryWalkSpec, ite_eq_left hk'] at hrun
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
    · rw [ite_eq_left h0] at hrun
      have hno' := hno k
      rw [hrun] at hno' ⊢
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      exact lContInv_flowStep (ih0 h0) k (D k) hno'
    · rw [ite_eq_right (by omega)] at hrun
      rw [hrun]
      refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
      exact lFlowInv_contStep (ih1 h1) θ

/-- **The connectors of the left walk lie in `(−∞, 0]`** (deterministic; mirror of `arcs_subset_Ici_of_forall_ne`). -/
theorem arcs_subset_Iic_of_forall_ne {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ}
    (hroot : -sleLambda κ < rightLim b 0 + θ * QuantumZipper.chiC κ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hno : ∀ k, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (k + 1)).2.2.2.2.2.1 ≠
      stThr (some true)) :
    ∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D
      (boundaryWalkSpec b jumps θ false).2.2.length).2.1, a ⊆ Iic 0 := by
  obtain ⟨h0, h1⟩ := lInv_run hroot D hno _ le_rfl
  rcases Nat.mod_two_eq_zero_or_one (boundaryWalkSpec b jumps θ false).2.2.length with h | h
  · exact (h0 h).1
  · exact (h1 h).1

end GW1Conn

end Theorem14

end InteractingSLE
