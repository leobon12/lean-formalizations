/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContPiece

/-!
# Lemma GW2a for every program: the connectors, deterministically and measurably

Packet PROVE-GW2AC. A boundary continuation (`ExplState.contStep`) appends at most one connector, a nondegenerate
closed interval `[pt, x]`, `[x, pt]` of the original real line, or a closed ray from the current point `pt`
(`ExplState.moveAlong`, `ExplState.moveToEnd`); an ordinary instruction appends none.

* `newArc`: the connector appended by a step; `arcAt_eq_newArc`, **`iUnion_arcs_run`**: the connectors of a run are
  those appended by its steps;
* **`arcAt_subset_closure_rat`**: every appended connector is the closure of its rational points;
* **`measurableSet_mem_arcAt`**: for measurable drivers regular at every sample, `{ω | y ∈ arcAt k ω}` is measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2aCont

open Exist.Staged Exist.StagedLaw PiecewiseConstantBoundaryData

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### The connector appended by one step -/

/-- The connectors appended when passing from the state `s` to the state `s'`. -/
def newArc (s s' : ExplState) : Set ℝ := ⋃ a ∈ s'.2.1.drop s.2.1.length, a

theorem arcAt_eq_newArc (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    arcAt κ b jumps spec D k = newArc (ExplState.run κ b jumps spec D k) (ExplState.run κ b jumps spec D (k + 1)) :=
  rfl

theorem newArc_of_arcs_eq {s s' : ExplState} (h : s'.2.1 = s.2.1) : newArc s s' = ∅ := by
  simp [newArc, h]

theorem newArc_of_arcs_eq_append {s s' : ExplState} {a : Set ℝ} (h : s'.2.1 = s.2.1 ++ [a]) : newArc s s' = a := by
  simp [newArc, h]

theorem newArc_moveAlong (s : ExplState) (right : Bool) (x : ℝ) (atMark : Bool) :
    newArc s (ExplState.moveAlong s right x atMark) = if right then Icc (stPt s) x else Icc x (stPt s) :=
  newArc_of_arcs_eq_append rfl

theorem newArc_moveToEnd (s : ExplState) (right : Bool) :
    newArc s (ExplState.moveToEnd s right) = if right then Ici (stPt s) else Iic (stPt s) :=
  newArc_of_arcs_eq_append rfl

theorem arcs_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k D θ t).2.1 = s.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  repeat' first
    | rfl
    | split

theorem arcs_flowStep (gw2 : Bool) (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.flowStep κ b gw2 s k D θ t).2.1 = s.2.1 := by
  rcases flowStep_trichotomy (κ := κ) (b := b) gw2 s k D θ t with e | e | e <;> rw [e]
  · rfl
  · exact arcs_launch s k D θ t

/-- A boundary continuation appends at most one connector. -/
theorem arcs_contStep_cases (s : ExplState) (vStop : Option ℝ) (pref : Bool) :
    (ExplState.contStep κ b jumps s vStop pref).2.1 = s.2.1 ∨
      ∃ a : Set ℝ, (ExplState.contStep κ b jumps s vStop pref).2.1 = s.2.1 ++ [a] := by
  rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s vStop pref with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩ <;>
    rw [e]
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

/-- **The connectors of the run only grow**, by at most one connector per step. -/
theorem arcs_run_succ (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    (ExplState.run κ b jumps spec D (k + 1)).2.1 = (ExplState.run κ b jumps spec D k).2.1 ∨
      ∃ a : Set ℝ, (ExplState.run κ b jumps spec D (k + 1)).2.1 = (ExplState.run κ b jumps spec D k).2.1 ++ [a] := by
  rw [run_succ]
  cases spec.2.2[k]? with
  | none => exact Or.inl rfl
  | some ins =>
    simp only
    rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
    · exact Or.inl (arcs_flowStep (κ := κ) (b := b) spec.2.1 _ k (D k) θ t)
    · exact arcs_contStep_cases _ none pref
    · exact arcs_contStep_cases _ (some v) pref

theorem arcAt_of_arcs_eq {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (h : (ExplState.run κ b jumps spec D (k + 1)).2.1 = (ExplState.run κ b jumps spec D k).2.1) :
    arcAt κ b jumps spec D k = ∅ :=
  newArc_of_arcs_eq h

/-- **The connectors of a run are those appended by its steps.** -/
theorem iUnion_arcs_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    (⋃ a ∈ (ExplState.run κ b jumps spec D n).2.1, a) = ⋃ k ∈ Finset.range n, arcAt κ b jumps spec D k := by
  induction n with
  | zero => simp [ExplState.run, ExplState.init]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, ← ih, union_comm]
    rcases arcs_run_succ (κ := κ) (b := b) (jumps := jumps) spec D n with e | ⟨a, e⟩
    · rw [e, arcAt_of_arcs_eq e, union_empty]
    · rw [arcAt_eq_newArc, newArc_of_arcs_eq_append e, e]
      simp only [List.mem_append, List.mem_singleton, iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left]

/-! ### Every connector is the closure of its rational points -/

/-- The closure of the rational points of a set. -/
theorem subset_closure_rat_of_subset_closure_open {A U : Set ℝ} (hU : IsOpen U) (hUA : U ⊆ A)
    (hA : A ⊆ closure U) : A ⊆ closure (A ∩ range ((↑) : ℚ → ℝ)) := by
  have h1 : U ⊆ closure (U ∩ range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast.open_subset_closure_inter hU
  calc A ⊆ closure U := hA
    _ ⊆ closure (closure (U ∩ range ((↑) : ℚ → ℝ))) := closure_mono h1
    _ = closure (U ∩ range ((↑) : ℚ → ℝ)) := closure_closure
    _ ⊆ closure (A ∩ range ((↑) : ℚ → ℝ)) := closure_mono (inter_subset_inter_left _ hUA)

theorem Icc_subset_closure_rat {a c : ℝ} (h : a < c) : Icc a c ⊆ closure (Icc a c ∩ range ((↑) : ℚ → ℝ)) :=
  subset_closure_rat_of_subset_closure_open isOpen_Ioo Ioo_subset_Icc_self (closure_Ioo h.ne).symm.subset

theorem Ici_subset_closure_rat (a : ℝ) : Ici a ⊆ closure (Ici a ∩ range ((↑) : ℚ → ℝ)) :=
  subset_closure_rat_of_subset_closure_open isOpen_Ioi Ioi_subset_Ici_self (closure_Ioi a).symm.subset

theorem Iic_subset_closure_rat (a : ℝ) : Iic a ⊆ closure (Iic a ∩ range ((↑) : ℚ → ℝ)) :=
  subset_closure_rat_of_subset_closure_open isOpen_Iio Iio_subset_Iic_self (closure_Iio a).symm.subset

/-- The property "the closure of its rational points". -/
def IsRatClosed (A : Set ℝ) : Prop := A ⊆ closure (A ∩ range ((↑) : ℚ → ℝ))

theorem isRatClosed_empty : IsRatClosed ∅ := empty_subset _

theorem isRatClosed_moveAlong (s : ExplState) (right : Bool) (x : ℝ) (atMark : Bool)
    (h : if right then stPt s < x else x < stPt s) : IsRatClosed (newArc s (ExplState.moveAlong s right x atMark)) := by
  rw [newArc_moveAlong]
  cases right
  · exact Icc_subset_closure_rat h
  · exact Icc_subset_closure_rat h

theorem isRatClosed_moveToEnd (s : ExplState) (right : Bool) :
    IsRatClosed (newArc s (ExplState.moveToEnd s right)) := by
  rw [newArc_moveToEnd]
  cases right
  · exact Iic_subset_closure_rat _
  · exact Ici_subset_closure_rat _

open Classical in
theorem isRatClosed_contBranch (s : ExplState) (vStop : Option ℝ) (right : Bool) :
    IsRatClosed (newArc s (contBranch κ b jumps s vStop right)) := by
  unfold contBranch
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with hC
    · cases vStop with
      | none =>
        exact isRatClosed_moveAlong _ _ _ _ (Finset.mem_filter.1 (Finset.max'_mem _ hC)).2.1
      | some v =>
        simp only
        split_ifs with hv
        · exact isRatClosed_moveAlong _ _ _ _ hv.2
        · exact isRatClosed_moveAlong _ _ _ _ (Finset.mem_filter.1 (Finset.max'_mem _ hC)).2.1
    · cases vStop with
      | none => exact isRatClosed_moveToEnd _ _
      | some v =>
        simp only
        split_ifs with hv
        · exact isRatClosed_moveAlong _ _ _ _ hv
        · exact isRatClosed_moveToEnd _ _
  · simp only [↓reduceIte]
    split_ifs with hC
    · cases vStop with
      | none =>
        exact isRatClosed_moveAlong _ _ _ _ (Finset.mem_filter.1 (Finset.min'_mem _ hC)).2.1
      | some v =>
        simp only
        split_ifs with hv
        · exact isRatClosed_moveAlong _ _ _ _ hv.1
        · exact isRatClosed_moveAlong _ _ _ _ (Finset.mem_filter.1 (Finset.min'_mem _ hC)).2.1
    · cases vStop with
      | none => exact isRatClosed_moveToEnd _ _
      | some v =>
        simp only
        split_ifs with hv
        · exact isRatClosed_moveAlong _ _ _ _ hv
        · exact isRatClosed_moveToEnd _ _

theorem isRatClosed_contStep (s : ExplState) (vStop : Option ℝ) (pref : Bool) :
    IsRatClosed (newArc s (ExplState.contStep κ b jumps s vStop pref)) := by
  rw [contStep_eq_byStatus]
  have hD : IsRatClosed (newArc s (setDead s)) := by
    rw [newArc_of_arcs_eq (s := s) (s' := setDead s) rfl]; exact isRatClosed_empty
  have hS : IsRatClosed (newArc s s) := by
    rw [newArc_of_arcs_eq (s := s) (s' := s) rfl]; exact isRatClosed_empty
  rcases stStatus s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | ⟨_ | _⟩) | ⟨_ | _, _ | _⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact hD
  · exact hD
  · show IsRatClosed (newArc s (match contDirNone κ b pref s with
      | none => setDead s
      | some true => contBranch κ b jumps s vStop true
      | some false => contBranch κ b jumps s vStop false))
    rcases contDirNone κ b pref s with _ | _ | _
    · exact hD
    · exact isRatClosed_contBranch _ _ _
    · exact isRatClosed_contBranch _ _ _
  · exact isRatClosed_contBranch s vStop false
  · exact isRatClosed_contBranch s vStop true
  · exact isRatClosed_contBranch s vStop false
  · exact hS
  · exact isRatClosed_contBranch s vStop true
  · exact hS
  · exact hS
  · exact hD

/-- **Every connector appended by a step is the closure of its rational points.** -/
theorem arcAt_subset_closure_rat (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    IsRatClosed (arcAt κ b jumps spec D k) := by
  rw [arcAt_eq_newArc, run_succ]
  cases spec.2.2[k]? with
  | none =>
    rw [newArc_of_arcs_eq (s := ExplState.run κ b jumps spec D k) (s' := ExplState.run κ b jumps spec D k) rfl]
    exact isRatClosed_empty
  | some ins =>
    simp only
    rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
    · change IsRatClosed (newArc (ExplState.run κ b jumps spec D k)
        (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t))
      rw [newArc_of_arcs_eq (arcs_flowStep (κ := κ) (b := b) spec.2.1 _ k (D k) θ t)]
      exact isRatClosed_empty
    · exact isRatClosed_contStep _ _ _
    · exact isRatClosed_contStep _ _ _

/-! ### Measurability of the appended connectors -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {S : Ω → ExplState}

theorem measurableSet_newArc_of_cases {S' S₁ S₂ : Ω → ExplState} {A : Set Ω} {y : ℝ} (hA : MeasurableSet A)
    (h₁ : MeasurableSet {ω | y ∈ newArc (S ω) (S₁ ω)}) (h₂ : MeasurableSet {ω | y ∈ newArc (S ω) (S₂ ω)})
    (e₁ : ∀ ω ∈ A, S' ω = S₁ ω) (e₂ : ∀ ω ∉ A, S' ω = S₂ ω) :
    MeasurableSet {ω | y ∈ newArc (S ω) (S' ω)} := by
  have e : {ω | y ∈ newArc (S ω) (S' ω)} =
      (A ∩ {ω | y ∈ newArc (S ω) (S₁ ω)}) ∪ (Aᶜ ∩ {ω | y ∈ newArc (S ω) (S₂ ω)}) := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [hω, e₁ ω hω]
    · simp [hω, e₂ ω hω]
  rw [e]
  exact (hA.inter h₁).union (hA.compl.inter h₂)

theorem measurableSet_newArc_moveAlong (hpt : Measurable fun ω => stPt (S ω)) {x : Ω → ℝ} (hx : Measurable x)
    (right atMark : Bool) (y : ℝ) :
    MeasurableSet {ω | y ∈ newArc (S ω) (ExplState.moveAlong (S ω) right (x ω) atMark)} := by
  simp_rw [newArc_moveAlong]
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc]
    exact (measurableSet_le hx measurable_const).inter (measurableSet_le measurable_const hpt)
  · simp only [↓reduceIte, mem_Icc]
    exact (measurableSet_le hpt measurable_const).inter (measurableSet_le measurable_const hx)

theorem measurableSet_newArc_moveToEnd (hpt : Measurable fun ω => stPt (S ω)) (right : Bool) (y : ℝ) :
    MeasurableSet {ω | y ∈ newArc (S ω) (ExplState.moveToEnd (S ω) right)} := by
  simp_rw [newArc_moveToEnd]
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte, mem_Iic]
    exact measurableSet_le measurable_const hpt
  · simp only [↓reduceIte, mem_Ici]
    exact measurableSet_le hpt measurable_const

theorem measurableSet_newArc_empty {S' : Ω → ExplState} (h : ∀ ω, (S' ω).2.1 = (S ω).2.1) (y : ℝ) :
    MeasurableSet {ω | y ∈ newArc (S ω) (S' ω)} := by
  have e : {ω | y ∈ newArc (S ω) (S' ω)} = ∅ := by
    ext ω
    simp [newArc_of_arcs_eq (h ω)]
  rw [e]
  exact MeasurableSet.empty

open Classical in
/-- **The connector of a continuation in a fixed direction has measurable fibres.** -/
theorem measurableSet_newArc_contBranch (hS : IsMeasState S) (vStop : Option ℝ) (right : Bool) (y : ℝ) :
    MeasurableSet {ω | y ∈ newArc (S ω) (contBranch κ b jumps (S ω) vStop right)} := by
  have hpt := hS.2.1
  have hang := hS.2.2.1
  cases right
  · -- to the left
    have hP : ∀ x, MeasurableSet {ω | x < stPt (S ω) ∧
        leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ} := fun x =>
      (measurableSet_lt measurable_const hpt).inter
        (measurableSet_lt (measurable_const.add (hang.mul_const _)) measurable_const)
    have hne := measurableSet_filter_nonempty (jumpSet b jumps) hP
    have hxm := measurableSet_filter_max'_eq (jumpSet b jumps) hP
    have hxmF := fun ω => filter_max'_mem (jumpSet b jumps) (fun x => x < stPt (S ω) ∧
        leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ)
    have hxmm := measurable_finite_choice (insert 0 (jumpSet b jumps)) hxmF hxm (g := fun c _ => c)
      fun _ => measurable_const
    have hA := measurableSet_newArc_moveAlong hpt hxmm false true y
    have hE := measurableSet_newArc_moveToEnd hpt (S := S) false y
    cases vStop with
    | none =>
      refine measurableSet_newArc_of_cases hne hA hE (fun ω hω => ?_) (fun ω hω => ?_)
      · simp only [mem_ofPred_eq] at hω
        simp only [contBranch, Bool.false_eq_true, ↓reduceIte, hω, ↓reduceDIte]
      · simp only [mem_ofPred_eq] at hω
        simp only [contBranch, Bool.false_eq_true, ↓reduceIte, hω, ↓reduceDIte]
    | some v =>
      have hV := measurableSet_newArc_moveAlong hpt (S := S) (x := fun _ => v) measurable_const false false y
      refine measurableSet_newArc_of_cases hne (measurableSet_newArc_of_cases (S' := fun ω =>
          if (if h : ((jumpSet b jumps).filter (fun x => x < stPt (S ω) ∧
              leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ)).Nonempty then
            ((jumpSet b jumps).filter (fun x => x < stPt (S ω) ∧
              leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ)).max' h else 0) < v ∧ v < stPt (S ω)
          then ExplState.moveAlong (S ω) false v false
          else ExplState.moveAlong (S ω) false (if h : ((jumpSet b jumps).filter (fun x => x < stPt (S ω) ∧
              leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ)).Nonempty then
            ((jumpSet b jumps).filter (fun x => x < stPt (S ω) ∧
              leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ)).max' h else 0) true)
        ((measurableSet_lt hxmm measurable_const).inter (measurableSet_lt measurable_const hpt)) hV hA
          (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω))
        (measurableSet_newArc_of_cases (S' := fun ω => if v < stPt (S ω) then ExplState.moveAlong (S ω) false v false
          else ExplState.moveToEnd (S ω) false) (measurableSet_lt measurable_const hpt) hV hE
          (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω))
        (fun ω hω => ?_) (fun ω hω => ?_)
      · simp only [mem_ofPred_eq] at hω
        simp only [contBranch, Bool.false_eq_true, ↓reduceIte, hω, ↓reduceDIte]
      · simp only [mem_ofPred_eq] at hω
        simp only [contBranch, Bool.false_eq_true, ↓reduceIte, hω, ↓reduceDIte]
  · -- to the right
    have hP : ∀ x, MeasurableSet {ω | stPt (S ω) < x ∧
        -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ} := fun x =>
      (measurableSet_lt hpt measurable_const).inter
        (measurableSet_lt measurable_const (measurable_const.add (hang.mul_const _)))
    have hne := measurableSet_filter_nonempty (jumpSet b jumps) hP
    have hxm := measurableSet_filter_min'_eq (jumpSet b jumps) hP
    have hxmF := fun ω => filter_min'_mem (jumpSet b jumps) (fun x => stPt (S ω) < x ∧
        -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ)
    have hxmm := measurable_finite_choice (insert 0 (jumpSet b jumps)) hxmF hxm (g := fun c _ => c)
      fun _ => measurable_const
    have hA := measurableSet_newArc_moveAlong hpt hxmm true true y
    have hE := measurableSet_newArc_moveToEnd hpt (S := S) true y
    cases vStop with
    | none =>
      refine measurableSet_newArc_of_cases hne hA hE (fun ω hω => ?_) (fun ω hω => ?_)
      · simp only [mem_ofPred_eq] at hω
        simp only [contBranch, ↓reduceIte, hω, ↓reduceDIte]
      · simp only [mem_ofPred_eq] at hω
        simp only [contBranch, ↓reduceIte, hω, ↓reduceDIte]
    | some v =>
      have hV := measurableSet_newArc_moveAlong hpt (S := S) (x := fun _ => v) measurable_const true false y
      refine measurableSet_newArc_of_cases hne (measurableSet_newArc_of_cases (S' := fun ω =>
          if stPt (S ω) < v ∧ v < (if h : ((jumpSet b jumps).filter (fun x => stPt (S ω) < x ∧
              -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ)).Nonempty then
            ((jumpSet b jumps).filter (fun x => stPt (S ω) < x ∧
              -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ)).min' h else 0)
          then ExplState.moveAlong (S ω) true v false
          else ExplState.moveAlong (S ω) true (if h : ((jumpSet b jumps).filter (fun x => stPt (S ω) < x ∧
              -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ)).Nonempty then
            ((jumpSet b jumps).filter (fun x => stPt (S ω) < x ∧
              -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ)).min' h else 0) true)
        ((measurableSet_lt hpt measurable_const).inter (measurableSet_lt measurable_const hxmm)) hV hA
          (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω))
        (measurableSet_newArc_of_cases (S' := fun ω => if stPt (S ω) < v then ExplState.moveAlong (S ω) true v false
          else ExplState.moveToEnd (S ω) true) (measurableSet_lt hpt measurable_const) hV hE
          (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω))
        (fun ω hω => ?_) (fun ω hω => ?_)
      · simp only [mem_ofPred_eq] at hω
        simp only [contBranch, ↓reduceIte, hω, ↓reduceDIte]
      · simp only [mem_ofPred_eq] at hω
        simp only [contBranch, ↓reduceIte, hω, ↓reduceDIte]

/-- **The connector of a boundary continuation of a measurable random state has measurable fibres.** -/
theorem measurableSet_newArc_contStep (hS : IsMeasState S) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (vStop : Option ℝ) (pref : Bool) (y : ℝ) :
    MeasurableSet {ω | y ∈ newArc (S ω) (ExplState.contStep κ b jumps (S ω) vStop pref)} := by
  classical
  have hR := (measurable_rightLim_of_pcbd hb).comp hS.2.1
  have hL := (measurable_leftLim_of_pcbd hb).comp hS.2.1
  have hang := hS.2.2.1
  have hBr : ∀ r, MeasurableSet {ω | y ∈ newArc (S ω) (contBranch κ b jumps (S ω) vStop r)} := fun r =>
    measurableSet_newArc_contBranch hS vStop r y
  have hDd : MeasurableSet {ω | y ∈ newArc (S ω) (setDead (S ω))} := measurableSet_newArc_empty (fun _ => rfl) y
  have hSs : MeasurableSet {ω | y ∈ newArc (S ω) (S ω)} := measurableSet_newArc_empty (fun _ => rfl) y
  have hc1 : MeasurableSet {ω | rightLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ ≤ -sleLambda κ ∧
      sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ} :=
    (measurableSet_le (hR.add (hang.mul_const _)) measurable_const).inter
      (measurableSet_le measurable_const (hL.add (hang.mul_const _)))
  have hc2 : MeasurableSet {ω | rightLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ ≤ -sleLambda κ} :=
    measurableSet_le (hR.add (hang.mul_const _)) measurable_const
  have hc3 : MeasurableSet {ω | sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ} :=
    measurableSet_le measurable_const (hL.add (hang.mul_const _))
  have hnone : MeasurableSet {ω | y ∈ newArc (S ω) (match contDirNone κ b pref (S ω) with
      | none => setDead (S ω)
      | some true => contBranch κ b jumps (S ω) vStop true
      | some false => contBranch κ b jumps (S ω) vStop false)} := by
    have h3 := measurableSet_newArc_of_cases (S := S) (S' := fun ω =>
      if sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ then
        contBranch κ b jumps (S ω) vStop false else setDead (S ω))
      hc3 (hBr false) hDd (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω)
    have h2 := measurableSet_newArc_of_cases (S := S) (S' := fun ω =>
      if rightLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ ≤ -sleLambda κ then
        contBranch κ b jumps (S ω) vStop true
      else if sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ then
        contBranch κ b jumps (S ω) vStop false else setDead (S ω))
      hc2 (hBr true) h3 (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω)
    refine measurableSet_newArc_of_cases hc1 (hBr pref) h2 (fun ω hω => ?_) (fun ω hω => ?_)
    · have h1 : rightLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ ≤ -sleLambda κ ∧
          sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ := hω
      simp only [contDirNone, h1, and_self, ↓reduceIte]
      cases pref <;> rfl
    · have h1 : ¬ (rightLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ ≤ -sleLambda κ ∧
          sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ) := hω
      simp only [contDirNone, h1, ↓reduceIte]
      by_cases h2 : rightLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ ≤ -sleLambda κ
      · simp only [h2, ↓reduceIte]
      · simp only [h2, ↓reduceIte]
        by_cases h3 : sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ
        · simp only [h3, ↓reduceIte]
        · simp only [h3, ↓reduceIte]
  have hcases : ∀ st : ExplStatus,
      MeasurableSet {ω | y ∈ newArc (S ω) (contByStatus κ b jumps st (S ω) vStop pref)} := fun st => by
    rcases st with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | ⟨_ | _⟩) | ⟨_ | _, _ | _⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · exact hDd
    · exact hDd
    · exact hnone
    · exact hBr false
    · exact hBr true
    · exact hBr false
    · exact hSs
    · exact hBr true
    · exact hSs
    · exact hSs
    · exact hDd
  have e : {ω | y ∈ newArc (S ω) (ExplState.contStep κ b jumps (S ω) vStop pref)} =
      ⋃ st : ExplStatus, {ω | stStatus (S ω) = st} ∩
        {ω | y ∈ newArc (S ω) (contByStatus κ b jumps st (S ω) vStop pref)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, contStep_eq_byStatus]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨st, hst, h⟩ => hst ▸ h⟩
  rw [e]
  exact MeasurableSet.iUnion fun st => (hS.1 st).inter (hcases st)

/-- **The connector appended by instruction `k` has measurable fibres** (measurable drivers regular at every
sample). -/
theorem measurableSet_mem_arcAt (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (k : ℕ) (y : ℝ) : MeasurableSet {ω | y ∈ arcAt κ b jumps spec (fun j => E j ω) k} := by
  have hS := isMeasState_run (κ := κ) hb spec hEm hreg k
  simp_rw [arcAt_eq_newArc, run_succ]
  cases hk : spec.2.2[k]? with
  | none => exact measurableSet_newArc_empty (fun _ => rfl) y
  | some ins =>
    simp only
    rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
    · exact measurableSet_newArc_empty (fun ω => arcs_flowStep (κ := κ) (b := b) spec.2.1 _ k (E k ω) θ t) y
    · exact measurableSet_newArc_contStep hS hb none pref y
    · exact measurableSet_newArc_contStep hS hb (some v) pref y

end Meas

end GW2aCont

end Theorem14

end InteractingSLE
