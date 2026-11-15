/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw2Launch

/-!
# The run of a staged history is Borel: `RunMeasStatement`

Packet PROVE-STAGEDLAW2. The steps of `ExplState.run` are flow steps (`ExplState.flowStep`: a launch, a death, or
nothing, decided by the status and the seed admissibility at the current heights) and boundary continuations
(`ExplState.contStep`: by the status and a direction read from the heights, a move along the boundary to the first
admissible original jump, to a chosen point, or to the target). Every step maps measurable random states to measurable
random states (`IsMeasState.flowStep`, `IsMeasState.contStep`), so every state of the run is measurable
(`isMeasState_run`), which gives the named input **`runMeasStatement`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged PiecewiseConstantBoundaryData

/-! ### Heights and admissibility -/

/-- The heights of a state, by status (`ExplState.heights`). -/
def heightsOf (κ : ℝ) (b : ℝ → ℝ) (st : ExplStatus) (pt angle : ℝ) : ℝ × ℝ :=
  match st with
  | .inr (.inr (.inl (some true))) => (-sleLambda κ - angle * QuantumZipper.chiC κ, rightLim b pt)
  | .inr (.inr (.inl (some false))) => (leftLim b pt, sleLambda κ - angle * QuantumZipper.chiC κ)
  | _ => (leftLim b pt, rightLim b pt)

theorem heights_eq (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) :
    ExplState.heights κ b s = heightsOf κ b (stStatus s) (stPt s) (stAngle s) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {S : Ω → ExplState} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem measurable_heights (hS : IsMeasState S) (hb : IsPiecewiseConstantBoundaryData b jumps) :
    Measurable fun ω => ExplState.heights κ b (S ω) := by
  simp_rw [heights_eq]
  have hL := measurable_leftLim_of_pcbd hb
  have hR := measurable_rightLim_of_pcbd hb
  refine measurable_status_cases hS.1 (g := fun st ω => heightsOf κ b st (stPt (S ω)) (stAngle (S ω))) fun st => ?_
  rcases st with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | ⟨_ | _⟩) | ⟨_, _⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
    simp only [heightsOf] <;>
    first
    | exact (hL.comp hS.2.1).prodMk (hR.comp hS.2.1)
    | exact (hL.comp hS.2.1).prodMk (measurable_const.sub (hS.2.2.1.mul_const _))
    | exact ((measurable_const.sub (hS.2.2.1.mul_const _))).prodMk (hR.comp hS.2.1)

theorem measurableSet_admissible (hS : IsMeasState S) (hb : IsPiecewiseConstantBoundaryData b jumps) (θ : ℝ) :
    MeasurableSet {ω | ExplState.IsAdmissibleSeed κ (ExplState.heights κ b (S ω)).1
      (ExplState.heights κ b (S ω)).2 θ} := by
  have h := measurable_heights (κ := κ) hS hb
  exact (measurableSet_lt (h.fst.add_const _) measurable_const).inter
    (measurableSet_lt measurable_const (h.snd.add_const _))

end Meas

/-! ### Flow steps -/

open Classical in
/-- A flow step, by status (`ExplState.flowStep`). -/
def flowByStatus (κ : ℝ) (b : ℝ → ℝ) (gw2 : Bool) (st : ExplStatus) (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) : ExplState :=
  match st with
  | .inl () => ExplState.launch s k D θ t
  | .inr (.inl ()) => ExplState.launch s k D θ t
  | .inr (.inr (.inr (.inr (.inl ())))) => s
  | .inr (.inr (.inr (.inr (.inr ())))) => s
  | _ => if gw2 then setDead s
      else if ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ then
        ExplState.launch s k D θ t
      else s

theorem flowStep_eq_byStatus (κ : ℝ) (b : ℝ → ℝ) (gw2 : Bool) (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (θ : ℝ) (t : ℝ≥0∞) : ExplState.flowStep κ b gw2 s k D θ t = flowByStatus κ b gw2 (stStatus s) s k D θ t := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | p | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl

section FlowMeas

variable {Ω : Type*} [MeasurableSpace Ω] {S : Ω → ExplState} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **A flow step of a measurable random state with a measurable regular driver is measurable.** -/
theorem IsMeasState.flowStep (hS : IsMeasState S) (hb : IsPiecewiseConstantBoundaryData b jumps) (gw2 : Bool)
    (k : ℕ) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : Measurable D) (hreg : ∀ ω, IsRegularDriver (D ω)) (θ : ℝ)
    (t : ℝ≥0∞) : IsMeasState fun ω => ExplState.flowStep κ b gw2 (S ω) k (D ω) θ t := by
  classical
  have hL := hS.launch hD hreg k θ t
  have hother : IsMeasState fun ω => if gw2 then StagedLaw.setDead (S ω)
      else if ExplState.IsAdmissibleSeed κ (ExplState.heights κ b (S ω)).1 (ExplState.heights κ b (S ω)).2 θ then
        ExplState.launch (S ω) k (D ω) θ t
      else S ω := by
    cases gw2
    · refine IsMeasState.of_cases hL hS (measurableSet_admissible (κ := κ) hS hb θ) (fun ω hω => ?_) (fun ω hω => ?_)
      · have h' : ExplState.IsAdmissibleSeed κ (ExplState.heights κ b (S ω)).1 (ExplState.heights κ b (S ω)).2 θ :=
          hω
        simp only [Bool.false_eq_true, ↓reduceIte, h']
      · have h' : ¬ ExplState.IsAdmissibleSeed κ (ExplState.heights κ b (S ω)).1 (ExplState.heights κ b (S ω)).2
            θ := hω
        simp only [Bool.false_eq_true, ↓reduceIte, h']
    · exact hS.setDead
  refine IsMeasState.of_status_cases hS.1 (T := fun st ω => flowByStatus κ b gw2 st (S ω) k (D ω) θ t)
    (fun st => ?_) fun ω => flowStep_eq_byStatus κ b gw2 (S ω) k (D ω) θ t
  rcases st with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | p | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact hL
  · exact hL
  · exact hother
  · exact hother
  · exact hS
  · exact hS

end FlowMeas


/-! ### Boundary continuations -/

theorem min'_eq_iff {C : Finset ℝ} (h : C.Nonempty) (c : ℝ) : C.min' h = c ↔ c ∈ C ∧ ∀ x ∈ C, c ≤ x := by
  constructor
  · rintro rfl; exact ⟨C.min'_mem h, fun x hx => C.min'_le x hx⟩
  · rintro ⟨hc, hle⟩; exact le_antisymm (C.min'_le c hc) (C.le_min' h c hle)

theorem max'_eq_iff {C : Finset ℝ} (h : C.Nonempty) (c : ℝ) : C.max' h = c ↔ c ∈ C ∧ ∀ x ∈ C, x ≤ c := by
  constructor
  · rintro rfl; exact ⟨C.max'_mem h, fun x hx => C.le_max' x hx⟩
  · rintro ⟨hc, hle⟩; exact le_antisymm (C.max'_le h c hle) (C.le_max' c hc)

section Finset

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurableSet_filter_nonempty (J : Finset ℝ) {P : Ω → ℝ → Prop} [∀ ω, DecidablePred (P ω)]
    (hP : ∀ x, MeasurableSet {ω | P ω x}) : MeasurableSet {ω | (J.filter (P ω)).Nonempty} := by
  have e : {ω | (J.filter (P ω)).Nonempty} = ⋃ x ∈ J, {ω | P ω x} := by
    ext ω; simp [Finset.filter_nonempty_iff]
  rw [e]
  exact MeasurableSet.biUnion J.countable_toSet fun x _ => hP x

/-- The minimum (`0` if empty) of a measurable random subset of a fixed finite set has measurable fibres. -/
theorem measurableSet_filter_min'_eq (J : Finset ℝ) {P : Ω → ℝ → Prop} [∀ ω, DecidablePred (P ω)]
    (hP : ∀ x, MeasurableSet {ω | P ω x}) (c : ℝ) :
    MeasurableSet {ω | (if h : (J.filter (P ω)).Nonempty then (J.filter (P ω)).min' h else 0) = c} := by
  have hne := measurableSet_filter_nonempty J hP
  have e : {ω | (if h : (J.filter (P ω)).Nonempty then (J.filter (P ω)).min' h else 0) = c} =
      ({ω | (J.filter (P ω)).Nonempty} ∩ ({ω | c ∈ J ∧ P ω c} ∩ ⋂ x ∈ J, {ω | P ω x → c ≤ x})) ∪
        ({ω | (J.filter (P ω)).Nonempty}ᶜ ∩ {_ω | (0 : ℝ) = c}) := by
    ext ω
    by_cases h : (J.filter (P ω)).Nonempty
    · simp only [h, ↓reduceDIte, mem_ofPred_eq, min'_eq_iff, Finset.mem_filter, mem_union, mem_inter_iff,
        mem_iInter, mem_compl_iff, not_true_eq_false, false_and, or_false, true_and]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2⟩, fun x hx hPx => h3 x ⟨hx, hPx⟩⟩,
        fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2⟩, fun x hx => h3 x hx.1 hx.2⟩⟩
    · simp [h]
  rw [e]
  refine (hne.inter (((MeasurableSet.const _).inter (hP c)).inter (MeasurableSet.biInter J.countable_toSet
    fun x _ => ?_))).union (hne.compl.inter (MeasurableSet.const _))
  have : {ω | P ω x → c ≤ x} = {ω | P ω x}ᶜ ∪ {_ω | c ≤ x} := by ext ω; simp [imp_iff_not_or]
  rw [this]; exact (hP x).compl.union (MeasurableSet.const _)

theorem measurableSet_filter_max'_eq (J : Finset ℝ) {P : Ω → ℝ → Prop} [∀ ω, DecidablePred (P ω)]
    (hP : ∀ x, MeasurableSet {ω | P ω x}) (c : ℝ) :
    MeasurableSet {ω | (if h : (J.filter (P ω)).Nonempty then (J.filter (P ω)).max' h else 0) = c} := by
  have hne := measurableSet_filter_nonempty J hP
  have e : {ω | (if h : (J.filter (P ω)).Nonempty then (J.filter (P ω)).max' h else 0) = c} =
      ({ω | (J.filter (P ω)).Nonempty} ∩ ({ω | c ∈ J ∧ P ω c} ∩ ⋂ x ∈ J, {ω | P ω x → x ≤ c})) ∪
        ({ω | (J.filter (P ω)).Nonempty}ᶜ ∩ {_ω | (0 : ℝ) = c}) := by
    ext ω
    by_cases h : (J.filter (P ω)).Nonempty
    · simp only [h, ↓reduceDIte, mem_ofPred_eq, max'_eq_iff, Finset.mem_filter, mem_union, mem_inter_iff,
        mem_iInter, mem_compl_iff, not_true_eq_false, false_and, or_false, true_and]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2⟩, fun x hx hPx => h3 x ⟨hx, hPx⟩⟩,
        fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2⟩, fun x hx => h3 x hx.1 hx.2⟩⟩
    · simp [h]
  rw [e]
  refine (hne.inter (((MeasurableSet.const _).inter (hP c)).inter (MeasurableSet.biInter J.countable_toSet
    fun x _ => ?_))).union (hne.compl.inter (MeasurableSet.const _))
  have : {ω | P ω x → x ≤ c} = {ω | P ω x}ᶜ ∪ {_ω | x ≤ c} := by ext ω; simp [imp_iff_not_or]
  rw [this]; exact (hP x).compl.union (MeasurableSet.const _)

theorem filter_min'_mem (J : Finset ℝ) (P : ℝ → Prop) [DecidablePred P] :
    (if h : (J.filter P).Nonempty then (J.filter P).min' h else 0) ∈ insert 0 J := by
  split_ifs with h
  · exact Finset.mem_insert_of_mem (Finset.mem_of_mem_filter _ ((J.filter P).min'_mem h))
  · exact Finset.mem_insert_self _ _

theorem filter_max'_mem (J : Finset ℝ) (P : ℝ → Prop) [DecidablePred P] :
    (if h : (J.filter P).Nonempty then (J.filter P).max' h else 0) ∈ insert 0 J := by
  split_ifs with h
  · exact Finset.mem_insert_of_mem (Finset.mem_of_mem_filter _ ((J.filter P).max'_mem h))
  · exact Finset.mem_insert_self _ _

end Finset

open Classical in
/-- The continuation in direction `right` (`ExplState.contStep`, its `some right` branches). -/
def contBranch (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (vStop : Option ℝ) (right : Bool) :
    ExplState :=
  if right then
    (if hC : ((jumpSet b jumps).filter (fun x => stPt s < x ∧
        -sleLambda κ < rightLim b x + stAngle s * QuantumZipper.chiC κ)).Nonempty then
      (match vStop with
        | some v => if stPt s < v ∧ v < ((jumpSet b jumps).filter (fun x => stPt s < x ∧
              -sleLambda κ < rightLim b x + stAngle s * QuantumZipper.chiC κ)).min' hC
            then ExplState.moveAlong s true v false
            else ExplState.moveAlong s true (((jumpSet b jumps).filter (fun x => stPt s < x ∧
              -sleLambda κ < rightLim b x + stAngle s * QuantumZipper.chiC κ)).min' hC) true
        | none => ExplState.moveAlong s true (((jumpSet b jumps).filter (fun x => stPt s < x ∧
              -sleLambda κ < rightLim b x + stAngle s * QuantumZipper.chiC κ)).min' hC) true)
    else
      (match vStop with
        | some v => if stPt s < v then ExplState.moveAlong s true v false else ExplState.moveToEnd s true
        | none => ExplState.moveToEnd s true))
  else
    (if hC : ((jumpSet b jumps).filter (fun x => x < stPt s ∧
        leftLim b x + stAngle s * QuantumZipper.chiC κ < sleLambda κ)).Nonempty then
      (match vStop with
        | some v => if ((jumpSet b jumps).filter (fun x => x < stPt s ∧
              leftLim b x + stAngle s * QuantumZipper.chiC κ < sleLambda κ)).max' hC < v ∧ v < stPt s
            then ExplState.moveAlong s false v false
            else ExplState.moveAlong s false (((jumpSet b jumps).filter (fun x => x < stPt s ∧
              leftLim b x + stAngle s * QuantumZipper.chiC κ < sleLambda κ)).max' hC) true
        | none => ExplState.moveAlong s false (((jumpSet b jumps).filter (fun x => x < stPt s ∧
              leftLim b x + stAngle s * QuantumZipper.chiC κ < sleLambda κ)).max' hC) true)
    else
      (match vStop with
        | some v => if v < stPt s then ExplState.moveAlong s false v false else ExplState.moveToEnd s false
        | none => ExplState.moveToEnd s false))

open Classical in
/-- The direction of a continuation from a zero-lifetime threshold (`ExplState.contStep`). -/
def contDirNone (κ : ℝ) (b : ℝ → ℝ) (pref : Bool) (s : ExplState) : Option Bool :=
  if rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ ∧
      sleLambda κ ≤ leftLim b (stPt s) + stAngle s * QuantumZipper.chiC κ then some pref
  else if rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ then some true
  else if sleLambda κ ≤ leftLim b (stPt s) + stAngle s * QuantumZipper.chiC κ then some false
  else none

/-- A boundary continuation, by status (`ExplState.contStep`). -/
def contByStatus (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (st : ExplStatus) (s : ExplState) (vStop : Option ℝ)
    (pref : Bool) : ExplState :=
  match st with
  | .inr (.inr (.inr (.inl (_, true)))) => s
  | .inr (.inr (.inr (.inr (.inl ())))) => s
  | .inr (.inr (.inl (some r))) => contBranch κ b jumps s vStop r
  | .inr (.inr (.inr (.inl (r, false)))) => contBranch κ b jumps s vStop r
  | .inr (.inr (.inl none)) =>
      (match contDirNone κ b pref s with
        | none => setDead s
        | some true => contBranch κ b jumps s vStop true
        | some false => contBranch κ b jumps s vStop false)
  | _ => setDead s

theorem contStep_eq_byStatus (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (vStop : Option ℝ)
    (pref : Bool) : ExplState.contStep κ b jumps s vStop pref = contByStatus κ b jumps (stStatus s) s vStop pref := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | ⟨_ | _⟩) | ⟨_ | _, _ | _⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  rotate_left 2
  · simp only [ExplState.contStep, contByStatus, contDirNone, stPt, stAngle]
    by_cases c1 : rightLim b pt + angle * QuantumZipper.chiC κ ≤ -sleLambda κ ∧
        sleLambda κ ≤ leftLim b pt + angle * QuantumZipper.chiC κ
    · cases pref <;> simp only [c1, ↓reduceIte] <;> rfl
    · simp only [c1, ↓reduceIte]
      by_cases c2 : rightLim b pt + angle * QuantumZipper.chiC κ ≤ -sleLambda κ
      · simp only [c2, ↓reduceIte]; rfl
      · simp only [c2, ↓reduceIte]
        by_cases c3 : sleLambda κ ≤ leftLim b pt + angle * QuantumZipper.chiC κ
        · simp only [c3, ↓reduceIte]; rfl
        · simp only [c3, ↓reduceIte]; rfl
  all_goals rfl


theorem ite_pos' {α : Sort*} {P : Prop} [Decidable P] {a b : α} (h : P) : (if P then a else b) = a :=
  ite_eq_left_iff.2 fun hn => absurd h hn

theorem ite_neg' {α : Sort*} {P : Prop} [Decidable P] {a b : α} (h : ¬ P) : (if P then a else b) = b :=
  ite_eq_right_iff.2 fun hp => absurd hp h

section ContMeas

variable {Ω : Type*} [MeasurableSpace Ω] {S : Ω → ExplState} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **A continuation in a fixed direction is measurable.** -/
theorem IsMeasState.contBranch (hS : IsMeasState S) (vStop : Option ℝ) (right : Bool) :
    IsMeasState fun ω => contBranch κ b jumps (S ω) vStop right := by
  classical
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
    have hA := hS.moveAlong false (insert 0 (jumpSet b jumps)) hxmF hxm true
    have hE := hS.moveToEnd false
    cases vStop with
    | none =>
      refine IsMeasState.of_cases hA hE hne (fun ω hω => ?_) (fun ω hω => ?_)
      · simp only [mem_ofPred_eq] at hω
        simp only [StagedLaw.contBranch, Bool.false_eq_true, ↓reduceIte, hω, ↓reduceDIte]
      · simp only [mem_ofPred_eq] at hω
        simp only [StagedLaw.contBranch, Bool.false_eq_true, ↓reduceIte, hω, ↓reduceDIte]
    | some v =>
      have hV := hS.moveAlong false {v} (x := fun _ => v) (fun _ => Finset.mem_singleton_self v)
        (fun c => MeasurableSet.const _) false
      refine IsMeasState.of_cases (IsMeasState.of_cases (S := fun ω =>
          if (if h : ((jumpSet b jumps).filter (fun x => x < stPt (S ω) ∧
              leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ)).Nonempty then
            ((jumpSet b jumps).filter (fun x => x < stPt (S ω) ∧
              leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ)).max' h else 0) < v ∧ v < stPt (S ω)
          then ExplState.moveAlong (S ω) false v false
          else ExplState.moveAlong (S ω) false (if h : ((jumpSet b jumps).filter (fun x => x < stPt (S ω) ∧
              leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ)).Nonempty then
            ((jumpSet b jumps).filter (fun x => x < stPt (S ω) ∧
              leftLim b x + stAngle (S ω) * QuantumZipper.chiC κ < sleLambda κ)).max' h else 0) true)
        hV hA ((measurableSet_lt hxmm measurable_const).inter (measurableSet_lt measurable_const hpt))
          (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω))
        (IsMeasState.of_cases (S := fun ω => if v < stPt (S ω) then ExplState.moveAlong (S ω) false v false
          else ExplState.moveToEnd (S ω) false) hV hE (measurableSet_lt measurable_const hpt)
          (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω))
        hne (fun ω hω => ?_) (fun ω hω => ?_)
      · simp only [mem_ofPred_eq] at hω
        simp only [StagedLaw.contBranch, Bool.false_eq_true, ↓reduceIte, hω, ↓reduceDIte]
      · simp only [mem_ofPred_eq] at hω
        simp only [StagedLaw.contBranch, Bool.false_eq_true, ↓reduceIte, hω, ↓reduceDIte]
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
    have hA := hS.moveAlong true (insert 0 (jumpSet b jumps)) hxmF hxm true
    have hE := hS.moveToEnd true
    cases vStop with
    | none =>
      refine IsMeasState.of_cases hA hE hne (fun ω hω => ?_) (fun ω hω => ?_)
      · simp only [mem_ofPred_eq] at hω
        simp only [StagedLaw.contBranch, ↓reduceIte, hω, ↓reduceDIte]
      · simp only [mem_ofPred_eq] at hω
        simp only [StagedLaw.contBranch, ↓reduceIte, hω, ↓reduceDIte]
    | some v =>
      have hV := hS.moveAlong true {v} (x := fun _ => v) (fun _ => Finset.mem_singleton_self v)
        (fun c => MeasurableSet.const _) false
      refine IsMeasState.of_cases (IsMeasState.of_cases (S := fun ω =>
          if stPt (S ω) < v ∧ v < (if h : ((jumpSet b jumps).filter (fun x => stPt (S ω) < x ∧
              -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ)).Nonempty then
            ((jumpSet b jumps).filter (fun x => stPt (S ω) < x ∧
              -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ)).min' h else 0)
          then ExplState.moveAlong (S ω) true v false
          else ExplState.moveAlong (S ω) true (if h : ((jumpSet b jumps).filter (fun x => stPt (S ω) < x ∧
              -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ)).Nonempty then
            ((jumpSet b jumps).filter (fun x => stPt (S ω) < x ∧
              -sleLambda κ < rightLim b x + stAngle (S ω) * QuantumZipper.chiC κ)).min' h else 0) true)
        hV hA ((measurableSet_lt hpt measurable_const).inter (measurableSet_lt measurable_const hxmm))
          (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω))
        (IsMeasState.of_cases (S := fun ω => if stPt (S ω) < v then ExplState.moveAlong (S ω) true v false
          else ExplState.moveToEnd (S ω) true) hV hE (measurableSet_lt hpt measurable_const)
          (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω))
        hne (fun ω hω => ?_) (fun ω hω => ?_)
      · simp only [mem_ofPred_eq] at hω
        simp only [StagedLaw.contBranch, ↓reduceIte, hω, ↓reduceDIte]
      · simp only [mem_ofPred_eq] at hω
        simp only [StagedLaw.contBranch, ↓reduceIte, hω, ↓reduceDIte]


/-- **A boundary continuation of a measurable random state is measurable.** -/
theorem IsMeasState.contStep (hS : IsMeasState S) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (vStop : Option ℝ) (pref : Bool) : IsMeasState fun ω => ExplState.contStep κ b jumps (S ω) vStop pref := by
  classical
  have hR := (measurable_rightLim_of_pcbd hb).comp hS.2.1
  have hL := (measurable_leftLim_of_pcbd hb).comp hS.2.1
  have hang := hS.2.2.1
  have hBr : ∀ r, IsMeasState fun ω => StagedLaw.contBranch κ b jumps (S ω) vStop r := fun r => hS.contBranch vStop r
  have hc1 : MeasurableSet {ω | rightLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ ≤ -sleLambda κ ∧
      sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ} :=
    (measurableSet_le (hR.add (hang.mul_const _)) measurable_const).inter
      (measurableSet_le measurable_const (hL.add (hang.mul_const _)))
  have hc2 : MeasurableSet {ω | rightLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ ≤ -sleLambda κ} :=
    measurableSet_le (hR.add (hang.mul_const _)) measurable_const
  have hc3 : MeasurableSet {ω | sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ} :=
    measurableSet_le measurable_const (hL.add (hang.mul_const _))
  have hnone : IsMeasState fun ω => (match contDirNone κ b pref (S ω) with
      | none => StagedLaw.setDead (S ω)
      | some true => StagedLaw.contBranch κ b jumps (S ω) vStop true
      | some false => StagedLaw.contBranch κ b jumps (S ω) vStop false) := by
    have h3 := IsMeasState.of_cases (S := fun ω =>
      if sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ then
        StagedLaw.contBranch κ b jumps (S ω) vStop false else StagedLaw.setDead (S ω))
      (hBr false) hS.setDead hc3 (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω)
    have h2 := IsMeasState.of_cases (S := fun ω =>
      if rightLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ ≤ -sleLambda κ then
        StagedLaw.contBranch κ b jumps (S ω) vStop true
      else if sleLambda κ ≤ leftLim b (stPt (S ω)) + stAngle (S ω) * QuantumZipper.chiC κ then
        StagedLaw.contBranch κ b jumps (S ω) vStop false else StagedLaw.setDead (S ω))
      (hBr true) h3 hc2 (fun ω hω => ite_pos' hω) (fun ω hω => ite_neg' hω)
    refine IsMeasState.of_cases (hBr pref) h2 hc1 (fun ω hω => ?_) (fun ω hω => ?_)
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
  refine IsMeasState.of_status_cases hS.1 (T := fun st ω => contByStatus κ b jumps st (S ω) vStop pref)
    (fun st => ?_) fun ω => contStep_eq_byStatus κ b jumps (S ω) vStop pref
  rcases st with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | ⟨_ | _⟩) | ⟨_ | _, _ | _⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact hS.setDead
  · exact hS.setDead
  · exact hnone
  · exact hBr false
  · exact hBr true
  · exact hBr false
  · exact hS
  · exact hBr true
  · exact hS
  · exact hS
  · exact hS.setDead

end ContMeas


/-! ### The run -/

section RunMeas

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Every state of the run is a measurable random state.** -/
theorem isMeasState_run (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec) {Ω : Type*}
    [MeasurableSpace Ω] {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ n, IsMeasState fun ω => ExplState.run κ b jumps spec (fun j => E j ω) n
  | 0 => by
    have e : ∀ ω, ExplState.run κ b jumps spec (fun j => E j ω) 0 = ExplState.init spec.1 := fun ω => by
      simp [ExplState.run]
    simp_rw [e]
    exact isMeasState_init spec.1
  | n + 1 => by
    have ih := isMeasState_run hb spec hE hreg n
    simp_rw [run_succ]
    rcases h : spec.2.2[n]? with _ | (⟨θ, t⟩ | pref | ⟨v, pref⟩)
    · exact ih
    · exact ih.flowStep hb spec.2.1 n (hE n) (hreg n) θ t
    · exact ih.contStep hb none pref
    · exact ih.contStep hb (some v) pref

theorem launches_flowByStatus_ne_none_iff (gw2 : Bool) (st : ExplStatus) (s : ExplState) {k : ℕ}
    (hs : s.2.2.2.1 k = none) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (flowByStatus κ b gw2 st s k D θ t).2.2.2.1 k ≠ none ↔
      (match st with
        | .inl () => True
        | .inr (.inl ()) => True
        | .inr (.inr (.inr (.inr (.inl ())))) => False
        | .inr (.inr (.inr (.inr (.inr ())))) => False
        | _ => gw2 = false ∧
            ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ) := by
  classical
  have hl : (ExplState.launch s k D θ t).2.2.2.1 k ≠ none := by
    rw [launches_launch, Function.update_self]; exact Option.some_ne_none _
  rcases st with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | p | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp only [flowByStatus]
  · exact iff_of_true hl trivial
  · exact iff_of_true hl trivial
  all_goals first
    | exact iff_of_false (by simp [hs]) id
    | (cases gw2
       · by_cases hA : ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ
         · simp only [Bool.false_eq_true, ↓reduceIte, hA, true_and]; exact iff_of_true hl trivial
         · simp only [Bool.false_eq_true, ↓reduceIte, hA, and_false, iff_false, not_not]; exact hs
       · simp only [↓reduceIte, Bool.true_eq_false, false_and, iff_false, not_not]; exact hs)

end RunMeas

/-- **`RunMeasStatement` holds**: the launch events and the forward chart maps of the run of a staged history are
measurable, for measurable drivers regular at every sample. -/
theorem runMeasStatement : RunMeasStatement.{u} := by
  intro κ b jumps hb spec Ω _ E hE hreg k
  refine ⟨?_, fun z => (isMeasState_run hb spec hE hreg k).2.2.2.2.2.1 z⟩
  have hk := isMeasState_run (κ := κ) hb spec hE hreg k
  have hnone : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.1 k = none := fun ω =>
    launches_run_of_le spec _ le_rfl
  simp_rw [run_succ]
  rcases h : spec.2.2[k]? with _ | (⟨θ, t⟩ | pref | ⟨v, pref⟩)
  · simp only [hnone, ne_eq, not_true_eq_false, ofPred_false, MeasurableSet.empty]
  · simp only [ExplState.step, flowStep_eq_byStatus]
    have e : {ω | (flowByStatus κ b spec.2.1 (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) k))
        (ExplState.run κ b jumps spec (fun j => E j ω) k) k (E k ω) θ t).2.2.2.1 k ≠ none} =
        ⋃ st : ExplStatus, {ω | stStatus (ExplState.run κ b jumps spec (fun j => E j ω) k) = st} ∩
          {ω | (flowByStatus κ b spec.2.1 st (ExplState.run κ b jumps spec (fun j => E j ω) k) k (E k ω) θ
            t).2.2.2.1 k ≠ none} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      exact ⟨fun h' => ⟨_, rfl, h'⟩, fun ⟨st, hst, h'⟩ => hst ▸ h'⟩
    rw [e]
    refine MeasurableSet.iUnion fun st => (hk.1 st).inter ?_
    simp_rw [launches_flowByStatus_ne_none_iff spec.2.1 st _ (hnone _)]
    rcases st with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | p | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp only [ofPred_true, ofPred_false,
      MeasurableSet.univ, MeasurableSet.empty]
    all_goals exact (MeasurableSet.const _).inter (measurableSet_admissible hk hb θ)
  · simp only [ExplState.step, launches_contStep, hnone, ne_eq, not_true_eq_false, ofPred_false,
      MeasurableSet.empty]
  · simp only [ExplState.step, launches_contStep, hnone, ne_eq, not_true_eq_false, ofPred_false,
      MeasurableSet.empty]

end StagedLaw

end Exist

end InteractingSLE
