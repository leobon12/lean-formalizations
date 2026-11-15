/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RSymStep

/-!
# The reflection symmetry of exploration runs and their physical sets

Packet PROVE-T14-SB4LEAF (ruling R104). The run of the reflected program with the negated drivers on the reflected
data is the reflected run:

* **`run_reflState`**: exactly, when no launch of the run has a two-sided hit;
* **`run_reflState_stuck`**: for GW2 programs of ordinary instructions only (schedules), always, up to the status side
  and point after a two-sided hit (`StuckRel`: both runs are then stuck, so nothing launches afterwards);
* `tipSet_reflChart`, **`prefixPhysSet_reflSpec`**: the physical sets are reflected;
* `reflSpec_boundaryWalkSpec`, `reflSpec_schedule`: the reflected walks and schedules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal ENNReal Pointwise
open QuantumZipper (chiC H Hbar)

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Exist.Staged Exist.StagedLaw GW2Schedule
open Sec7.StripWall (negDrv)
open Sec7.FlowReflect (reflData reflJumps)
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- The negated driver family. -/
def reflDrv (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => negDrv (D j)

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
include hb

/-- **One step commutes with the reflection** (exactly, when its launch has no two-sided hit). -/
theorem step_reflState (gw2 : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : ExplState) (i : Instr) (k : ℕ)
    (hT : ∀ θ t, i = .inl (θ, t) →
      ExplState.flowStep κ b gw2 s k (D k) θ t = ExplState.launch s k (D k) θ t → TieFree s t (D k)) :
    ExplState.step κ (reflData b) (reflJumps J) gw2 (reflDrv D) (reflState s) (reflInstr i, k) =
      reflState (ExplState.step κ b J gw2 D s (i, k)) := by
  rcases i with ⟨θ, t⟩ | pref | ⟨v, pref⟩
  · exact flowStep_reflState hb gw2 s k (D k) θ t (hT θ t rfl)
  · exact contStep_reflState (κ := κ) hb s none pref
  · exact contStep_reflState (κ := κ) hb s (some v) pref

omit hb in
theorem getElem?_reflSpec (spec : ExplSpec) (k : ℕ) :
    (reflSpec spec).2.2[k]? = (spec.2.2[k]?).map reflInstr := by
  simp [reflSpec]

/-- **The reflected run is the reflection of the run**, when no launch of the run has a two-sided hit. -/
theorem run_reflState (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (hT : ∀ j < k, ∀ θ t, spec.2.2[j]? = some (.inl (θ, t)) →
      ExplState.flowStep κ b spec.2.1 (ExplState.run κ b J spec D j) j (D j) θ t =
        ExplState.launch (ExplState.run κ b J spec D j) j (D j) θ t →
      TieFree (ExplState.run κ b J spec D j) t (D j)) :
    ExplState.run κ (reflData b) (reflJumps J) (reflSpec spec) (reflDrv D) k =
      reflState (ExplState.run κ b J spec D k) := by
  induction k with
  | zero => exact (reflState_init spec.1).symm
  | succ k ih =>
    rw [run_succ, run_succ, getElem?_reflSpec, ih fun j hj => hT j (Nat.lt_succ_of_lt hj)]
    rcases hk : spec.2.2[k]? with _ | i
    · rfl
    · exact step_reflState hb spec.2.1 D _ i k fun θ t hi => hT k (Nat.lt_succ_self k) θ t (by rw [hk, hi])

/-- The relation of a run and the reflected run in a GW2 schedule: equal up to reflection, or both stuck with the
same reflected pieces, connectors, retained data, launch records and chart. -/
def StuckRel (s s' : ExplState) : Prop :=
  s' = reflState s ∨
    (s'.1 = (reflState s).1 ∧ s'.2.1 = (reflState s).2.1 ∧ s'.2.2.1 = (reflState s).2.2.1 ∧
      s'.2.2.2.1 = (reflState s).2.2.2.1 ∧ stChart s' = stChart (reflState s) ∧
      IsStuck (stStatus s) ∧ IsStuck (stStatus s'))

omit hb in
theorem StuckRel.components {s s' : ExplState} (h : StuckRel s s') :
    s'.1 = (reflState s).1 ∧ s'.2.1 = (reflState s).2.1 ∧ s'.2.2.1 = (reflState s).2.2.1 ∧
      s'.2.2.2.1 = (reflState s).2.2.2.1 ∧ stChart s' = stChart (reflState s) := by
  rcases h with rfl | ⟨h1, h2, h3, h4, h5, -⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨h1, h2, h3, h4, h5⟩

omit hb in
theorem flowStep_gw2_of_isStuck {s : ExplState} (hs : IsStuck (stStatus s)) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.flowStep κ b true s k d θ t = setDead s ∨ ExplState.flowStep κ b true s k d θ t = s := by
  rw [flowStep_eq_cases]
  rcases hs with h | ⟨o, h⟩
  · right
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [h]; simp [stTip])),
      ite_eq_left_of_eq_true _ _ (eq_true (Or.inr h))]
  · left
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [h]; simp [stTip])),
      ite_eq_right_of_eq_false _ _ (eq_false (by rw [h]; simp [stDone, stDead])),
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]

omit hb in
theorem isStuck_setDead (s : ExplState) : IsStuck (stStatus (setDead s)) := Or.inl rfl

/-- **One GW2 flow step preserves `StuckRel`.** -/
theorem flowStep_stuckRel {s s' : ExplState} (h : StuckRel s s') (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (t : ℝ≥0∞) :
    StuckRel (ExplState.flowStep κ b true s k d θ t)
      (ExplState.flowStep κ (reflData b) true s' k (negDrv d) (-θ) t) := by
  rcases h with rfl | ⟨h1, h2, h3, h4, h5, hs, hs'⟩
  · by_cases hT : ExplState.flowStep κ b true s k d θ t = ExplState.launch s k d θ t → TieFree s t d
    · exact Or.inl (flowStep_reflState hb true s k d θ t hT)
    · simp only [Classical.not_imp] at hT
      obtain ⟨hl, hnt⟩ := hT
      have hl' : ExplState.flowStep κ (reflData b) true (reflState s) k (negDrv d) (-θ) t =
          ExplState.launch (reflState s) k (negDrv d) (-θ) t := by
        rw [flowStep_eq_cases] at hl ⊢
        rw [stStatus_reflState, reflStatus_eq_iff_of_fixed (st₀ := .inl ()) rfl,
          reflStatus_eq_iff_of_fixed (st₀ := stTip) rfl, reflStatus_eq_iff_of_fixed (st₀ := stDone) rfl,
          reflStatus_eq_iff_of_fixed (st₀ := stDead) rfl]
        by_cases h1 : stStatus s = .inl () ∨ stStatus s = stTip
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
        · exfalso
          rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hl
          by_cases h2 : stStatus s = stDone ∨ stStatus s = stDead
          · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)] at hl
            have := launch_status_of_not_tieFree s k d θ t hnt
            rw [← hl] at this
            rcases h2 with h2 | h2 <;> rw [h2] at this <;> exact absurd this.1 (by simp [stDone, stDead])
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_left_of_eq_true _ _ (eq_true rfl)] at hl
            have := launch_status_of_not_tieFree s k d θ t hnt
            rw [← hl] at this
            exact absurd this.1 (by simp [setDead, stStatus, stThr])
      obtain ⟨c1, c2, c3, c4, c5, -, -, -⟩ := launch_reflState_components s k d θ t
      obtain ⟨s1, s2⟩ := launch_status_of_not_tieFree s k d θ t hnt
      refine Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hl', hl]; exact c1
      · rw [hl', hl]; exact c2
      · rw [hl', hl]; exact c3
      · rw [hl', hl]; exact c4
      · rw [hl', hl]; exact c5
      · rw [hl, s1]; exact Or.inr ⟨_, rfl⟩
      · rw [hl', s2]; exact Or.inr ⟨_, rfl⟩
  · refine Or.inr ?_
    have hc : ∀ {x : ExplState}, (x = setDead s ∨ x = s) →
        x.1 = s.1 ∧ x.2.1 = s.2.1 ∧ x.2.2.1 = s.2.2.1 ∧ x.2.2.2.1 = s.2.2.2.1 ∧ stChart x = stChart s ∧
          IsStuck (stStatus x) := by
      rintro x (rfl | rfl)
      · exact ⟨rfl, rfl, rfl, rfl, rfl, isStuck_setDead s⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, hs⟩
    have hc' : ∀ {x : ExplState}, (x = setDead s' ∨ x = s') →
        x.1 = s'.1 ∧ x.2.1 = s'.2.1 ∧ x.2.2.1 = s'.2.2.1 ∧ x.2.2.2.1 = s'.2.2.2.1 ∧ stChart x = stChart s' ∧
          IsStuck (stStatus x) := by
      rintro x (rfl | rfl)
      · exact ⟨rfl, rfl, rfl, rfl, rfl, isStuck_setDead s'⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, hs'⟩
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hc (flowStep_gw2_of_isStuck (b := b) hs k d θ t)
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hc' (flowStep_gw2_of_isStuck (b := reflData b) hs' k (negDrv d) (-θ) t)
    refine ⟨?_, ?_, ?_, ?_, ?_, a6, b6⟩
    · rw [b1, h1, reflState_pieces, reflState_pieces, a1]
    · rw [b2, h2, reflState_arcs, reflState_arcs, a2]
    · rw [b3, h3, reflState_retained, reflState_retained, a3]
    · rw [b4, h4, reflState_launches, reflState_launches, a4]
    · rw [b5, h5, stChart_reflState, stChart_reflState, a5]

/-- **The reflected schedule run** (a GW2 program of ordinary instructions) is the reflected run up to `StuckRel`. -/
theorem run_reflState_stuck (spec : ExplSpec) (hgw : spec.2.1 = true)
    (hflow : ∀ (j : ℕ) (i : Instr), spec.2.2[j]? = some i → ∃ θ t, i = .inl (θ, t))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    StuckRel (ExplState.run κ b J spec D k)
      (ExplState.run κ (reflData b) (reflJumps J) (reflSpec spec) (reflDrv D) k) := by
  induction k with
  | zero => exact Or.inl (reflState_init spec.1).symm
  | succ k ih =>
    rw [run_succ, run_succ, getElem?_reflSpec]
    rcases hk : spec.2.2[k]? with _ | i
    · exact ih
    · obtain ⟨θ, t, rfl⟩ := hflow k _ hk
      have hgw' : (reflSpec spec).2.1 = true := hgw
      show StuckRel (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b J spec D k) k (D k) θ t)
        (ExplState.flowStep κ (reflData b) (reflSpec spec).2.1
          (ExplState.run κ (reflData b) (reflJumps J) (reflSpec spec) (reflDrv D) k) k (negDrv (D k)) (-θ) t)
      generalize ExplState.run κ b J spec D k = r at ih ⊢
      generalize ExplState.run κ (reflData b) (reflJumps J) (reflSpec spec) (reflDrv D) k = r' at ih ⊢
      rw [hgw, hgw']
      exact flowStep_stuckRel (κ := κ) hb ih k (D k) θ t

end Run

/-! ### Physical sets -/

theorem refl_mul_I (y : ℝ) : Supp9B.refl ((y : ℂ) * I) = (y : ℂ) * I := by
  simp [Supp9B.refl]

/-- **The tip set of a reflected piece is the reflected tip set.** -/
theorem tipSet_reflChart (c : Chart) (W : ℝ≥0 → ℝ) (s : ℝ≥0∞) :
    (reflChart c).tipSet (-W) s = Supp9B.refl '' c.tipSet W s := by
  have hf : ∀ t : ℝ≥0, (fun y : ℝ => (reflChart c).2.1 (QuantumZipper.fwdMapInv (fun r : ℝ => (-W) r.toNNReal) t
      ((y : ℂ) * I))) = fun y : ℝ => Supp9B.refl (c.2.1 (QuantumZipper.fwdMapInv (fun r : ℝ => W r.toNNReal) t
        ((y : ℂ) * I))) := by
    intro t
    funext y
    show Supp9B.refl (c.2.1 (Supp9B.refl (QuantumZipper.fwdMapInv (-fun r : ℝ => W r.toNNReal) t ((y : ℂ) * I)))) = _
    have := fwdMapInv_neg_all (fun r : ℝ => W r.toNNReal) (NNReal.coe_nonneg t) ((y : ℂ) * I)
    rw [refl_mul_I] at this
    rw [this, refl_refl]
  have hrefl : ∀ {F : Filter ℝ} {f : ℝ → ℂ} {z : ℂ},
      Tendsto (fun y => Supp9B.refl (f y)) F (𝓝 z) ↔ Tendsto f F (𝓝 (Supp9B.refl z)) := by
    intro F f z
    constructor
    · intro h
      have := (continuous_refl.tendsto z).comp h
      simpa [Function.comp_def] using this
    · intro h
      have := (continuous_refl.tendsto _).comp h
      simpa [Function.comp_def] using this
  ext z
  simp only [Chart.tipSet, mem_ofPred_eq, hf, hrefl, mem_image]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨Supp9B.refl z, ⟨t, ht, hz⟩, refl_refl z⟩
  · rintro ⟨w, ⟨t, ht, hw⟩, rfl⟩
    exact ⟨t, ht, by rwa [refl_refl]⟩

/-- **The physical set of the reflected run is the reflected physical set**, as soon as the reflected run has the
reflected pieces and connectors. -/
theorem prefixPhysSet_reflSpec {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (spec : ExplSpec)
    (D' D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (h1 : (ExplState.run κ (reflData b) (reflJumps J) (reflSpec spec) D' k).1 =
      (reflState (ExplState.run κ b J spec D k)).1)
    (h2 : (ExplState.run κ (reflData b) (reflJumps J) (reflSpec spec) D' k).2.1 =
      (reflState (ExplState.run κ b J spec D k)).2.1) :
    prefixPhysSet κ (reflData b) (reflJumps J) (reflSpec spec) D' k =
      Supp9B.refl '' prefixPhysSet κ b J spec D k := by
  have hA : ∀ a : Set ℝ, Supp9B.refl '' (((↑) : ℝ → ℂ) '' a) = ((↑) : ℝ → ℂ) '' (-a) := by
    intro a
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨-x, by simpa using hx, (refl_ofReal x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(-x : ℝ), ⟨-x, hx, rfl⟩, by rw [refl_ofReal, neg_neg]⟩
  have hP : ∀ L : List (Chart × (ℝ≥0 → ℝ) × ℝ≥0∞), (⋃ p ∈ L.map reflPiece, p.1.tipSet p.2.1 p.2.2) =
      Supp9B.refl '' ⋃ p ∈ L, p.1.tipSet p.2.1 p.2.2 := by
    intro L
    rw [image_iUnion₂]
    ext z
    simp only [mem_iUnion, exists_prop, List.mem_map]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hz⟩
      refine ⟨p, hp, ?_⟩
      rw [← tipSet_reflChart]
      exact hz
    · rintro ⟨p, hp, hz⟩
      refine ⟨reflPiece p, ⟨p, hp, rfl⟩, ?_⟩
      show z ∈ (reflChart p.1).tipSet (-p.2.1) p.2.2
      rw [tipSet_reflChart]
      exact hz
  have hC : ∀ L : List (Set ℝ), (⋃ a ∈ L.map (fun a => -a), ((↑) : ℝ → ℂ) '' a) =
      Supp9B.refl '' ⋃ a ∈ L, ((↑) : ℝ → ℂ) '' a := by
    intro L
    rw [image_iUnion₂]
    ext z
    simp only [mem_iUnion, exists_prop, List.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, hz⟩
      exact ⟨a, ha, by rw [hA]; exact hz⟩
    · rintro ⟨a, ha, hz⟩
      exact ⟨-a, ⟨a, ha, rfl⟩, by rw [hA] at hz; exact hz⟩
  show {((-spec.1 : ℝ) : ℂ)} ∪ _ ∪ _ = _
  rw [h1, h2, reflState_pieces, reflState_arcs, hP, hC]
  show _ = Supp9B.refl '' ({(spec.1 : ℂ)} ∪ (⋃ p ∈ (ExplState.run κ b J spec D k).1, p.1.tipSet p.2.1 p.2.2) ∪
    ⋃ a ∈ (ExplState.run κ b J spec D k).2.1, ((↑) : ℝ → ℂ) '' a)
  rw [image_union, image_union, image_singleton, refl_ofReal]

/-! ### Reflected walks and schedules -/

theorem scheduleProgram_reflAngles (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    (scheduleProgram τ₀ l).map reflInstr = scheduleProgram τ₀ (reflAngles l) := by
  induction l generalizing τ₀ with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨θ, τ⟩ := p
    simp only [scheduleProgram, List.map_cons, reflAngles, List.map_cons] at ih ⊢
    rw [ih]
    rfl

theorem reflSpec_schedule (x : ℝ) (l : List (ℝ × ℝ≥0)) :
    reflSpec (x, true, scheduleProgram 0 l) = (-x, true, scheduleProgram 0 (reflAngles l)) := by
  simp only [reflSpec, scheduleProgram_reflAngles]

theorem reflSpec_boundaryWalkSpec {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (θ : ℝ) (right : Bool) :
    reflSpec (boundaryWalkSpec (reflData b) (reflJumps J) θ right) = boundaryWalkSpec b J (-θ) (!right) := by
  simp only [reflSpec, boundaryWalkSpec, neg_zero, jumpSet_reflData hb, Finset.card_map, List.map_flatten,
    List.map_replicate, List.map_cons, List.map_nil]
  rfl

end InteractingSLE.Theorem14.SB.Lf
