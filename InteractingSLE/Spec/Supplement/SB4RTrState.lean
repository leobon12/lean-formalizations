/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RSymState

/-!
# The translation of exploration states

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). The translation `z ↦ z − v` of the physical plane
acts on the frozen exploration states (`trState v`): charts are precomposed with `z ↦ z + v` (`trChart v`), connectors,
the current point and the records are translated, and everything else (drivers, retained data, statuses, angles)
is unchanged. The drivers of a staged history are **not** changed by a translation.

* `trChart`, `trState`, `trInstr`, `trSpec`; component lemmas;
* `trState_init`, `moveAlong_trState`, `moveToEnd_trState`, `trChart_loewner` (all exact);
* the launch observables: `lAlive_trChart`, `lHit_trChart` and `lStatus_trState` exactly; the new records
  `lRecR_trState`, `lRecL_trState` and point `lPt_trState` when the swallowed real sets are bounded (`RecBdd`; in
  the frozen definition the records are `sSup`/`sInf` of these sets, whose junk value `0` is not translation
  invariant); **`launch_trState`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw

/-! ### Translated charts and states -/

/-- The chart `c` read in the plane translated by `−v`: `fwd ↦ fwd (· + v)`, `inv ↦ inv − v`. -/
def trChart (v : ℝ) (c : Chart) : Chart :=
  (fun z => c.1 (z + v), fun w => c.2.1 w - v, fun z => c.2.2 (z + v))

/-- The translated piece: chart translated, driver unchanged. -/
def trPiece (v : ℝ) (p : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞) : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞ := (trChart v p.1, p.2.1, p.2.2)

/-- The translated connector. -/
def trArc (v : ℝ) (a : Set ℝ) : Set ℝ := (fun x => x - v) '' a

/-- The translated launch record: chart translated, angle unchanged. -/
def trLaunch (v : ℝ) (o : Option (Chart × ℝ)) : Option (Chart × ℝ) := o.map fun q => (trChart v q.1, q.2)

/-- **The translated state.** -/
def trState (v : ℝ) : ExplState → ExplState
  | (pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL) =>
    (pieces.map (trPiece v), arcs.map (trArc v), retained, fun k => trLaunch v (launches k), trChart v chart, status,
      pt - v, angle, recR - v, recL - v)

/-- The translated instruction (only a connector stop moves). -/
def trInstr (v : ℝ) : Instr → Instr
  | .inr (.inr (w, pref)) => .inr (.inr (w - v, pref))
  | i => i

/-- The translated program. -/
def trSpec (v : ℝ) (spec : ExplSpec) : ExplSpec := (spec.1 - v, spec.2.1, spec.2.2.map (trInstr v))

section Components

variable (v : ℝ) (s : ExplState)

theorem trState_pieces : (trState v s).1 = s.1.map (trPiece v) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem trState_arcs : (trState v s).2.1 = s.2.1.map (trArc v) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem trState_retained : (trState v s).2.2.1 = s.2.2.1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem trState_launches : (trState v s).2.2.2.1 = fun k => trLaunch v (s.2.2.2.1 k) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stChart_trState : stChart (trState v s) = trChart v (stChart s) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stStatus_trState : stStatus (trState v s) = stStatus s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stPt_trState : stPt (trState v s) = stPt s - v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stAngle_trState : stAngle (trState v s) = stAngle s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stRecR_trState : stRecR (trState v s) = stRecR s - v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stRecL_trState : stRecL (trState v s) = stRecL s - v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

end Components

/-! ### Charts -/

theorem trChart_fwd (v : ℝ) (c : Chart) (z : ℂ) : (trChart v c).1 z = c.1 (z + v) := rfl

theorem trChart_fwd_ofReal (v : ℝ) (c : Chart) (x : ℝ) : (trChart v c).1 ((x - v : ℝ) : ℂ) = c.1 (x : ℂ) := by
  rw [trChart_fwd, show ((x - v : ℝ) : ℂ) + (v : ℂ) = (x : ℂ) by push_cast; ring]

theorem trChart_id_recenter (v x : ℝ) : trChart v (Chart.id.recenter x) = Chart.id.recenter (x - v) := by
  refine Prod.ext (funext fun z => ?_) (Prod.ext (funext fun w => ?_) rfl)
  · show z + (v : ℂ) - (x : ℂ) = z - ((x - v : ℝ) : ℂ)
    push_cast; ring
  · show w + (x : ℂ) - (v : ℂ) = w + ((x - v : ℝ) : ℂ)
    push_cast; ring

theorem trChart_recenter (v : ℝ) (c : Chart) (a : ℝ) : (trChart v c).recenter a = trChart v (c.recenter a) := rfl

/-- **A Loewner chart of a translated chart is the translated Loewner chart** (same driver). -/
theorem trChart_loewner (v : ℝ) (c : Chart) (W : ℝ → ℝ) (T : ℝ) :
    (trChart v c).loewner W T = trChart v (c.loewner W T) := rfl

/-! ### Initial states and connectors -/

theorem trState_init (v x₀ : ℝ) : trState v (ExplState.init x₀) = ExplState.init (x₀ - v) := by
  refine explState_ext rfl rfl rfl rfl (trChart_id_recenter v x₀) rfl rfl rfl rfl rfl

theorem moveAlong_trState (v : ℝ) (s : ExplState) (right : Bool) (x : ℝ) (atMark : Bool) :
    ExplState.moveAlong (trState v s) right (x - v) atMark = trState v (ExplState.moveAlong s right x atMark) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  have hc : ((trChart v chart).1 ((x - v : ℝ) : ℂ)).re = (chart.1 (x : ℂ)).re := by rw [trChart_fwd_ofReal]
  cases right
  · simp only [ExplState.moveAlong, trState, List.map_append, List.map_cons, List.map_nil, ↓reduceIte,
      Bool.false_eq_true, hc, trChart_recenter, trArc, Set.image_sub_const_Icc, min_sub_sub_right]
  · simp only [ExplState.moveAlong, trState, List.map_append, List.map_cons, List.map_nil, ↓reduceIte, hc,
      trChart_recenter, trArc, Set.image_sub_const_Icc, max_sub_sub_right]

theorem moveToEnd_trState (v : ℝ) (s : ExplState) (right : Bool) :
    ExplState.moveToEnd (trState v s) right = trState v (ExplState.moveToEnd s right) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  cases right <;>
  · simp only [ExplState.moveToEnd, trState, List.map_append, List.map_cons, List.map_nil, ↓reduceIte,
      Bool.false_eq_true, trArc, Set.image_sub_const_Ici, Set.image_sub_const_Iic]

/-! ### The observables of a launch -/

theorem lAlive_trChart (v : ℝ) (c : Chart) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ) :
    lAlive (trChart v c) t d ((x - v : ℝ) : ℂ) ↔ lAlive c t d (x : ℂ) := by
  unfold lAlive
  rw [trChart_fwd_ofReal]

theorem lHit_trChart (v : ℝ) (c : Chart) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ) :
    lHit (trChart v c) t d ((x - v : ℝ) : ℂ) ↔ lHit c t d (x : ℂ) := by
  unfold lHit
  rw [lAlive_trChart, trChart_fwd_ofReal]

theorem exists_hitR_trState (v : ℝ) (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (∃ x : ℝ, stRecR (trState v s) < x ∧ lHit (stChart (trState v s)) t d x) ↔
      ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t d x := by
  rw [stRecR_trState, stChart_trState]
  constructor
  · rintro ⟨x, hx, hh⟩
    refine ⟨x + v, by linarith, (lHit_trChart v _ t d (x + v)).1 ?_⟩
    rwa [add_sub_cancel_right]
  · rintro ⟨x, hx, hh⟩
    exact ⟨x - v, by linarith, (lHit_trChart v _ t d x).2 hh⟩

theorem exists_hitL_trState (v : ℝ) (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (∃ x : ℝ, x < stRecL (trState v s) ∧ lHit (stChart (trState v s)) t d x) ↔
      ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t d x := by
  rw [stRecL_trState, stChart_trState]
  constructor
  · rintro ⟨x, hx, hh⟩
    refine ⟨x + v, by linarith, (lHit_trChart v _ t d (x + v)).1 ?_⟩
    rwa [add_sub_cancel_right]
  · rintro ⟨x, hx, hh⟩
    exact ⟨x - v, by linarith, (lHit_trChart v _ t d x).2 hh⟩

/-- **Bounded swallowed real sets** beyond both records (then the frozen `sSup`/`sInf` records are the true extrema,
which translate). -/
def RecBdd (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  BddAbove (insert (stRecR s) {x : ℝ | stRecR s < x ∧ ¬ lAlive (stChart s) t d x}) ∧
    BddBelow (insert (stRecL s) {x : ℝ | x < stRecL s ∧ ¬ lAlive (stChart s) t d x})

theorem image_sub_recR (v : ℝ) (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    insert (stRecR (trState v s)) {x : ℝ | stRecR (trState v s) < x ∧ ¬ lAlive (stChart (trState v s)) t d x} =
      (fun x => x - v) '' insert (stRecR s) {x : ℝ | stRecR s < x ∧ ¬ lAlive (stChart s) t d x} := by
  rw [Set.image_insert_eq, stRecR_trState, stChart_trState]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨y + v, ⟨by linarith, ?_⟩, by ring⟩
    rwa [← lAlive_trChart v, add_sub_cancel_right]
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨by linarith, by rwa [lAlive_trChart]⟩

theorem image_sub_recL (v : ℝ) (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    insert (stRecL (trState v s)) {x : ℝ | x < stRecL (trState v s) ∧ ¬ lAlive (stChart (trState v s)) t d x} =
      (fun x => x - v) '' insert (stRecL s) {x : ℝ | x < stRecL s ∧ ¬ lAlive (stChart s) t d x} := by
  rw [Set.image_insert_eq, stRecL_trState, stChart_trState]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨y + v, ⟨by linarith, ?_⟩, by ring⟩
    rwa [← lAlive_trChart v, add_sub_cancel_right]
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨by linarith, by rwa [lAlive_trChart]⟩

theorem lRecR_trState (v : ℝ) (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (h : BddAbove (insert (stRecR s) {x : ℝ | stRecR s < x ∧ ¬ lAlive (stChart s) t d x})) :
    lRecR (trState v s) t d = lRecR s t d - v := by
  unfold lRecR
  rw [image_sub_recR]
  have := (OrderIso.addRight (-v)).map_csSup' (Set.insert_nonempty _ _) h
  simp only [OrderIso.addRight_apply, ← sub_eq_add_neg] at this
  rw [this]

theorem lRecL_trState (v : ℝ) (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (h : BddBelow (insert (stRecL s) {x : ℝ | x < stRecL s ∧ ¬ lAlive (stChart s) t d x})) :
    lRecL (trState v s) t d = lRecL s t d - v := by
  unfold lRecL
  rw [image_sub_recL]
  have := (OrderIso.addRight (-v)).map_csInf' (Set.insert_nonempty _ _) h
  simp only [OrderIso.addRight_apply, ← sub_eq_add_neg] at this
  rw [this]

theorem lStatus_trState (v : ℝ) (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    lStatus (trState v s) t d = lStatus s t d := by
  unfold lStatus
  rw [exists_hitR_trState, exists_hitL_trState, stStatus_trState]

theorem lPt_trState (v : ℝ) (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (h : RecBdd s t d) :
    lPt (trState v s) t d = lPt s t d - v := by
  unfold lPt
  rw [exists_hitR_trState, exists_hitL_trState, stPt_trState, lRecR_trState v s t d h.1,
    lRecL_trState v s t d h.2]
  split_ifs <;> rfl

/-! ### The launch -/

theorem launch_components (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k d θ t).1 =
        s.1 ++ [(stChart s, fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min t d.2)).toNNReal, min t d.2)] ∧
      (ExplState.launch s k d θ t).2.1 = s.2.1 ∧
      (ExplState.launch s k d θ t).2.2.1 = Function.update s.2.2.1 k
        (fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min t d.2)).toNNReal, min t d.2, decide (d.2 ≤ t)) ∧
      (ExplState.launch s k d θ t).2.2.2.1 = Function.update s.2.2.2.1 k (some (stChart s, θ)) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  simp only [ExplState.launch]
  split_ifs <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem trLaunch_update (v : ℝ) (f : ℕ → Option (Chart × ℝ)) (k : ℕ) (c : Chart) (θ : ℝ) :
    (fun j => trLaunch v (Function.update f k (some (c, θ)) j)) =
      Function.update (fun j => trLaunch v (f j)) k (some (trChart v c, θ)) := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [trLaunch]
  · simp [Function.update_of_ne hj]

/-- **The launch commutes with the translation** (same driver), when the swallowed real sets are bounded. -/
theorem launch_trState (v : ℝ) (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (h : min t d.2 ≠ ⊤ → RecBdd s t d) :
    ExplState.launch (trState v s) k d θ t = trState v (ExplState.launch s k d θ t) := by
  obtain ⟨c1, c2, c3, c4⟩ := launch_components (trState v s) k d θ t
  obtain ⟨e1, e2, e3, e4⟩ := launch_components s k d θ t
  refine explState_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [c1, trState_pieces, trState_pieces, e1, List.map_append, stChart_trState]; rfl
  · rw [c2, trState_arcs, trState_arcs, e2]
  · rw [c3, trState_retained, trState_retained, e3]
  · rw [c4, trState_launches, trState_launches, e4, stChart_trState, trLaunch_update]
  all_goals by_cases hmin : min t d.2 = ⊤
  · rw [stChart_trState, (launch_eq_of_top _ k d θ t hmin).1, (launch_eq_of_top _ k d θ t hmin).1,
      stChart_trState]
  · rw [stChart_trState, (launch_eq_of_ne_top _ k d θ t hmin).1, (launch_eq_of_ne_top _ k d θ t hmin).1,
      stChart_trState, stopDrv_def]
    rfl
  · rw [stStatus_trState, (launch_eq_of_top _ k d θ t hmin).2.2.2.2.1, (launch_eq_of_top _ k d θ t hmin).2.2.2.2.1]
  · rw [stStatus_trState, (launch_eq_of_ne_top _ k d θ t hmin).2.2.2.2.1,
      (launch_eq_of_ne_top _ k d θ t hmin).2.2.2.2.1, lStatus_trState]
  · rw [stPt_trState, (launch_eq_of_top _ k d θ t hmin).2.2.2.2.2, (launch_eq_of_top _ k d θ t hmin).2.2.2.2.2,
      stPt_trState]
  · rw [stPt_trState, (launch_eq_of_ne_top _ k d θ t hmin).2.2.2.2.2,
      (launch_eq_of_ne_top _ k d θ t hmin).2.2.2.2.2, lPt_trState v s t d (h hmin)]
  · rw [stAngle_trState, (launch_eq_of_top _ k d θ t hmin).2.1, (launch_eq_of_top _ k d θ t hmin).2.1]
  · rw [stAngle_trState, (launch_eq_of_ne_top _ k d θ t hmin).2.1, (launch_eq_of_ne_top _ k d θ t hmin).2.1]
  · rw [stRecR_trState, (launch_eq_of_top _ k d θ t hmin).2.2.1, (launch_eq_of_top _ k d θ t hmin).2.2.1,
      stRecR_trState]
  · rw [stRecR_trState, (launch_eq_of_ne_top _ k d θ t hmin).2.2.1, (launch_eq_of_ne_top _ k d θ t hmin).2.2.1,
      lRecR_trState v s t d (h hmin).1]
  · rw [stRecL_trState, (launch_eq_of_top _ k d θ t hmin).2.2.2.1, (launch_eq_of_top _ k d θ t hmin).2.2.2.1,
      stRecL_trState]
  · rw [stRecL_trState, (launch_eq_of_ne_top _ k d θ t hmin).2.2.2.1,
      (launch_eq_of_ne_top _ k d θ t hmin).2.2.2.1, lRecL_trState v s t d (h hmin).2]

end InteractingSLE.Theorem14.SB.Lf
