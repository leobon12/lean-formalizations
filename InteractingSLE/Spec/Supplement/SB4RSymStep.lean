/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RSymState
import InteractingSLE.Spec.Supplement.GW2aConnMove

/-!
# The reflection symmetry of the exploration steps

Packet PROVE-T14-SB4LEAF (ruling R104). Every step of the frozen exploration machine commutes with the reflection
(`SB4RSymState`): the launch of a piece (exactly when the piece has no two-sided hit, `TieFree`; otherwise up to the
side of its threshold and its current point), the boundary continuation (its two branches exchanged), and the flow
step (the seed admissibility test is reflection symmetric).

* `launch_reflState` (exact), `launch_reflState_components` (always);
* `heights_reflState`, `isAdmissibleSeed_reflState_iff`;
* `flowStep_reflState`;
* `jumpSet_reflData`, `rBranch_reflState`, `lBranch_reflState`, `contStep_reflState`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal ENNReal Pointwise
open QuantumZipper (chiC H Hbar)

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Exist.Staged Exist.StagedLaw
open Sec7.StripWall (negDrv)
open Sec7.FlowReflect (reflData reflJumps)
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-! ### Launches -/

theorem reflPiece_launch (c : Chart) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0∞) :
    reflPiece (c, fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min t d.2)).toNNReal, min t d.2) =
      (reflChart c, fun r : ℝ≥0 => (negDrv d).1 (min (r : ℝ≥0∞) (min t (negDrv d).2)).toNNReal,
        min t (negDrv d).2) := rfl

/-- **The launch commutes with the reflection, except for the status side and point at a two-sided hit**: pieces,
connectors, retained data, launch records, chart, angle and records always agree. -/
theorem launch_reflState_components (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch (reflState s) k (negDrv d) (-θ) t).1 = (reflState (ExplState.launch s k d θ t)).1 ∧
      (ExplState.launch (reflState s) k (negDrv d) (-θ) t).2.1 = (reflState (ExplState.launch s k d θ t)).2.1 ∧
      (ExplState.launch (reflState s) k (negDrv d) (-θ) t).2.2.1 =
        (reflState (ExplState.launch s k d θ t)).2.2.1 ∧
      (ExplState.launch (reflState s) k (negDrv d) (-θ) t).2.2.2.1 =
        (reflState (ExplState.launch s k d θ t)).2.2.2.1 ∧
      stChart (ExplState.launch (reflState s) k (negDrv d) (-θ) t) =
        stChart (reflState (ExplState.launch s k d θ t)) ∧
      stAngle (ExplState.launch (reflState s) k (negDrv d) (-θ) t) =
        stAngle (reflState (ExplState.launch s k d θ t)) ∧
      stRecR (ExplState.launch (reflState s) k (negDrv d) (-θ) t) =
        stRecR (reflState (ExplState.launch s k d θ t)) ∧
      stRecL (ExplState.launch (reflState s) k (negDrv d) (-θ) t) =
        stRecL (reflState (ExplState.launch s k d θ t)) := by
  have hd : (negDrv d).2 = d.2 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [CounterflowRange.pieces_launch, reflState_pieces (ExplState.launch s k d θ t),
      CounterflowRange.pieces_launch, List.map_append, reflState_pieces s]
    rfl
  · rw [Lx.arcs_launch', reflState_arcs, reflState_arcs, Lx.arcs_launch']
  · rw [retained_launch, reflState_retained, reflState_retained, retained_launch]
    funext j
    by_cases hj : j = k
    · subst hj; simp only [Function.update_self]; rfl
    · simp only [Function.update_of_ne hj]
  · rw [launches_launch, reflState_launches, reflState_launches, launches_launch]
    funext j
    by_cases hj : j = k
    · subst hj; simp only [Function.update_self]; rfl
    · simp only [Function.update_of_ne hj]
  by_cases hmin : min t d.2 = ⊤
  · have hmin' : min t (negDrv d).2 = ⊤ := hmin
    obtain ⟨c1, a1, r1, l1, -, -⟩ := launch_eq_of_top (reflState s) k (negDrv d) (-θ) t hmin'
    obtain ⟨c2, a2, r2, l2, -, -⟩ := launch_eq_of_top s k d θ t hmin
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [c1, stChart_reflState, stChart_reflState, c2]
    · rw [a1, stAngle_reflState, a2]
    · rw [r1, stRecR_reflState, stRecR_reflState, l2]
    · rw [l1, stRecL_reflState, stRecL_reflState, r2]
  · have hmin' : min t (negDrv d).2 ≠ ⊤ := hmin
    obtain ⟨c1, a1, r1, l1, -, -⟩ := launch_eq_of_ne_top (reflState s) k (negDrv d) (-θ) t hmin'
    obtain ⟨c2, a2, r2, l2, -, -⟩ := launch_eq_of_ne_top s k d θ t hmin
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [c1, stChart_reflState, stChart_reflState, c2, stopDrv_negDrv, stopTime_negDrv]
      exact reflChart_loewner _ _ (stopTime_nonneg t d)
    · rw [a1, stAngle_reflState, a2]
    · rw [r1, stRecR_reflState, l2, lRecR_reflState]
    · rw [l1, stRecL_reflState, r2, lRecL_reflState]

/-- **The launch commutes with the reflection** when the piece has no two-sided hit. -/
theorem launch_reflState (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (h : TieFree s t d) :
    ExplState.launch (reflState s) k (negDrv d) (-θ) t = reflState (ExplState.launch s k d θ t) := by
  obtain ⟨h1, h2, h3, h4, h5, h8, h9, h10⟩ := launch_reflState_components s k d θ t
  refine explState_ext h1 h2 h3 h4 h5 ?_ ?_ h8 h9 h10
  · by_cases hmin : min t d.2 = ⊤
    · rw [(launch_eq_of_top (reflState s) k (negDrv d) (-θ) t hmin).2.2.2.2.1, stStatus_reflState,
        (launch_eq_of_top s k d θ t hmin).2.2.2.2.1]
      rfl
    · rw [(launch_eq_of_ne_top (reflState s) k (negDrv d) (-θ) t hmin).2.2.2.2.1,
        stStatus_reflState (ExplState.launch s k d θ t), (launch_eq_of_ne_top s k d θ t hmin).2.2.2.2.1]
      exact lStatus_reflState s t d h hmin
  · by_cases hmin : min t d.2 = ⊤
    · rw [(launch_eq_of_top (reflState s) k (negDrv d) (-θ) t hmin).2.2.2.2.2, stPt_reflState s,
        stPt_reflState (ExplState.launch s k d θ t), (launch_eq_of_top s k d θ t hmin).2.2.2.2.2]
    · rw [(launch_eq_of_ne_top (reflState s) k (negDrv d) (-θ) t hmin).2.2.2.2.2,
        stPt_reflState (ExplState.launch s k d θ t), (launch_eq_of_ne_top s k d θ t hmin).2.2.2.2.2]
      exact lPt_reflState s t d h hmin

/-- At a two-sided hit both launches end at right thresholds. -/
theorem launch_status_of_not_tieFree (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (h : ¬ TieFree s t d) :
    stStatus (ExplState.launch s k d θ t) = stThr (some true) ∧
      stStatus (ExplState.launch (reflState s) k (negDrv d) (-θ) t) = stThr (some true) := by
  have hmin : min t d.2 ≠ ⊤ := by
    simp only [TieFree, not_forall] at h
    obtain ⟨-, -, hm, -⟩ := h
    exact hm
  rw [(launch_eq_of_ne_top s k d θ t hmin).2.2.2.2.1,
    (launch_eq_of_ne_top (reflState s) k (negDrv d) (-θ) t hmin).2.2.2.2.1]
  exact lStatus_of_not_tieFree s t d h

/-! ### Heights and the seed test -/

theorem heights_reflState {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (s : ExplState) :
    ExplState.heights κ (reflData b) (reflState s) =
      (-(ExplState.heights κ b s).2, -(ExplState.heights κ b s).1) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  have hl := Sec7.FlowReflect.leftLim_reflData hb (-pt)
  have hr := Sec7.FlowReflect.rightLim_reflData hb (-pt)
  rw [neg_neg] at hl hr
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | (_ | _)) | ⟨r, m⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
  · simp only [ExplState.heights, reflState, reflStatus, Bool.not_true, Bool.not_false, hl, hr]
    try (refine Prod.ext ?_ ?_ <;> simp only <;> ring)

theorem isAdmissibleSeed_reflState_iff {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (s : ExplState) (θ : ℝ) :
    ExplState.IsAdmissibleSeed κ (ExplState.heights κ (reflData b) (reflState s)).1
        (ExplState.heights κ (reflData b) (reflState s)).2 (-θ) ↔
      ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ := by
  rw [heights_reflState hb]
  simp only [ExplState.IsAdmissibleSeed]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem setDead_reflState (s : ExplState) : setDead (reflState s) = reflState (setDead s) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem reflStatus_eq_iff_of_fixed {st st₀ : ExplStatus} (h₀ : reflStatus st₀ = st₀) :
    reflStatus st = st₀ ↔ st = st₀ := by
  constructor
  · intro h; rw [← reflStatus_reflStatus st, h, h₀]
  · intro h; rw [h, h₀]

open Classical in
/-- **The flow step as a function of the status.** -/
theorem flowStep_eq_cases {κ : ℝ} {b : ℝ → ℝ} (gw2 : Bool) (s : ExplState) (k : ℕ)
    (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.flowStep κ b gw2 s k d θ t =
      if stStatus s = .inl () ∨ stStatus s = stTip then ExplState.launch s k d θ t
      else if stStatus s = stDone ∨ stStatus s = stDead then s
      else if gw2 = true then setDead s
      else if ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ then
        ExplState.launch s k d θ t
      else s := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | ⟨r, m⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> cases gw2 <;>
  · simp only [stStatus, stTip, stDone, stDead, Sum.inr.injEq, reduceCtorEq, or_self, or_false, false_or,
      ↓reduceIte, Bool.false_eq_true]
    rfl

/-- **The flow step commutes with the reflection**, when its launch (if any) has no two-sided hit. -/
theorem flowStep_reflState {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (gw2 : Bool) (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (hT : ExplState.flowStep κ b gw2 s k d θ t = ExplState.launch s k d θ t → TieFree s t d) :
    ExplState.flowStep κ (reflData b) gw2 (reflState s) k (negDrv d) (-θ) t =
      reflState (ExplState.flowStep κ b gw2 s k d θ t) := by
  rw [flowStep_eq_cases] at hT
  rw [flowStep_eq_cases, flowStep_eq_cases, stStatus_reflState,
    reflStatus_eq_iff_of_fixed (st₀ := .inl ()) rfl, reflStatus_eq_iff_of_fixed (st₀ := stTip) rfl,
    reflStatus_eq_iff_of_fixed (st₀ := stDone) rfl, reflStatus_eq_iff_of_fixed (st₀ := stDead) rfl,
    isAdmissibleSeed_reflState_iff hb]
  split_ifs with h1 h2 h3 h4
  · exact launch_reflState s k d θ t (hT (by simp only [h1, ↓reduceIte]))
  · rfl
  · exact setDead_reflState s
  · exact launch_reflState s k d θ t (hT (by simp only [h1, h2, h3, h4, ↓reduceIte, Bool.false_eq_true]))
  · rfl

/-! ### The boundary continuation -/

theorem jumpSet_reflData {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) :
    jumpSet (reflData b) (reflJumps J) = (jumpSet b J).map (Equiv.neg ℝ).toEmbedding := by
  ext y
  rw [Sec7.FlowReflect.mem_jumpSet_reflData hb, Finset.mem_map_equiv]
  rfl

theorem min'_map_neg {C : Finset ℝ} (hC : C.Nonempty) (h' : (C.map (Equiv.neg ℝ).toEmbedding).Nonempty) :
    (C.map (Equiv.neg ℝ).toEmbedding).min' h' = -C.max' hC := by
  refine le_antisymm (Finset.min'_le _ _ ?_) ?_
  · exact Finset.mem_map_equiv.2 (by simpa using C.max'_mem hC)
  · obtain ⟨y, hy, hye⟩ := Finset.mem_map.1 ((C.map (Equiv.neg ℝ).toEmbedding).min'_mem h')
    rw [← hye]
    have := C.le_max' y hy
    show -C.max' hC ≤ -y
    linarith

theorem max'_map_neg {C : Finset ℝ} (hC : C.Nonempty) (h' : (C.map (Equiv.neg ℝ).toEmbedding).Nonempty) :
    (C.map (Equiv.neg ℝ).toEmbedding).max' h' = -C.min' hC := by
  refine le_antisymm ?_ (Finset.le_max' _ _ ?_)
  · obtain ⟨y, hy, hye⟩ := Finset.mem_map.1 ((C.map (Equiv.neg ℝ).toEmbedding).max'_mem h')
    rw [← hye]
    have := C.min'_le y hy
    show -y ≤ -C.min' hC
    linarith
  · exact Finset.mem_map_equiv.2 (by simpa using C.min'_mem hC)

section Branches

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
include hb

theorem filter_right_reflState (s : ExplState) :
    (jumpSet (reflData b) (reflJumps J)).filter
        (fun x => stPt (reflState s) < x ∧ -sleLambda κ < rightLim (reflData b) x + stAngle (reflState s) * chiC κ) =
      ((jumpSet b J).filter (fun x => x < stPt s ∧ leftLim b x + stAngle s * chiC κ < sleLambda κ)).map
        (Equiv.neg ℝ).toEmbedding := by
  rw [jumpSet_reflData hb, Finset.filter_map]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  simp only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.neg_apply, stPt_reflState, stAngle_reflState,
    Sec7.FlowReflect.rightLim_reflData hb, neg_neg]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem filter_left_reflState (s : ExplState) :
    (jumpSet (reflData b) (reflJumps J)).filter
        (fun x => x < stPt (reflState s) ∧ leftLim (reflData b) x + stAngle (reflState s) * chiC κ < sleLambda κ) =
      ((jumpSet b J).filter (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ)).map
        (Equiv.neg ℝ).toEmbedding := by
  rw [jumpSet_reflData hb, Finset.filter_map]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  simp only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.neg_apply, stPt_reflState, stAngle_reflState,
    Sec7.FlowReflect.leftLim_reflData hb, neg_neg]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **The rightward branch of the reflected state is the reflected leftward branch.** -/
theorem rBranch_reflState (s : ExplState) (vStop : Option ℝ) :
    GW2aConn.rBranch κ (reflData b) (reflJumps J) (reflState s) (vStop.map Neg.neg) =
      reflState (GW2aConn.lBranch κ b J s vStop) := by
  unfold GW2aConn.rBranch GW2aConn.lBranch
  rw [filter_right_reflState hb]
  by_cases hC : ((jumpSet b J).filter
      (fun x => x < stPt s ∧ leftLim b x + stAngle s * chiC κ < sleLambda κ)).Nonempty
  · have hC' := hC.map (f := (Equiv.neg ℝ).toEmbedding)
    simp only [hC, hC', ↓reduceDIte]
    rw [min'_map_neg hC]
    rcases vStop with _ | v
    · exact moveAlong_reflState s false _ true
    · simp only [Option.map_some, stPt_reflState]
      by_cases hv : Finset.max' _ hC < v ∧ v < stPt s
      · have hv' : -stPt s < -v ∧ -v < -Finset.max' _ hC := ⟨by linarith, by linarith⟩
        simp only [hv, hv', and_self, ↓reduceIte]
        exact moveAlong_reflState s false v false
      · have hv' : ¬ (-stPt s < -v ∧ -v < -Finset.max' _ hC) := fun h => hv ⟨by linarith, by linarith⟩
        simp only [hv, hv', ↓reduceIte]
        exact moveAlong_reflState s false _ true
  · have hC' : ¬ (((jumpSet b J).filter
        (fun x => x < stPt s ∧ leftLim b x + stAngle s * chiC κ < sleLambda κ)).map
          (Equiv.neg ℝ).toEmbedding).Nonempty := by
      rwa [Finset.map_nonempty]
    simp only [hC, hC', ↓reduceDIte]
    rcases vStop with _ | v
    · exact moveToEnd_reflState s false
    · simp only [Option.map_some, stPt_reflState]
      by_cases hv : v < stPt s
      · have hv' : -stPt s < -v := by linarith
        simp only [hv, hv', ↓reduceIte]
        exact moveAlong_reflState s false v false
      · have hv' : ¬ -stPt s < -v := fun h => hv (by linarith)
        simp only [hv, hv', ↓reduceIte]
        exact moveToEnd_reflState s false

/-- **The leftward branch of the reflected state is the reflected rightward branch.** -/
theorem lBranch_reflState (s : ExplState) (vStop : Option ℝ) :
    GW2aConn.lBranch κ (reflData b) (reflJumps J) (reflState s) (vStop.map Neg.neg) =
      reflState (GW2aConn.rBranch κ b J s vStop) := by
  unfold GW2aConn.rBranch GW2aConn.lBranch
  rw [filter_left_reflState hb]
  by_cases hC : ((jumpSet b J).filter
      (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ)).Nonempty
  · have hC' := hC.map (f := (Equiv.neg ℝ).toEmbedding)
    simp only [hC, hC', ↓reduceDIte]
    rw [max'_map_neg hC]
    rcases vStop with _ | v
    · exact moveAlong_reflState s true _ true
    · simp only [Option.map_some, stPt_reflState]
      by_cases hv : stPt s < v ∧ v < Finset.min' _ hC
      · have hv' : -Finset.min' _ hC < -v ∧ -v < -stPt s := ⟨by linarith, by linarith⟩
        simp only [hv, hv', and_self, ↓reduceIte]
        exact moveAlong_reflState s true v false
      · have hv' : ¬ (-Finset.min' _ hC < -v ∧ -v < -stPt s) := fun h => hv ⟨by linarith, by linarith⟩
        simp only [hv, hv', ↓reduceIte]
        exact moveAlong_reflState s true _ true
  · have hC' : ¬ (((jumpSet b J).filter
        (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ)).map
          (Equiv.neg ℝ).toEmbedding).Nonempty := by
      rwa [Finset.map_nonempty]
    simp only [hC, hC', ↓reduceDIte]
    rcases vStop with _ | v
    · exact moveToEnd_reflState s true
    · simp only [Option.map_some, stPt_reflState]
      by_cases hv : stPt s < v
      · have hv' : -v < -stPt s := by linarith
        simp only [hv, hv', ↓reduceIte]
        exact moveAlong_reflState s true v false
      · have hv' : ¬ -v < -stPt s := fun h => hv (by linarith)
        simp only [hv, hv', ↓reduceIte]
        exact moveToEnd_reflState s true

/-- **The boundary continuation commutes with the reflection** (its branches and preference exchanged). -/
theorem contStep_reflState (s : ExplState) (vStop : Option ℝ) (pref : Bool) :
    ExplState.contStep κ (reflData b) (reflJumps J) (reflState s) (vStop.map Neg.neg) (!pref) =
      reflState (ExplState.contStep κ b J s vStop pref) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ, recR, recL⟩ := s
  have hl := Sec7.FlowReflect.leftLim_reflData hb (-pt)
  have hr := Sec7.FlowReflect.rightLim_reflData hb (-pt)
  rw [neg_neg] at hl hr
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | (_ | _)) | ⟨(_ | _), (_ | _)⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · rfl
  · rfl
  · -- the threshold without side: the outward heights decide
    by_cases hR : rightLim b pt + θ * chiC κ ≤ -sleLambda κ <;>
    by_cases hL : sleLambda κ ≤ leftLim b pt + θ * chiC κ
    · have hR' : rightLim (reflData b) (-pt) + -θ * chiC κ ≤ -sleLambda κ := by rw [hr]; linarith
      have hL' : sleLambda κ ≤ leftLim (reflData b) (-pt) + -θ * chiC κ := by rw [hl]; linarith
      cases pref
      · have e₁ : ExplState.contStep κ b J (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL)
            vStop false = GW2aConn.lBranch κ b J
              (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL) vStop := by
          simp only [ExplState.contStep, hR, hL, and_self, ↓reduceIte]; rfl
        have e₂ : ExplState.contStep κ (reflData b) (reflJumps J)
            (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL))
            (vStop.map Neg.neg) (!false) = GW2aConn.rBranch κ (reflData b) (reflJumps J)
              (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL))
              (vStop.map Neg.neg) := by
          simp only [reflState, reflStatus, ExplState.contStep, hR', hL', and_self, ↓reduceIte, Bool.not_false]
          rfl
        rw [e₁, e₂]; exact rBranch_reflState hb _ vStop
      · have e₁ : ExplState.contStep κ b J (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL)
            vStop true = GW2aConn.rBranch κ b J
              (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL) vStop := by
          simp only [ExplState.contStep, hR, hL, and_self, ↓reduceIte]; rfl
        have e₂ : ExplState.contStep κ (reflData b) (reflJumps J)
            (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL))
            (vStop.map Neg.neg) (!true) = GW2aConn.lBranch κ (reflData b) (reflJumps J)
              (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL))
              (vStop.map Neg.neg) := by
          simp only [reflState, reflStatus, ExplState.contStep, hR', hL', and_self, ↓reduceIte, Bool.not_true]
          rfl
        rw [e₁, e₂]; exact lBranch_reflState hb _ vStop
    · have hR' : ¬ rightLim (reflData b) (-pt) + -θ * chiC κ ≤ -sleLambda κ := by rw [hr]; intro h; apply hL; linarith
      have hL' : sleLambda κ ≤ leftLim (reflData b) (-pt) + -θ * chiC κ := by rw [hl]; linarith
      have e₁ : ExplState.contStep κ b J (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL)
          vStop pref = GW2aConn.rBranch κ b J
            (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL) vStop := by
        simp only [ExplState.contStep, hR, hL, and_false, ↓reduceIte]; rfl
      have e₂ : ExplState.contStep κ (reflData b) (reflJumps J)
          (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL))
          (vStop.map Neg.neg) (!pref) = GW2aConn.lBranch κ (reflData b) (reflJumps J)
            (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL))
            (vStop.map Neg.neg) := by
        simp only [reflState, reflStatus, ExplState.contStep, hR', hL', false_and, ↓reduceIte]
        rfl
      rw [e₁, e₂]; exact lBranch_reflState hb _ vStop
    · have hR' : rightLim (reflData b) (-pt) + -θ * chiC κ ≤ -sleLambda κ := by rw [hr]; linarith
      have hL' : ¬ sleLambda κ ≤ leftLim (reflData b) (-pt) + -θ * chiC κ := by rw [hl]; intro h; apply hR; linarith
      have e₁ : ExplState.contStep κ b J (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL)
          vStop pref = GW2aConn.lBranch κ b J
            (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL) vStop := by
        simp only [ExplState.contStep, hR, hL, false_and, ↓reduceIte]; rfl
      have e₂ : ExplState.contStep κ (reflData b) (reflJumps J)
          (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL))
          (vStop.map Neg.neg) (!pref) = GW2aConn.rBranch κ (reflData b) (reflJumps J)
            (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL))
            (vStop.map Neg.neg) := by
        simp only [reflState, reflStatus, ExplState.contStep, hR', hL', and_false, ↓reduceIte]
        rfl
      rw [e₁, e₂]; exact rBranch_reflState hb _ vStop
    · have hR' : ¬ rightLim (reflData b) (-pt) + -θ * chiC κ ≤ -sleLambda κ := by rw [hr]; intro h; apply hL; linarith
      have hL' : ¬ sleLambda κ ≤ leftLim (reflData b) (-pt) + -θ * chiC κ := by rw [hl]; intro h; apply hR; linarith
      have e₁ : ExplState.contStep κ b J (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL)
          vStop pref = setDead (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL) := by
        simp only [ExplState.contStep, hR, hL, and_false, ↓reduceIte]; rfl
      have e₂ : ExplState.contStep κ (reflData b) (reflJumps J)
          (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL))
          (vStop.map Neg.neg) (!pref) =
            setDead (reflState (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL)) := by
        simp only [reflState, reflStatus, ExplState.contStep, hR', hL', and_false, ↓reduceIte]
        rfl
      rw [e₁, e₂]; exact setDead_reflState _
  · exact rBranch_reflState (κ := κ) hb
      (pieces, arcs, retained, launches, chart, stThr (some false), pt, θ, recR, recL) vStop
  · exact lBranch_reflState (κ := κ) hb
      (pieces, arcs, retained, launches, chart, stThr (some true), pt, θ, recR, recL) vStop
  · exact rBranch_reflState (κ := κ) hb
      (pieces, arcs, retained, launches, chart, .inr (.inr (.inr (.inl (false, false)))), pt, θ, recR, recL) vStop
  · rfl
  · exact lBranch_reflState (κ := κ) hb
      (pieces, arcs, retained, launches, chart, .inr (.inr (.inr (.inl (true, false)))), pt, θ, recR, recL) vStop
  · rfl
  · rfl
  · rfl

end Branches

end InteractingSLE.Theorem14.SB.Lf
