/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrState
import InteractingSLE.Spec.Supplement.SB4RSymStep

/-!
# The translation of exploration steps and runs

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). Every step of the frozen exploration machine commutes
with the translation `z ↦ z − v` (`SB4RTrState`) for the translated data `y ↦ b (y + v)` (`affData 1 (−v) b`, jump
candidates `affJumps 1 (−v) J`) and **the same drivers**; the launch exactly when its swallowed real sets are bounded
(`RecBdd`):

* `heights_trState`, `flowStep_trState`;
* `jumpSet_trData`, `rBranch_trState`, `lBranch_trState`, `contStep_trState`;
* **`run_trState`**, `tipSet_trChart`, **`prefixPhysSet_trSpec`**, `physSet_trSpec`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw FlowDilate
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

section Data

variable {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
include hb

theorem leftLim_trData (v x : ℝ) : leftLim (affData 1 (-v) b) (x - v) = leftLim b x := by
  rw [leftLim_affData one_pos hb]
  congr 1
  ring

theorem rightLim_trData (v x : ℝ) : rightLim (affData 1 (-v) b) (x - v) = rightLim b x := by
  rw [rightLim_affData one_pos hb]
  congr 1
  ring

theorem jumpSet_trData (v : ℝ) :
    jumpSet (affData 1 (-v) b) (affJumps 1 (-v) J) = (jumpSet b J).map (Equiv.subRight v).toEmbedding := by
  ext y
  rw [mem_jumpSet_affData one_pos hb, Finset.mem_map_equiv]
  simp only [Equiv.subRight_symm_apply]
  rw [show (y - -v) / 1 = y + v by ring]

end Data

theorem min'_map_sub {C : Finset ℝ} (v : ℝ) (hC : C.Nonempty) (h' : (C.map (Equiv.subRight v).toEmbedding).Nonempty) :
    (C.map (Equiv.subRight v).toEmbedding).min' h' = C.min' hC - v := by
  refine le_antisymm (Finset.min'_le _ _ ?_) ?_
  · exact Finset.mem_map_equiv.2 (by simpa using C.min'_mem hC)
  · obtain ⟨y, hy, hye⟩ := Finset.mem_map.1 ((C.map (Equiv.subRight v).toEmbedding).min'_mem h')
    rw [← hye]
    have := C.min'_le y hy
    show C.min' hC - v ≤ y - v
    linarith

theorem max'_map_sub {C : Finset ℝ} (v : ℝ) (hC : C.Nonempty) (h' : (C.map (Equiv.subRight v).toEmbedding).Nonempty) :
    (C.map (Equiv.subRight v).toEmbedding).max' h' = C.max' hC - v := by
  refine le_antisymm ?_ (Finset.le_max' _ _ ?_)
  · obtain ⟨y, hy, hye⟩ := Finset.mem_map.1 ((C.map (Equiv.subRight v).toEmbedding).max'_mem h')
    rw [← hye]
    have := C.le_max' y hy
    show y - v ≤ C.max' hC - v
    linarith
  · exact Finset.mem_map_equiv.2 (by simpa using C.max'_mem hC)

/-! ### Heights and the flow step -/

theorem heights_trState {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ)
    (s : ExplState) : ExplState.heights κ (affData 1 (-v) b) (trState v s) = ExplState.heights κ b s := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  have hl := leftLim_trData hb v pt
  have hr := rightLim_trData hb v pt
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | (_ | _)) | ⟨r, m⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
  · simp only [ExplState.heights, trState, hl, hr]

theorem setDead_trState (v : ℝ) (s : ExplState) : setDead (trState v s) = trState v (setDead s) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

/-- **The flow step commutes with the translation** (same driver), when its launch (if any) has bounded swallowed
real sets. -/
theorem flowStep_trState {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ)
    (gw2 : Bool) (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (hT : ExplState.flowStep κ b gw2 s k d θ t = ExplState.launch s k d θ t → min t d.2 ≠ ⊤ → RecBdd s t d) :
    ExplState.flowStep κ (affData 1 (-v) b) gw2 (trState v s) k d θ t =
      trState v (ExplState.flowStep κ b gw2 s k d θ t) := by
  rw [flowStep_eq_cases] at hT
  rw [flowStep_eq_cases, flowStep_eq_cases, stStatus_trState, heights_trState hb]
  split_ifs with h1 h2 h3 h4
  · exact launch_trState v s k d θ t (hT (by simp only [h1, ↓reduceIte]))
  · rfl
  · exact setDead_trState v s
  · exact launch_trState v s k d θ t (hT (by simp only [h1, h2, h3, h4, ↓reduceIte, Bool.false_eq_true]))
  · rfl

/-! ### The boundary continuation -/

section Branches

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ)
include hb

theorem filter_right_trState (s : ExplState) :
    (jumpSet (affData 1 (-v) b) (affJumps 1 (-v) J)).filter
        (fun x => stPt (trState v s) < x ∧
          -sleLambda κ < rightLim (affData 1 (-v) b) x + stAngle (trState v s) * chiC κ) =
      ((jumpSet b J).filter (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ)).map
        (Equiv.subRight v).toEmbedding := by
  rw [jumpSet_trData hb, Finset.filter_map]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  simp only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.subRight_apply, stPt_trState, stAngle_trState,
    rightLim_trData hb, sub_lt_sub_iff_right]

theorem filter_left_trState (s : ExplState) :
    (jumpSet (affData 1 (-v) b) (affJumps 1 (-v) J)).filter
        (fun x => x < stPt (trState v s) ∧
          leftLim (affData 1 (-v) b) x + stAngle (trState v s) * chiC κ < sleLambda κ) =
      ((jumpSet b J).filter (fun x => x < stPt s ∧ leftLim b x + stAngle s * chiC κ < sleLambda κ)).map
        (Equiv.subRight v).toEmbedding := by
  rw [jumpSet_trData hb, Finset.filter_map]
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  simp only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.subRight_apply, stPt_trState, stAngle_trState,
    leftLim_trData hb, sub_lt_sub_iff_right]

/-- **The rightward branch commutes with the translation.** -/
theorem rBranch_trState (s : ExplState) (vStop : Option ℝ) :
    GW2aConn.rBranch κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trState v s) (vStop.map (· - v)) =
      trState v (GW2aConn.rBranch κ b J s vStop) := by
  unfold GW2aConn.rBranch
  rw [filter_right_trState hb]
  by_cases hC : ((jumpSet b J).filter
      (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ)).Nonempty
  · have hC' := hC.map (f := (Equiv.subRight v).toEmbedding)
    simp only [hC, hC', ↓reduceDIte]
    rw [min'_map_sub v hC]
    rcases vStop with _ | w
    · exact moveAlong_trState v s true _ true
    · simp only [Option.map_some, stPt_trState, sub_lt_sub_iff_right]
      by_cases hw : stPt s < w ∧ w < Finset.min' _ hC
      · simp only [hw, and_self, ↓reduceIte]
        exact moveAlong_trState v s true w false
      · simp only [hw, ↓reduceIte]
        exact moveAlong_trState v s true _ true
  · have hC' : ¬ (((jumpSet b J).filter
        (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ)).map
          (Equiv.subRight v).toEmbedding).Nonempty := by
      rwa [Finset.map_nonempty]
    simp only [hC, hC', ↓reduceDIte]
    rcases vStop with _ | w
    · exact moveToEnd_trState v s true
    · simp only [Option.map_some, stPt_trState, sub_lt_sub_iff_right]
      by_cases hw : stPt s < w
      · simp only [hw, ↓reduceIte]
        exact moveAlong_trState v s true w false
      · simp only [hw, ↓reduceIte]
        exact moveToEnd_trState v s true

/-- **The leftward branch commutes with the translation.** -/
theorem lBranch_trState (s : ExplState) (vStop : Option ℝ) :
    GW2aConn.lBranch κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trState v s) (vStop.map (· - v)) =
      trState v (GW2aConn.lBranch κ b J s vStop) := by
  unfold GW2aConn.lBranch
  rw [filter_left_trState hb]
  by_cases hC : ((jumpSet b J).filter
      (fun x => x < stPt s ∧ leftLim b x + stAngle s * chiC κ < sleLambda κ)).Nonempty
  · have hC' := hC.map (f := (Equiv.subRight v).toEmbedding)
    simp only [hC, hC', ↓reduceDIte]
    rw [max'_map_sub v hC]
    rcases vStop with _ | w
    · exact moveAlong_trState v s false _ true
    · simp only [Option.map_some, stPt_trState, sub_lt_sub_iff_right]
      by_cases hw : Finset.max' _ hC < w ∧ w < stPt s
      · simp only [hw, and_self, ↓reduceIte]
        exact moveAlong_trState v s false w false
      · simp only [hw, ↓reduceIte]
        exact moveAlong_trState v s false _ true
  · have hC' : ¬ (((jumpSet b J).filter
        (fun x => x < stPt s ∧ leftLim b x + stAngle s * chiC κ < sleLambda κ)).map
          (Equiv.subRight v).toEmbedding).Nonempty := by
      rwa [Finset.map_nonempty]
    simp only [hC, hC', ↓reduceDIte]
    rcases vStop with _ | w
    · exact moveToEnd_trState v s false
    · simp only [Option.map_some, stPt_trState, sub_lt_sub_iff_right]
      by_cases hw : w < stPt s
      · simp only [hw, ↓reduceIte]
        exact moveAlong_trState v s false w false
      · simp only [hw, ↓reduceIte]
        exact moveToEnd_trState v s false

/-- **The boundary continuation commutes with the translation.** -/
theorem contStep_trState (s : ExplState) (vStop : Option ℝ) (pref : Bool) :
    ExplState.contStep κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trState v s) (vStop.map (· - v)) pref =
      trState v (ExplState.contStep κ b J s vStop pref) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ, recR, recL⟩ := s
  have hl := leftLim_trData hb v pt
  have hr := rightLim_trData hb v pt
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | (_ | _)) | ⟨(_ | _), (_ | _)⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · rfl
  · rfl
  · -- the threshold without side: the same outward heights decide
    set s₀ : ExplState := (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL) with hs₀
    have hst : trState v s₀ = (pieces.map (trPiece v), arcs.map (trArc v), retained,
        fun k => trLaunch v (launches k), trChart v chart, stThr none, pt - v, θ, recR - v, recL - v) := rfl
    by_cases hR : rightLim b pt + θ * chiC κ ≤ -sleLambda κ <;>
    by_cases hL : sleLambda κ ≤ leftLim b pt + θ * chiC κ
    · cases pref
      · have e₁ : ExplState.contStep κ b J s₀ vStop false = GW2aConn.lBranch κ b J s₀ vStop := by
          simp only [hs₀, ExplState.contStep, hR, hL, and_self, ↓reduceIte]; rfl
        have e₂ : ExplState.contStep κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trState v s₀)
            (vStop.map (· - v)) false = GW2aConn.lBranch κ (affData 1 (-v) b) (affJumps 1 (-v) J)
              (trState v s₀) (vStop.map (· - v)) := by
          rw [hst]
          simp only [ExplState.contStep, hr, hl, hR, hL, and_self, ↓reduceIte]
          rfl
        rw [e₁, e₂]; exact lBranch_trState hb v _ vStop
      · have e₁ : ExplState.contStep κ b J s₀ vStop true = GW2aConn.rBranch κ b J s₀ vStop := by
          simp only [hs₀, ExplState.contStep, hR, hL, and_self, ↓reduceIte]; rfl
        have e₂ : ExplState.contStep κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trState v s₀)
            (vStop.map (· - v)) true = GW2aConn.rBranch κ (affData 1 (-v) b) (affJumps 1 (-v) J)
              (trState v s₀) (vStop.map (· - v)) := by
          rw [hst]
          simp only [ExplState.contStep, hr, hl, hR, hL, and_self, ↓reduceIte]
          rfl
        rw [e₁, e₂]; exact rBranch_trState hb v _ vStop
    · have e₁ : ExplState.contStep κ b J s₀ vStop pref = GW2aConn.rBranch κ b J s₀ vStop := by
        simp only [hs₀, ExplState.contStep, hR, hL, and_false, ↓reduceIte]; rfl
      have e₂ : ExplState.contStep κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trState v s₀)
          (vStop.map (· - v)) pref = GW2aConn.rBranch κ (affData 1 (-v) b) (affJumps 1 (-v) J)
            (trState v s₀) (vStop.map (· - v)) := by
        rw [hst]
        simp only [ExplState.contStep, hr, hl, hR, hL, and_false, ↓reduceIte]
        rfl
      rw [e₁, e₂]; exact rBranch_trState hb v _ vStop
    · have e₁ : ExplState.contStep κ b J s₀ vStop pref = GW2aConn.lBranch κ b J s₀ vStop := by
        simp only [hs₀, ExplState.contStep, hR, hL, false_and, ↓reduceIte]; rfl
      have e₂ : ExplState.contStep κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trState v s₀)
          (vStop.map (· - v)) pref = GW2aConn.lBranch κ (affData 1 (-v) b) (affJumps 1 (-v) J)
            (trState v s₀) (vStop.map (· - v)) := by
        rw [hst]
        simp only [ExplState.contStep, hr, hl, hR, hL, false_and, ↓reduceIte]
        rfl
      rw [e₁, e₂]; exact lBranch_trState hb v _ vStop
    · have e₁ : ExplState.contStep κ b J s₀ vStop pref = setDead s₀ := by
        simp only [hs₀, ExplState.contStep, hR, hL, and_false, ↓reduceIte]; rfl
      have e₂ : ExplState.contStep κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trState v s₀)
          (vStop.map (· - v)) pref = setDead (trState v s₀) := by
        rw [hst]
        simp only [ExplState.contStep, hr, hl, hR, hL, and_false, ↓reduceIte]
        rfl
      rw [e₁, e₂]; exact setDead_trState v _
  · exact lBranch_trState (κ := κ) hb v
      (pieces, arcs, retained, launches, chart, stThr (some false), pt, θ, recR, recL) vStop
  · exact rBranch_trState (κ := κ) hb v
      (pieces, arcs, retained, launches, chart, stThr (some true), pt, θ, recR, recL) vStop
  · exact lBranch_trState (κ := κ) hb v
      (pieces, arcs, retained, launches, chart, .inr (.inr (.inr (.inl (false, false)))), pt, θ, recR, recL) vStop
  · rfl
  · exact rBranch_trState (κ := κ) hb v
      (pieces, arcs, retained, launches, chart, .inr (.inr (.inr (.inl (true, false)))), pt, θ, recR, recL) vStop
  · rfl
  · rfl
  · rfl

end Branches

/-! ### Steps and runs -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ)

omit hb in
theorem getElem?_trSpec (spec : ExplSpec) (k : ℕ) : (trSpec v spec).2.2[k]? = (spec.2.2[k]?).map (trInstr v) := by
  simp [trSpec]

include hb in
/-- **One step commutes with the translation** (same drivers). -/
theorem step_trState (gw2 : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : ExplState) (i : Instr) (k : ℕ)
    (hT : ∀ θ t, i = .inl (θ, t) → ExplState.flowStep κ b gw2 s k (D k) θ t = ExplState.launch s k (D k) θ t →
      min t (D k).2 ≠ ⊤ → RecBdd s t (D k)) :
    ExplState.step κ (affData 1 (-v) b) (affJumps 1 (-v) J) gw2 D (trState v s) (trInstr v i, k) =
      trState v (ExplState.step κ b J gw2 D s (i, k)) := by
  rcases i with ⟨θ, t⟩ | pref | ⟨w, pref⟩
  · exact flowStep_trState hb v gw2 s k (D k) θ t (hT θ t rfl)
  · exact contStep_trState (κ := κ) hb v s none pref
  · exact contStep_trState (κ := κ) hb v s (some w) pref

include hb in
/-- **The translated run is the translation of the run** (same drivers), when every launch of the run has bounded
swallowed real sets. -/
theorem run_trState (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (hT : ∀ j < k, ∀ θ t, spec.2.2[j]? = some (.inl (θ, t)) →
      ExplState.flowStep κ b spec.2.1 (ExplState.run κ b J spec D j) j (D j) θ t =
        ExplState.launch (ExplState.run κ b J spec D j) j (D j) θ t →
      min t (D j).2 ≠ ⊤ → RecBdd (ExplState.run κ b J spec D j) t (D j)) :
    ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D k =
      trState v (ExplState.run κ b J spec D k) := by
  induction k with
  | zero => exact (trState_init v spec.1).symm
  | succ k ih =>
    rw [run_succ, run_succ, getElem?_trSpec, ih fun j hj => hT j (Nat.lt_succ_of_lt hj)]
    rcases hk : spec.2.2[k]? with _ | i
    · rfl
    · exact step_trState hb v spec.2.1 D _ i k fun θ t hi => hT k (Nat.lt_succ_self k) θ t (by rw [hk, hi])

end Run

/-! ### Physical sets -/

/-- **The tip set of a translated piece is the translated tip set.** -/
theorem tipSet_trChart (v : ℝ) (c : Chart) (W : ℝ≥0 → ℝ) (s : ℝ≥0∞) :
    (trChart v c).tipSet W s = (fun z => z - (v : ℂ)) '' c.tipSet W s := by
  ext z
  simp only [Chart.tipSet, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨t, ht, hz⟩
    refine ⟨z + v, ⟨t, ht, ?_⟩, by ring⟩
    have := hz.add_const (v : ℂ)
    simpa only [trChart, sub_add_cancel] using this
  · rintro ⟨w, ⟨t, ht, hw⟩, rfl⟩
    exact ⟨t, ht, hw.sub_const (v : ℂ)⟩

/-- **The physical set of the translated run is the translated physical set**, as soon as the translated run has
the translated pieces and connectors. -/
theorem prefixPhysSet_trSpec {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (v : ℝ) (spec : ExplSpec)
    (D' D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (h1 : (ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D' k).1 =
      (trState v (ExplState.run κ b J spec D k)).1)
    (h2 : (ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D' k).2.1 =
      (trState v (ExplState.run κ b J spec D k)).2.1) :
    prefixPhysSet κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D' k =
      (fun z => z - (v : ℂ)) '' prefixPhysSet κ b J spec D k := by
  have hA : ∀ a : Set ℝ, ((↑) : ℝ → ℂ) '' trArc v a = (fun z => z - (v : ℂ)) '' (((↑) : ℝ → ℂ) '' a) := by
    intro a
    rw [trArc, Set.image_image, Set.image_image]
    push_cast
    rfl
  have hP : ∀ L : List (Chart × (ℝ≥0 → ℝ) × ℝ≥0∞), (⋃ p ∈ L.map (trPiece v), p.1.tipSet p.2.1 p.2.2) =
      (fun z => z - (v : ℂ)) '' ⋃ p ∈ L, p.1.tipSet p.2.1 p.2.2 := by
    intro L
    rw [Set.image_iUnion₂]
    ext z
    simp only [Set.mem_iUnion, exists_prop, List.mem_map]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hz⟩
      exact ⟨p, hp, by rw [← tipSet_trChart]; exact hz⟩
    · rintro ⟨p, hp, hz⟩
      exact ⟨trPiece v p, ⟨p, hp, rfl⟩, by show z ∈ (trChart v p.1).tipSet p.2.1 p.2.2; rw [tipSet_trChart]; exact hz⟩
  have hC : ∀ L : List (Set ℝ), (⋃ a ∈ L.map (trArc v), ((↑) : ℝ → ℂ) '' a) =
      (fun z => z - (v : ℂ)) '' ⋃ a ∈ L, ((↑) : ℝ → ℂ) '' a := by
    intro L
    rw [Set.image_iUnion₂]
    ext z
    simp only [Set.mem_iUnion, exists_prop, List.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, hz⟩
      exact ⟨a, ha, by rw [← hA]; exact hz⟩
    · rintro ⟨a, ha, hz⟩
      exact ⟨trArc v a, ⟨a, ha, rfl⟩, by rw [hA]; exact hz⟩
  show {((spec.1 - v : ℝ) : ℂ)} ∪ _ ∪ _ = _
  rw [h1, h2, trState_pieces, trState_arcs, hP, hC]
  show _ = (fun z => z - (v : ℂ)) '' ({(spec.1 : ℂ)} ∪ (⋃ p ∈ (ExplState.run κ b J spec D k).1,
    p.1.tipSet p.2.1 p.2.2) ∪ ⋃ a ∈ (ExplState.run κ b J spec D k).2.1, ((↑) : ℝ → ℂ) '' a)
  rw [Set.image_union, Set.image_union, Set.image_singleton]
  push_cast
  rfl

theorem physSet_trSpec {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (v : ℝ) (spec : ExplSpec)
    (D' D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (h1 : (ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D' spec.2.2.length).1 =
      (trState v (ExplState.run κ b J spec D spec.2.2.length)).1)
    (h2 : (ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D' spec.2.2.length).2.1 =
      (trState v (ExplState.run κ b J spec D spec.2.2.length)).2.1) :
    ExplState.physSet κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) D' =
      (fun z => z - (v : ℂ)) '' ExplState.physSet κ b J spec D := by
  rw [← prefixPhysSet_length, ← prefixPhysSet_length]
  have hlen : (trSpec v spec).2.2.length = spec.2.2.length := List.length_map _
  rw [hlen]
  exact prefixPhysSet_trSpec v spec D' D _ h1 h2

end InteractingSLE.Theorem14.SB.Lf
