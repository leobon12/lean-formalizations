/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LpStep

/-!
# SB2(2)'s physical sets from the named inputs (one sample)

Packet PROVE-SB2-LIFTSET (round 2). The end-to-end range identities of `SB2LuRange` take the step data `StepOK`,
`StepPiece` as hypotheses. Here they are supplied from the named inputs of PROVE-T14-SB2LIFT's
`stCorr_run_of_inputs` (with finite launched lifetimes only before the last stage used, `SB2LpStep`):

* `flowSt_after_arc`: after the arc start the actual walk is done, or at a mark beyond `R` with record beyond `R`;
  **`range_eq_physSet_of_inputs_arc`**: the arc start (`R` on a connector or the threshold point), then the inputs
  from relative stage `2` (or nothing, if the actual walk is already done);
* `contSt_after_launch`: after the piece start (nonzero lifetime, no left hit) the actual walk is at a right
  threshold, done, or dead; **`range_eq_physSet_of_inputs_piece`**: the piece start (with its launch observables),
  the record after it reaching `R`, one connector step (`stepOK_of_status`), then the inputs from relative stage `2`.

Both conclude `range γ = ExplState.physSet … D₂` for the lift curve `γ` of the actual tail, the body of
`RelWalkRange` at one sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ}

/-- **After the arc start the actual walk is done, or at a mark beyond `R` with record beyond `R`.** -/
theorem flowSt_after_arc {D₁ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o : ℕ}
    (hn : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (ho : o % 2 = 0)
    (hmove : ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) none
        true =
      if hC : (restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).Nonempty then
        ExplState.moveAlong (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true
          ((restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true)
    (hgap : ∀ x ∈ restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)), R < x) :
    stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) = stDone ∨
      (FlowSt R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) ∧
        R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))) := by
  have e : 2 + o = o + 1 + 1 := by omega
  rw [e, run_succ_walk_cont hn (by omega), hmove]
  split_ifs with hC
  · have hx := hgap _ (Finset.min'_mem _ hC)
    refine Or.inr ⟨Or.inl ⟨stStatus_moveAlong' _ _ _ _, ?_⟩, ?_⟩
    · rw [GW1W.stPt_moveAlong]; exact hx
    · rw [stRecR_moveAlong_true]; exact hx.le.trans (le_max_right _ _)
  · exact Or.inl (stStatus_moveToEnd'' _ _)


variable {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **SB2(2)'s physical sets from the named inputs, starting on an actual connector** (deterministic, one sample):
the arc start of `range_eq_physSet_start_arc`, the run inputs of `stepData_of_inputs` from relative stage `2`, the
lift relation at every launch, and the hypotheses on `β₀` and the lift curve `γ`. -/
theorem range_eq_physSet_of_inputs_arc (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
    {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ} (ho : o % 2 = 0)
    (hn : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hmove : ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) none
        true =
      if hC : (restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).Nonempty then
        ExplState.moveAlong (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true
          ((restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true)
    (hθ : stAngle (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) = θ)
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≤ R)
    (hgap : ∀ x ∈ restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)), R < x)
    (hlow : rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ) (hreg : IsRegularDriver (D₂ 0)) (h0 : (D₂ 0).2 = 0)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hfin₂ : ∀ j, j + 1 < N →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hlm₂ : ∀ j, NoLeftMove κ b₂ J₂ θ D₂ j) (hlh₂ : ∀ j, NoLeftHit κ b₂ J₂ θ D₂ j)
    (hnz₁ : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0)
    (hL1 : ∀ i, 2 ≤ i → i < N →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      ((D₂ i).2 = ⊤ ↔ (D₁ (i + o)).2 = ⊤) ∧ ((D₂ i).2 = 0 ↔ (D₁ (i + o)).2 = 0))
    (hF : ∀ i, 2 ≤ i → i < N →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      (D₁ (i + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (i + o) b₂ J₂ D₂ i ι)
    (hpc : ∀ i, 2 ≤ i → i < N →
      StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (h2N : 2 ≤ N) (hlen : ∀ i, 2 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hP₀ : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ⊆
      β₀ '' Iic tL) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  refine range_eq_physSet_start_arc hι ho hn hmove hθ hpt hrec hgap hlow hreg h0 h2N hlen ?_ hN₁ hN₂ hd hβr hβ hβL
    hγ0 hhead htail hray hP₀
  rcases flowSt_after_arc hn ho hmove hgap with hdone | ⟨hs₀, hp₀⟩
  · intro i hi hiN _
    have e := Lx.run_eq_of_done _ D₁ hdone (i + o) (by omega)
    rw [e]
    exact stepData_of_done _ hdone
  · exact stepData_of_inputs hι hcont le_rfl hP₁ hP₂ o 2 N hfin₁ hfin₂ hlm₁ hlh₁ hlm₂ hlh₂ ho (by norm_num) hlen
      hN₁ hnz₁ hp₀ hs₀ hL1 hF hpc


/-- **After the piece start the actual walk is at a right threshold, done, or dead** (nonzero lifetime, no left
hit). -/
theorem contSt_after_launch {D₁ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o : ℕ} (p : ℝ)
    (hlaunch : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) =
      ExplState.launch (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) o (D₁ o) θ ⊤)
    (hnz : (D₁ o).2 ≠ 0) (hlh : NoLeftHit κ b₁ J₁ θ D₁ o) :
    ContSt p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) := by
  set s := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o with hs
  have hlne : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
    rw [hlaunch, launches_launch, Function.update_self]; simp
  rw [hlaunch]
  by_cases htop : (D₁ o).2 = ⊤
  · exact Or.inr (Or.inr (Or.inl (launch_eq_of_top s o (D₁ o) θ ⊤ (by rw [htop, min_self])).2.2.2.2.1))
  · have hmin : min (⊤ : ℝ≥0∞) (D₁ o).2 ≠ ⊤ := by rw [min_eq_right le_top]; exact htop
    obtain ⟨-, -, -, -, hst', -⟩ := launch_eq_of_ne_top s o (D₁ o) θ ⊤ hmin
    have hnlt : ¬ (⊤ : ℝ≥0∞) < (D₁ o).2 := not_lt.2 le_top
    have hleft : ¬ ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) ⊤ (D₁ o) x := hlh hlne
    unfold ContSt FlowSt
    rw [hst']
    by_cases hR : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) ⊤ (D₁ o) x
    · left; simp only [lStatus, hnlt, hnz, hR, ↓reduceIte]
    · right; right; right; simp only [lStatus, hnlt, hnz, hR, hleft, ↓reduceIte]


/-- **SB2(2)'s physical sets from the named inputs, starting on an actual piece** (deterministic, one sample): the
piece start of `range_eq_physSet_start_piece` (whose launch observables are inputs), the record after the start piece
reaching `R`, one connector step, the run inputs of `stepData_of_inputs` from relative stage `2`, the lift relation
at every launch, and the hypotheses on `β₀` and the lift curve `γ`. -/
theorem range_eq_physSet_of_inputs_piece (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
    {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ} (ho : o % 2 = 0)
    (hlaunch : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) =
      ExplState.launch (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) o (D₁ o) θ ⊤)
    (htip : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≠ .inr (.inl ()))
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R)
    (hT : (D₂ 0).2 = ⊤ ↔ (D₁ o).2 = ⊤) (h0 : (D₂ 0).2 = 0 ↔ (D₁ o).2 = 0)
    (hR : (∃ x : ℝ, 0 < x ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x) ↔
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) ⊤ (D₁ o) x)
    (hL₂ : ¬ ∃ x : ℝ, x < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x)
    (hrec' : (D₁ o).2 ≠ ⊤ → lRecR (ExplState.init 0) ⊤ (D₂ 0) =
      ι (max (lRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊤ (D₁ o)) R))
    (hlift₀ : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o))
      (newPc (ExplState.init 0) (D₂ 0)))
    (hRmem : (R : ℂ) ∈ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).1.tipSet
      (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.1
      (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.2)
    (hRrec : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hfin₂ : ∀ j, j + 1 < N →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hlm₂ : ∀ j, NoLeftMove κ b₂ J₂ θ D₂ j) (hlh₂ : ∀ j, NoLeftHit κ b₂ J₂ θ D₂ j)
    (hnz₁ : ∀ k, o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0)
    (hL1 : ∀ i, 2 ≤ i → i < N →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      ((D₂ i).2 = ⊤ ↔ (D₁ (i + o)).2 = ⊤) ∧ ((D₂ i).2 = 0 ↔ (D₁ (i + o)).2 = 0))
    (hF : ∀ i, 2 ≤ i → i < N →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      (D₁ (i + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (i + o) b₂ J₂ D₂ i ι)
    (hpc : ∀ i, 2 ≤ i → i < N →
      StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (h2N : 2 ≤ N) (hlen : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hP₀ : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊆ β₀ '' Iic tL) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  have hlne : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
    rw [hlaunch, launches_launch, Function.update_self]; simp
  have hL₁ := hlh₁ o hlne
  -- the stage after the start piece
  have hc1 := contSt_after_launch R hlaunch (hnz₁ o le_rfl hlne) (hlh₁ o)
  obtain ⟨hinv1, hpt1⟩ := recInv_ptRec_run_le hP₁ (N := o + 1) (fun j hj => hfin₁ j (by omega)) hlm₁ hlh₁ (o + 1)
    le_rfl
  have hlen1 : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length := by
    have := (hlen 1 le_rfl (by omega)).1; omega
  have hs₀ : FlowSt R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) := by
    rw [show 2 + o = o + 1 + 1 by omega]
    exact flowSt_of_contSt hlen1 (by omega) hpt1 hRrec hc1
  have hp₀ : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) := by
    rw [show 2 + o = o + 1 + 1 by omega]
    exact hRrec.trans (stRecR_run_le_succ' hP₁ hinv1)
  have hdata := stepData_of_inputs (L := LiftRel β₀ tL γ) hι hcont le_rfl hP₁ hP₂ o 2 N hfin₁ hfin₂ hlm₁ hlh₁
    hlm₂ hlh₂ ho (by norm_num) (fun i hi hiN => hlen i (by omega) hiN) hN₁ (fun k hk => hnz₁ k (by omega)) hp₀ hs₀
    hL1 hF hpc
  refine range_eq_physSet_start_piece hι ho hlaunch htip hpt hrec hT h0 hR hL₁ hL₂ hrec' hlift₀ hRmem (by omega)
    hlen ?_ hN₁ hN₂ hd hβr hβ hβL hγ0 hhead htail hray hP₀
  intro i hi hiN hc
  rcases eq_or_lt_of_le hi with hi1 | hi2
  · subst hi1
    refine ⟨?_, fun h => absurd h (by simp)⟩
    rw [show 1 + o = o + 1 by omega] at hc ⊢
    exact stepOK_of_status le_rfl false hpt1 hRrec ⟨fun h => absurd h (by simp), fun _ => hc1⟩
      (fun h => absurd h (by simp))
  · exact hdata i hi2 hiN hc

end InteractingSLE.Theorem14.SB.Lk
