/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootTest

/-!
# What GW2's stopped stage records determine

Packet PROVE-T14-GW2ROOT2. These deterministic lemmas verify the record dependence
needed by the repaired relative capacity. They assert no conditional next-piece law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

/-- Equal stopped records of regular drivers give equal launch states. -/
theorem launch_eq_of_recOf_eq {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) (he' : IsRegularDriver e') {t : ℝ≥0∞}
    (hrec : recOf t e = recOf t e') (st : ExplState) (k : ℕ) (θ : ℝ) :
    ExplState.launch st k e θ t = ExplState.launch st k e' θ t := by
  rw [← launch_canonDrv st k e, ← launch_canonDrv st k e']
  exact congrArg (fun d => ExplState.launch st k d θ t)
    (canonDrv_eq_of_readRec_eq he he' hrec)

/-- A flow step depends only on the stopped record, including its death flag. -/
theorem flowStep_eq_of_recOf_eq {κ : ℝ} {b : ℝ → ℝ}
    {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (he' : IsRegularDriver e') {t : ℝ≥0∞} (hrec : recOf t e = recOf t e')
    (gw : Bool) (st : ExplState) (k : ℕ) (θ : ℝ) :
    ExplState.flowStep κ b gw st k e θ t = ExplState.flowStep κ b gw st k e' θ t := by
  rcases flowStep_cases (κ := κ) (b := b) gw st k θ t with hc | hc
  · exact hc e e'
  · rw [hc, hc]
    exact launch_eq_of_recOf_eq he he' hrec st k θ

/-- For a program of flow instructions, its prescribed stopped records determine
the state, without inspecting unexecuted continuations. -/
theorem run_eq_of_piece_recOf_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}
    (hprog : IsFlowProg spec.2.2 θ Δ)
    {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} (hn : n ≤ spec.2.2.length)
    (hD : ∀ j < n, IsRegularDriver (D j))
    (hD' : ∀ j < n, IsRegularDriver (D' j))
    (hrec : ∀ j < n, recOf (Δ j) (D j) = recOf (Δ j) (D' j)) :
    ExplState.run κ b jumps spec D n = ExplState.run κ b jumps spec D' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (Nat.le_of_succ_le hn)
      (fun j hj => hD j (Nat.lt_succ_of_lt hj))
      (fun j hj => hD' j (Nat.lt_succ_of_lt hj))
      (fun j hj => hrec j (Nat.lt_succ_of_lt hj))
    have hins := hprog n (Nat.lt_of_succ_le hn)
    rw [Staged.run_succ, Staged.run_succ, hins, heq]
    exact flowStep_eq_of_recOf_eq (hD n (Nat.lt_succ_self n))
      (hD' n (Nat.lt_succ_self n)) (hrec n (Nat.lt_succ_self n)) _ _ _ _

section Canon

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens)

/-- Equal stopped canonical records give the same state of a finite schedule.
The assertion holds at every sample, including killed schedules. -/
theorem run_eq_of_stopRec_eq (x : ℝ) (l : List (ℝ × ℝ≥0)) {ω ω' : Ω} :
    ∀ {n : ℕ}, n ≤ l.length →
      (∀ j < n, stopRec hκ h12p βA c₀ h (schedSpec x l) j ω =
        stopRec hκ h12p βA c₀ h (schedSpec x l) j ω') →
      ExplState.run κ b jumps (schedSpec x l)
          (fun j => canonSpecFam hκ h12p βA c₀ h (schedSpec x l) j ω) n =
        ExplState.run κ b jumps (schedSpec x l)
          (fun j => canonSpecFam hκ h12p βA c₀ h (schedSpec x l) j ω') n
    := by
  intro n hn hrec
  apply run_eq_of_piece_recOf_eq (schedSpec x l) (isFlowProg_spec x true l)
  · exact hn.trans_eq (length_scheduleProgram 0 l).symm
  · intro j _
    exact isRegularDriver_canonDrive hκ h12p βA c₀ x _ _ _ j
  · intro j _
    exact isRegularDriver_canonDrive hκ h12p βA c₀ x _ _ _ j
  · exact hrec

/-- The physical prefix is determined by the stopped canonical records. -/
theorem prefixSet_eq_of_stopRec_eq (x : ℝ) (l : List (ℝ × ℝ≥0)) {ω ω' : Ω}
    (hrec : ∀ j < l.length, stopRec hκ h12p βA c₀ h (schedSpec x l) j ω =
      stopRec hκ h12p βA c₀ h (schedSpec x l) j ω') :
    prefixSet hκ h12p βA b jumps c₀ h x l ω =
      prefixSet hκ h12p βA b jumps c₀ h x l ω' := by
  apply StagedReg.physSet_eq_of_run_eq
  have hl : (schedSpec x l).2.2.length = l.length := length_scheduleProgram 0 l
  simp only [hl]
  exact run_eq_of_stopRec_eq hκ h12p βA b jumps c₀ h x l le_rfl hrec

end Canon

end InteractingSLE.Theorem14.GW2TipSystem
