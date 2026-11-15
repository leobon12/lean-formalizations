/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JdFill
import InteractingSLE.Spec.Supplement.SBLuMeas

/-!
# SB2(2)'s joint stage induction (D29): the relative run chart at a stage from the earlier pieces

Packet PROVE-SB2-LIFTSET (round 19). The relative facts at stage `j` read the relative run chart after `j`
instructions. Its generic facts (conformal: continuous inverse on `ℍ` with right inverse; boundary limits within
bounded distance of the identity; fibres) need only the regularity of the pieces launched **before** `j`, which the
joint induction supplies stage by stage:

* `truncDrv`: the drivers before `n`, the zero driver from `n` on (it runs like the original up to `n`);
* **`runChart_facts_of_lt`**: if every piece launched before `n` is regular, the run chart at `n` is conformal and has
  `GW1Z.FiberGood` for the prefix (`chartFiber_run` and `isConformal_runChart_of_reg` on the truncated family).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

open Classical in
/-- The drivers before `n`, the zero driver from `n` on. -/
def truncDrv (D : ℕ → Drv) (n : ℕ) : ℕ → Drv := fun k => if k < n then D k else LuM.zeroDrv0

theorem run_truncDrv {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec) (D : ℕ → Drv) {n k : ℕ}
    (hk : k ≤ n) : ExplState.run κ b jumps spec (truncDrv D n) k = ExplState.run κ b jumps spec D k :=
  Staged.run_congr spec fun j hj => by
    unfold truncDrv; simp only [show j < n by omega, ↓reduceIte]

/-- **The run chart at `n` from the regularity of the pieces launched before `n`.** -/
theorem runChart_facts_of_lt {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec) {D : ℕ → Drv} {n : ℕ}
    (hreg : ∀ k < n, ∀ (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) :
    (stChart (ExplState.run κ b jumps spec D n)).IsConformal ∧
      GW1Z.FiberGood (stChart (ExplState.run κ b jumps spec D n)) (SB.prefixPhysSet κ b jumps spec D n) := by
  classical
  have hP : RegLaunches κ b jumps spec (truncDrv D n) := by
    intro k c θ hl
    by_cases hk : k < n
    · rw [run_truncDrv spec D (show k + 1 ≤ n by omega)] at hl
      have h := hreg k hk c θ hl
      unfold truncDrv; simp only [hk, ↓reduceIte]; exact h
    · unfold truncDrv; simp only [hk, ↓reduceIte]
      exact LuM.pieceRegular_zeroDrv0 _
  have h1 := isConformal_runChart_of_reg spec hP n
  have h2 := GW1Z.chartFiber_run spec (truncDrv D n) hP n
  rw [run_truncDrv spec D le_rfl] at h1
  have hpre : SB.prefixPhysSet κ b jumps spec (truncDrv D n) n = SB.prefixPhysSet κ b jumps spec D n := by
    unfold SB.prefixPhysSet; rw [run_truncDrv spec D le_rfl]
  rw [run_truncDrv spec D le_rfl, hpre] at h2
  exact ⟨h1, h2⟩

end InteractingSLE.Theorem14.SB.Lk
