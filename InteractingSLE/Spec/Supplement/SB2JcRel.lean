/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JaZero
import InteractingSLE.Spec.Supplement.SB2TwLock

/-!
# SB2(2)'s joint stage induction: the relative chart at a restart mark from the earlier stages only

Packet PROVE-SB2-LIFTSET (round 20). Inside the joint induction the relative pieces are known to be regular, finite,
without left moves and without left hits only **before** the current stage `n`. The landed record invariant
(`recInv_ptRec_run_le'`) and the forward continuity (`continuousWithinAt_runChart_fwd`) ask for regular launches at
every stage; the truncated family `truncDrv D n` (zero drivers from `n` on) has them and runs like `D` up to `n`.

* `noLeftMove_truncDrv`, `noLeftHit_truncDrv`: the step predicates before `n` transfer to the truncated family;
* **`zero_cont_of_lt`**: at a restart mark at stage `n`, the run chart reads `0` at the current point and is continuous
  from `ℍ` there.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem truncDrv_of_lt (D : ℕ → Drv) {n j : ℕ} (hj : j < n) : truncDrv D n j = D j := by
  unfold truncDrv; simp only [hj, ↓reduceIte]

theorem noLeftMove_truncDrv {D : ℕ → Drv} {n j : ℕ} (hj : j < n) (h : NoLeftMove κ b jumps θ D j) :
    NoLeftMove κ b jumps θ (truncDrv D n) j := by
  intro w mk e
  rw [run_truncDrv _ D (show j + 1 ≤ n by omega), run_truncDrv _ D (show j ≤ n by omega)] at e
  exact h w mk e

theorem noLeftHit_truncDrv {D : ℕ → Drv} {n j : ℕ} (hj : j < n) (h : NoLeftHit κ b jumps θ D j) :
    NoLeftHit κ b jumps θ (truncDrv D n) j := by
  intro hl
  rw [run_truncDrv _ D (show j + 1 ≤ n by omega)] at hl
  rw [run_truncDrv _ D (show j ≤ n by omega), truncDrv_of_lt D hj]
  exact h hl

/-- **At a restart mark the run chart reads `0` at the current point and is continuous from `ℍ` there**, from the
regularity, finiteness, no-left-move and no-left-hit of the stages before `n` only. -/
theorem zero_cont_of_lt {D : ℕ → Drv} {n : ℕ}
    (hreg : ∀ k < n, ∀ (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ true) k) (D k).2))
    (hfin : ∀ j, j < n → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤)
    (hlm : ∀ j, j < n → NoLeftMove κ b jumps θ D j) (hlh : ∀ j, j < n → NoLeftHit κ b jumps θ D j)
    (hn : n ≤ (boundaryWalkSpec b jumps θ true).2.2.length) {r : Bool}
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = GW1W.stArcM r) :
    (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).1
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) = 0 ∧
      ContinuousWithinAt (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).1 H
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) := by
  classical
  set spec := boundaryWalkSpec b jumps θ true with hspec
  refine ⟨chart_zero_of_arcM D n hn r hst, ?_⟩
  have hP : RegLaunches κ b jumps spec (truncDrv D n) := by
    intro k c θ' hl
    by_cases hk : k < n
    · rw [run_truncDrv spec D (show k + 1 ≤ n by omega)] at hl
      rw [truncDrv_of_lt D hk]; exact hreg k hk c θ' hl
    · unfold truncDrv; simp only [hk, ↓reduceIte]
      exact LuM.pieceRegular_zeroDrv0 _
  have hfin' : ∀ j, j < n → (ExplState.run κ b jumps spec (truncDrv D n) (j + 1)).2.2.2.1 j ≠ none →
      (truncDrv D n j).2 ≠ ⊤ := fun j hj hl => by
    rw [run_truncDrv spec D (show j + 1 ≤ n by omega)] at hl
    rw [truncDrv_of_lt D hj]; exact hfin j hj hl
  have hri := recInv_ptRec_run_le' hP hfin' (fun j hj => noLeftMove_truncDrv hj (hlm j hj))
    (fun j hj => noLeftHit_truncDrv hj (hlh j hj))
  have hinv : ∀ k < n, RecInv κ b jumps θ (truncDrv D n) k ∧ WalkMovesRight κ b jumps θ (truncDrv D n) k :=
    fun k hk => ⟨(hri k hk.le).1, walkMovesRight_of_ptRec _ (hri k hk.le).2 (noLeftMove_truncDrv hk (hlm k hk))⟩
  have hrun := run_truncDrv (κ := κ) (b := b) (jumps := jumps) spec D (le_refl n)
  have hst' : stStatus (ExplState.run κ b jumps spec (truncDrv D n) n) = GW1W.stArcM r := by rw [hrun]; exact hst
  have h := continuousWithinAt_of_arcM hP n hn hinv r hst'
  rwa [hrun] at h

end InteractingSLE.Theorem14.SB.Lk
