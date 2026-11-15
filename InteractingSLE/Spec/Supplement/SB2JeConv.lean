/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JeRoot

/-!
# SB2(2) under the v6 rule: GEOM2's mask read at one sample

Packet PROVE-SB2-LIFTSET (round 21). Conversions between GEOM2's launch-level v6 events (`Nv.maskEv`, `Nv.denseEv`,
`Nv.recGoodEv`, `Nv.launchEv`, the zero events `cZ4`) and the per-sample forms of the joint induction (`RecGoodAt`,
`DenseAt`, the root readings), and the per-sample rules `RootRule6`, `StageRule6` that the v6 hypotheses on a family
give at one sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P
open Sec7.PocketTraversal Sec7.Lemma71C

/-- **The relative root's rule at one sample** (v6): the zero driver at a zero root or a corner, and the generation
of the root stage curve on the mask (dense readings). -/
def RootRule6 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ) (D₁ D₂ : ℕ → Drv) : Prop :=
  ((ZeroRoot κ θ b₁ J₁ R D₁ ∨ (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0) → D₂ 0 = zeroDrv) ∧
  (¬ ZeroRoot κ θ b₁ J₁ R D₁ → (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
    Nv.DenseReads c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R)
      (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (ExplState.init 0) →
    (D₂ 0).2 = capLife (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
      (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
      (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (ExplState.init 0)) ∧
    ∀ T < capLife (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
        (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
        (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (ExplState.init 0)),
      IsGeneratingTrace (D₂ 0).1 T (capTrace (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
        (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
        (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (ExplState.init 0))))

/-- **The later stages' rule at one sample** (v6): generation below `N` on the mask. -/
def StageRule6 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (c : Chart) (m : ℝ)
    (D₁ D₂ : ℕ → Drv) (o N : ℕ) : Prop :=
  ∀ j, 2 ≤ j → j < N →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o + 1)).2.2.2.1 (j + o) ≠ none →
    (D₁ (j + o)).2 ≠ 0 → RecGoodAt κ θ b₂ J₂ D₂ j → DenseAt κ θ b₁ J₁ b₂ J₂ D₁ D₂ o c m j →
    (D₂ j).2 = capLife (stCurvep c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
      (D₁ (j + o))) (D₁ (j + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)) ∧
    ∀ T < capLife (stCurvep c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
        (D₁ (j + o))) (D₁ (j + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)),
      IsGeneratingTrace (D₂ j).1 T (capTrace (stCurvep c m
        (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)) (D₁ (j + o))) (D₁ (j + o)).2
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)))

section Conv

variable {Ω : Type*} {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ} {c : Chart}
  {m : ℝ} {D₁ : Ω → ℕ → Drv}

/-- The dense readings at a stage `j ≠ 0` are `DenseAt`. -/
theorem mem_denseEv_iff_of_ne {j : ℕ} (hj : j ≠ 0) (F : ℕ → Ω → Drv) (ω : Ω) :
    ω ∈ Nv.denseEv κ θ b₁ J₁ b₂ J₂ R c m D₁ j F ↔
      DenseAt κ θ b₁ J₁ b₂ J₂ (D₁ ω) (fun i => F i ω) (relOff κ θ b₁ J₁ R (D₁ ω)) c m j := by
  have hp : Nv.stP κ θ b₁ J₁ R D₁ j ω = pcPt (wRun κ θ b₁ J₁ (D₁ ω) (j + relOff κ θ b₁ J₁ R (D₁ ω)))
      (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))) := by
    funext t; simp only [Nv.stP, stageShift_of_ne κ θ b₁ J₁ R D₁ hj ω, zero_add]
  have hL : Nv.stL κ θ b₁ J₁ R D₁ j ω = (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2 := by
    simp only [Nv.stL, stageShift_of_ne κ θ b₁ J₁ R D₁ hj ω, ENNReal.coe_zero, tsub_zero]
  show Nv.DenseReads c m (Nv.stP κ θ b₁ J₁ R D₁ j ω) (Nv.stL κ θ b₁ J₁ R D₁ j ω) _ ↔ _
  rw [hp, hL]
  rfl

/-- The dense readings at stage `0` are the root's readings in the initial chart. -/
theorem mem_denseEv_zero_iff (F : ℕ → Ω → Drv) (ω : Ω) :
    ω ∈ Nv.denseEv κ θ b₁ J₁ b₂ J₂ R c m D₁ 0 F ↔
      Nv.DenseReads c m (rootPt (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω)))
          (D₁ ω (relOff κ θ b₁ J₁ R (D₁ ω))) R)
        (rootLife (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω))) (D₁ ω (relOff κ θ b₁ J₁ R (D₁ ω))) R)
        (ExplState.init 0) := by
  have hp : Nv.stP κ θ b₁ J₁ R D₁ 0 ω = rootPt (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω)))
      (D₁ ω (relOff κ θ b₁ J₁ R (D₁ ω))) R := by
    funext t; simp only [Nv.stP, stageShift, ↓reduceIte, zero_add, rootPt]
  have hL : Nv.stL κ θ b₁ J₁ R D₁ 0 ω = rootLife (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω)))
      (D₁ ω (relOff κ θ b₁ J₁ R (D₁ ω))) R := by
    simp only [Nv.stL, stageShift, ↓reduceIte, zero_add, rootLife]
  show Nv.DenseReads c m (Nv.stP κ θ b₁ J₁ R D₁ 0 ω) (Nv.stL κ θ b₁ J₁ R D₁ 0 ω) _ ↔ _
  rw [hp, hL]
  rfl

theorem mem_launchEv_zero_iff (ω : Ω) :
    ω ∈ Nv.launchEv κ θ b₁ J₁ R D₁ 0 ↔
      (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none := by
  simp only [Nv.launchEv, zero_add, mem_ofPred_eq]

theorem mem_cZ4_of_ne {j : ℕ} (hj : j ≠ 0) (F : ℕ → Ω → Drv) (ω : Ω) :
    ω ∈ cZ4 κ θ b₁ J₁ R D₁ j F ↔ j % 2 = 1 ∨ (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2 = 0 := by
  simp only [cZ4, mem_ofPred_eq, hj, false_and, false_or, stageShift_of_ne κ θ b₁ J₁ R D₁ hj ω, ENNReal.coe_zero,
    tsub_zero]

end Conv

end InteractingSLE.Theorem14.SB.Lk
