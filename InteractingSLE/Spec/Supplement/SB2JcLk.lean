/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JbLock
import InteractingSLE.Spec.Supplement.SB2JcRel
import InteractingSLE.Spec.Supplement.SB2XbAE

/-!
# SB2(2)'s joint stage induction: the lockstep at a stage from the earlier stages

Packet PROVE-SB2-LIFTSET (round 20). Inside the joint induction, at relative stage `N` the relative pieces are known to
be regular only before `N`; SB2LIFT's lockstep asks for regular launches of the relative walk at every stage. The
truncated family `truncDrv D₂ N` has them and runs like `D₂` up to `N`, so the lockstep is run on it and read back:

* **`TrLiftAt`**: the per-time lift at a stage (SB2LIFT's `RunInputs''.trLift` field);
* `stepPiece_truncDrv`, `trLiftAt_truncDrv`: the piece and per-time lifts before `N` transfer to the truncation;
* **`lockAt_of_truncDrv`**: the lockstep facts at `N` read back from the truncation;
* **`lockAt_upto`**: the lockstep facts at `N` from the start data, the actual walk's facts up to `N + o`, the
  relative regularity before `N` and the piece and per-time lifts before `N` (`lockAt_piece`, `lockAt_arc`); at a
  connector start, unless both walks are done at the first lockstep stage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The per-time lift at stage `i`** (the field `trLift` of SB2LIFT's `RunInputs''`). -/
def TrLiftAt (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (D₁ D₂ : ℕ → Drv)
    (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o i : ℕ) : Prop :=
  (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
    (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
    (D₁ (i + o)).2 ≠ ⊤ →
    (∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ (i + o)) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ i) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i)) '' (trOf (D₂ i) '' Icc 0
          r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))) ''
          (trOf (D₁ (i + o)) '' Icc 0 r.toNNReal))) ∧
    (∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ i) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ (i + o)) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i)) '' (trOf (D₂ i) '' Icc 0
          r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))) ''
          (trOf (D₁ (i + o)) '' Icc 0 r.toNNReal)))

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

theorem stepPiece_truncDrv {L : Pc → Pc → Prop} {D₁ D₂ : ℕ → Drv} {o N i : ℕ} (hi : i < N)
    (h : StepPiece κ θ b₁ L (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i)) :
    StepPiece κ θ b₁ L (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (truncDrv D₂ N) i) (D₁ (i + o)) (truncDrv D₂ N i) := by
  rw [run_truncDrv _ D₂ hi.le, truncDrv_of_lt D₂ hi]; exact h

theorem trLiftAt_truncDrv {D₁ D₂ : ℕ → Drv} {o N i : ℕ} (hi : i < N)
    (h : TrLiftAt κ θ b₁ J₁ b₂ J₂ D₁ D₂ β₀ γ tL o i) :
    TrLiftAt κ θ b₁ J₁ b₂ J₂ D₁ (truncDrv D₂ N) β₀ γ tL o i := by
  unfold TrLiftAt at h ⊢
  rw [run_truncDrv _ D₂ (show i + 1 ≤ N by omega), run_truncDrv _ D₂ hi.le, truncDrv_of_lt D₂ hi]
  exact h

theorem noLeftMove_of_truncDrv {D : ℕ → Drv} {n j : ℕ} (hj : j < n)
    (h : NoLeftMove κ b₂ J₂ θ (truncDrv D n) j) : NoLeftMove κ b₂ J₂ θ D j := by
  intro w mk e
  apply h w mk
  rw [run_truncDrv _ D (show j + 1 ≤ n by omega), run_truncDrv _ D (show j ≤ n by omega)]
  exact e

theorem noLeftHit_of_truncDrv {D : ℕ → Drv} {n j : ℕ} (hj : j < n)
    (h : NoLeftHit κ b₂ J₂ θ (truncDrv D n) j) : NoLeftHit κ b₂ J₂ θ D j := by
  intro hl
  have h' := h (by rw [run_truncDrv _ D (show j + 1 ≤ n by omega)]; exact hl)
  rwa [run_truncDrv _ D (show j ≤ n by omega), truncDrv_of_lt D hj] at h'

/-- **The lockstep facts at `N` read back from the truncated relative family.** -/
theorem lockAt_of_truncDrv {D₁ D₂ : ℕ → Drv} {o N : ℕ}
    (h : LockAt κ θ b₁ J₁ b₂ J₂ R ι D₁ (truncDrv D₂ N) β₀ γ tL o N) :
    LockAt κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N := by
  obtain ⟨hc, hok, hlm, hlh, hinv, hpre, hrec, hfl, hmem⟩ := h
  refine ⟨fun j hj hjN => ?_, fun j hj hjN => ?_, fun j hj => noLeftMove_of_truncDrv hj (hlm j hj),
    fun j hj => noLeftHit_of_truncDrv hj (hlh j hj), ?_, ?_, hrec, hfl, hmem⟩
  · have := hc j hj hjN
    rwa [run_truncDrv _ D₂ hjN] at this
  · have := hok j hj hjN
    rwa [run_truncDrv _ D₂ hjN.le, truncDrv_of_lt D₂ hjN] at this
  · rwa [run_truncDrv _ D₂ le_rfl] at hinv
  · have hp : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (truncDrv D₂ N) N =
        SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N := by
      unfold SB.prefixPhysSet; rw [run_truncDrv _ D₂ le_rfl]
    rwa [hp] at hpre

/-- **The lockstep facts at `N` from the earlier stages** (start data, the actual walk up to `N + o`, the relative
regularity before `N`, the piece and per-time lifts before `N`). -/
theorem lockAt_upto (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
    {D₁ D₂ : ℕ → Drv} {o N : ℕ} (h2N : 2 ≤ N)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧ (D₁ o).2 ≠ ⊤))
    (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hreg : ∀ k < N, ∀ (c : Chart) (θ' : ℝ),
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D₂ k).1 (min (instrTime (boundaryWalkSpec b₂ J₂ θ true) k) (D₂ k).2))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ ⊤ →
      (D₁ k).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hpc : ∀ i, 2 ≤ i → i < N →
      StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (hlen : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : TailArc κ θ b₁ J₁ D₁ R β₀ tL)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁) (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ)
    (hD : LiftCurveData β₀ γ tL R ι) (hβ0 : β₀ 0 = 0)
    (htr : ∀ i, 2 ≤ i → i < N → TrLiftAt κ θ b₁ J₁ b₂ J₂ D₁ D₂ β₀ γ tL o i) :
    LockAt κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N ∨
      (stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) = stDone ∧
        stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) = stDone) := by
  classical
  have e0 : (truncDrv D₂ N) 0 = D₂ 0 := truncDrv_of_lt D₂ (by omega)
  have hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (truncDrv D₂ N) := by
    intro k c θ' hl
    by_cases hk : k < N
    · rw [run_truncDrv _ D₂ (show k + 1 ≤ N by omega)] at hl
      rw [truncDrv_of_lt D₂ hk]; exact hreg k hk c θ' hl
    · unfold truncDrv; simp only [hk, ↓reduceIte]
      exact LuM.pieceRegular_zeroDrv0 _
  have hreg₂' : ∀ j, IsRegularDriver ((truncDrv D₂ N) j) := fun j => by
    by_cases hj : j < N
    · rw [truncDrv_of_lt D₂ hj]; exact hreg₂ j
    · unfold truncDrv; simp only [hj, ↓reduceIte]; exact LuM.isRegularDriver_zeroDrv0
  have hpc' : ∀ i, 2 ≤ i → i < N →
      StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (truncDrv D₂ N) i) (D₁ (i + o)) ((truncDrv D₂ N) i) :=
    fun i hi hiN => stepPiece_truncDrv hiN (hpc i hi hiN)
  have htr' : ∀ i, 2 ≤ i → i < N → TrLiftAt κ θ b₁ J₁ b₂ J₂ D₁ (truncDrv D₂ N) β₀ γ tL o i :=
    fun i hi hiN => trLiftAt_truncDrv hiN (htr i hi hiN)
  have hrun2 : ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (truncDrv D₂ N) 2 =
      ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2 := run_truncDrv _ D₂ h2N
  rcases hS with hA | ⟨hPV, hfin0⟩
  · have h := lockAt_arc hι hcont hA.even hA.len hA.move hA.angle hA.pt hA.recLe hA.gap hA.low hreg₂'
      (by rw [e0]; exact hA.zero₀) hP₁ hP₂ hfin₁ hlm₁ hlh₁ hallow hexit₁ hA.nz₁ hpc' h2N
      (fun i h1 h2 => hlen i (by omega) h2) hN₁ hβr hβ hβL hγ0 hhead htail hray hA.head hW₁ hβp hγp hD hβ0 htr'
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (lockAt_of_truncDrv h)
    · exact Or.inr ⟨h1, by rwa [hrun2] at h2⟩
  · refine Or.inl (lockAt_of_truncDrv ?_)
    exact lockAt_piece hι hcont hPV.even hPV.launch hPV.tip hPV.pt hPV.recLe (by rw [e0]; exact hPV.top)
      (by rw [e0]; exact hPV.zero) (by rw [e0]; exact hPV.hitR) (by rw [e0]; exact hPV.hitL₂)
      (by rw [e0]; exact hPV.recR) (by rw [e0]; exact hPV.lift₀) hPV.memR (hPV.recAfter hfin0) hreg₂' hP₁ hP₂
      hfin₁ hlm₁ hlh₁ hallow hexit₁ hPV.nz₁ hpc' h2N hlen hN₁ hβr hβ hβL hγ0 hhead htail hray hPV.head hW₁ hβp hγp
      hD hβ0 htr'

end InteractingSLE.Theorem14.SB.Lk
