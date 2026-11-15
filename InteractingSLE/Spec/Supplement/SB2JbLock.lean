/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XzGlue
import InteractingSLE.Spec.Supplement.SB2JiGeom

/-!
# SB2(2)'s joint stage induction: the stage-truncated lockstep

Packet PROVE-SB2-LIFTSET (round 20). SB2LIFT's corrected lockstep (`l1_fillCorr_of_liftsW`, `stCorr_run_strong2`,
`prefix_lift_of_stepsW`, with `TailArc`) runs up to a stage `N` from the piece lifts and per-time lifts **before**
`N` only. Its landed wrappers (`prefix_lift_of_lifts_pieceW`, `prefix_lift_of_lifts_arcW`) ask for the whole run up
to the actual walk's completion (`hd`), which the joint induction cannot supply at an intermediate stage. Here the same
proofs stop at `N`:

* **`LockAt`**: the lockstep facts at `N` (the state correspondence and the step data before `N`, the relative walk's
  no-left-move and no-left-hit before `N` and its profile invariant at `N`, the relative prefix as the lift image of
  B's prefix, and the actual walk's flow status at the first lockstep stage);
* **`lockAt_piece`**, **`lockAt_arc`**: `LockAt` at `N` from a piece start resp. a connector start (the proofs of
  SB2LIFT's wrappers without `hd`; at a connector start, unless both walks are done at the first lockstep stage).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1WalkExit GW1WalkFinish GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The lockstep facts at relative stage `N`** (actual stage `N + o`). -/
structure LockAt (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
    (D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o N : ℕ) : Prop where
  corr : ∀ j, 2 ≤ j → j ≤ N →
    StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)
  ok : ∀ j, 2 ≤ j → j < N →
    StepOK κ θ b₁ J₁ R ι R (j % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j) (D₁ (j + o)) (D₂ j)
  lm₂ : ∀ j, j < N → NoLeftMove κ b₂ J₂ θ D₂ j
  lh₂ : ∀ j, j < N → NoLeftHit κ b₂ J₂ θ D₂ j
  inv : InvR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N)
  pre : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N =
    liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o))
  rec₀ : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))
  flow₀ : FlowSt R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))
  memR : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The lockstep facts at `N`, starting on an actual piece** (`prefix_lift_of_lifts_pieceW` without completion). -/
theorem lockAt_piece (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
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
    (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ ⊤ →
      (D₁ k).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hnz₁ : ∀ k, o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0)
    (hpc : ∀ i, 2 ≤ i → i < N →
      StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (h2N : 2 ≤ N) (hlen : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : TailArc κ θ b₁ J₁ D₁ R β₀ tL)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hP₀ : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊆ β₀ '' Iic tL)
    (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁) (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ)
    (hD : LiftCurveData β₀ γ tL R ι) (hβ0 : β₀ 0 = 0)
    (htr : ∀ i, 2 ≤ i → i < N → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o)
        ≠ none → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
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
              (trOf (D₁ (i + o)) '' Icc 0 r.toNNReal)))) :
    LockAt κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N := by
  have hlne : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
    rw [hlaunch, launches_launch, Function.update_self]; simp
  have hL₁ := hlh₁ o hlne
  have hc1 := contSt_after_launch R hlaunch (hnz₁ o le_rfl hlne) (hlh₁ o)
  obtain ⟨hinv1, hpt1⟩ := recInv_ptRec_run_le hP₁ (N := o + 1) (fun j hj => hfin₁ j (by omega)) hlm₁ hlh₁
    (o + 1) le_rfl
  have hlen1 : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length := by
    have := (hlen 1 le_rfl (by omega)).1; omega
  have hs₀ : FlowSt R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) := by
    rw [show 2 + o = o + 1 + 1 by omega]
    exact flowSt_of_contSt hlen1 (by omega) hpt1 hRrec hc1
  have hp₀ : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) := by
    rw [show 2 + o = o + 1 + 1 by omega]
    exact hRrec.trans (stRecR_run_le_succ' hP₁ hinv1)
  have hok1 : StepOK κ θ b₁ J₁ R ι R ((1 : ℕ) % 2 = 0)
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) (D₁ (o + 1)) (D₂ 1) :=
    stepOK_of_status le_rfl false hpt1 hRrec ⟨fun h => absurd h (by simp), fun _ => hc1⟩
      (fun h => absurd h (by simp))
  have hc₁ := stCorr_start_piece (κ := κ) (θ := θ) hι hlaunch htip hpt hrec hT h0 hR hL₁ hL₂ hrec'
  have h₀ : StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) := by
    have h := stCorr_step (κ := κ) (θ := θ) hι le_rfl hlen1 (hlen 1 le_rfl (by omega)).2 (by omega) hc₁ hok1
    rwa [show o + 1 + 1 = 2 + o by omega] at h
  have hnz₂ : (D₂ 0).2 ≠ 0 := fun h => hnz₁ o le_rfl hlne (h0.1 h)
  have hfin₂ : (D₂ 0).2 ≠ ⊤ := fun h => hfin₁ o (by omega) hlne (hT.1 h)
  obtain ⟨hinv₀, hlm₂₀, hlh₂₀, hfin₂₀⟩ := relStart_piece hP₂ (hreg₂ 0) hnz₂ hfin₂ hL₂
  -- the history correspondence from relative stage `1`
  obtain ⟨hS₁, hS₂⟩ := start_piece_phys (b₂ := b₂) (J₂ := J₂) (D₂ := D₂) hlaunch
  have e1 : 1 + o = o + 1 := by omega
  have hca₀ : StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (1 + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) := by rw [e1]; exact hc₁
  have hstart : statePhysicalSet 0 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) =
      liftImage β₀ tL γ (statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
        (1 + o))) := by
    rw [e1, hS₁, hS₂]
    exact (liftImage_start_piece hβ hγ0 hP₀ hlift₀ (by rw [hβL]; exact Or.inr hRmem)).symm
  have hRmem' : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (1 + o) := by
    rw [hβL]
    show (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (1 + o))
    rw [e1, hS₁]
    exact Or.inr hRmem
  have hpre : ∀ i, 1 ≤ i → i < 2 →
      StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι R (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
        StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
          (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) := by
    intro i h1 h2 _
    obtain rfl : i = 1 := by omega
    refine ⟨?_, fun h => absurd h (by simp)⟩
    rw [e1]
    exact hok1
  have hLF := l1_fillCorr_of_liftsW hι hcont hP₁ hP₂ hreg₂ o 1 2 N (by norm_num) h2N hfin₁ hfin₂₀ hlm₁ hlh₁
    hlm₂₀ hlh₂₀ hinv₀ hallow hexit₁ ho (by norm_num) hlen hN₁ (fun k hk => hnz₁ k (by omega)) hp₀ hs₀ h₀ hW₁
    hβp hγp hD hβr hβ0 hhead htail hRmem' hca₀ hstart hpre hpc htr
  have hSf := stCorr_run_strong2 hι hcont le_rfl hP₁ hP₂ hreg₂ o 2 N hfin₁ hfin₂₀ hlm₁ hlh₁ hlm₂₀ hlh₂₀ hinv₀
    hallow hexit₁ ho (by norm_num) (fun i hi hiN => hlen i (by omega) hiN) hN₁ (fun k hk => hnz₁ k (by omega))
    hp₀ hs₀ h₀ hLF.1 hLF.2 N h2N le_rfl
  refine ⟨fun j hj hjN => hSf.1 j hj hjN, hSf.2.1, hSf.2.2.1, hSf.2.2.2.1, hSf.2.2.2.2, ?_, hp₀, hs₀,
    WalkIntRunChron.prefixPhysSet_mono _ D₁ (show 1 + o ≤ 2 + o by omega) hRmem'⟩
  refine prefix_lift_of_stepsW hι ho (fun i h1 h2 => hlen i h1 h2) hca₀ (fun i h1 h2 hci => ?_) (by omega) hN₁
    hstart hβr hβ hβL hγ0 hhead htail hray
  rcases Nat.lt_or_ge i 2 with hi | hi
  · exact hpre i h1 hi hci
  · exact ⟨hSf.2.1 i hi h2, hpc i hi h2⟩


/-- **The lockstep facts at `N`, starting on an actual connector** (`prefix_lift_of_lifts_arcW` without completion;
the relative walk is not done at `N`). -/
theorem lockAt_arc (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
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
    (hlow : rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (h0 : (D₂ 0).2 = 0)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ ⊤ →
      (D₁ k).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hnz₁ : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0)
    (hpc : ∀ i, 2 ≤ i → i < N →
      StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (h2N : 2 ≤ N) (hlen : ∀ i, 2 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : TailArc κ θ b₁ J₁ D₁ R β₀ tL)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hP₀ : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ⊆
      β₀ '' Iic tL)
    (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁) (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ)
    (hD : LiftCurveData β₀ γ tL R ι) (hβ0 : β₀ 0 = 0)
    (htr : ∀ i, 2 ≤ i → i < N → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o)
        ≠ none → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
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
              (trOf (D₁ (i + o)) '' Icc 0 r.toNNReal)))) :
    LockAt κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N ∨
      (stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) = stDone ∧
        stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) = stDone) := by
  rcases flowSt_after_arc hn ho hmove hgap with hdone | ⟨hs₀, hp₀⟩
  · right
    have hc0 := (stCorr_start_arc (κ := κ) (θ := θ) hι hn (by omega) hmove hθ hpt hrec hgap hlow (hreg₂ 0) h0).1
    rw [show o + 1 + 1 = 2 + o by omega] at hc0
    exact ⟨hc0.2.1.symm.trans (hc0.2.1.trans hdone), hc0.2.1.trans hdone⟩
  · obtain ⟨hinv₀, hlm₂₀, hlh₂₀, hfin₂₀⟩ := relStart_arc hι hP₂ (hreg₂ 0) h0 hlow
    obtain ⟨a, hRa, hc, hS₁, hS₂, haA⟩ := start_arc_physW (κ := κ) (θ := θ) (D₁ := D₁) (D₂ := D₂) hι hn (by omega)
      hmove hθ hpt hrec hgap hlow (hreg₂ 0) h0
    have e : 2 + o = o + 1 + 1 := by omega
    have h₀ : StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) := by rw [e]; exact hc
    have hl2 : o + 1 + 1 ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length := by omega
    have hsubS : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1 + 1)) ⊆
        range β₀ := by
      rw [hβr]
      exact prefix_subset_physSet D₁ (n := o + 1 + 1) (by omega)
    have hstart : statePhysicalSet 0 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) =
        liftImage β₀ tL γ (statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
          (2 + o))) := by
      rw [e, hS₁, hS₂]
      rw [hS₁] at hsubS
      exact (liftImage_start_arcW hβ hβL hγ0 hι.map_base hhead (htail.of_mem haA) hray hP₀ hRa
        fun x hx _ => hsubS (Or.inr ⟨x, hx, rfl⟩)).symm
    have hRmem : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o) := by
      rw [hβL]
      show (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))
      rw [e, hS₁]
      exact Or.inr ⟨R, hRa, rfl⟩
    have hLF := l1_fillCorr_of_liftsW hι hcont hP₁ hP₂ hreg₂ o 2 2 N le_rfl h2N hfin₁ hfin₂₀ hlm₁ hlh₁ hlm₂₀
      hlh₂₀ hinv₀ hallow hexit₁ ho (by norm_num) hlen hN₁ hnz₁ hp₀ hs₀ h₀ hW₁ hβp hγp hD hβr hβ0 hhead htail
      hRmem h₀ hstart (fun i h1 h2 => absurd h2 (by omega)) hpc htr
    have hSf := stCorr_run_strong2 hι hcont le_rfl hP₁ hP₂ hreg₂ o 2 N hfin₁ hfin₂₀ hlm₁ hlh₁ hlm₂₀ hlh₂₀ hinv₀
      hallow hexit₁ ho (by norm_num) hlen hN₁ hnz₁ hp₀ hs₀ h₀ hLF.1 hLF.2 N h2N le_rfl
    refine Or.inl ⟨fun j hj hjN => hSf.1 j hj hjN, hSf.2.1, hSf.2.2.1, hSf.2.2.2.1, hSf.2.2.2.2, ?_, hp₀, hs₀,
      hRmem⟩
    exact prefix_lift_of_stepsW hι ho (fun i h1 h2 => hlen i h1 h2) h₀
      (fun i h1 h2 _ => ⟨hSf.2.1 i h1 h2, hpc i h1 h2⟩) h2N hN₁ hstart hβr hβ hβL hγ0 hhead htail hray

end InteractingSLE.Theorem14.SB.Lk
