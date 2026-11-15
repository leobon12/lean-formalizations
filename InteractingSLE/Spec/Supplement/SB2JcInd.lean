/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JcLk
import InteractingSLE.Spec.Supplement.SB2JbTop
import InteractingSLE.Spec.Supplement.SB2XyAsm
import InteractingSLE.Spec.Supplement.SB2XyTr
import InteractingSLE.Spec.Supplement.SB2JvReg
import InteractingSLE.Spec.Supplement.SB2XtSample

/-!
# SB2(2)'s joint stage-by-stage induction at relative stages `j ≥ 2` (D29), one sample

Packet PROVE-SB2-LIFTSET (round 20). **`JointIn`** collects, at one sample, the actual walk's facts, the upper chart
and prefix, the proper parametrization with Lemmas S1 and S3, the tail lift, the ray correspondence, SB2LIFT's start
data at the offset `o`, the relative family's regularity and generation (EL's rule) and the density of good times.
**`joint_all`**: by strong induction on the relative stage `M ≥ 2`, with the facts at the stages before `M`:

* the lockstep at `M` (`lockAt_upto`: SB2LIFT's corrected lockstep on the truncated relative family);
* at an actual launch at `M + o` (a restart mark beyond `R`): the relative chart's facts from the regularity before
  `M` (`relChart_facts_of_lt`, `relChart_bound_of_lt`), the relative chart reads `0` and is continuous at the lifted
  seed (`zero_cont_of_lt`), the fill identity from the lockstep, F2a carried to the run chart with the good-set
  matching (`stageFin_walk`, `stageInf_walk`), the regularity of the relative piece (`pieceRegular_of_stageRelP`);
* the piece lift (`liftRel_of_stage3`) and the per-time lift (`Mn.trLift_of_facts`) at `M`.

Past the actual walk's completion the relative walk is done (the lockstep at the completion stage). Outputs:
**`joint_stageFacts`** (`Mn.StageFacts` at every launching relative stage `j ≥ 2` of positive lifetime) and
**`joint_stageRelP`** (drivenness and `StageRelP` at every actual launch at `i + o`, `i ≥ 2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open Sec7.PocketTraversal Sec7.Lemma71C
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The per-sample inputs of the joint induction.** -/
structure JointIn (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
    (D₁ D₂ : ℕ → Drv) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o : ℕ) (c : Chart) (m : ℝ) (pA : ℝ → ℂ) : Prop where
  hR : R = realMax (pA '' Icc 0 1)
  ho : o % 2 = 0
  P₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
  W₁ : WalkChainFacts κ b₁ J₁ θ D₁
  lm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j
  lh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j
  allow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)
  exit₁ : ∀ k, 2 + o ≤ k →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ ⊤ →
    (D₁ k).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧
      lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x
  doneL : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
    (boundaryWalkSpec b₁ J₁ θ true).2.2.length) = stDone
  pinv : ∀ n, stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≠ stDone →
    LuM.PInv 0 (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)
  pc : ContinuousOn pA (Icc 0 1)
  p0 : pA 0 = 0
  pH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im
  pv : LuM.PInv 0 (pA '' Icc 0 1)
  cdom : IsDomainChart (H \ fillH (pA '' Icc 0 1)) c
  cN : WalkIntCanon.IsNormalized c
  cbd : ∃ (ĝ : ℂ → ℂ) (C : ℝ), (∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) ∧ ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C
  cU : UpperChartOK c
  βp : IsProperCurve β₀
  β0 : β₀ 0 = 0
  βr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
  S1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β₀
  S3 : ∀ tR : ℝ≥0, β₀ tR = (R : ℂ) → ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H
  lift : IsTailLiftCurve c R m β₀ tL γ
  hull : β₀ '' Icc 0 tL ⊆ hullK (pA '' Icc 0 1)
  headR : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R
  tail : TailArc κ θ b₁ J₁ D₁ R β₀ tL
  ray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x
  lcd : LiftCurveData β₀ γ tL R ι
  rc : RayCorr b₁ J₁ b₂ J₂ R ι
  cont : ContinuousOn ι (Ici R)
  start : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧ (D₁ o).2 ≠ ⊤)
  reg₂ : ∀ j, IsRegularDriver (D₂ j)
  root : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1).2.2.2.1 0 ≠ none →
    GW1P.PieceRegular (D₂ 0).1 (D₂ 0).2
  gen : ∀ j, 2 ≤ j → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o + 1)).2.2.2.1 (j + o) ≠ none →
    (D₁ (j + o)).2 ≠ 0 →
    (D₂ j).2 = capLife (stCurvep c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
      (D₁ (j + o))) (D₁ (j + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)) ∧
    ∀ T < capLife (stCurvep c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))
        (D₁ (j + o))) (D₁ (j + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)),
      IsGeneratingTrace (D₂ j).1 T (capTrace (stCurvep c m
        (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)) (D₁ (j + o))) (D₁ (j + o)).2
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)))
  gd : ∀ i, 2 ≤ i → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
    {t : ℝ≥0 | (t : ℝ≥0∞) < (D₁ (i + o)).2} ⊆
      closure (goodT c (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o)) (D₁ (i + o)))

/-- **The facts at an actual launch at `i + o`**: drivenness and `StageRelP` of the run-chart stage curve, and the
regularity of the relative piece. -/
def ActFacts (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (D₁ D₂ : ℕ → Drv) (o : ℕ)
    (c : Chart) (m : ℝ) (i : ℕ) : Prop :=
  IsDrivenCurve (stCurvep c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
    (D₁ (i + o))) (D₁ (i + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i)) ∧
  StageRelP c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o)) (D₁ (i + o)))
    (D₁ (i + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₂ i) ∧
  GW1P.PieceRegular (D₂ i).1 (D₂ i).2

/-- **The induction claim at stage `i`.** -/
def JointQ (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (D₁ D₂ : ℕ → Drv)
    (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o : ℕ) (c : Chart) (m : ℝ) (i : ℕ) : Prop :=
  StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
    TrLiftAt κ θ b₁ J₁ b₂ J₂ D₁ D₂ β₀ γ tL o i ∧
    ((ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none) ∧
    ((ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      ActFacts κ θ b₁ J₁ b₂ J₂ D₁ D₂ o c m i)

/-- `Mn.StageFacts` at an unshifted stage from the facts at an actual launch, the generation and the density. -/
theorem stageFacts_of_act {c : Chart} {m : ℝ} {s₁ s₂ : ExplState} {e₁ e₂ : Drv}
    (hdr : IsDrivenCurve (stCurvep c m (pcPt s₁ e₁) e₁.2 s₂)) (hrel : StageRelP c m (pcPt s₁ e₁) e₁.2 s₂ e₂)
    (hpr : GW1P.PieceRegular e₂.1 e₂.2) (he₂ : e₂.2 = capLife (stCurvep c m (pcPt s₁ e₁) e₁.2 s₂))
    (hgen : ∀ T < capLife (stCurvep c m (pcPt s₁ e₁) e₁.2 s₂),
      IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m (pcPt s₁ e₁) e₁.2 s₂)))
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁)) (hpos : e₁.2 ≠ 0) :
    Mn.StageFacts c m s₁ e₁ 0 s₂ e₂ := by
  have hq : (fun t => pcPt s₁ e₁ (0 + t)) = pcPt s₁ e₁ := funext fun t => by rw [zero_add]
  have hL : e₁.2 - ((0 : ℝ≥0) : ℝ≥0∞) = e₁.2 := by simp
  unfold Mn.StageFacts
  rw [hq, hL]
  exact ⟨hdr, he₂, hgen, hrel, hgd, hpos, hpr⟩

/-- **The joint induction** (D29): the claim at every relative stage `M ≥ 2`. -/
theorem joint_all {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
    {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o : ℕ} {c : Chart} {m : ℝ} {pA : ℝ → ℂ}
    (hJ : JointIn κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o c m pA) :
    ∀ M, 2 ≤ M → JointQ κ θ b₁ J₁ b₂ J₂ D₁ D₂ β₀ γ tL o c m M := by
  classical
  obtain ⟨hR, ho, hP₁, hW₁, hlm₁, hlh₁, hallow, hexit₁, hdoneL, hpinv, hpc, hp0, hpH, hpv, hcdom, hcN, hcbd, hcU,
    hβp, hβ0, hβr, hS1, hS3, hγ, hhull, hheadR, htail, hray, hlcd, hι, hcont, hS, hreg₂, hroot, hgen, hgd⟩ := hJ
  subst hR
  -- the actual walk's completion and the global bounds
  obtain ⟨Md, hMd, hmin⟩ := exists_first_done (κ := κ) (b := b₁) (jumps := J₁) (θ := θ) (D := D₁) ⟨_, hdoneL⟩
  have hML : Md ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length := by
    by_contra h; push Not at h; exact hmin _ h hdoneL
  have hnd1 : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≠ stDone := by
    rcases hS with hA | ⟨hPV, hfin⟩
    · exact Mn.notDone_of_arcStart hA
    · exact Mn.notDone_of_pieceStart hPV hfin
  have hoM : o + 1 < Md := by
    by_contra h; push Not at h; exact hnd1 (done_of_le hMd h)
  have hfinMd : ∀ j, j + 1 < Md →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤ :=
    fun j hj hl => fin_before_first_done hmin j hj hl
  have hnz : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0 := by
    rcases hS with hA | ⟨hPV, -⟩
    · exact hA.nz₁
    · exact fun k hk => hPV.nz₁ k (by omega)
  obtain ⟨N₀, hN₀o⟩ : ∃ N₀, N₀ + o = Md := ⟨Md - o, by omega⟩
  have h2N₀ : 2 ≤ N₀ := by omega
  have hfin₀ : ∀ j, j + 1 < N₀ + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤ :=
    fun j hj hl => hfinMd j (by omega) hl
  have hN₀₁ : N₀ + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length := by omega
  have hflow := Mn.flowSt_of_start hP₁ hlm₁ hlh₁ hfin₀ hN₀₁ h2N₀ ho hnz hS
  have hcontS := Mn.contSt_of_start hP₁ hlm₁ hlh₁ hfin₀ hN₀₁ ho hnz hS
  have hrp := recInv_ptRec_run_le hP₁ (N := Md - 1) (fun j hj hl => hfinMd j (by omega) hl) hlm₁ hlh₁
  have hrec : ∀ k, k < Md → RecInv κ b₁ J₁ θ D₁ k := fun k hk => (hrp k (by omega)).1
  have hWall : ∀ k, k < Md → WalkMovesRight κ b₁ J₁ θ D₁ k := fun k hk =>
    walkMovesRight_of_ptRec D₁ (hrp k (by omega)).2 (hlm₁ k)
  have hq0 := Mn.q0_of_start hMd hoM.le hP₁ hlm₁ hlh₁ (fun j hj hl => hfinMd j (by omega) hl) hS
  have hcount := Mn.first_done_le hP₁ hrec hWall hMd hmin hML ho
    (fun k h1 h2 h3 => hflow k (by omega) (by omega) h3) (fun k h1 h2 h3 => hcontS k (by omega) (by omega) h3) hq0
  have hlen₂ : N₀ ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length := Mn.len_rel hι (o := o) (by omega)
  -- the upper chart
  obtain ⟨ĝ, Cg, hĝ, hCg⟩ := hcbd
  have hcc : c.IsConformal := hcdom.1
  have hDom : c.2.1 '' H = H \ fillH (pA '' Icc 0 1) := hcdom.2.1
  obtain ⟨hcH, hc1, hoff⟩ := hcU
  have hcU : UpperChartOK c := ⟨hcH, hc1, hoff⟩
  have hcH' : ∀ w ∈ H, c.2.1 w ∈ H := fun w hw => hcc.2.1 hw
  have hβL : β₀ tL = realMax (pA '' Icc 0 1) := hγ.1
  -- the induction
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro h2M
  have hreg_lt : ∀ k < M, ∀ (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k + 1)).2.2.2.1 k = some (c', θ') →
      GW1P.PieceRegular (D₂ k).1 (min (instrTime (boundaryWalkSpec b₂ J₂ θ true) k) (D₂ k).2) := by
    intro k hk c' θ' hl
    have hl' : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k + 1)).2.2.2.1 k ≠ none := by
      rw [hl]; simp
    rw [GW1W.instrTime_walk hl', min_eq_right le_top]
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain ⟨hev, -⟩ := GW1W.even_of_launches_walk hl'
      obtain rfl : k = 0 := by omega
      exact hroot hl'
    · obtain ⟨-, -, hra, hfa⟩ := ih k hk hk2
      exact (hfa (hra hl')).2.2
  have hlock : ∀ N, 2 ≤ N → N ≤ M → N + o ≤ Md →
      LockAt κ θ b₁ J₁ b₂ J₂ (realMax (pA '' Icc 0 1)) ι D₁ D₂ β₀ γ tL o N ∨
        (stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) = stDone ∧
          stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) = stDone) :=
    fun N h2 hNM hNd => lockAt_upto hι hcont h2 hS hreg₂ (fun k hk => hreg_lt k (by omega)) hP₁
      (fun j hj hl => hfinMd j (by omega) hl) hlm₁ hlh₁ hallow hexit₁ (fun i hi hiN => (ih i (by omega) hi).1)
      (fun i hi hiN => ⟨by omega, by omega⟩) (by omega) hβr hβp.2.1 hβL hlcd.zero hheadR htail hray hW₁ hβp
      hγ.2.1 hlcd hβ0 (fun i hi hiN => (ih i (by omega) hi).2.1)
  by_cases hA : M + o < Md
  · obtain lk : LockAt κ θ b₁ J₁ b₂ J₂ (realMax (pA '' Icc 0 1)) ι D₁ D₂ β₀ γ tL o M := by
      rcases hlock M h2M le_rfl hA.le with lk | ⟨h1, -⟩
      · exact lk
      · exact absurd h1 (hmin _ (by omega))
    rcases Nat.mod_two_eq_zero_or_one M with hev | hodd
    · have hk₁ : M + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length := by omega
      have hk₂ : M < (boundaryWalkSpec b₂ J₂ θ true).2.2.length := by omega
      have hev₁ : (M + o) % 2 = 0 := by omega
      have hfl := hflow (M + o) (by omega) (by omega) hev₁
      have hcM := lk.corr M h2M le_rfl
      have hrelact : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (M + 1)).2.2.2.1 M ≠ none →
          (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠ none :=
        fun hl₂ => launched_of_corr_rel hι le_rfl hcM hk₁ hk₂ hev₁ hev hfl hl₂
      have hfacts : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠ none →
          ActFacts κ θ b₁ J₁ b₂ J₂ D₁ D₂ o c m M := by
        intro hl₁
        obtain ⟨hst₁, -⟩ := Mn.arcM_of_flowSt_launch hk₁ hev₁ hfl hl₁
        have hRlt : realMax (pA '' Icc 0 1) <
            stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) := by
          rcases hfl with ⟨-, h⟩ | hd | hd
          · exact h
          · rw [hd] at hst₁; cases hst₁
          · rw [hd] at hst₁; cases hst₁
        have hpos := hnz (M + o) (by omega) hl₁
        have hstat₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) = GW1W.stArcM true :=
          hcM.2.1.trans hst₁
        have hnd₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) ≠ stDone := by
          rw [hstat₂]; exact fun h => by cases h
        obtain ⟨h₁, hc₁N, hB₂, hcH₂, hc1₂, hc₂⟩ := relChart_facts_of_lt hreg_lt hnd₂
        obtain ⟨C₂, hC₂⟩ := relChart_bound_of_lt (b := b₂) (jumps := J₂) (θ := θ) (D := D₂) (n := M) hreg_lt
        have hfin₂ : ∀ j, j < M →
            (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
            (D₂ j).2 ≠ ⊤ := fun j hj hl =>
          fin_of_not_done (fun hd => hnd₂ (done_of_le hd (by omega))) hl
        obtain ⟨hz₀, hcw₀⟩ := zero_cont_of_lt hreg_lt hfin₂ lk.lm₂ lk.lh₂ hk₂.le hstat₂
        have hpt₂ : stPt (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) =
            ι (stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o))) := by
          rw [hcM.1, max_eq_left hRlt.le]
        have hw₀ : ∀ s, β₀ (tL + s) =
            ((stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) : ℝ) : ℂ) →
            γ s = ((stPt (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) : ℝ) : ℂ) :=
          fun s h => by rw [hpt₂]; exact hray s _ hRlt h
        have hRmem : (realMax (pA '' Icc 0 1) : ℂ) ∈
            statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) := by
          have h := WalkIntRunChron.prefixPhysSet_mono _ D₁ (show 2 + o ≤ M + o by omega) lk.memR
          rw [hβL] at h; exact h
        have hpinvM := hpinv (M + o) (fun hd => hmin _ hA hd)
        have hfill : fillH (SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) =
            fillH (liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o))) := by
          rw [lk.pre]
        obtain ⟨he₂, hg⟩ := hgen M h2M hl₁ hpos
        by_cases htop : (D₁ (M + o)).2 = ⊤
        · obtain ⟨hdr, hinf, htrρ, htopρ⟩ := stageInf_walk hP₁ hW₁ hlm₁ hlh₁ hl₁ hpos htop hpinvM hpc hp0 hpH hpv
            hβp hβ0 hβr hS1 hRmem hS3 hcdom hcN hĝ hCg hcH hc1 hcH' hoff hDom hγ hhull (hgd M h2M hl₁) h₁ hc₁N
            hfill hB₂ hC₂ hcH₂ hc1₂ hc₂ hw₀ hcw₀ hz₀ he₂ (hreg₂ M)
          have hrel : StageRelP c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o))
              (D₁ (M + o))) (D₁ (M + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) (D₂ M) :=
            ⟨fun h => absurd htop h, fun _ => hinf⟩
          exact ⟨hdr, hrel, pieceRegular_of_stageRelP hrel he₂ hg (hreg₂ M).2.1
            (fun _ _ => tendsto_norm_capTrace hdr htopρ htrρ)⟩
        · obtain ⟨hdr, hfinP⟩ := stageFin_walk hP₁ hW₁ hlm₁ hlh₁ hl₁ hpos htop hpinvM hpc hp0 hpH hpv hβp hβ0 hβr
            hS1 hRmem hcdom hcN hĝ hCg hcH hc1 hcH' hoff hDom hγ hhull (hgd M h2M hl₁) h₁ hc₁N hfill hB₂ hcH₂ hc1₂
            hc₂ hw₀ hcw₀ hz₀ he₂ hg (hreg₂ M)
          have hrel : StageRelP c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o))
              (D₁ (M + o))) (D₁ (M + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) (D₂ M) :=
            ⟨fun _ => hfinP, fun h => absurd h htop⟩
          exact ⟨hdr, hrel, pieceRegular_of_stageRelP hrel he₂ hg (hreg₂ M).2.1 (fun h => absurd h htop)⟩
      refine ⟨fun _ hst hadm => ?_, fun hl₁ _ hfin => ?_, hrelact, hfacts⟩
      · have hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠ none := by
          rw [launched_of_admissible hk₁ hev₁ hst hadm]; simp
        obtain ⟨hdr, hrel, -⟩ := hfacts hl₁
        have hpos := hnz (M + o) (by omega) hl₁
        obtain ⟨he₂, hg⟩ := hgen M h2M hl₁ hpos
        exact liftRel_of_stage3 hγ hcc hcU hDom hhull hβp hβr hP₁ hl₁ hpos (hgd M h2M hl₁) hrel hdr he₂ hg
          (hreg₂ M).2.1
      · obtain ⟨hdr, hrel, hpr⟩ := hfacts hl₁
        have hpos := hnz (M + o) (by omega) hl₁
        obtain ⟨he₂, hg⟩ := hgen M h2M hl₁ hpos
        exact Mn.trLift_of_facts hγ hβp hcU hhull hDom hβr hP₁ hl₁ hfin hpos
          (stageFacts_of_act hdr hrel hpr he₂ hg (hgd M h2M hl₁) hpos)
    · refine ⟨fun h => absurd (of_decide_eq_true h) (by omega), fun hl₁ => ?_, fun hl₂ => ?_, fun hl₁ => ?_⟩
      · exact absurd (GW1W.even_of_launches_walk hl₁).1 (by omega)
      · exact absurd (GW1W.even_of_launches_walk hl₂).1 (by omega)
      · exact absurd (GW1W.even_of_launches_walk hl₁).1 (by omega)
  · -- past the actual walk's completion both walks are done
    have hdM : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) = stDone :=
      done_of_le hMd (by omega)
    have hdM₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) = stDone := by
      rcases hlock N₀ h2N₀ (by omega) (by omega) with lk | ⟨-, h2⟩
      · exact done_of_le ((lk.corr N₀ h2N₀ le_rfl).2.1.trans (by rw [hN₀o]; exact hMd)) (by omega)
      · exact done_of_le h2 h2M
    refine ⟨fun _ hst _ => ?_, fun hl₁ => ?_, fun hl₂ => ?_, fun hl₁ => ?_⟩
    · rw [hdM] at hst; cases hst
    · exfalso
      obtain ⟨⟨c', θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl₁
      exact WalkIntRunChron.not_done_of_launch _ D₁ hl' hdM
    · exfalso
      obtain ⟨⟨c', θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl₂
      exact WalkIntRunChron.not_done_of_launch _ D₂ hl' hdM₂
    · exfalso
      obtain ⟨⟨c', θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl₁
      exact WalkIntRunChron.not_done_of_launch _ D₁ hl' hdM

/-- **The per-stage facts at every launching relative stage `j ≥ 2` of positive lifetime** (the `j ≥ 2` part of
`Mn.StageFactsAll`, unshifted). -/
theorem joint_stageFacts {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
    {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o : ℕ} {c : Chart} {m : ℝ} {pA : ℝ → ℂ}
    (hJ : JointIn κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o c m pA) :
    ∀ j, 2 ≤ j → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
      Mn.StageFacts c m (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)) (D₁ (j + o)) 0
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j) (D₂ j) := by
  intro j hj hl₂
  obtain ⟨-, -, hra, hfa⟩ := joint_all hJ j hj
  have hl₁ := hra hl₂
  obtain ⟨hdr, hrel, hpr⟩ := hfa hl₁
  have hpos : (D₁ (j + o)).2 ≠ 0 := by
    rcases hJ.start with hA | ⟨hPV, -⟩
    · exact hA.nz₁ _ (by omega) hl₁
    · exact hPV.nz₁ _ (by omega) hl₁
  obtain ⟨he₂, hg⟩ := hJ.gen j hj hl₁ hpos
  exact stageFacts_of_act hdr hrel hpr he₂ hg (hJ.gd j hj hl₁) hpos

/-- **Drivenness and `StageRelP` at every actual launch at `i + o`, `i ≥ 2`** (the `j ≥ 2` part of
`StagesGeom4`). -/
theorem joint_stageRelP {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
    {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o : ℕ} {c : Chart} {m : ℝ} {pA : ℝ → ℂ}
    (hJ : JointIn κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o c m pA) :
    ∀ i, 2 ≤ i → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      IsDrivenCurve (stCurvep c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (D₁ (i + o))) (D₁ (i + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i)) ∧
      StageRelP c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o)) (D₁ (i + o)))
        (D₁ (i + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₂ i) := fun i hi hl => by
  obtain ⟨hdr, hrel, -⟩ := (joint_all hJ i hi).2.2.2 hl
  exact ⟨hdr, hrel⟩

/-- **At an infinite start piece no stage `j ≥ 2` launches** (relative or actual): both walks are done after the start
piece. -/
theorem joint_top_vacuous {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
    {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o : ℕ} (hPV : PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o)
    (htop : (D₁ o).2 = ⊤) :
    (∀ j, 1 ≤ j → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j = none) ∧
    ∀ i, 1 ≤ i → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) = none := by
  have h2top : (D₂ 0).2 = ⊤ := hPV.top.2 htop
  have hdone1 : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) = stDone := by
    rw [run_one_walk]
    exact (launch_eq_of_top _ 0 (D₂ 0) θ ⊤ (by rw [h2top, min_self])).2.2.2.2.1
  have hdoneA : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) = stDone := by
    rw [hPV.launch]
    exact (launch_eq_of_top _ o (D₁ o) θ ⊤ (by rw [htop, min_self])).2.2.2.2.1
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · by_contra hl
    obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
    exact WalkIntRunChron.not_done_of_launch _ D₂ hl' (done_of_le hdone1 hj)
  · by_contra hl
    obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
    exact WalkIntRunChron.not_done_of_launch _ D₁ hl' (done_of_le hdoneA (by omega))

end InteractingSLE.Theorem14.SB.Lk
