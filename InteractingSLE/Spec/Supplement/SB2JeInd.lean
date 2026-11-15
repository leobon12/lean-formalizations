/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JeCore

/-!
# SB2(2)'s joint stage induction under GEOM2's v6 rule

Packet PROVE-SB2-LIFTSET (round 21). Under the v6 rule the relative driver of a stage generates its stage curve only
on the mask: besides a non-zero launched actual instruction, the earlier launched relative records with finite stop
are good (`RecGoodAt`) and the stage's readings in the relative chart are dense (`DenseAt`). **`JointIn6`** is
`JointIn` with the generation asked only below a stage `N` and only under these two conditions, and with the relative
root's record good. **`joint6_all`**: by strong induction, at every relative stage `2 ≤ M ≤ N`,

* below `N`: the claim `JointQ M` of `joint_all`, and at an actual launch the mask's conditions `RecGoodAt M`,
  `DenseAt M` (record goodness from the earlier `StageRelP`, `isDrvGood_of_continuousOn_le`; dense readings from the
  generation-free core `stageCore_walk`);
* at every `M ≤ N`: drivenness of the run-chart stage curve at an actual launch of positive lifetime, from the earlier
  stages only (`stageCore_walk`) — the admissibility of GEOM2's v6 rule.
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

/-- **The earlier launched relative records with finite stop are good** (GEOM2's `Nv.recGoodEv` at one sample). -/
def RecGoodAt (κ θ : ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (D₂ : ℕ → Drv) (j : ℕ) : Prop :=
  ∀ i < j, (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
    min (instrTime (boundaryWalkSpec b₂ J₂ θ true) i) (D₂ i).2 ≠ ⊤ →
    LocalExt.IsDrvGood (recHist (recOf (instrTime (boundaryWalkSpec b₂ J₂ θ true) i) (D₂ i)))

/-- **The readings of stage `j` in the relative chart are dense** (GEOM2's `Nv.denseEv` at one sample, unshifted). -/
def DenseAt (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (D₁ D₂ : ℕ → Drv) (o : ℕ)
    (c : Chart) (m : ℝ) (j : ℕ) : Prop :=
  Nv.DenseReads c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)) (D₁ (j + o)))
    (D₁ (j + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)

/-- **The per-sample inputs of the joint induction under the v6 rule** (generation below `N`, on the mask). -/
structure JointIn6 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
    (D₁ D₂ : ℕ → Drv) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o : ℕ) (c : Chart) (m : ℝ) (pA : ℝ → ℂ)
    (N : ℕ) : Prop where
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
  rootGood : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1).2.2.2.1 0 ≠ none → (D₂ 0).2 ≠ ⊤ →
    LocalExt.IsDrvGood (recHist (recOf ⊤ (D₂ 0)))
  gen : ∀ j, 2 ≤ j → j < N →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o + 1)).2.2.2.1 (j + o) ≠ none →
    (D₁ (j + o)).2 ≠ 0 → RecGoodAt κ θ b₂ J₂ D₂ j → DenseAt κ θ b₁ J₁ b₂ J₂ D₁ D₂ o c m j →
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


/-- **The v6 induction claim at stage `M`.** -/
def JointQ6 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (D₁ D₂ : ℕ → Drv)
    (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o : ℕ) (c : Chart) (m : ℝ) (N M : ℕ) : Prop :=
  (M < N → JointQ κ θ b₁ J₁ b₂ J₂ D₁ D₂ β₀ γ tL o c m M ∧
    ((ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠ none →
      RecGoodAt κ θ b₂ J₂ D₂ M ∧ DenseAt κ θ b₁ J₁ b₂ J₂ D₁ D₂ o c m M)) ∧
  ((ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠ none →
    (D₁ (M + o)).2 ≠ 0 →
    IsDrivenCurve (stCurvep c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o))
      (D₁ (M + o))) (D₁ (M + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M)))

/-- **The joint induction under the v6 rule**, at every relative stage `2 ≤ M ≤ N`. -/
theorem joint6_all {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
    {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o : ℕ} {c : Chart} {m : ℝ} {pA : ℝ → ℂ} {N : ℕ}
    (hJ : JointIn6 κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o c m pA N) :
    ∀ M, 2 ≤ M → M ≤ N → JointQ6 κ θ b₁ J₁ b₂ J₂ D₁ D₂ β₀ γ tL o c m N M := by
  classical
  obtain ⟨hR, ho, hP₁, hW₁, hlm₁, hlh₁, hallow, hexit₁, hdoneL, hpinv, hpc, hp0, hpH, hpv, hcdom, hcN, hcbd, hcU,
    hβp, hβ0, hβr, hS1, hS3, hγ, hhull, hheadR, htail, hray, hlcd, hι, hcont, hS, hreg₂, hroot, hrootG, hgen, hgd⟩ :=
    hJ
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
  intro h2M hMN
  have ihQ : ∀ i < M, 2 ≤ i → JointQ κ θ b₁ J₁ b₂ J₂ D₁ D₂ β₀ γ tL o c m i := fun i hi h2 =>
    ((ih i hi h2 (by omega)).1 (by omega)).1
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
    · obtain ⟨-, -, hra, hfa⟩ := ihQ k hk hk2
      exact (hfa (hra hl')).2.2
  have hlock : ∀ N, 2 ≤ N → N ≤ M → N + o ≤ Md →
      LockAt κ θ b₁ J₁ b₂ J₂ (realMax (pA '' Icc 0 1)) ι D₁ D₂ β₀ γ tL o N ∨
        (stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) = stDone ∧
          stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) = stDone) :=
    fun N h2 hNM hNd => lockAt_upto hι hcont h2 hS hreg₂ (fun k hk => hreg_lt k (by omega)) hP₁
      (fun j hj hl => hfinMd j (by omega) hl) hlm₁ hlh₁ hallow hexit₁ (fun i hi hiN => (ihQ i (by omega) hi).1)
      (fun i hi hiN => ⟨by omega, by omega⟩) (by omega) hβr hβp.2.1 hβL hlcd.zero hheadR htail hray hW₁ hβp
      hγ.2.1 hlcd hβ0 (fun i hi hiN => (ihQ i (by omega) hi).2.1)
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
      have hfacts6 : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠
          none → IsDrivenCurve (stCurvep c m (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o))
            (D₁ (M + o))) (D₁ (M + o)).2 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M)) ∧
          DenseAt κ θ b₁ J₁ b₂ J₂ D₁ D₂ o c m M ∧ RecGoodAt κ θ b₂ J₂ D₂ M ∧
          (M < N → ActFacts κ θ b₁ J₁ b₂ J₂ D₁ D₂ o c m M) := by
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
        obtain ⟨hdr0, -, hdense⟩ := stageCore_walk hP₁ hW₁ hlm₁ hlh₁ hl₁ hpos hpinvM hpc hp0 hpH hpv hβp hβ0 hβr
          hS1 hRmem hS3 hcdom hcN hĝ hCg hcH hc1 hcH' hoff hDom hγ hhull (hgd M h2M hl₁) h₁ hc₁N hfill hw₀ hcw₀ hz₀
        have hrg : RecGoodAt κ θ b₂ J₂ D₂ M := by
          intro i hi hl hfin
          rcases Nat.lt_or_ge i 2 with hi2 | hi2
          · obtain ⟨hev', -⟩ := GW1W.even_of_launches_walk hl
            obtain rfl : i = 0 := by omega
            rw [GW1W.instrTime_walk hl] at hfin ⊢
            exact hrootG hl (by rwa [min_eq_right le_top] at hfin)
          · obtain ⟨-, -, hra, hfa⟩ := ihQ i hi hi2
            obtain ⟨-, hrel, -⟩ := hfa (hra hl)
            refine isDrvGood_of_continuousOn_le (hreg₂ i) hfin ?_
            rw [GW1W.instrTime_walk hl, min_eq_right le_top]
            by_cases hL : (D₁ (i + o)).2 = ⊤
            · exact (hrel.2 hL).1
            · exact (hrel.1 hL).2.1
        refine ⟨hdr0, hdense, hrg, fun hMN' => ?_⟩
        obtain ⟨he₂, hg⟩ := hgen M h2M hMN' hl₁ hpos hrg hdense
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
      have hfacts : M < N →
          (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠ none →
          ActFacts κ θ b₁ J₁ b₂ J₂ D₁ D₂ o c m M := fun hMN' hl₁ => (hfacts6 hl₁).2.2.2 hMN'
      refine ⟨fun hMN' => ⟨⟨fun _ hst hadm => ?_, fun hl₁ _ hfin => ?_, hrelact, hfacts hMN'⟩,
        fun hl₁ => ⟨(hfacts6 hl₁).2.2.1, (hfacts6 hl₁).2.1⟩⟩, fun hl₁ _ => (hfacts6 hl₁).1⟩
      · have hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠ none := by
          rw [launched_of_admissible hk₁ hev₁ hst hadm]; simp
        obtain ⟨hdr, hrel, -⟩ := hfacts hMN' hl₁
        have hpos := hnz (M + o) (by omega) hl₁
        obtain ⟨-, hdense, hrg, -⟩ := hfacts6 hl₁
        obtain ⟨he₂, hg⟩ := hgen M h2M hMN' hl₁ hpos hrg hdense
        exact liftRel_of_stage3 hγ hcc hcU hDom hhull hβp hβr hP₁ hl₁ hpos (hgd M h2M hl₁) hrel hdr he₂ hg
          (hreg₂ M).2.1
      · obtain ⟨hdr, hrel, hpr⟩ := hfacts hMN' hl₁
        have hpos := hnz (M + o) (by omega) hl₁
        obtain ⟨-, hdense, hrg, -⟩ := hfacts6 hl₁
        obtain ⟨he₂, hg⟩ := hgen M h2M hMN' hl₁ hpos hrg hdense
        exact Mn.trLift_of_facts hγ hβp hcU hhull hDom hβr hP₁ hl₁ hfin hpos
          (stageFacts_of_act hdr hrel hpr he₂ hg (hgd M h2M hl₁) hpos)
    · refine ⟨fun _ => ⟨⟨fun h => absurd (of_decide_eq_true h) (by omega), fun hl₁ => ?_, fun hl₂ => ?_,
        fun hl₁ => ?_⟩, fun hl₁ => ?_⟩, fun hl₁ => ?_⟩
      · exact absurd (GW1W.even_of_launches_walk hl₁).1 (by omega)
      · exact absurd (GW1W.even_of_launches_walk hl₂).1 (by omega)
      · exact absurd (GW1W.even_of_launches_walk hl₁).1 (by omega)
      · exact absurd (GW1W.even_of_launches_walk hl₁).1 (by omega)
      · exact absurd (GW1W.even_of_launches_walk hl₁).1 (by omega)
  · -- past the actual walk's completion both walks are done
    have hdM : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) = stDone :=
      done_of_le hMd (by omega)
    have hdM₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) = stDone := by
      rcases hlock N₀ h2N₀ (by omega) (by omega) with lk | ⟨-, h2⟩
      · exact done_of_le ((lk.corr N₀ h2N₀ le_rfl).2.1.trans (by rw [hN₀o]; exact hMd)) (by omega)
      · exact done_of_le h2 h2M
    have hnl : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠ none →
        False := fun hl₁ => by
      obtain ⟨⟨c', θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl₁
      exact WalkIntRunChron.not_done_of_launch _ D₁ hl' hdM
    refine ⟨fun _ => ⟨⟨fun _ hst _ => ?_, fun hl₁ => ?_, fun hl₂ => ?_, fun hl₁ => ?_⟩,
      fun hl₁ => (hnl hl₁).elim⟩, fun hl₁ => (hnl hl₁).elim⟩
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

end InteractingSLE.Theorem14.SB.Lk
