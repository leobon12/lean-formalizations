/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JeConv

/-!
# SB2(2) under the v6 rule: one sample, every family

Packet PROVE-SB2-LIFTSET (round 21). **`sample_core6`** (deterministic, one sample): from the actual walk's and the
upper chart's facts at the sample, the root facts and the start-piece facts, for every relative family following the
v6 rule at the sample (`RootRule6`, `StageRule6` below `N`) with the start data at the sample (D40, the disjunction of
SB2LIFT's `startData_of0`):

* either the start piece is infinite and no stage `≥ 1` launches on either walk (`joint_top_vacuous`),
* or the joint induction's claim `JointQ6` holds at every stage `2 ≤ M ≤ N` (`joint6_all`, with the root's facts from
  `root_pkg` and the start disjunction from the start data).
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

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {c : Chart} {m : ℝ} {pA : ℝ → ℂ}

/-- **One sample, one family following the v6 rule**: the infinite start case, or the joint induction's claim at
every stage `2 ≤ M ≤ N`. -/
theorem sample_core6 {N : ℕ} (hR : R = realMax (pA '' Icc 0 1))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + relOff κ θ b₁ J₁ R D₁ ≤ k →
      AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + relOff κ θ b₁ J₁ R D₁ ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ ⊤ →
      (D₁ k).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hdoneL : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
      (boundaryWalkSpec b₁ J₁ θ true).2.2.length) = stDone)
    (hpinv : ∀ n, stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≠ stDone →
      LuM.PInv 0 (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n))
    (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im)
    (hpv : LuM.PInv 0 (pA '' Icc 0 1)) (hcdom : IsDomainChart (H \ fillH (pA '' Icc 0 1)) c)
    (hcN : WalkIntCanon.IsNormalized c)
    (hcbd : ∃ (ĝ : ℂ → ℂ) (C : ℝ), (∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) ∧ ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C)
    (hcU : UpperChartOK c) (hβp : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β₀)
    (hS3 : ∀ tR : ℝ≥0, β₀ tR = (R : ℂ) → ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H)
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hhull : β₀ '' Icc 0 tL ⊆ hullK (pA '' Icc 0 1))
    (hheadR : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R)
    (harc : ∀ n, ∀ a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n).2.1, a ⊆ Ici 0)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x) (hlcd : LiftCurveData β₀ γ tL R ι)
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
    (hgd : ∀ i, 2 ≤ i →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1
        (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
      {t : ℝ≥0 | (t : ℝ≥0∞) < (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2} ⊆
        closure (goodT c (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁))
          (D₁ (i + relOff κ θ b₁ J₁ R D₁))))
    (hRF : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R ≠ 0 →
      ∀ s₂ : ExplState, stChart s₂ = Chart.id.recenter 0 →
        IsDrivenCurve (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
          (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂) ∧
        ∀ e₂ : Drv, IsRegularDriver e₂ → e₂.2 = capLife (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁
            (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁
            (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂) →
          (∀ T < capLife (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
              (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
              (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂),
            IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
              (D₁ (relOff κ θ b₁ J₁ R D₁)) R) (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
              (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂))) →
          StageRelP c m (rootPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R)
              (rootLife (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R) s₂ e₂ ∧
            Mn.StageFacts c m (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
              (shiftD κ θ b₁ J₁ R D₁ 0) s₂ e₂)
    (hlaunch0 : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none)
    (hS0A : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
      (D₁ (relOff κ θ b₁ J₁ R D₁)).2 ≠ 0 →
      (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
      Stage0Act c m β₀ tL (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
        (fun t => pcPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
          (shiftD κ θ b₁ J₁ R D₁ 0 + t))
        ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0))
    (hcorner : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
      (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0 →
      ∀ e₂ : Drv, IsRegularDriver e₂ → e₂.2 = 0 →
        LiftRel β₀ tL γ (newPc (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)))
          (newPc (ExplState.init 0) e₂))
    (hS : (ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL (relOff κ θ b₁ J₁ R D₁) ∨
        (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) ∧
          (D₁ (relOff κ θ b₁ J₁ R D₁)).2 ≠ ⊤)) ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) ∧
        (D₁ (relOff κ θ b₁ J₁ R D₁)).2 = ⊤))
    (hreg₂ : ∀ j, IsRegularDriver (D₂ j)) (hroot : RootRule6 κ θ b₁ J₁ R c m D₁ D₂)
    (hstage : StageRule6 κ θ b₁ J₁ b₂ J₂ c m D₁ D₂ (relOff κ θ b₁ J₁ R D₁) N) :
    ((∀ j, 1 ≤ j → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j = none) ∧
      ∀ i, 1 ≤ i → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
        (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (i + relOff κ θ b₁ J₁ R D₁) = none) ∨
    ∀ M, 2 ≤ M → M ≤ N →
      JointQ6 κ θ b₁ J₁ b₂ J₂ D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) c m N M := by
  subst hR
  obtain ⟨ĝ, Cg, hĝ, hCg⟩ := hcbd
  have hO : IsOpen (c.2.1 '' H) := hcdom.1.isOpen_image
  obtain ⟨-, hpr, hgood, -, -⟩ := root_pkg (b₂ := b₂) (J₂ := J₂) hP₁ hcU.2.1 hO (hreg₂ 0) hroot.1 hroot.2 hRF
    hlaunch0 hS0A hcorner hγ hcU hcdom.2.1 hhull hβp hβr
  have htail : TailArc κ θ b₁ J₁ D₁ (realMax (pA '' Icc 0 1)) β₀ tL := by
    rcases hS with (hA | ⟨hV, -⟩) | ⟨hV, -⟩
    · exact tailArc_of_arcStart hβp hβr hγ.1 hheadR harc hP₁ hlm₁ hlh₁ hA
    · exact tailArc_of_pieceStart hβp hγ.1 harc hP₁ hlm₁ hlh₁ hV
    · exact tailArc_of_pieceStart hβp hγ.1 harc hP₁ hlm₁ hlh₁ hV
  have hJ : ∀ hS' : ArcStart κ θ b₁ J₁ (realMax (pA '' Icc 0 1)) D₁ D₂ β₀ tL
        (relOff κ θ b₁ J₁ (realMax (pA '' Icc 0 1)) D₁) ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ (realMax (pA '' Icc 0 1)) ι D₁ D₂ β₀ γ tL
        (relOff κ θ b₁ J₁ (realMax (pA '' Icc 0 1)) D₁) ∧
        (D₁ (relOff κ θ b₁ J₁ (realMax (pA '' Icc 0 1)) D₁)).2 ≠ ⊤),
      ∀ M, 2 ≤ M → M ≤ N →
        JointQ6 κ θ b₁ J₁ b₂ J₂ D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ (realMax (pA '' Icc 0 1)) D₁) c m N M :=
    fun hS' => joint6_all ⟨rfl, relOff_even _ _ _ _ _ _, hP₁, hW₁, hlm₁, hlh₁, hallow, hexit₁, hdoneL, hpinv,
      hpc, hp0, hpH, hpv, hcdom, hcN, ⟨ĝ, Cg, hĝ, hCg⟩, hcU, hβp, hβ0, hβr, hS1, hS3, hγ, hhull, hheadR, htail, hray,
      hlcd, hι, hcont, hS', hreg₂, fun _ => hpr, fun _ hfin => hgood hfin, hstage, hgd⟩
  rcases hS with (hA | hV) | ⟨hV, htop⟩
  · exact Or.inr (hJ (Or.inl hA))
  · exact Or.inr (hJ (Or.inr hV))
  · exact Or.inl (joint_top_vacuous hV htop)

end InteractingSLE.Theorem14.SB.Lk
