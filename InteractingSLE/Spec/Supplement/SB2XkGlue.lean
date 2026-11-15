/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XiPrefix

/-!
# Sample-level glue for (G1): the relative prefix at a launching stage is the lift image of B's prefix

Packet PROVE-T14-SB2LIFT (round 26). The identity `prefix_lift_of_steps` (round 25) at the launching relative stages
`j ≥ 2`, from the lift data of `range_eq_physSet_of_lifts_*` (the round-23 lockstep, `l1_fillCorr_of_lifts`,
`stCorr_run_strong2`; the start states' lift identity as in `SB2XbRange`):

* **`prefix_lift_of_lifts_arc`**, **`prefix_lift_of_lifts_piece`**;
* **`prefix_lift_of_bundles''`**: at one sample with the bundle of `RelDriverAt''`, for every relative stage `j ≥ 2`
  that launches, `prefixPhysSet₂ j = liftImage β₀ t_L γ (prefixPhysSet₁ (j + o))`.
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

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The relative prefix as a lift image at the launching lockstep stages, starting on an actual connector.** -/
theorem prefix_lift_of_lifts_arc (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
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
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (_hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
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
    ∀ j, 2 ≤ j → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
      SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j =
        liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)) := by
  rcases flowSt_after_arc hn ho hmove hgap with hdone | ⟨hs₀, hp₀⟩
  · intro j hj hl
    exfalso
    have hc0 := (stCorr_start_arc (κ := κ) (θ := θ) hι hn (by omega) hmove hθ hpt hrec hgap hlow (hreg₂ 0) h0).1
    rw [show o + 1 + 1 = 2 + o by omega] at hc0
    obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
    apply WalkIntRunChron.not_done_of_launch _ D₂ hl'
    exact done_of_le (hc0.2.1.trans hdone) hj
  · obtain ⟨hinv₀, hlm₂₀, hlh₂₀, hfin₂₀⟩ := relStart_arc hι hP₂ (hreg₂ 0) h0 hlow
    obtain ⟨a, hRa, hc, hS₁, hS₂⟩ := start_arc_phys (κ := κ) (θ := θ) (D₁ := D₁) (D₂ := D₂) hι hn (by omega)
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
      exact (liftImage_start_arc hβ hβL hγ0 hι.map_base hhead htail hray hP₀ hRa
        fun x hx _ => hsubS (Or.inr ⟨x, hx, rfl⟩)).symm
    have hRmem : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o) := by
      rw [hβL]
      show (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))
      rw [e, hS₁]
      exact Or.inr ⟨R, hRa, rfl⟩
    have hLF := l1_fillCorr_of_lifts hι hcont hP₁ hP₂ hreg₂ o 2 2 N le_rfl h2N hfin₁ hfin₂₀ hlm₁ hlh₁ hlm₂₀
      hlh₂₀ hinv₀ hallow hexit₁ ho (by norm_num) hlen hN₁ hnz₁ hp₀ hs₀ h₀ hW₁ hβp hγp hD hβr hβ0 hhead htail
      hRmem h₀ hstart (fun i h1 h2 => absurd h2 (by omega)) hpc htr
    have hSf := stCorr_run_strong2 hι hcont le_rfl hP₁ hP₂ hreg₂ o 2 N hfin₁ hfin₂₀ hlm₁ hlh₁ hlm₂₀ hlh₂₀ hinv₀
      hallow hexit₁ ho (by norm_num) hlen hN₁ hnz₁ hp₀ hs₀ h₀ hLF.1 hLF.2 N h2N le_rfl
    intro j hj hl
    have hl₁ := actual_launch_of_corr hι h2N ho hSf.1
      (fun j hj hjN hev => (status_run_le hP₁ (2 + o) (N + o) hfin₁ hlm₁ hlh₁ hN₁ (by omega) hnz₁ hp₀ hs₀ (j + o)
        (by omega) (by omega)).2.1 hev)
      (fun j hj hjN => (hlen j hj hjN).1) hd j hj hl
    have hjN : j < N := by
      by_contra hjN
      obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl₁
      exact WalkIntRunChron.not_done_of_launch _ D₁ hl' (done_of_le hd (by omega))
    exact prefix_lift_of_steps hι ho (fun i h1 h2 => hlen i h1 (by omega)) h₀
      (fun i h1 h2 _ => ⟨hSf.2.1 i h1 (by omega), hpc i h1 (by omega)⟩) hj
      (by have := (hlen j hj hjN).1; omega) hstart hβr hβ hβL hγ0 hhead htail hray

/-- **The relative prefix as a lift image at the launching lockstep stages, starting on an actual piece.** -/

theorem prefix_lift_of_lifts_piece (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
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
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (_hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
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
    ∀ j, 2 ≤ j → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
      SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j =
        liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)) := by
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
  have hLF := l1_fillCorr_of_lifts hι hcont hP₁ hP₂ hreg₂ o 1 2 N (by norm_num) h2N hfin₁ hfin₂₀ hlm₁ hlh₁
    hlm₂₀ hlh₂₀ hinv₀ hallow hexit₁ ho (by norm_num) hlen hN₁ (fun k hk => hnz₁ k (by omega)) hp₀ hs₀ h₀ hW₁
    hβp hγp hD hβr hβ0 hhead htail hRmem' hca₀ hstart hpre hpc htr
  have hSf := stCorr_run_strong2 hι hcont le_rfl hP₁ hP₂ hreg₂ o 2 N hfin₁ hfin₂₀ hlm₁ hlh₁ hlm₂₀ hlh₂₀ hinv₀
    hallow hexit₁ ho (by norm_num) (fun i hi hiN => hlen i (by omega) hiN) hN₁ (fun k hk => hnz₁ k (by omega))
    hp₀ hs₀ h₀ hLF.1 hLF.2 N h2N le_rfl
  intro j hj hl
  have hl₁ := actual_launch_of_corr hι h2N ho hSf.1
    (fun j hj hjN hev => (status_run_le hP₁ (2 + o) (N + o) hfin₁ hlm₁ hlh₁ hN₁ (by omega)
      (fun k hk => hnz₁ k (by omega)) hp₀ hs₀ (j + o) (by omega) (by omega)).2.1 hev)
    (fun j hj hjN => (hlen j (by omega) hjN).1) hd j hj hl
  have hjN : j < N := by
    by_contra hjN
    obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl₁
    exact WalkIntRunChron.not_done_of_launch _ D₁ hl' (done_of_le hd (by omega))
  refine prefix_lift_of_steps hι ho (fun i h1 h2 => hlen i h1 (by omega)) hca₀ (fun i h1 h2 hci => ?_) (by omega)
    (by have := (hlen j (by omega) hjN).1; omega) hstart hβr hβ hβL hγ0 hhead htail hray
  rcases Nat.lt_or_ge i 2 with hi | hi
  · exact hpre i h1 hi hci
  · exact ⟨hSf.2.1 i hi (by omega), hpc i hi (by omega)⟩

variable {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}

/-- **The relative prefix at every launching stage `j ≥ 2` is the lift image of B's prefix**, at one sample with the
bundle of `RelDriverAt''`. -/
theorem prefix_lift_of_bundles'' (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputs κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hR : RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none →
        (D₁ k).2 ≠ ⊤ → (D₁ k).2 ≠ 0 →
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧ lHit (stChart (ExplState.run
          κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ) (hβ0 : β₀ 0 = 0)
    (hD : LiftCurveData β₀ γ tL R ι)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) :
    ∀ j, 2 ≤ j → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
      SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j =
        liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)) := by
  intro j hj hl
  rcases hS with hA | hPV
  · exact prefix_lift_of_lifts_arc hι hR.cont hA.even hA.len hA.move hA.angle hA.pt hA.recLe hA.gap hA.low
      hreg₂ hA.zero₀ hP₁ hR.reg₂ hR.fin₁ hlm₁ hlh₁ hallow hexit₁ hA.nz₁ hR.piece hR.two_le hR.len hR.len₁ hR.len₂
      hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail hC.ray hA.head hW₁ hβp hγp hD hβ0
      hR.trLift j hj hl
  · have hlen' : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
        i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length := by
      intro i hi hiN
      rcases eq_or_lt_of_le hi with h1 | h2
      · subst h1
        exact ⟨by have := hPV.len.1; omega, hPV.len.2⟩
      · exact hR.len i h2 hiN
    by_cases htop : (D₁ o).2 = ⊤
    · exfalso
      have h2top : (D₂ 0).2 = ⊤ := hPV.top.2 htop
      have hdone1 : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) = stDone := by
        rw [run_one_walk]
        exact (launch_eq_of_top _ 0 (D₂ 0) θ ⊤ (by rw [h2top, min_self])).2.2.2.2.1
      obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
      exact WalkIntRunChron.not_done_of_launch _ D₂ hl' (done_of_le hdone1 (by omega))
    have hP := hPV.toPieceStart htop
    exact prefix_lift_of_lifts_piece hι hR.cont hP.even hP.launch hP.tip hP.pt hP.recLe hP.top hP.zero
      hP.hitR hP.hitL₂ hP.recR hP.lift₀ hP.memR hP.recAfter hreg₂ hP₁ hR.reg₂ hR.fin₁ hlm₁ hlh₁ hallow hexit₁
      hP.nz₁ hR.piece hR.two_le hlen' hR.len₁ hR.len₂ hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head
      hC.tail hC.ray hP.head hW₁ hβp hγp hD hβ0 hR.trLift j hj hl

end InteractingSLE.Theorem14.SB.Lk
