/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveRun
import InteractingSLE.Spec.Supplement.GW1ActiveChartL

/-!
# Lemma GW1's walks: one stage of the left walk (deterministic)

Packet PROVE-T14-GW1W. The mirror of `rInv_walk_step` for the left boundary walk (`boundaryWalkSpec b jumps θ false`):
from a launch-ready state with the left invariant `LInv`, the next launch is launch-ready with the invariant for the
recentred stop word, provided the piece has a good record at a finite stop, does not end at a new right record, and
leaves a high original height outward of a new left record.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (IsForwardSol chiC fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW1W

open Exist Exist.StagedLaw Exist.Staged Restart

section StageL

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- A flow step from a state on an arc at its mark (moving left) with an inadmissible seed changes nothing. -/
theorem flowStep_arcL_eq_self (s : ExplState) (k : ℕ) (D₀ : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (hst : stStatus s = .inr (.inr (.inr (.inl (false, true)))))
    (hna : ¬ ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) θ) :
    ExplState.flowStep κ b false s k D₀ θ t = s := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  change st = _ at hst
  subst hst
  simp only [ExplState.flowStep, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h
  · exact absurd h hna
  · rfl

/-- **The right side after a launch with zero lifetime**: unchanged. -/
theorem rRight_launch_zero {s : ExplState} (hc : IsRealChart (stChart s)) (hRR : RRight s) (k : ℕ)
    {D₀ : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (hreg : IsRegularDriver D₀) (h0 : D₀.2 = 0) :
    RRight (ExplState.launch s k D₀ θ ⊤) := by
  have hmin : min ⊤ D₀.2 ≠ ⊤ := by rw [h0]; simp
  obtain ⟨hch, -, hrec, -, -, -⟩ := launch_eq_of_ne_top s k D₀ θ ⊤ hmin
  have hT : stopTime ⊤ D₀ = 0 := by simp [stopTime, h0]
  have hW0 : stopDrv ⊤ D₀ 0 = 0 := stopDrv_zero hreg ⊤
  have hprof : rProf (stChart (ExplState.launch s k D₀ θ ⊤)) = rProf (stChart s) := by
    funext x
    rw [hch, hT]
    change (fwdMap (stopDrv ⊤ D₀) 0 ((stChart s).1 x)).re = _
    rw [fwdMap_zero_time hW0]
    rfl
  have hR : stRecR (ExplState.launch s k D₀ θ ⊤) = stRecR s := by
    rw [hrec]
    unfold lRecR
    have he : {x : ℝ | stRecR s < x ∧ ¬ lAlive (stChart s) ⊤ D₀ x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      unfold lAlive
      rw [hT, hc.eq_ofReal x]
      exact exists_isForwardSol_zero hW0 (hRR.2 x hx).ne'
    rw [he, insert_empty_eq, csSup_singleton]
  rw [RRight, hprof, hR]
  exact hRR

/-- **One stage of the left walk restores the left invariant at the next launch** (deterministic; the mirror of
`rInv_walk_step`). -/
theorem lInv_walk_step (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {ℓ k : ℕ}
    (hℓk : ℓ < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (k + 1)).2.2.2.1 k ≠ none)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hn : ∀ j, ℓ < j → j < k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (j + 1)).2.2.2.1 j = none)
    (hI : LInv κ θ b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D ℓ))
    (hR : LReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D ℓ))
    (hroot : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D ℓ) = .inl () →
      -sleLambda κ <
        rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D ℓ)) + θ * chiC κ)
    (hreg : IsRegularDriver (D ℓ)) (hgood : (D ℓ).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D ℓ))))
    (hnoR : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (ℓ + 1)) ≠ stThr (some true))
    (hF2 : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (ℓ + 1)) = stThr (some false) →
      sleLambda κ ≤
        leftLim b (stRecL (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (ℓ + 1))) + θ * chiC κ) :
    LInv κ θ b jumps (BoundaryWord.shiftW (rProf (stChart (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps θ false) D (ℓ + 1))) (stPt (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps θ false) D k))) (stopWord κ (β, θ, recOf ⊤ (D ℓ))))
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k) ∧
    LReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k) ∧
    rProf (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (ℓ + 1)))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k)) =
      ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D (ℓ + 1))).1 0 -
        (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D k)).1 0).re := by
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) D with hRdef
  obtain ⟨-, hrunk, r, hstk⟩ := run_eq_of_last_launch hℓk hk hl hn
  have hrun1 : R (ℓ + 1) = ExplState.launch (R ℓ) ℓ (D ℓ) θ ⊤ := launch_walk hl
  have hγR : ∀ y, 0 < y → -sleLambda κ < (stopWord κ (β, θ, recOf ⊤ (D ℓ))).fn y + θ * chiC κ :=
    fun y hy => stopWord_fn_add_gt_of_pos hκ hI.1 _ hy
  have hstk' : ∃ r, stStatus (R k) = .inr (.inr (.inr (.inl (r, true)))) := ⟨r, hstk⟩
  have hc := hI.2.1.1
  by_cases htop : (D ℓ).2 = ⊤
  · exfalso
    have hmin : min ⊤ (D ℓ).2 = ⊤ := by rw [htop]; rfl
    have hd := (launch_eq_of_top (R ℓ) ℓ (D ℓ) θ ⊤ hmin).2.2.2.2.1
    rw [← hrun1] at hd
    have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) false (Or.inr (Or.inl hd))
    rw [← hrunk] at this
    rw [this, hd] at hstk
    exact absurd hstk (by simp [stArcM])
  by_cases h0 : (D ℓ).2 = 0
  · have hnt : stStatus (R ℓ) ≠ .inr (.inl ()) := by
      rcases hR.1 with h | h <;> rw [h] <;> simp
    obtain ⟨hst1, hpt1, hang1⟩ := launch_zero (k := ℓ) (θ := θ) h0 hnt
    rw [← hrun1] at hst1 hpt1 hang1
    rcases hR.1 with hroot' | harc
    · have hR0 := hroot hroot'
      by_cases hhigh : sleLambda κ ≤ leftLim b (stPt (R (ℓ + 1))) + θ * chiC κ
      · have hc' := contStep_thr_none_left (κ := κ) b jumps (R (ℓ + 1)) hst1
          (by rw [hpt1, hang1]; exact hR0) (by rw [hang1]; exact hhigh)
        rw [← hrunk] at hc'
        obtain ⟨hs₁, hrel⟩ := lProf_launch_zero hI.2.1 ℓ θ hreg h0
        rw [← hrun1] at hs₁ hrel
        have hO := lOrig_of_rel hκ hb (s₁ := R (ℓ + 1)) hI.2.1 hI.2.2.1 θ ⟨hs₁, hrel⟩
        have hRR := rRight_launch_zero hc hI.2.2.2 ℓ θ hreg h0
        rw [← hrun1] at hRR
        have hLL : stRecL (R (ℓ + 1)) = stRecL (R ℓ) := by
          rw [hrun1]; exact stRecL_launch_zero hI.2.1 ℓ θ hreg h0
        have hpt : stPt (R (ℓ + 1)) = stRecL (R (ℓ + 1)) := by rw [hpt1, hLL]; exact hR.2
        exact lInv_tail hκ hb hs₁ hO hRR hγR hpt hang1 hhigh hc' hstk'
      · exfalso
        have hd := contStep_thr_none_dead (κ := κ) b jumps (R (ℓ + 1)) hst1
          (by rw [hang1]; exact lt_of_not_ge hhigh) (by rw [hpt1, hang1]; exact hR0) false
        rw [← hrunk, hstk] at hd
        exact absurd hd (by simp [stArcM, stDead])
    · exfalso
      have hadm : ExplState.IsAdmissibleSeed κ (leftLim b (stPt (R ℓ))) (rightLim b (stPt (R ℓ))) θ := by
        have e := run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := false) (D := D)
          (k := ℓ) (even_of_launches_walk hl).2 (even_of_launches_walk hl).1
        rw [← hRdef] at e
        by_contra hna
        have hfs : ExplState.flowStep κ b false (R ℓ) ℓ (D ℓ) θ ⊤ = R ℓ :=
          flowStep_arcL_eq_self (R ℓ) ℓ (D ℓ) θ ⊤ harc hna
        rw [e, hfs, launches_run_of_le _ _ le_rfl] at hl
        exact hl rfl
      have hd := contStep_thr_none_dead (κ := κ) b jumps (R (ℓ + 1)) hst1
        (by rw [hpt1, hang1]; exact hadm.1) (by rw [hpt1, hang1]; exact hadm.2) false
      rw [← hrunk, hstk] at hd
      exact absurd hd (by simp [stArcM, stDead])
  · have hcases := launch_status_of_pos (s := R ℓ) (k := ℓ) (θ := θ) htop h0
    rw [← hrun1] at hcases
    rcases hcases with hthr | hthr | hthr
    · exact absurd hthr hnoR
    · obtain ⟨-, hhit, hpt, hang⟩ :=
        launch_thr_false (s := R ℓ) (k := ℓ) (θ := θ) htop (by rw [← hrun1]; exact hthr)
      rw [← hrun1] at hpt hang
      obtain ⟨hs₁, hrel⟩ := lProf_launch hI.2.1 ℓ θ hreg (hgood htop) htop hhit
      rw [← hrun1] at hs₁ hrel
      have hO := lOrig_of_rel hκ hb (s₁ := R (ℓ + 1)) hI.2.1 hI.2.2.1 θ ⟨hs₁, hrel⟩
      have hRR := (rRight_launch hc hI.2.2.2 ℓ θ hreg (hgood htop) htop).2
      rw [← hrun1] at hRR
      have hc' := contStep_thr_false (κ := κ) b jumps (R (ℓ + 1)) hthr false
      rw [← hrunk] at hc'
      exact lInv_tail hκ hb hs₁ hO hRR hγR hpt hang (by rw [hpt]; exact hF2 hthr) hc' hstk'
    · exfalso
      have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) false (Or.inr (Or.inr hthr))
      rw [← hrunk] at this
      rw [this, hthr] at hstk
      exact absurd hstk (by simp [stArcM, stDead])

end StageL

end GW1W

end Theorem14

end InteractingSLE
