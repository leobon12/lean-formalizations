/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WeRec

/-!
# SB2(1)'s second clause through one stage of the lower walk

Packet PROVE-T14-SB2WORD (round 2). The left-side invariant `LW` (round 1), the second clause `OW` and the left
record bound `RecLBound` together (`LWO`), carried through a stage of the right walk exactly as GW1's `rInv_walk_step`
(a launch, then the rightward continuation along a low connector):

* `lwo_tail` (the continuation), **`lwo_walk_step`** (one stage), `lwo_root`.

Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap H)

namespace InteractingSLE.Theorem14.GW1W

open Exist Exist.StagedLaw Exist.Staged Restart
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The left-side invariants of the lower walk** (round 1's `LW`, the second clause `OW`, the record bound). -/
def LWO (κ θ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  LW κ θ b jumps β s ∧ OW κ θ b jumps β s ∧ RecLBound s

section Bundle

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The invariants at the root. -/
theorem lwo_root {c₀ : BoundaryWord} (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    LWO κ θ b jumps (BoundaryWord.shiftW 0 c₀) (ExplState.init 0) :=
  ⟨lw_root hc₀, ow_root hc₀, recLBound_root⟩

/-- **The end of a stage** (the mirror of `rInv_tail` for `LWO`). -/
theorem lwo_tail (hb : IsPiecewiseConstantBoundaryData b jumps) {γ : BoundaryWord} {s₁ s₂ : ExplState}
    (hs₁ : RProf s₁) (hO : ROrig b jumps γ s₁) (hI : LWO κ θ b jumps γ s₁) (hpt : stPt s₁ = stRecR s₁)
    (hang : stAngle s₁ = θ) (hlow : rightLim b (stPt s₁) + θ * chiC κ ≤ -sleLambda κ)
    (he : s₂ = if hC : (restartSet κ b jumps s₁).Nonempty then
      ExplState.moveAlong s₁ true ((restartSet κ b jumps s₁).min' hC) true else ExplState.moveToEnd s₁ true)
    (hst : ∃ r, stStatus s₂ = .inr (.inr (.inr (.inl (r, true))))) :
    LWO κ θ b jumps (BoundaryWord.shiftW (rProf (stChart s₁) (stPt s₂)) γ) s₂ := by
  refine ⟨lw_tail hb hs₁ hO hI.1 hpt hang hlow he hst, ?_, ?_⟩
  · split_ifs at he with hC
    swap
    · exfalso
      obtain ⟨r, hr⟩ := hst
      rw [he] at hr
      obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
      exact absurd hr (by simp [ExplState.moveToEnd, stStatus])
    subst he
    have hmem := Finset.mem_filter.1 (Finset.min'_mem _ hC)
    rw [stPt_moveAlong]
    exact ow_moveAlong hI.2.1 (by rw [← hpt]; exact hmem.2.1)
  · split_ifs at he with hC
    swap
    · exfalso
      obtain ⟨r, hr⟩ := hst
      rw [he] at hr
      obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
      exact absurd hr (by simp [ExplState.moveToEnd, stStatus])
    subst he
    exact recLBound_moveAlong hI.2.2 _

end Bundle

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **One stage of the right walk keeps all the left-side invariants** (the companion of `rInv_walk_step` and of
round 1's `lw_walk_step`, with the second clause, the record bound and a boundary map of the launch chart). -/
theorem lwo_walk_step (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {ℓ k : ℕ}
    (hℓk : ℓ < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hn : ∀ j, ℓ < j → j < k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j = none)
    (hI : RInv κ θ b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hR : RReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hroot : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ) = .inl () →
      leftLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)) + θ * chiC κ <
        sleLambda κ)
    (hreg : IsRegularDriver (D ℓ)) (hgood : (D ℓ).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D ℓ))))
    (hnoL : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)) ≠ stThr (some false))
    (hF2 : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)) = stThr (some true) →
      rightLim b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1))) + θ * chiC κ ≤
        -sleLambda κ)
    (hLW : LW κ θ b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hcc : (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)).IsConformal)
    (hP : (D ℓ).2 ≠ ⊤ → GW1P.PieceRegular (D ℓ).1 (D ℓ).2)
    (hOW : OW κ θ b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hRB : RecLBound (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)).2.1 H) :
    LWO κ θ b jumps (BoundaryWord.shiftW (rProf (stChart (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps θ true) D (ℓ + 1))) (stPt (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps θ true) D k))) (stopWord κ (β, θ, recOf ⊤ (D ℓ))))
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) := by
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D with hRdef
  obtain ⟨-, hrunk, r, hstk⟩ := run_eq_of_last_launch hℓk hk hl hn
  have hrun1 : R (ℓ + 1) = ExplState.launch (R ℓ) ℓ (D ℓ) θ ⊤ := launch_walk hl
  have hstk' : ∃ r, stStatus (R k) = .inr (.inr (.inr (.inl (r, true)))) := ⟨r, hstk⟩
  by_cases htop : (D ℓ).2 = ⊤
  · exfalso
    have hmin : min ⊤ (D ℓ).2 = ⊤ := by rw [htop]; rfl
    have hd := (launch_eq_of_top (R ℓ) ℓ (D ℓ) θ ⊤ hmin).2.2.2.2.1
    rw [← hrun1] at hd
    have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) true (Or.inr (Or.inl hd))
    rw [← hrunk] at this
    rw [this, hd] at hstk
    exact absurd hstk (by simp [stArcM])
  have hLW1 : LW κ θ b jumps (stopWord κ (β, θ, recOf ⊤ (D ℓ))) (R (ℓ + 1)) := by
    rw [hrun1]
    exact lw_launch hκ hb hI.2.1.1 hcc hLW ℓ hreg (hgood htop) htop (hP htop)
  have hRB1 : RecLBound (R (ℓ + 1)) := by
    obtain ⟨S, Fx, Fy, hSL, -, -, hSc, -⟩ := hOW
    rw [hrun1]
    exact recLBound_launch hI.2.1.1 hLW.1 hcc hgc hgi (fun x hx => hSc x (hSL x hx)) hRB ℓ θ hreg (hgood htop)
      htop (hP htop)
  have hOW1 : RProf (R (ℓ + 1)) → OW κ θ b jumps (stopWord κ (β, θ, recOf ⊤ (D ℓ))) (R (ℓ + 1)) := by
    intro hs₁
    rw [hrun1] at hs₁ ⊢
    exact ow_launch hκ hI.2.1.1 hcc hLW.1 hI.2.1.2.1 hOW ℓ hreg (hgood htop) htop hs₁
  by_cases h0 : (D ℓ).2 = 0
  · have hnt : stStatus (R ℓ) ≠ .inr (.inl ()) := by
      rcases hR.1 with h | h <;> rw [h] <;> simp
    obtain ⟨hst1, hpt1, hang1⟩ := launch_zero (k := ℓ) (θ := θ) h0 hnt
    rw [← hrun1] at hst1 hpt1 hang1
    rcases hR.1 with hroot' | harc
    · have hL0 := hroot hroot'
      by_cases hlow : rightLim b (stPt (R (ℓ + 1))) + θ * chiC κ ≤ -sleLambda κ
      · have hc := contStep_thr_none_right (κ := κ) b jumps (R (ℓ + 1)) hst1 (by rw [hang1]; exact hlow)
        rw [← hrunk] at hc
        obtain ⟨hs₁, hrel⟩ := rProf_launch_zero hI.2.1 ℓ θ hreg h0
        rw [← hrun1] at hs₁ hrel
        have hO := rOrig_of_rel hκ hb (s₁ := R (ℓ + 1)) hI.2.1 hI.2.2 θ ⟨hs₁, hrel⟩
        have hRR : stRecR (R (ℓ + 1)) = stRecR (R ℓ) := by
          rw [hrun1]
          obtain ⟨-, -, hrec, -, -, -⟩ := launch_eq_of_ne_top (R ℓ) ℓ (D ℓ) θ ⊤ (min_top_ne_top htop)
          rw [hrec]
          unfold lRecR
          have he : {x : ℝ | stRecR (R ℓ) < x ∧ ¬ lAlive (stChart (R ℓ)) ⊤ (D ℓ) x} = ∅ := by
            ext x
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
            intro hx
            unfold lAlive
            have hT : stopTime ⊤ (D ℓ) = 0 := by simp [stopTime, h0]
            rw [hT, hI.2.1.1.eq_ofReal x]
            exact exists_isForwardSol_zero (stopDrv_zero hreg ⊤) (hI.2.1.2.2.1 x hx).ne'
          rw [he, insert_empty_eq, csSup_singleton]
        have hpt : stPt (R (ℓ + 1)) = stRecR (R (ℓ + 1)) := by rw [hpt1, hRR]; exact hR.2
        exact lwo_tail hb hs₁ hO ⟨hLW1, hOW1 hs₁, hRB1⟩ hpt hang1 hlow hc hstk'
      · exfalso
        have hd := contStep_thr_none_dead (κ := κ) b jumps (R (ℓ + 1)) hst1
          (by rw [hpt1, hang1]; exact hL0) (by rw [hang1]; exact lt_of_not_ge hlow) true
        rw [← hrunk, hstk] at hd
        exact absurd hd (by simp [stArcM, stDead])
    · exfalso
      have hadm : ExplState.IsAdmissibleSeed κ (leftLim b (stPt (R ℓ))) (rightLim b (stPt (R ℓ))) θ := by
        have e := run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true) (D := D)
          (k := ℓ) (even_of_launches_walk hl).2 (even_of_launches_walk hl).1
        rw [← hRdef] at e
        by_contra hna
        have hfs : ExplState.flowStep κ b false (R ℓ) ℓ (D ℓ) θ ⊤ = R ℓ :=
          flowStep_arc_eq_self (R ℓ) ℓ (D ℓ) θ ⊤ harc hna
        rw [e, hfs, launches_run_of_le _ _ le_rfl] at hl
        exact hl rfl
      have hd := contStep_thr_none_dead (κ := κ) b jumps (R (ℓ + 1)) hst1
        (by rw [hpt1, hang1]; exact hadm.1) (by rw [hpt1, hang1]; exact hadm.2) true
      rw [← hrunk, hstk] at hd
      exact absurd hd (by simp [stArcM, stDead])
  · have hcases := launch_status_of_pos (s := R ℓ) (k := ℓ) (θ := θ) htop h0
    rw [← hrun1] at hcases
    rcases hcases with hthr | hthr | hthr
    · obtain ⟨-, hhit, hpt, hang⟩ := launch_thr_true (s := R ℓ) (k := ℓ) (θ := θ) htop (by rw [← hrun1]; exact hthr)
      rw [← hrun1] at hpt hang
      obtain ⟨hs₁, hrel⟩ := rProf_launch hI.2.1 ℓ θ hreg (hgood htop) htop hhit
      rw [← hrun1] at hs₁ hrel
      have hO := rOrig_of_rel hκ hb (s₁ := R (ℓ + 1)) hI.2.1 hI.2.2 θ ⟨hs₁, hrel⟩
      have hc := contStep_thr_true' (κ := κ) b jumps (R (ℓ + 1)) hthr
      rw [← hrunk] at hc
      exact lwo_tail hb hs₁ hO ⟨hLW1, hOW1 hs₁, hRB1⟩ hpt hang (by rw [hpt]; exact hF2 hthr) hc hstk'
    · exact absurd hthr hnoL
    · exfalso
      have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) true (Or.inr (Or.inr hthr))
      rw [← hrunk] at this
      rw [this, hthr] at hstk
      exact absurd hstk (by simp [stArcM, stDead])

end Stage

end InteractingSLE.Theorem14.GW1W
