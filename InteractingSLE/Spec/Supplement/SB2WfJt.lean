/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfJs

/-!
# The junction invariant through one stage of the lower walk

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). `jw_tail` (the move to the next restart mark) and
`jw_walk_step` (one stage: the launch, by `jw_launch_full`, then the move), with the case analysis of round 2's
`GW1W.lwo_walk_step` (an infinite stop is impossible; a zero stop at the root; a positive stop ends at a right
threshold).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap H)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ ψ u : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The junction invariant at the end of a stage** (the move to the next restart mark). -/
theorem jw_tail {γ : BoundaryWord} {s₁ s₂ : ExplState} (hI : JW κ θ ψ u b γ s₁)
    (he : s₂ = if hC : (restartSet κ b jumps s₁).Nonempty then
      ExplState.moveAlong s₁ true ((restartSet κ b jumps s₁).min' hC) true else ExplState.moveToEnd s₁ true)
    (hst : ∃ r, stStatus s₂ = .inr (.inr (.inr (.inl (r, true))))) :
    JW κ θ ψ u b (BoundaryWord.shiftW (rProf (stChart s₁) (stPt s₂)) γ) s₂ := by
  split_ifs at he with hC
  swap
  · exfalso
    obtain ⟨r, hr⟩ := hst
    rw [he] at hr
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    exact absurd hr (by simp [ExplState.moveToEnd, stStatus])
  subst he
  rw [stPt_moveAlong]
  exact jw_moveAlong hI _

/-- **One stage of the right walk keeps the junction invariant.** -/
theorem jw_walk_step (hκ : 0 < κ) (hκ4 : κ < 4) (hθψ : θ < ψ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {β : BoundaryWord} {ℓ k : ℕ}
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
    (hLW : LW κ θ b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hcc : (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)).IsConformal)
    (hOW : OW κ θ b jumps β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)).2.1 H)
    (hJW : JW κ θ ψ u b β (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hR0 : 0 ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    (hR0₁ : 0 ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1))) {γ : ℝ → ℂ}
    (hγ : (D ℓ).2 ≠ ⊤ → IsLoewnerTraceLT (rdrv (recOf ⊤ (D ℓ))) (rtime (recOf ⊤ (D ℓ))) γ)
    (hγc : (D ℓ).2 ≠ ⊤ → ContinuousOn γ (Icc 0 (rtime (recOf ⊤ (D ℓ)))))
    (hseed : (D ℓ).2 ≠ ⊤ → 0 < rtime (recOf ⊤ (D ℓ)) →
      -2 < Sec4.cumWeightRight κ (rightLim β.fn 0 + θ * chiC κ))
    (hRT : (D ℓ).2 ≠ ⊤ → ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < rtime (recOf ⊤ (D ℓ)) → (γ t₀).im = 0 → 0 < (γ t₀).re →
      -2 < Sec4.cumWeightRight κ (rightLim β.fn (γ t₀).re + θ * chiC κ))
    (hLT : (D ℓ).2 ≠ ⊤ → ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < rtime (recOf ⊤ (D ℓ)) → (γ t₀).im = 0 → (γ t₀).re < 0 →
      ∃ a a' v : ℝ, a < (γ t₀).re ∧ (γ t₀).re < a' ∧ (∀ y ∈ Ioo a a', y ∉ β.jumps → β.fn y = v) ∧
        Sec4.cumWeightLeft κ (v + θ * chiC κ) < κ / 2 - 2) :
    JW κ θ ψ u b (BoundaryWord.shiftW (rProf (stChart (ExplState.run κ b jumps
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
  have hOW1 : RProf (R (ℓ + 1)) → OW κ θ b jumps (stopWord κ (β, θ, recOf ⊤ (D ℓ))) (R (ℓ + 1)) := by
    intro hs₁
    rw [hrun1] at hs₁ ⊢
    exact ow_launch hκ hI.2.1.1 hcc hLW.1 hI.2.1.2.1 hOW ℓ hreg (hgood htop) htop hs₁
  have hJW1 : RProf (R (ℓ + 1)) → ROrig b jumps (stopWord κ (β, θ, recOf ⊤ (D ℓ))) (R (ℓ + 1)) →
      JW κ θ ψ u b (stopWord κ (β, θ, recOf ⊤ (D ℓ))) (R (ℓ + 1)) := by
    intro hs₁ hO₁
    have hOW₁ := hOW1 hs₁
    have hR0₁' := hR0₁
    rw [hrun1] at hs₁ hO₁ hOW₁ hR0₁' ⊢
    exact jw_launch_full hκ hκ4 hθψ hb hI.2.1.1 hcc hLW.1 hLW.2.2.2.2.2 hR0 hI.2.1 hI.2.2 hOW hJW hgc hgi ℓ hreg
      (hgood htop) htop (hγ htop) (hγc htop) hs₁ hO₁ hOW₁ hR0₁' (hseed htop) (hRT htop) (hLT htop)
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
        exact jw_tail (hJW1 hs₁ hO) hc hstk'
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
      exact jw_tail (hJW1 hs₁ hO) hc hstk'
    · exact absurd hthr hnoL
    · exfalso
      have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (ℓ + 1)) true (Or.inr (Or.inr hthr))
      rw [← hrunk] at this
      rw [this, hthr] at hstk
      exact absurd hstk (by simp [stArcM, stDead])

end InteractingSLE.Theorem14.SB.Wf
