/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WeStep
import InteractingSLE.Spec.Supplement.SB2WdInd
import InteractingSLE.Spec.Supplement.SBLwShift

/-!
# SB2(1)'s second clause at every launch of the lower walk

Packet PROVE-T14-SB2WORD (round 2): GW1's witness induction (`GW1W.exists_witness_right`, round 1's
`exists_witness_right_lw`) rerun with all the left-side invariants `LWO` (round 1's `LW`, the second clause `OW`, the
record bound `RecLBound`): **`exists_witness_right_lwo`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

universe u

namespace InteractingSLE.Theorem14.GW1W

open Exist Exist.StagedLaw Exist.Staged Restart LQGMetric
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **GW1's classification with all the left-side invariants** (`LWO`; the companion of
`exists_witness_right`): at every
instruction `k` the staged conditional law has a witness whose word, almost surely at a launch at `k`, has GW1's
invariant and the left-side invariant `LW`. -/
theorem exists_witness_right_lwo (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hRS : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps θ true) E)
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + θ * chiC κ < sleLambda κ) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ true) E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
          none →
        RInv κ θ b jumps (β ω) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) ∧
        RReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) ∧
        (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) = .inl () →
          leftLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k)) +
            θ * chiC κ < sleLambda κ) ∧
        LWO κ θ b jumps (β ω) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) := by
  set spec := boundaryWalkSpec b jumps θ true with hspec
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hRL := regLaunches_of_stagedPiecesRegular hRS
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => flowField spec.1 0 (h ω),
        isStageWitness_zero hh hc₀J hc₀, Eventually.of_forall fun ω _ => ?_⟩
      have h0 := rInv_root (κ := κ) (θ := θ) hb hamb hc₀J hc₀
      exact ⟨h0.1, h0.2.1, fun _ => h0.2.2, lwo_root hc₀⟩
    have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens), ℓ < k →
        IsStageWitness κ b jumps P h spec E ℓ β Y ∧
        ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          RInv κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          RReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
            leftLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ < sleLambda κ) ∧
          LWO κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨β, Y, hW, hI⟩ := ih ℓ hℓ
        exact ⟨β, Y, fun _ => ⟨hW, hI⟩⟩
      · exact ⟨fun _ => default, fun _ => 0, fun h' => absurd h' hℓ⟩
    choose β Y hWI using H
    obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
      hk (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y fun ℓ hℓ => (hWI ℓ hℓ).1
    refine ⟨βk, Yk, hWk, ?_⟩
    have hstage : ∀ ℓ, ℓ < k → ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some false) ∧
          ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some true) →
            rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ ≤
              -sleLambda κ) := fun ℓ hℓ =>
      ae_stage_right hκ hb hh hE hreg (hWI ℓ hℓ).1 ((hWI ℓ hℓ).2.mono fun ω hω hl => (hω hl).1)
    have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          RInv κ θ b jumps (β ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          RReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
            leftLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ < sleLambda κ) ∧
          LWO κ θ b jumps (β ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) ∧
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some false) ∧
          ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some true) →
            rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ ≤
              -sleLambda κ)) := by
      refine ae_all_iff.2 fun ℓ => ?_
      by_cases hℓ : ℓ < k
      · filter_upwards [(hWI ℓ hℓ).2, hstage ℓ hℓ] with ω h1 h2 _ using ⟨h1, h2⟩
      · exact Eventually.of_forall fun ω h' => absurd h' hℓ
    filter_upwards [hall, hRL] with ω hω hRLω hlk
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
    obtain ⟨ℓ, hℓk, ⟨c', θ'', hl'⟩, -, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
    have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hl']; simp
    obtain ⟨hinv, hst⟩ := hω ℓ hℓk
    obtain ⟨hI, hR, hroot, hLW⟩ := hinv hl
    obtain ⟨hnoL, hgood, hF2⟩ := hst hl
    obtain ⟨hInv, hReady, ha⟩ := rInv_walk_step (D := fun j => E j ω) hκ hb hℓk hlk hl hn hI hR hroot (hreg ℓ ω)
      hgood hnoL hF2
    have hcc := SB.LuM.isConformal_runChart_of_reg spec hRLω ℓ
    have hP : (E ℓ ω).2 ≠ ⊤ → GW1P.PieceRegular (E ℓ ω).1 (E ℓ ω).2 := fun _ => by
      have := hRLω ℓ c' θ'' hl'
      rwa [instrTime_walk hl, min_eq_right le_top] at this
    obtain ⟨g, hgc, hgi, -, -⟩ := SB.Lw.exists_bdryMap_of_hasProperBdryExt hcc
      (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hRLω ℓ).1
    have hLWk := lwo_walk_step (D := fun j => E j ω) hκ hb hℓk hlk hl hn hI hR hroot (hreg ℓ ω) hgood hnoL hF2
      hLW.1 hcc hP hLW.2.1 hLW.2.2 hgc hgi
    have hβ := hexpl ℓ ω hℓk hlk hl hn
    rw [instrAngle_walk hl, pastMap_last_of_launch hl, instrTime_walk hl, ← ha] at hβ
    rw [hβ]
    refine ⟨hInv, hReady, fun hroot' => ?_, hLWk⟩
    obtain ⟨-, -, r, hr⟩ := run_eq_of_last_launch (D := fun j => E j ω) hℓk hlk hl hn
    rw [hr] at hroot'
    exact absurd hroot' (by simp [stArcM])

end InteractingSLE.Theorem14.GW1W
