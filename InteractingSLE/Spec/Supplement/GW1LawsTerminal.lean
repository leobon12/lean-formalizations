/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsPost

/-!
# GW1's terminal restart: the next-launch word is the recentred good stop word

Packet PROVE-GW1-LAWS. At a launch `2(n+1)` of either boundary walk preceded by the launch `2n`, the next-launch stage
witness word is, almost surely, the stop word of the piece `2n` recentred at the next seed
(PROVE-T14-GW1W's `isStageWitness_succ_expl`), and that stop word satisfies both height bounds of the counterflow
lifetime criterion (`GW1LawsPost`). `exists_post_witness` packages this for either walk.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Laws

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData GW1W

section Witness

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The recentring amount between the post-piece chart and the next-launch chart. -/
def postShift (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) : ℝ :=
  ((ExplState.run κ b jumps spec D (2 * n + 1)).2.2.2.2.1.1 0 -
    (ExplState.run κ b jumps spec D (2 * (n + 1))).2.2.2.2.1.1 0).re

/-- **The next-launch word of the right walk is the recentred good stop word.** -/
theorem exists_post_witness_right (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hambL : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hambR : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + Real.pi / 2 * chiC κ) (n : ℕ) :
    ∃ (βk : Ω → BoundaryWord) (Yk : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E (2 * (n + 1)) βk Yk ∧
      ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω)
          (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω)
          (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
        ∃ γ : BoundaryWord, IsCfGoodWord κ γ ∧
          βk ω = BoundaryWord.shiftW
            (postShift κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) n) γ := by
  set θ : ℝ := -(Real.pi / 2) with hθ
  set spec := boundaryWalkSpec b jumps θ true with hspec
  have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E ℓ β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        RInv κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        RReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
          leftLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ < sleLambda κ) :=
    fun ℓ => exists_witness_right hκ hb hh hE hreg hambL ℓ
  choose β Y hW hI using H
  obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
    (k := 2 * (n + 1)) (by omega) (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y
    fun ℓ _ => hW ℓ
  refine ⟨βk, Yk, hWk, ?_⟩
  filter_upwards [hI (2 * n), ae_stage_right hκ hb hh hE hreg (hW (2 * n)) ((hI (2 * n)).mono fun ω hω hl => (hω hl).1)]
    with ω hIω hst hlk hl
  have hn : ∀ j, 2 * n < j → j < 2 * (n + 1) →
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none := by
    intro j hj1 hj2
    have hj : j = 2 * n + 1 := by omega
    subst hj
    exact GW1RestartPair.noLaunch_walk_odd _ n
  have hβ := hexpl (2 * n) ω (by omega) hlk hl hn
  rw [instrAngle_walk hl, pastMap_last_of_launch hl, instrTime_walk hl] at hβ
  obtain ⟨hinv, -, -⟩ := hIω hl
  obtain ⟨hnoL, hgood, -⟩ := hst hl
  obtain ⟨hfin, hcase⟩ := post_case (D := fun j => E j ω) false hl hlk hnoL
  have hrun1 := launch_walk (D := fun j => E j ω) hl
  rw [hrun1] at hcase
  obtain ⟨hP, hO⟩ := post_rProf_rOrig hκ hb hinv (hreg (2 * n) ω) hgood hfin hcase
  have h0 : 0 ≤ stRecR (ExplState.launch (ExplState.run κ b jumps spec (fun j => E j ω) (2 * n)) (2 * n)
      (E (2 * n) ω) θ ⊤) := by
    rw [← hrun1]
    exact zero_le_stRecR_run κ b jumps spec _ le_rfl _
  refine ⟨stopWord κ (β (2 * n) ω, θ, recOf ⊤ (E (2 * n) ω)), ⟨isSorted_stopWord κ _,
    fun y hy _ => stopWord_fn_add_lt_of_neg hκ hinv.1 _ hy, fn_bound_pos_of_rOrig hP hO h0 hambR⟩, ?_⟩
  rw [hβ]
  rfl

/-- **The next-launch word of the left walk is the recentred good stop word.** -/
theorem exists_post_witness_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (Real.pi / 2) false) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hambL : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hambR : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + Real.pi / 2 * chiC κ) (n : ℕ) :
    ∃ (βk : Ω → BoundaryWord) (Yk : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps (Real.pi / 2) false) E (2 * (n + 1)) βk Yk ∧
      ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
          (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω)
          (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
        ∃ γ : BoundaryWord, IsCfGoodWord κ γ ∧
          βk ω = BoundaryWord.shiftW
            (postShift κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) (fun j => E j ω) n) γ := by
  set θ : ℝ := Real.pi / 2 with hθ
  set spec := boundaryWalkSpec b jumps θ false with hspec
  have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E ℓ β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        LInv κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        LReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
          -sleLambda κ < rightLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ) :=
    fun ℓ => exists_witness_left hκ hb hh hE hreg hambR ℓ
  choose β Y hW hI using H
  obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
    (k := 2 * (n + 1)) (by omega) (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y
    fun ℓ _ => hW ℓ
  refine ⟨βk, Yk, hWk, ?_⟩
  filter_upwards [hI (2 * n), ae_stage_left hκ hb hh hE hreg (hW (2 * n)) ((hI (2 * n)).mono fun ω hω hl => (hω hl).1)]
    with ω hIω hst hlk hl
  have hn : ∀ j, 2 * n < j → j < 2 * (n + 1) →
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none := by
    intro j hj1 hj2
    have hj : j = 2 * n + 1 := by omega
    subst hj
    exact GW1RestartPair.noLaunch_walk_odd _ n
  have hβ := hexpl (2 * n) ω (by omega) hlk hl hn
  rw [instrAngle_walk hl, pastMap_last_of_launch hl, instrTime_walk hl] at hβ
  obtain ⟨hinv, -, -⟩ := hIω hl
  obtain ⟨hnoR, hgood, -⟩ := hst hl
  obtain ⟨hfin, hcase⟩ := post_case (D := fun j => E j ω) true hl hlk hnoR
  have hrun1 := launch_walk (D := fun j => E j ω) hl
  rw [hrun1] at hcase
  obtain ⟨hP, hO⟩ := post_lProf_lOrig hκ hb hinv (hreg (2 * n) ω) hgood hfin hcase
  have h0 : stRecL (ExplState.launch (ExplState.run κ b jumps spec (fun j => E j ω) (2 * n)) (2 * n)
      (E (2 * n) ω) θ ⊤) ≤ 0 := by
    rw [← hrun1]
    exact stRecL_run_nonpos κ b jumps spec _ le_rfl _
  refine ⟨stopWord κ (β (2 * n) ω, θ, recOf ⊤ (E (2 * n) ω)), ⟨isSorted_stopWord κ _,
    fn_bound_neg_of_lOrig hP hO h0 hambL, fun y hy _ => stopWord_fn_add_gt_of_pos hκ hinv.1 _ hy⟩, ?_⟩
  rw [hβ]
  rfl

end Witness

end InteractingSLE.Theorem14.GW1Laws
