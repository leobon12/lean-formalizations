/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PathLow

/-!
# GW1's retargeting: the post-piece word is low on the connector

Packet PROVE-GW1-PATH. For the right walk at a launch `2(n+1)` preceded by the launch `2n`:

* `exists_post_witness_right_prof`: PROVE-GW1-LAWS's `exists_post_witness_right` with the right profile and the
  original-word property of the post-piece state exported (same construction);
* **`ae_post_low_right`**: almost surely at a next launch the recentring amount `v = postShift` is positive and the
  post-piece word (`GW1Laws.postWord`) is low on `(0, v)` (`γ(y) − (π/2)χ ≤ −λ`): it is the original word there
  (`ROrig`), and the original data are low on the connector `(q, w)` (`connector_right`, BW2's (4.9)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Path

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData GW1W GW1WalkExit GW1Laws

section Witness

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The next-launch word of the right walk is the recentred stop word**, with the right profile and the
original-word property of the post-piece state (the construction of `GW1Laws.exists_post_witness_right`). -/
theorem exists_post_witness_right_prof (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
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
            (postShift κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) n) γ ∧
          RProf (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω)
            (2 * n + 1)) ∧
          ROrig b jumps γ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => E j ω) (2 * n + 1)) := by
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
    fun y hy _ => stopWord_fn_add_lt_of_neg hκ hinv.1 _ hy, fn_bound_pos_of_rOrig hP hO h0 hambR⟩, ?_,
    by rw [hrun1]; exact hP, by rw [hrun1]; exact hO⟩
  rw [hβ]
  rfl

end Witness

section Low

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The post-piece word is low on the connector** (right walk): almost surely at a next launch, the recentring
amount `v = postShift` is positive and `postWord` is low on `(0, v)` at angle `−π/2`. -/
theorem ae_post_low_right (hb : IsPiecewiseConstantBoundaryData b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hstages : ∀ᵐ ω ∂P, WalkStageData κ b jumps (-(Real.pi / 2)) true (fun j => E j ω)) (n : ℕ)
    {βk : Ω → BoundaryWord}
    (hgood : ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω)
          (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω)
          (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
        ∃ γ : BoundaryWord, IsCfGoodWord κ γ ∧
          βk ω = BoundaryWord.shiftW
            (postShift κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) n) γ ∧
          RProf (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω)
            (2 * n + 1)) ∧
          ROrig b jumps γ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => E j ω) (2 * n + 1)))
    (hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      0 < postShift κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) n ∧
      ∀ y, 0 < y →
        y < postShift κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) n →
        y ∉ (postWord κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E n βk ω).jumps →
        (postWord κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E n βk ω).fn y +
          -(Real.pi / 2) * chiC κ ≤ -sleLambda κ := by
  set θ : ℝ := -(Real.pi / 2) with hθ
  set spec := boundaryWalkSpec b jumps θ true with hspec
  filter_upwards [hgood, hprev, hstages] with ω hg hp hs hlk
  have hl := hp hlk
  obtain ⟨γ, -, hβk, hP, hO⟩ := hg hlk hl
  set R := ExplState.run κ b jumps spec (fun j => E j ω) with hRdef
  -- the stage data at the launch `2n`
  obtain ⟨hprof, hready, hgd, hC⟩ := hs (2 * n) hl
  change OwnProfile true (R (2 * n)) at hprof
  change OwnReady true (R (2 * n)) at hready
  change ClassifiedExit κ b true (R (2 * n)) (R (2 * n + 1)) at hC
  have hrun1 : R (2 * n + 1) = ExplState.launch (R (2 * n)) (2 * n) (E (2 * n) ω) θ ⊤ := launch_walk hl
  have hnoL : stStatus (R (2 * n + 1)) ≠ stThr (some false) := by
    intro hbad
    rcases hC.1 with hd | ⟨-, ho⟩
    · rw [hbad] at hd; exact absurd hd (by simp)
    · rcases ho with he | ⟨he, -⟩ <;> rw [hbad] at he <;> exact absurd he (by simp)
  obtain ⟨hfin, -⟩ := post_case (D := fun j => E j ω) false hl hlk hnoL
  have hgd' : LocalExt.IsDrvGood (recHist (recOf ⊤ (E (2 * n) ω))) := hgd hfin
  rw [hrun1] at hC
  obtain ⟨-, hpt⟩ := profile_point_of_finite_classified hprof hready (2 * n) (hreg (2 * n) ω) hgd' hfin hC
  rw [← hrun1] at hC hpt
  change stPt (R (2 * n + 1)) = stRecR (R (2 * n + 1)) at hpt
  have hang : stAngle (R (2 * n + 1)) = θ := by rw [hrun1]; exact angle_launch _ _ _ _
  obtain ⟨hqw, hlowx, hchart, -⟩ := connector_right hb hl hlk hC hang
  set w := stPt (R (2 * (n + 1))) with hw
  -- the recentring amount is the profile of `w`
  have hv : postShift κ b jumps spec (fun j => E j ω) n = rProf (stChart (R (2 * n + 1))) w := by
    unfold postShift
    change ((stChart (R (2 * n + 1))).1 0 - (stChart (R (2 * (n + 1)))).1 0).re = _
    change stChart (R (2 * (n + 1))) =
      (stChart (R (2 * n + 1))).recenter (rProf (stChart (R (2 * n + 1))) w) at hchart
    rw [hchart]
    simp only [InteractingSLE.Chart.recenter, rProf, Complex.sub_re, Complex.ofReal_re]
    ring
  have hrw : stRecR (R (2 * n + 1)) < w := hpt ▸ hqw
  have hpos : 0 < rProf (stChart (R (2 * n + 1))) w := hP.2.2.1 w hrw
  have hpw : postWord κ b jumps spec E n βk ω = γ := by
    unfold postWord
    rw [hβk, shiftW_neg_shiftW]
  refine ⟨hv ▸ hpos, fun y hy hyv hyJ => ?_⟩
  rw [hpw] at hyJ ⊢
  rw [hv] at hyv
  refine fn_low_of_rOrig hP hO hrw (fun x hx hxw hxJ => ?_) y hy hyv hyJ
  exact hlowx x (hpt ▸ hx) hxw hxJ

end Low

end InteractingSLE.Theorem14.GW1Path
