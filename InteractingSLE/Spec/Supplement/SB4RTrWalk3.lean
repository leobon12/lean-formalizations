/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrWalk2
import InteractingSLE.Spec.Supplement.GW1WalkExitData
import InteractingSLE.Spec.Supplement.BR3Ref

/-!
# The lower walk launches good drivers ending on the right

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). For a staged lower walk with drivers regular at
every sample, under GW1's ambient bound, almost surely every launch has a good driver and ends at a new right record,
immediately or at the target (`GW1WalkExit.ae_walkStageData_right`, `ClassifiedExit`): **`ae_walk_rightExit`**. The
same holds for the translated walk (`ae_walk_rightExit_tr`), which is the hypothesis of the restart
(`statePhys_restart`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar IsForwardSol fwdMap fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw FlowDilate
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

theorem lStatus_ne_done (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : lStatus s t d ≠ stDone := by
  unfold lStatus
  split_ifs <;> (try split) <;> simp [stTip, stDone, stDead, stThr]

/-- **A finite exit classified as GW1's forward exit ends on the right.** -/
theorem rightExit_of_classified {κ : ℝ} {b : ℝ → ℝ} {s : ExplState} {k : ℕ} {d : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ}
    (hC : GW1WalkExit.ClassifiedExit κ b true s (ExplState.launch s k d θ ⊤)) : RightExit s ⊤ d := by
  intro _ hz hfin
  obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top s k d θ ⊤ hfin
  rcases hC.1 with hdone | ⟨-, hout⟩
  · exact absurd (hst ▸ hdone) (lStatus_ne_done s ⊤ d)
  · by_contra hR
    have hnlt : ¬ (⊤ : ℝ≥0∞) < d.2 := not_top_lt
    rcases hout with h1 | ⟨h1, -⟩
    · rw [hst, lStatus] at h1
      simp only [hnlt, hz, hR, ↓reduceIte] at h1
      split_ifs at h1 <;> simp [stThr, stDead] at h1
    · rw [hst, lStatus] at h1
      simp only [hnlt, hz, hR, ↓reduceIte] at h1
      split_ifs at h1 <;> simp [stThr, stDead] at h1

theorem walkProg_flow {b : ℝ → ℝ} {J : Finset ℝ} {j : ℕ} {θ : ℝ} {t : ℝ≥0∞}
    (h : (walkProg b J)[j]? = some (.inl (θ, t))) : θ = -(Real.pi / 2) ∧ t = ⊤ := by
  unfold walkProg boundaryWalkSpec at h
  have hm := List.mem_of_getElem? h
  simp only [List.mem_flatten, List.mem_replicate] at hm
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hm
  simp only [List.mem_cons, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, List.not_mem_nil, or_false] at hl
  exact ⟨hl.1, hl.2⟩

section Walk

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The staged lower walk launches good drivers ending on the right**, almost surely. -/
theorem ae_walk_rightExit (h13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : IsStagedHistory κ b J P h (boundaryWalkSpec b J (-(Real.pi / 2)) true) D)
    (hreg : ∀ j ω, IsRegularDriver (D j ω)) :
    ∀ᵐ ω ∂P, ∀ j θ t, (walkProg b J)[j]? = some (.inl (θ, t)) →
      ExplState.flowStep κ b false
          (ExplState.run κ b J (boundaryWalkSpec b J (-(Real.pi / 2)) true) (fun i => D i ω) j) j (D j ω) θ t =
        ExplState.launch
          (ExplState.run κ b J (boundaryWalkSpec b J (-(Real.pi / 2)) true) (fun i => D i ω) j) j (D j ω) θ t →
      (min t (D j ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (D j ω)))) ∧
        RightExit (ExplState.run κ b J (boundaryWalkSpec b J (-(Real.pi / 2)) true) (fun i => D i ω) j) t (D j ω) := by
  have hamb := (GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hb hh hcf hζ').1
  filter_upwards [GW1WalkExit.ae_walkStageData_right hκ hb hh hD hreg hamb] with ω hω j θ t hj hfl
  obtain ⟨rfl, rfl⟩ := walkProg_flow hj
  have hl : (ExplState.run κ b J (boundaryWalkSpec b J (-(Real.pi / 2)) true) (fun i => D i ω) (j + 1)).2.2.2.1 j ≠
      none := by
    rw [run_succ, show (boundaryWalkSpec b J (-(Real.pi / 2)) true).2.2[j]? = some (.inl (-(Real.pi / 2), ⊤))
      from hj]
    show (ExplState.flowStep κ b false
      (ExplState.run κ b J (boundaryWalkSpec b J (-(Real.pi / 2)) true) (fun i => D i ω) j) j (D j ω)
        (-(Real.pi / 2)) ⊤).2.2.2.1 j ≠ none
    rw [launches_of_flowStep_eq_launch hfl]
    exact Option.some_ne_none _
  obtain ⟨-, -, hgood, hC⟩ := hω j hl
  refine ⟨fun hfin => hgood (by simpa using hfin), ?_⟩
  have hstep : ExplState.run κ b J (boundaryWalkSpec b J (-(Real.pi / 2)) true) (fun i => D i ω) (j + 1) =
      ExplState.launch (ExplState.run κ b J (boundaryWalkSpec b J (-(Real.pi / 2)) true) (fun i => D i ω) j) j
        (D j ω) (-(Real.pi / 2)) ⊤ := by
    rw [run_succ, show (boundaryWalkSpec b J (-(Real.pi / 2)) true).2.2[j]? = some (.inl (-(Real.pi / 2), ⊤))
      from hj]
    exact hfl
  rw [hstep] at hC
  exact rightExit_of_classified hC

theorem rightExit_trState {s : ExplState} {t : ℝ≥0∞} {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (v : ℝ) (h : RightExit s t d) :
    RightExit (trState v s) t d := fun h1 h2 h3 => (exists_hitR_trState v s t d).2 (h h1 h2 h3)

end Walk

end InteractingSLE.Theorem14.SB.Lf
