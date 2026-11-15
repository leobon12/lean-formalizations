/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrWalk3

/-!
# The lower walk restarted at `v`: its physical set

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). For the actual staged lower walk (regularized) of
`h`, and the walk of the translated field `affField (−v) h` from `0` whose first driver is any regular driver of zero
lifetime and whose later drivers are the original ones (`restartFam`), almost surely the translated lower walk is the
arc `[−v, 0]` together with the restarted walk (**`ae_lowerWalk_restart`**).

* `flowStep_eq_launch_iff`: whether a flow step launches only depends on the status and the heights.
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

theorem launch_ne_self (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    s ≠ ExplState.launch s k d θ t := fun h => by
  have := congrArg (fun x : ExplState => x.1.length) h
  simp only [(launch_components s k d θ t).1, List.length_append, List.length_singleton] at this
  omega

theorem setDead_ne_launch (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    Exist.StagedLaw.setDead s ≠ ExplState.launch s k d θ t := fun h => by
  have := congrArg (fun x : ExplState => x.1.length) h
  have e : (Exist.StagedLaw.setDead s).1 = s.1 := by obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl
  simp only [e, (launch_components s k d θ t).1, List.length_append, List.length_singleton] at this
  omega

open Classical in
/-- **Whether a flow step launches only depends on the status and the heights.** -/
theorem flowStep_eq_launch_iff {κ : ℝ} {b : ℝ → ℝ} (gw2 : Bool) (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.flowStep κ b gw2 s k d θ t = ExplState.launch s k d θ t ↔
      (stStatus s = .inl () ∨ stStatus s = stTip) ∨
        (¬ (stStatus s = stDone ∨ stStatus s = stDead) ∧ gw2 = false ∧
          ExplState.IsAdmissibleSeed κ (ExplState.heights κ b s).1 (ExplState.heights κ b s).2 θ) := by
  rw [flowStep_eq_cases]
  split_ifs with h1 h2 h3 h4
  · exact iff_of_true rfl (Or.inl h1)
  · refine iff_of_false (launch_ne_self s k d θ t) ?_
    rintro (h | ⟨h, -, -⟩)
    · exact h1 h
    · exact h h2
  · refine iff_of_false (setDead_ne_launch s k d θ t) ?_
    rintro (h | ⟨-, hg, -⟩)
    · exact h1 h
    · exact absurd h3 (by simp [hg])
  · exact iff_of_true rfl (Or.inr ⟨h2, by simpa using h3, h4⟩)
  · refine iff_of_false (launch_ne_self s k d θ t) ?_
    rintro (h | ⟨-, -, hA⟩)
    · exact h1 h
    · exact h4 hA

theorem flowStep_eq_launch_trState_iff {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ) (gw2 : Bool) (s : ExplState) (k : ℕ)
    (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.flowStep κ (affData 1 (-v) b) gw2 (trState v s) k d θ t = ExplState.launch (trState v s) k d θ t ↔
      ExplState.flowStep κ b gw2 s k d θ t = ExplState.launch s k d θ t := by
  rw [flowStep_eq_launch_iff, flowStep_eq_launch_iff, stStatus_trState, heights_trState hb]

/-! ### The restarted walk -/

/-- **The restarted lower-walk family**: a given first driver, then the given drivers. -/
def restartFam {Ω : Type*} (d₀ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j ω => if j = 0 then d₀ ω else D j ω

theorem physSet_eq_statePhys (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.physSet κ b J spec D = statePhys spec.1 (ExplState.run κ b J spec D spec.2.2.length) := by
  rw [← prefixPhysSet_length, prefixPhysSet_eq_statePhys]

theorem two_le_walkProg_length (b : ℝ → ℝ) (J : Finset ℝ) : 2 ≤ (walkProg b J).length := by
  simp [walkProg, boundaryWalkSpec, List.length_flatten, List.replicate_succ]

section Fam

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The lower walk is the forced arc `[0, v]` together with the walk restarted at `v`** (in the plane translated by
`−v`), almost surely, when the restarted walk starts with a zero-lifetime piece. -/
theorem ae_lowerWalk_restart (h13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b J P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b J P spec (E spec))
    {v : ℝ} (hv : 0 < v) (hlow0 : rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow : ∀ x ∈ jumpSet b J, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    {d₀ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hd₀ : ∀ ω, IsRegularDriver (d₀ ω)) (hz₀ : ∀ᵐ ω ∂P, (d₀ ω).2 = 0) :
    ∀ᵐ ω ∂P, (fun z => z - (v : ℂ)) '' lowerWalkSet κ b J E ω =
      ((↑) : ℝ → ℂ) '' Icc (-v) 0 ∪ ExplState.physSet κ (affData 1 (-v) b) (affJumps 1 (-v) J)
        (boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J) (-(Real.pi / 2)) true)
        (fun j => restartFam d₀ (StagedReg.regHist (boundaryWalkSpec b J (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b J (-(Real.pi / 2)) true))) j ω) := by
  set lw := boundaryWalkSpec b J (-(Real.pi / 2)) true with hlw
  set D := StagedReg.regHist lw (E lw) with hDdef
  have hprog : IsBoundaryContinuedProgram lw.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b J ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hD : IsStagedHistory κ b J P h lw D := StagedReg.isStagedHistory_regHist hb (hE lw hprog) (hER lw hprog)
  have hR : StagedPiecesRegular κ b J P lw D := WalkLaw.stagedPiecesRegular_regHist (hER lw hprog)
  have hreg : ∀ j ω, IsRegularDriver (D j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  set B := affData 1 (-v) b with hB
  set JB := affJumps 1 (-v) J with hJB
  have hlow₁ : rightLim B (-v) - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
    rw [show -v = 0 - v by ring, hB, rightLim_trData hb v 0]; exact hlow0
  have hlow₂ : rightLim B 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
    rw [show (0 : ℝ) = v - v by ring, hB, rightLim_trData hb v v]; exact rightLim_low_of_arc hb hv hlow0 hlow
  have hmid : ∀ y ∈ jumpSet B JB, -v < y → y ≤ 0 → ¬ -sleLambda κ < rightLim B y + -(Real.pi / 2) * chiC κ := by
    intro y hy h1 h2 hlt
    rw [hB, hJB, jumpSet_trData hb] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    simp only [Equiv.coe_toEmbedding, Equiv.subRight_apply] at h1 h2 hlt
    rw [hB, rightLim_trData hb] at hlt
    have := hlow x hx (by linarith) (by linarith)
    linarith
  filter_upwards [StagedReg.ae_run_regHist (hER lw hprog), ae_run_trState (κ := κ) hb v hR hreg,
    ae_walk_rightExit h13₀ hκ hκ4 hb hh hcf hζ' hD hreg,
    ae_walk_zero_lifetime hκ hb hh hD (not_admissible_of_low hlow0), hz₀] with ω h1 h2 h3 h4 h5
  have hlen : lw.2.2.length = (walkProg b J).length := rfl
  rw [trSpec_walk] at h2
  -- the left side
  have hL : lowerWalkSet κ b J E ω = ExplState.physSet κ b J lw (fun j => D j ω) :=
    (StagedReg.physSet_eq_of_run_eq (h1 _)).symm
  have hT := physSet_trSpec (κ := κ) (b := b) (J := J) v lw (fun j => D j ω) (fun j => D j ω)
    (by rw [trSpec_walk, h2 _]) (by rw [trSpec_walk, h2 _])
  rw [trSpec_walk] at hT
  rw [hL, ← hT, physSet_eq_statePhys, walkSpec_tr hb v, physSet_eq_statePhys]
  -- the restart
  have hstep : ∀ j, 2 ≤ j → ∀ θ t, ((-v : ℝ), false, walkProg b J).2.2[j]? = some (.inl (θ, t)) →
      ExplState.flowStep κ B false (ExplState.run κ B JB (-v, false, walkProg b J) (fun i => D i ω) j) j (D j ω) θ t =
        ExplState.launch (ExplState.run κ B JB (-v, false, walkProg b J) (fun i => D i ω) j) j (D j ω) θ t →
      (min t (D j ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (D j ω)))) ∧
        RightExit (ExplState.run κ B JB (-v, false, walkProg b J) (fun i => D i ω) j) t (D j ω) := by
    intro j _ θ t hj hfl
    rw [h2 j] at hfl ⊢
    rw [flowStep_eq_launch_trState_iff hb] at hfl
    obtain ⟨hg, hR⟩ := h3 j θ t hj hfl
    exact ⟨hg, rightExit_trState v hR⟩
  exact statePhys_restart (walkProg b J) (walkProg_zero b J) (walkProg_one b J) (by linarith) rfl
    (show restartFam d₀ D 0 ω = d₀ ω by simp [restartFam]) (hreg 0 ω) (hd₀ ω) h4 h5 hlow₁ hlow₂ hmid
    (fun j => hreg j ω) (fun j hj => by simp [restartFam, show j ≠ 0 by omega]) hstep _
    (two_le_walkProg_length b J)

end Fam

end InteractingSLE.Theorem14.SB.Lf
