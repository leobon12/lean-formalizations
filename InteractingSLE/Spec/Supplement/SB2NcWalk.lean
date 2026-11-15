/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcK

/-!
# F2b′: the walk facts at a good sample

Packet PROVE-AUX61-NOJUMP (round 21, D34). **`ae_walkGood`**: almost surely at a launch of the upper schedule, the
facts about the lower walk that PROVE-R6-CORNER's F2a uses (`Dv.sb2LowerStageDrivenStatement_of_thm12_thm13`,
`SBS3DuMain`), collected in **`WalkGood`**:
* GW1's walk chain facts and regular launches;
* no left moves or hits;
* pinch-invariant walk prefixes containing the walk's point;
* the upper prefix as a pinch-invariant path image from `0`;
* a proper parametrization `β` of the walk with the upper prefix on its closed left, and Lemma S3's tail form.

The filter is CORNER's verbatim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open Exist Exist.Staged Exist.StagedLaw Restart Lk LuM

/-- **The walk facts at one sample** (the lower walk's drivers `D = E walk · ω`). -/
structure WalkGood {Ω : Type*} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω : Ω) : Prop where
  chain : WalkChainFacts κ b jumps (-(Real.pi / 2)) fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω
  reg : RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω
  noLeftMove : ∀ n, NoLeftMove κ b jumps (-(Real.pi / 2))
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n
  noLeftHit : ∀ n, NoLeftHit κ b jumps (-(Real.pi / 2))
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n
  pinv : ∀ n, stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n) ≠ GW1Conn.stDone →
    LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n) ∧
    ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n) : ℝ) : ℂ) ∈
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n
  upath : ∃ pA : ℝ → ℂ, ContinuousOn pA (Icc 0 1) ∧ pA 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) ∧
    LuM.PInv 0 (pA '' Icc 0 1) ∧ pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω
  proper : ∃ β : ℝ≥0 → ℂ, Supp9B.IsProperCurve β ∧ β 0 = 0 ∧
    range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
    upperPrefix κ b jumps E u l k ω ⊆ InteractingSLE.closedLeftSide β ∧
    ∀ tR : ℝ≥0, β tR = (realMax (upperPrefix κ b jumps E u l k ω) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ upperPrefix κ b jumps E u l k ω ∩ H

/-- **The walk facts hold almost surely at a launch of the upper schedule** (CORNER's filter). -/
theorem ae_walkGood (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k → WalkGood κ b jumps E u l k ω := by
  have h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  -- GW1's walk statements (as in `S3.Asm.ae_lowerTail_noArc_H`)
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
  have hGB6 := Wire.gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀
    (BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀) (GW1Det.retargetPathStatement hBR4a h12p h13 h13₀)
  have hS := GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 h13 h13₀ hClock
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hT := GW1WalkFinish.walkTipCoordinatesStatement_of_d4 h13 hD4
  have hC := GW1WalkFinish.walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 h13₀) hD4
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hEu := hE _ hsu
  have hRu := hER _ hsu
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set Ew := StagedReg.regFam E w with hEwdef
  have hEw := hE' w hwbc
  have hregw := hreg' w
  have hRw : StagedPiecesRegular κ b jumps P w Ew := stagedPiecesRegular_of_regular h13 hκ hb hEw hregw
  have hWC := Lk.ae_walkChainFacts_of_reg hS h13 hT hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
    (StagedReg.regFam E) hE' hreg'
  have hTip := hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hreg' true
  have hInj := ae_all_iff.2 fun j => LuM.ae_injOn_trOf_walk hκ hκ4 hb hEw hregw hRw j
  have hprop := (Wire.walkProperRegStatements_of_thm12_thm13 h12 h13 h12₀ h13₀).1 κ hκ hκ4 b jumps hb P h hh W' ζ'
    hcf hζ' E hE hER
  have hS3 := S3.Asm.ae_lowerTail_noArc_H h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft
  filter_upwards [hWC, hTip, hInj, GW1W.regLaunches_of_stagedPiecesRegular hRw,
    GW1W.regLaunches_of_stagedPiecesRegular (hER w hwbc), hrun w hwbc, hRu, Lk.ae_injLaunches h13 hκ hκ4 hb hEu hRu,
    Lk.ae_walkInputs_of_theorem13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER, hprop, hS3, hleft] with ω hWCω htipω hinjω
    hRLω hRLEω hrunω hRuω hinjuω hinpω hpropω hS3ω hleftω
  intro hF
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set Dw : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => Ew i ω with hDw
  set Du : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E (Lu.upperSpec u l) i ω with hDu
  have hWω : WalkChainFacts κ b jumps (-(Real.pi / 2)) D := walkChainFacts_of_run_eq hrunω hWCω
  have hpinv : ∀ n, stStatus (ExplState.run κ b jumps w D n) ≠ GW1Conn.stDone →
      LuM.PInv 0 (SB.prefixPhysSet κ b jumps w D n) ∧
        ((stPt (ExplState.run κ b jumps w D n) : ℝ) : ℂ) ∈ SB.prefixPhysSet κ b jumps w D n := by
    intro n hn
    have hpre : SB.prefixPhysSet κ b jumps w D n = SB.prefixPhysSet κ b jumps w Dw n := by
      unfold SB.prefixPhysSet; rw [hrunω n]
    have hn' : stStatus (ExplState.run κ b jumps w Dw n) ≠ GW1Conn.stDone := by rw [hrunω n]; exact hn
    have hpw := LuM.pinv_prefix_walk hRLω hinjω htipω le_rfl n hn'
    have h1 := hpw.1
    have h0 : ((↑) : ℝ → ℂ) '' Icc 0 0 ⊆ SB.prefixPhysSet κ b jumps w Dw n := by
      rw [Icc_self, image_singleton, singleton_subset_iff]
      exact WalkIntRunChron.prefixPhysSet_mono w Dw (Nat.zero_le n)
        (show ((0 : ℝ) : ℂ) ∈ SB.prefixPhysSet κ b jumps w Dw 0 from Or.inl (Or.inl (by simp [hw, boundaryWalkSpec])))
    rw [union_eq_left.2 h0] at h1
    refine ⟨by rw [hpre]; exact h1, ?_⟩
    rw [hpre, ← hrunω n]
    exact hpw.2
  have hreg₀ : ∀ (i : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (Lf.sspec u l) Du (i + 1)).2.2.2.1 i = some (c', θ') →
      GW1P.PieceRegular (Du i).1 (min (instrTime (Lf.sspec u l) i) (Du i).2) :=
    fun i c' θ' hl' => hRuω i θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ := Lf.exists_path_upperPrefix hu l Du hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω := hpA
  have hpv : LuM.PInv 0 (pA '' Icc 0 1) := by rw [hpA]; exact Lk.pinv_schedule hu l Du hreg₀ hinjuω k
  obtain ⟨β, hβ, hβ0, hβr⟩ := hpropω
  have hav := hleftω hF
  have hav' : SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) Du k ∩ rightSideOf (range β) = ∅ := by
    rw [hβr]
    exact eq_empty_of_subset_empty ((inter_subset_inter_left _ subset_union_left).trans hav.subset)
  have hAL : upperPrefix κ b jumps E u l k ω ⊆ closedLeftSide β := Lf.subset_closedLeftSide_of_avoid hβ hβ0 hcl hav'
  exact ⟨hWω, hRLEω, fun n => (hinpω n).1, fun n => (hinpω n).2.1, hpinv, ⟨pA, hp, hp0, hpH, hpv, hpA'⟩,
    ⟨β, hβ, hβ0, hβr, hAL, hS3ω hF β hβ hβ0 hβr⟩⟩

end InteractingSLE.Theorem14.SB.Nc
