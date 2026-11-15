/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QuCore
import InteractingSLE.Spec.Supplement.SB2QtBaseLaw
import InteractingSLE.Spec.Supplement.SB2LgChain
import InteractingSLE.Spec.Supplement.SB2MaSet
import InteractingSLE.Spec.Supplement.SB2JqRun
import InteractingSLE.Spec.Supplement.SB2XvProper
import InteractingSLE.Spec.Supplement.SB4RPath
import InteractingSLE.Spec.Supplement.SB2LkS2
import InteractingSLE.Spec.Supplement.WalkInfLaunch

/-!
# The head inclusion at the base of SB2(2)'s retained-law induction, proved

Worker REVIEW-FABLE-T14. **`sb2LowerBaseHeadStatement`** (Theorems 1.2–1.3): `Qt.SB2LowerBaseHeadStatement`, the named
input of `Qt.sb2LowerBaseLawStatement_of_head`; hence **`sb2LowerBaseLawStatement_of_thms`**:
`Mv.SB2LowerBaseLawStatement`, the base of PROVE-SB2-LCMEAN's retained-law induction.

At the `P` level (the actual samples, no retained kernel): almost surely the lower walk carries GW1's per-step facts,
LIFTSET's run facts, a proper parametrization `β₀`, and — on the upper launch event, by the one-sidedness hypothesis
of SB2(2)'s setting and Lemma S2 (`Lk.s2HullRight`) — the head of `β₀` up to every visit of `R` lies in `hullK A`.
`Qu.statePhysicalSet_inter_H_subset_fillH` then puts `B`'s prefix through a launching stage `ℓ ≤ relOff` in `fill A`,
and `Qu.tipSet_zero_inter_H_eq_empty` adds the piece of stage `ℓ` run for time `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qu

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P Lk

/-- **The head inclusion at the base of SB2(2)'s induction** (Theorems 1.2–1.3). -/
theorem sb2LowerBaseHeadStatement (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Qt.SB2LowerBaseHeadStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft ℓ
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hlwp := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  -- GW1's per-step facts at the `P` level
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
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
  have hregC := ae_walkChainFacts_of_reg hS h13 hT hC
  have hWC : ∀ᵐ ω ∂P, WalkChainFacts κ b jumps (-(Real.pi / 2))
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) := by
    filter_upwards [hregC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hreg',
      hrun _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)] with ω hω hrω
    exact walkChainFacts_of_run_eq hrω hω
  -- LIFTSET's run facts at the `P` level
  have hSD := GW1WalkExit.walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hE' hreg' true
  have hCo := GW1WalkExit.walkCompletionStatement_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _
    hE' hreg' true
  have hWI := ae_walkInputs_of_theorem13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER
  have hβex := Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER
  filter_upwards [hWC, hSD, hCo, hWI, hβex, hER _ hlwp, hER _ hsp, hleft, hrun _ hlwp, hrun _ hsp]
    with ω hWω hSDω hCoω hWIω hβω hRw hRu hleftω hrw hru hst hrel
  -- the walk facts at `ω`
  have hX : RunExitData κ b jumps (-(Real.pi / 2))
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) :=
    runExitData_of_run_eq (fun n => (hrw n).symm) (runExitData_of_stageData hSDω)
  have hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n) := fun n hn => by
    rw [← hrw n]
    exact (allowedSt_run hSDω n).1 hn
  have hdone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω)
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) = stDone := by
    rw [← hrw]
    exact hCoω
  have hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) :=
    fun j c' θ' hl' => hRw j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
  -- the head lies in `hullK A` (Lemma S2, at the sample)
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      PieceRegular (E (upperSpec u l) j ω).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω).2) :=
    fun j c' θ' hl' => hRu j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ :=
    Lf.exists_path_upperPrefix (κ := κ) (b := b) (jumps := jumps) hu l (fun j => E (upperSpec u l) j ω) hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω := hpA
  have hav := hleftω hst.1
  have hav' : prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∩
      rightSideOf (range β₀) = ∅ := by
    rw [hβr]
    exact eq_empty_of_subset_empty ((inter_subset_inter_left _ subset_union_left).trans hav.subset)
  have hAL : upperPrefix κ b jumps E u l k ω ⊆ closedLeftSide β₀ :=
    Lf.subset_closedLeftSide_of_avoid hβ hβ0 hcl hav'
  have hK : ∀ tL : ℝ≥0, β₀ tL = realMax (upperPrefix κ b jumps E u l k ω) →
      β₀ '' Icc 0 tL ⊆ hullK (upperPrefix κ b jumps E u l k ω) := by
    intro tL hβL
    rw [← hpA'] at hAL hβL ⊢
    obtain ⟨-, tR, htR, -, hKR, -⟩ := s2HullRight hp hp0 hpH hβ hβ0 hAL
    have e : tR = tL := hβ.2.1 (htR.trans hβL.symm)
    subst e
    exact hKR
  -- the prefix through `ℓ`
  obtain ⟨hlm, hlh⟩ : (∀ j, NoLeftMove κ b jumps (-(Real.pi / 2))
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) j) ∧
      ∀ j, NoLeftHit κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) j :=
    ⟨fun j => (hWIω j).1, fun j => (hWIω j).2.1⟩
  have hpre := statePhysicalSet_inter_H_subset_fillH hb hX hP hWω hlm hlh hallow hdone hβ hβ0 hβr hK hst.2 hrel
  -- the target hull
  have hfill : fillH (upperPrefix κ b jumps E u l k ω) =
      fillH (SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) k) := by
    show fillH (prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∪
      ((↑) : ℝ → ℂ) '' Icc u 0) = _
    rw [Lw.fillH_union_real]
    unfold SB.prefixPhysSet
    rw [hru k]
  rw [← hfill]
  -- the explored set through the start of stage `ℓ`
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hst.2
  have hℓlen := lt_length_of_launch _ _ hst.2
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  obtain ⟨-, hqP⟩ := prefix_facts hWω.1 hWω.2 ℓ
  obtain ⟨f, α, C, hf, -, -, -, -, hα, -, -, hs, -, -⟩ := hWω.1 ℓ c θ' hcθ (hqP hnd)
  have hc := (eq_launch_of_launches _ _ hcθ).2.2
  intro z hz
  rw [WalkLaw.stageSet_succ] at hz
  rcases hz with hz | hz
  · rw [WalkInf.stageSet_capSpec_of_le hℓlen.le ω le_rfl, Qt.stageSet_eq_prefixPhysSet_inter_H] at hz
    refine hpre ⟨?_, hz.2⟩
    have hz1 := hz.1
    unfold SB.prefixPhysSet at hz1
    rw [hrw ℓ] at hz1
    exact hz1
  · -- the piece of stage `ℓ` run for time `0`
    unfold WalkLaw.pieceSet at hz
    split_ifs at hz with hlz
    · exact absurd hz (notMem_empty z)
    rw [WalkSide.run_capSpec_of_le hℓlen.le _ le_rfl, WalkSide.instrTime_capSpec hℓlen.le, ENNReal.coe_zero,
      min_eq_left zero_le] at hz
    have hW0 : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).1 0 = 0 :=
      (hreg' _ ℓ ω).2.1
    have hchart : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ).2.2.2.2.1 = c := by
      rw [hrw ℓ, hc]
    rw [hchart] at hz
    have hα0 : α 0 = 0 := hα.1
    have hf0 : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (f 0)) := hf 0 (by show (0 : ℝ) ≤ (0 : ℂ).im; simp)
    have hq : f 0 = ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) : ℝ) : ℂ) := by
      rw [← hα0]
      exact hs
    have := tipSet_zero_inter_H_eq_empty hf0 hq hW0
    exact absurd hz (by rw [this]; exact notMem_empty z)

/-- **The base of SB2(2)'s retained-law induction, outright** (Theorems 1.2–1.3): LCMEAN's
`Mv.SB2LowerBaseLawStatement`. -/
theorem sb2LowerBaseLawStatement_of_thms (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Mv.SB2LowerBaseLawStatement.{u} :=
  Qt.sb2LowerBaseLawStatement_of_head (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
    (sb2LowerBaseHeadStatement h12 h13 h12₀ h13₀)

end InteractingSLE.Theorem14.SB.Qu
