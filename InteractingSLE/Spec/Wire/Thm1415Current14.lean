/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415CurrentCone
import InteractingSLE.Spec.Supplement.GW2ConeQFixed
import InteractingSLE.Spec.Supplement.GB11GateFinal
import InteractingSLE.Spec.Supplement.CounterflowSeedGerm
import InteractingSLE.Spec.Supplement.GW1ParamEvery
import InteractingSLE.Spec.Supplement.WalkUnionMeanAE
import InteractingSLE.Spec.Supplement.WalkStageLocalKernel
import InteractingSLE.Spec.Supplement.GW4BarrierSelf
import InteractingSLE.Spec.Supplement.SB4SewAssembly
import InteractingSLE.Spec.Supplement.GB6LawFinal
import InteractingSLE.Spec.Supplement.GW2TipUnbounded
import InteractingSLE.Spec.Supplement.GW1RestartPairParam

/-!
# Current conditional assembly of Theorem 1.4

The conclusion contains all four unchanged R51 anchors. GB11, nonreturn,
the schedule condition and the companion are discharged. The frontier adapter
uses the regular light cone directly, avoiding an unregularized GW2 premise.
The expanded theorem exposes the remaining walk, sewing and law obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Wire
open Theorem14

/-- The trace part of Theorem 1.3 is exactly completeness of an ordered word. -/
theorem completeForceWord_of_theorem13 (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact (h13 hκ hF hE).mono fun _ hω => hω.2

/-- Theorem 1.3 supplies the two-seed input to the landed nonreturn theorem. -/
theorem counterflowNoReturnStatement_of_theorem13 (h13 : Exist.Theorem13Statement.{u}) :
    GW4Ident.CounterflowNoReturnStatement.{u} := by
  apply CfNoReturn.counterflowNoReturnStatement_of_twoSeedComplete
  intro κ hκ rL rR _ _
  exact completeForceWord_of_theorem13 h13 (lt_trans (show (0 : ℝ) < 4 by norm_num) hκ)
    (fun _ => rL) (fun _ => rR) LP.isOrderedForceWord_twoSeed

/-- SB's closure argument with the R51 light-cone conclusion and its regular family. -/
theorem sbFrontierRegStatement_of_current (hCone : LightCone14Statement.{u})
    (hSB : SB.SBRegStatement.{u}) : SB.SBFrontierRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hΘ : Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ) ⊆
      Ioo (-(Real.pi / 2)) (Real.pi / 2) := inter_subset_left
  have hΘc : (Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ)).Countable :=
    (countable_range _).mono inter_subset_right
  have hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆
      closure (Ioo (-(Real.pi / 2)) (Real.pi / 2) ∩ range ((↑) : ℚ → ℝ)) :=
    Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo
  obtain ⟨Q, hQc, _, _, hQ⟩ := hCone hκ hκ4 b jumps hb hh hcf hζ' _ hΘ hΘc hΘd
  filter_upwards [(hQ E hE hreg).1,
    hSB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _ hΘ hΘc Q hQc,
    GW1P.gw1ProperRegStatement κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg]
    with ω hω hsb hpr
  rw [← hω]
  refine ⟨SB.closure_inter_eq_empty (SB.isOpen_rightSideOf hpr.1) ?_,
    SB.closure_inter_eq_empty (SB.isOpen_leftSideOf hpr.2) ?_⟩
  · rw [union_inter_distrib_right, hsb.1, empty_union]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hz0, hzR⟩ := hz
    rw [mem_singleton_iff] at hz0
    subst hz0
    exact SB.ofReal_notMem_H 0 (by simpa only [Complex.ofReal_zero] using hzR.1.1)
  · rw [union_inter_distrib_right, hsb.2, empty_union]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hz0, hzL⟩ := hz
    rw [mem_singleton_iff] at hz0
    subst hz0
    exact SB.ofReal_notMem_H 0 (by simpa only [Complex.ofReal_zero] using hzL.1.1)

/-- The three frontier clauses from regular SB and the already landed GW6 reduction. -/
theorem frontiers14Statement_of_current (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) : Frontiers14Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hpi := Real.pi_pos
  have hR := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
      (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)
  have hL := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
      (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false)
  filter_upwards [hR, hL, hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    GW1.gw6Statement_of_gw2aContainment hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE]
    with ω hRω hLω hFω h6ω
  exact ⟨⟨hRω, hFω.1⟩, ⟨hLω, hFω.2⟩, h6ω⟩

/-- All four Theorem 1.4 anchors from the current unresolved named inputs.
This is conditional assembly, not a sealed provider. -/
theorem theorem14Statement_current
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
    (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GW2Later.GB6PrefixPairStatement.{u})
    (hU : GW2Tip.GW2TipJointUnboundedStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hDS : SB.SB4DistinctSeedRegStatement.{u}) (hIA : SB.SB4InitialArcRegStatement.{u})
    (hClock : GW1Z.WalkLaunchClockStatement.{u}) (hpair : WalkPiece.WalkPiecePairRegStatement.{u})
    (hUnion : GW3Between.GW3UnionLawBetweenRegStatement.{u})
    (hB : GW4Reg.GW4BarrierSelfRegStatement.{u}) (hLaw : GW4Reg.GW4RelativeLawRegStatement.{u}) :
    Theorem14Statement.{u} := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hEx := GW2Tip.gw2TipExhaustionAllQStatement_of_canonAllQ h12 h13
    (GW2Tip.gw2TipExhaustionCanonAllQStatement_of_jointUnbounded hU)
  have hCone : LightCone14Statement.{u} := lightCone14Statement_of_inputs_current h13 h13₀ hBR4a hGB6 hG h12p hEx hA
  have hF := sbFrontierRegStatement_of_current hCone
    (SB.sbRegStatement_of_sb4_sb5 (SB.sb4RegStatement_of_distinctSeed hDS)
      (SB.sb5RegStatement_of_inputs (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hIA hDS))
  obtain ⟨hGR, hGL⟩ := GW1WalkExit.paramEveryRegStatements_of_walkClock hGB6 h13 h13₀ hClock
  have hPR := GW1X.rightWalkProperRegStatement_of_gw1ParamR51
    (GW1X.gw1ParamR51Statement_of_everyReg hGR)
  have hPL := WalkProper.leftWalkProperRegStatement_of_everyReg hGL
  have hS := GW1X.walkConnectorSideRegStatement_of_theorem13 h13₀
  have hNP := WalkPiece.walkPieceContinuumRegStatement_of_pair hPR hPL hpair
  have hGeom := GW3SidedProof.gw3GeometryRegStatement_of_walks hPR hPL hA hF
    (GW3SidedProof.rightWalkNegRealRegStatement_of_pieces hPR hS hNP)
  have hO := GW3Sided.betweenComponentsOpenRegStatement_of_geometry hGeom
  have hWB := GW4R51.gw3WordBoundRegStatement_of_inputs hO
    (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hS
  have hT := GW4Reg.gw4TraversalCoreRegStatement_of_relParam h12 h13 hO hWB GB11Chart.gb11RelParamStatement
    (GW4Reg.gw4BarrierPocketRegStatement_of_self hB) hLaw
    (counterflowNoReturnStatement_of_theorem13 h13)
  refine ⟨hCone, frontiers14Statement_of_current hA hF, ?_, ?_⟩
  · intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
    exact GW3Between.componentKernels_of_betweenPair hPR hPL hA hF hpair hUnion hT h12 h13 h13₀
      hκ hκ4 hb hh hcf hζ' hE hreg
  · intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh
    exact exists_isStagedHistory_of_wire6 h12 h13 hκ hκ4 hb hh

/-- Fully expanded open leaves on the current Theorem 1.4 route.
The per-stage exhaustion construction and the retained laws remain explicit;
GB11, walk geometry, completion and nonreturn are not hypotheses. -/
theorem theorem14Statement_current_expanded
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBR4a : BR4a.BR4aStatement.{u})
    (hD : Supp8.GB6.GB6CondDetStatement.{u}) (hG : GW2Later.GB6PrefixPairStatement.{u})
    (hStages : GW2TipStage.GW2StageSystemStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hDS : SB.SB4DistinctSeedRetainedTailStatement.{u}) (hIA : SB.SB4InitialArcRetainedTailStatement.{u})
    (hTerminal : GW1RestartPair.TerminalRestartLawStatement.{u})
    (hRetarget : GW1RestartPair.FiniteRetargetLawStatement.{u})
    (hpair : WalkPiece.WalkPiecePairRegStatement.{u})
    (hkR : WalkLaw.WalkStageLaunchLocalStatement.{u} (-(Real.pi / 2)) true)
    (hkL : WalkLaw.WalkStageLaunchLocalStatement.{u} (Real.pi / 2) false)
    (hM : WalkLaw.WalkUnionMeanRegAEStatement.{u})
    (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hPS : GW4BarrierSelf.WalkPocketShapeRegStatement.{u})
    (hVO : GW4BarrierSelf.CounterflowWallOrderRegStatement.{u})
    (hLaw : GW4Reg.GW4RelativeLawRegStatement.{u}) : Theorem14Statement.{u} := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hComplete : Supp8.GB6.CompleteSixteenDivStatement := by
    intro κ hκ _ nL nR xL xR ρL ρR hF
    exact completeForceWord_of_theorem13 h13₀ (div_pos (by norm_num) hκ) ρL ρR hF
  have hGB6 := Supp8.GB6.gb6RestartStatement_of_param_complete h12p₀ h13₀ hComplete hD
  have hU := GW2TipStage.gw2TipJointUnboundedStatement_of_stageSystems hStages
  have hClock := GW1RestartPair.walkLaunchClockStatement_of_terminal_and_retarget_laws
    hGB6 h13 h13₀ hTerminal hRetarget
  have hDS' := SB.sb4DistinctSeedRegStatement_of_retainedTail hDS
  have hIA' := SB.sb4InitialArcRegStatement_of_retainedTail hIA
  have hEx := GW2Tip.gw2TipExhaustionAllQStatement_of_canonAllQ h12 h13
    (GW2Tip.gw2TipExhaustionCanonAllQStatement_of_jointUnbounded hU)
  have hCone : LightCone14Statement.{u} := lightCone14Statement_of_inputs_current h13 h13₀ hBR4a hGB6 hG h12p hEx hA
  have hF := sbFrontierRegStatement_of_current hCone
    (SB.sbRegStatement_of_sb4_sb5 (SB.sb4RegStatement_of_distinctSeed hDS')
      (SB.sb5RegStatement_of_inputs (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hIA' hDS'))
  obtain ⟨hGR, hGL⟩ := GW1WalkExit.paramEveryRegStatements_of_walkClock hGB6 h13 h13₀ hClock
  have hPR := GW1X.rightWalkProperRegStatement_of_gw1ParamR51
    (GW1X.gw1ParamR51Statement_of_everyReg hGR)
  have hPL := WalkProper.leftWalkProperRegStatement_of_everyReg hGL
  have hS := GW1X.walkConnectorSideRegStatement_of_theorem13 h13₀
  have hNP := WalkPiece.walkPieceContinuumRegStatement_of_pair hPR hPL hpair
  have hNC := WalkCont.walkNoCommonContinuumRegStatement_of_pieces hPR hS hNP
  have hB := GW4BarrierSelf.gw4BarrierSelfRegStatement_of_walks h13 hPR hPL hNC hF hCO hPS hVO
  exact theorem14Statement_current h12 h13 h13₀ hBR4a hGB6 hG hU hA hDS' hIA' hClock hpair
    (WalkLaw.gw3UnionLawBetweenRegStatement_of_kernel h12p h13
      (WalkLaw.walkStageKernelLocalStatement_of_launch ⟨le_rfl, by linarith [Real.pi_pos]⟩ hkR)
      (WalkLaw.walkStageKernelLocalStatement_of_launch ⟨by linarith [Real.pi_pos], le_rfl⟩ hkL) hM) hB hLaw

end InteractingSLE.Wire
