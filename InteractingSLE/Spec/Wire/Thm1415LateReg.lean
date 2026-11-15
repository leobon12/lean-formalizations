/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415Now14
import InteractingSLE.Spec.Supplement.GW2aStepWire
import InteractingSLE.Spec.Supplement.PocketMirrorAssembly

/-!
# R51 adapters for the containment consumers of Theorem 1.4

These specialize the landed proofs to regular staged families. Every direct
containment call now receives the regularity already present in the R51
conclusion. No unregularized containment or old BW1 prefix statement is used.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar isOpen_H)
open LQGMetric (DistOn)
universe u
namespace InteractingSLE.Theorem14.LateReg
open Exist Exist.Staged Exist.StagedLaw GW1X GW1Bookkeep GW1WalkChain GW1Conn
open GW4Leaf GW4Traverse GW4Ident GW4Reg GW4BarrierSelf GW3SidedProof GW3Between

def GW6RegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P,
        interior (((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω)) = ∅ →
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
            (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤

/-- R51 specialization of the landed `gw6Statement_of_gw2a` proof. -/
theorem gw6Statement_of_gw2a_lateReg (hGW2a : GW2aCont.GW2aContainmentRegStatement.{u})
    (hthr : GW1FirstThresholdStatement.{u}) : GW6RegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hpi := Real.pi_pos
  have hR := hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
      ⟨le_rfl, by linarith⟩ true)
  have hL := hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2)
      ⟨by linarith, le_rfl⟩ false)
  have tR := hthr κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE (-(Real.pi / 2)) true
    (Or.inl ⟨rfl, rfl⟩)
  have tL := hthr κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE (Real.pi / 2) false
    (Or.inr ⟨rfl, rfl⟩)
  filter_upwards [hR, hL, tR, tL] with ω h1 h2 h3 h4 hint
  have key : ∀ (θ : ℝ) (right : Bool),
      ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right)
          (fun k => E (boundaryWalkSpec b jumps θ right) k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) →
      ((E (boundaryWalkSpec b jumps θ right) 0 ω).2 ≠ ⊤ →
        IsThresholdEnd κ b
          (ExplState.launch (ExplState.init 0) 0 (E (boundaryWalkSpec b jumps θ right) 0 ω) θ ⊤)) →
      (E (boundaryWalkSpec b jumps θ right) 0 ω).2 = ⊤ := by
    intro θ right hsub hthr'
    by_contra hne
    obtain ⟨A, hA, hAi⟩ := exists_mem_arcs_run_boundaryWalkSpec κ b jumps θ right
      (fun k => E (boundaryWalkSpec b jumps θ right) k ω) (hthr' hne)
    have hAsub : A ⊆ ((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω) := fun x hx =>
      hsub (image_subset_physSet κ b jumps _ _ hA (mem_image_of_mem _ hx))
    obtain ⟨x, hx⟩ := hAi
    have := interior_mono hAsub hx
    rw [hint] at this
    exact this
  exact ⟨key _ _ h1 h3, key _ _ h2 h4⟩

/-- R51 specialization of the landed `gw3GeometryRegStatement_of_walks` proof. -/
theorem gw3GeometryRegStatement_of_walks_lateReg (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : LeftWalkProperRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u}) (hF : SB.SBFrontierRegStatement.{u})
    (hNR : RightWalkNegRealRegStatement.{u}) : GW3Sided.GW3GeometryRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hpi := Real.pi_pos
  have hRA := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg, hRA,
    hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hPRω hPLω hRAω hFω hNRω
  obtain ⟨γR, hγR, hγR0, hγRr⟩ := hPRω
  obtain ⟨γL, hγL, hγL0, hγLr⟩ := hPLω
  intro C hC
  right
  rw [← hγRr, ← hγLr] at hC ⊢
  have hRK : range γR ⊆ counterflowCompletedRange (fun t => W' t ω₀) := hγRr ▸ hRAω
  have hKL := hFω.2
  rw [← hγLr] at hKL
  refine hasOrientedUniformizer_of_touching hγR hγR0 hγL hγL0 ?_ ?_ hC
  · rw [Set.disjoint_left]
    intro z hzR hzL
    exact (Set.eq_empty_iff_forall_notMem.1 hKL) z ⟨hRK hzR, hzL⟩
  · exact neg_real_mem_of_frontier hγR (isClosed_range_of_isProperCurve hγL hγL0) hRK hKL (hγRr ▸ hNRω)

/-- R51 specialization of the landed `ae_reverseVisits_walk` proof. -/
theorem ae_reverseVisits_walk_lateReg (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (hClock : GW1Z.WalkLaunchClockStatement.{u})
    (hA : GW2aCont.GW2aContainmentRegStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec k ω, IsRegularDriver (E spec k ω)) (right : Bool) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ →
      ∃ g : ℝ≥0 → ℂ, Supp9B.IsProperCurve g ∧ g 0 = 0 ∧
        range g = ExplState.physSet κ b jumps (GW1Z.walkSpec b jumps right)
          (fun k => E (GW1Z.walkSpec b jumps right) k ω) ∧ ReverseVisits γ g := by
  have hGW0 := BR3Ref.gw0ForwardStatement_of_theorem13.{u} h13₀
  have hR : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec) :=
    fun spec hs => stagedPiecesRegular_of_regular h13 hκ hb (hE spec hs) (hreg spec)
  have hX := GW1WalkExit.walkExitClassificationStatement_of_theorem13.{u} h13₀
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hS := GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 h13 h13₀ hClock κ hκ hκ4 b jumps hb P h hh W' ζ'
    hcf hζ' E hE hreg hR right
  have hT := GW1WalkFinish.walkTipCoordinatesStatement_of_d4 h13 hD4 κ hκ hκ4 b jumps hb P h hh W' ζ'
    hcf hζ' E hE hreg right
  have hC := GW1WalkFinish.walkConnectorClearanceStatement_of_d4_and_exit hX hD4 κ hκ hκ4 b jumps hb P h hh W' ζ'
    hcf hζ' E hE hreg right
  have hDn := GW1WalkFinish.walkCompletionStatement_of_exitClassification hX κ hκ hκ4 b jumps hb P h hh W' ζ'
    hcf hζ' E hE hreg right
  have hPV := walkPieceVisitStatement_of_clock hGB6 hGW0 h13 hClock GW1Z.chartFiberStatement κ hκ hκ4 b jumps hb
    P h hh W' ζ' hcf hζ' E hE hreg hR right
  have hwR := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  have hcont := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR _ hwR
  have htr := GW4Traverse.ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ'
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds hGW0 hκ hκ4 hb hh hcf hζ'
  obtain ⟨hrootL, hrootR⟩ := GW1Conn.root_bounds hb hambL hambR
  have hpi := Real.pi_pos
  have hnoR := GW1W.ae_status_ne_left_right_walk hκ hb hh (hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)) (hreg _) hambL
  have hnoL := GW1W.ae_status_ne_right_left_walk hκ hb hh (hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false)) (hreg _) hambR
  filter_upwards [hS, hT, hC, hDn, hPV, hcont, htr, hnoR, hnoL] with ω hSω hTω hCω hDω hPVω hcω htrω hnoRω hnoLω
  intro γ hγ
  obtain ⟨hW'c, hW'0, -⟩ := htrω
  have hvis : ∀ z ∈ statePhysicalSet 0 (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (GW1Z.walkSpec b jumps right).2.2.length), z ≠ 0 →
      ∃ t, γ t ≠ 0 ∧ -(γ t)⁻¹ = z := fun z hz hz0 =>
    exists_neg_inv_of_mem_completedRange hγ hW'c hW'0 (hcω hz) hz0
  have hP : ∀ k c θ',
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) k) →
      PieceSimpleAt c (E (GW1Z.walkSpec b jumps right) k ω).1
        (min (instrTime (GW1Z.walkSpec b jumps right) k) (E (GW1Z.walkSpec b jumps right) k ω).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) k))
        (stPt (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) k))
        (stPt (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) (k + 1))) := by
    intro k c θ hl hseed
    have hpr : ∀ j c θ, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (E (GW1Z.walkSpec b jumps right) j ω).1
          (min (instrTime (GW1Z.walkSpec b jumps right) j) (E (GW1Z.walkSpec b jumps right) j ω).2) := by
      intro j c θ hj
      obtain ⟨f, α, C, hf, hC, h0, hW, hα, htr, hi, ha⟩ := hSω j c θ hj
      exact ⟨h0, hW, α, hα, htr⟩
    have hmaps := maps_H_chart_run (κ := κ) (b := b) (jumps := jumps)
      (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω) hpr k
    obtain ⟨_, _, hc⟩ := eq_launch_of_launches (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) hl
    have hmaps' : MapsTo c.2.1 QuantumZipper.H QuantumZipper.H := by rw [hc]; exact hmaps
    exact pieceSimpleAt_of_isSimplePiece (hSω k c θ hl) hmaps' hseed (hTω k c θ hl).1 (hTω k c θ hl).2
  have hCV : WalkConnVisit (κ := κ) (b := b) (jumps := jumps) γ (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) right := by
    cases right
    · exact walkConnVisit_left hW'c hW'0 hγ hrootR hnoLω hvis
    · exact walkConnVisit_right hW'c hW'0 hγ hrootL hnoRω hvis
  exact exists_reverseVisits_of_run γ hP (fun k c θ' hl => hPVω γ hγ k c θ' hl) hCω hCV hDω

/-! ### The R51 statement -/

/-- R51 specialization of the landed `counterflowWallOrderRegStatement_of_inputs` proof. -/
theorem counterflowWallOrderRegStatement_of_inputs_lateReg (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0}) (hClock : GW1Z.WalkLaunchClockStatement.{u})
    (hA : GW2aCont.GW2aContainmentRegStatement.{u}) : GW4BarrierSelf.CounterflowWallOrderRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hreg
  have hpi := Real.pi_pos
  filter_upwards [ae_reverseVisits_walk_lateReg hGB6 h13 h13₀ hClock hA hκ hκ4 hb hh hcf hζ' hE' hreg' true,
    ae_reverseVisits_walk_lateReg hGB6 h13 h13₀ hClock hA hκ hκ4 hb hh hcf hζ' hE' hreg' false,
    hrun _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true),
    hrun _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false)]
    with ω hRω hLω hrRω hrLω
  intro αR αL hrR hrL hfR hfL γ hγ
  obtain ⟨gR, hgR, hgR0, hgRr, hgRV⟩ := hRω γ hγ
  obtain ⟨gL, hgL, hgL0, hgLr, hgLV⟩ := hLω γ hγ
  have hRr : range αR = range gR := by
    rw [hrR, hgRr]
    exact (StagedReg.physSet_eq_of_run_eq (hrRω _)).symm
  have hLr : range αL = range gL := by
    rw [hrL, hgLr]
    exact (StagedReg.physSet_eq_of_run_eq (hrLω _)).symm
  exact ⟨reverseVisits_of_range_eq hfR (isCompleteSimpleFlow_of_isProperCurve hgR hgR0) hRr hgRV,
    reverseVisits_of_range_eq hfL (isCompleteSimpleFlow_of_isProperCurve hgL hgL0) hLr hgLV⟩

/-- R51 specialization of the landed `walkContactOrderRegStatement_of_inputs` proof. -/
theorem walkContactOrderRegStatement_of_inputs_lateReg (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0}) (hClock : GW1Z.WalkLaunchClockStatement.{u})
    (hA : GW2aCont.GW2aContainmentRegStatement.{u}) : GW4BarrierSelf.WalkContactOrderRegStatement.{u} :=
  walkContactOrderRegStatement_of_wallOrder h13 (counterflowWallOrderRegStatement_of_inputs_lateReg hGB6 h13 h13₀ hClock hA)

/-- R51 specialization of the landed `walkPocketShapeRegStatement_of_det` proof. -/
theorem walkPocketShapeRegStatement_of_det_lateReg (hdet : PocketShapeDetStatement)
    (hCO : WalkContactOrderRegStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hSB : SB.SBFrontierRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hGeom : GW3Sided.GW3GeometryRegStatement.{u}) : WalkPocketShapeRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hpi := Real.pi_pos
  filter_upwards [hCO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hNC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hSB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true),
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false),
    hGeom κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω hC hN hS hAR hAL hG
  intro αR αL hrR hrL hfR hfL
  refine hdet αR αL hfR hfL (hC αR αL hrR hrL hfR hfL) (fun a b' hab hsub => ?_) ?_ ?_ ?_
  · have hS' : αR '' Icc a b' ⊆ range αR ∩ range αL := fun z hz => ⟨image_subset_range _ _ hz, hsub hz⟩
    rw [hrR, hrL] at hS'
    have hsing := hN (αR '' Icc a b') hS' (isPreconnected_Icc.image _ hfR.1.continuousOn)
    have he := hsing ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩ ⟨b', ⟨hab.le, le_rfl⟩, rfl⟩
    exact absurd (hfR.2.1 he) hab.ne
  · rw [hrR, hrL, Set.disjoint_left]
    intro z hzL hzR
    exact eq_empty_iff_forall_notMem.1 hS.1 z ⟨hAL hzL, hzR⟩
  · rw [hrR, hrL, Set.disjoint_left]
    intro z hzR hzL
    exact eq_empty_iff_forall_notMem.1 hS.2 z ⟨hAR hzR, hzL⟩
  · rw [hrR, hrL]
    exact hG

/-- R51 specialization of the landed `componentKernels_of_betweenInputs` proof. -/
theorem componentKernels_of_betweenInputs_lateReg (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hS : WalkCont.WalkConnectorSideRegStatement.{u})
    (hNP : WalkCont.WalkPieceContinuumRegStatement.{u}) (hUB : GW3UnionLawBetweenRegStatement.{u})
    (hT : GW4R51.GW4TraversalCoreRegStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption)
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) := by assumption) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν := by
  have hG := gw3GeometryRegStatement_of_walks_lateReg hPR hPL hA hF
    (GW3SidedProof.rightWalkNegRealRegStatement_of_pieces hPR hS hNP)
  have hO := GW3Sided.betweenComponentsOpenRegStatement_of_geometry hG
  exact GW4R51.componentKernels_of_regKernels (GW3Sided.gw3ChartRegStatement_of_geometry hG)
    (GW4R51.gw4KernelRegStatement_of_thm12
      (GW3Joint.gw3FieldLawRegStatement_of_oneChart hO (WalkCont.walkNoCommonContinuumRegStatement_of_pieces hPR hS hNP)
        (gw3FieldLawOneChartRegStatement_of_betweenLaw hUB))
      (GW4R51.gw4TraversalRegStatement_of_core hT
        (GW4R51.gw3WordBoundRegStatement_of_inputs hO (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hS)) h12 h13)
    hκ hκ4 hb hh hcf hζ' hE hreg

end InteractingSLE.Theorem14.LateReg
