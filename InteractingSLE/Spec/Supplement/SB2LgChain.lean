/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LoAE
import InteractingSLE.Spec.Restart.StoppedK2Wire
import InteractingSLE.Spec.Supplement.GW1ParamEvery
import InteractingSLE.Spec.Supplement.SB4RTop
import InteractingSLE.Spec.Supplement.GW1WalkExitParam

/-!
# SB2(2): GW1's per-step facts for the lower walk under the retained kernel (`SB2LowerChainStatement` PROVED)

Packet PROVE-SB2-LIFTSET (round 4). `SB2LoAE.SB2LowerChainStatement` (the per-step facts behind the head inclusion)
follows from Theorems 1.2–1.3 through GW1's landed results:

* **`pieceSimpleAt_congr`**: piece simplicity reads the driver only up to the stop;
  **`walkChainFacts_of_run_eq`**: GW1's per-step facts transfer between driver families with the same runs (the stop
  and the stopped driver of each launched piece are recorded in the run);
* **`ae_walkChainFacts_of_reg`**: for everywhere regular staged families, almost surely (GW1Z's piece simplicity, tip
  coordinates, connector clearance — the per-sample step of `GW1ParamEvery.walkChainStatement_of_pieceSimple`);
* **`sb2LowerChainStatement_of_thm12_thm13`**: GW1's clock route for piece simplicity (as in
  `Wire.walkProperRegStatements_of_thm12_thm13`), tip coordinates and connector clearance from Theorem 1.3, the
  regularized family (`StagedReg.regFam_spec`: the same runs almost surely), and the kernel tower;
* `sb2LowerRelWalkRangeStatement_of_data_thm`, `sb2LowerLaunchLiftStatement_of_data`: the range statement and SB2(2)'s
  combined target (R104a) from `SB2LowerRelDriverDataStatement` (and the conditional half) alone.

R48: Theorems 1.2–1.3 are hypotheses of these Theorem 1.4 results only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

/-- **Piece simplicity reads the driver only up to the stop.** -/
theorem pieceSimpleAt_congr {c : Chart} {W W' : ℝ≥0 → ℝ} {S : ℝ≥0∞} {old : Set ℂ} {q₀ q₁ : ℝ}
    (hWW : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → W t = W' t) (h : PieceSimpleAt c W S old q₀ q₁) :
    PieceSimpleAt c W' S old q₀ q₁ := by
  obtain ⟨f, α, C, hf, hC, hmaps, hW0, hWc, hgen, htr, hinj, hs, he, hm⟩ := h
  have hstop : (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) = fun r : ℝ≥0 => W' (min (r : ℝ≥0∞) S).toNNReal := by
    funext r
    refine hWW _ ?_
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  refine ⟨f, α, C, hf, hC, hmaps, (hWW 0 zero_le).symm.trans hW0, hWc.congr fun t ht => (hWW t ht).symm,
    Restart.StoppedK2.isGeneratingTrace_congr (fun t ht => hWW t ht.le) hgen, htr, hinj, hs, he, ?_⟩
  rw [← hstop]
  exact hm


/-- **GW1's per-step facts transfer between driver families with the same runs** (the piece's stop and stopped
driver are recorded in the run). -/
theorem walkChainFacts_of_run_eq {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hrun : ∀ k, ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' k)
    (h : WalkChainFacts κ b jumps θ D) : WalkChainFacts κ b jumps θ D' := by
  refine ⟨fun k c θ' hl hseed => ?_, fun k => ?_⟩
  · have hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k = some (c, θ') := by
      rw [hrun]; exact hl
    have hseed' : (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) := by
      rw [hrun]; exact hseed
    have hp := h.1 k c θ' hl' hseed'
    rw [hrun k, hrun (k + 1)] at hp
    obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl'
    obtain ⟨-, he', -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D' hl
    have hpc := congrArg (fun s : ExplState => s.1) ((he.symm.trans (hrun (k + 1))).trans he')
    simp only [launch_pieces, hrun k, List.append_cancel_left_eq, List.cons.injEq, Prod.mk.injEq, and_true] at hpc
    obtain ⟨-, hW, hS⟩ := hpc
    rw [hS] at hp
    refine pieceSimpleAt_congr (fun t ht => ?_) hp
    have h1 := congrFun hW t
    have hmin : min (t : ℝ≥0∞) (min (instrTime (boundaryWalkSpec b jumps θ true) k) (D' k).2) = t := min_eq_left ht
    have hmin' : min (t : ℝ≥0∞) (min (instrTime (boundaryWalkSpec b jumps θ true) k) (D k).2) = t := by
      rw [hS]; exact hmin
    rw [hmin, hmin', ENNReal.toNNReal_coe] at h1
    exact h1
  · have := h.2 k
    simp only at this ⊢
    rw [← hrun k, ← hrun (k + 1)]
    exact this


universe u

/-- **GW1's per-step facts for the right walk of an everywhere regular staged family, almost surely** (as in
`GW1ParamEvery.walkChainStatement_of_pieceSimple`: piece simplicity in GW1Z's form, tip coordinates, connector
clearance). -/
theorem ae_walkChainFacts_of_reg (hS : GW1Z.GW1PieceSimpleStatement.{u}) (hT13 : Theorem13Statement.{u})
    (hT : GW1ParamEvery.WalkTipCoordinatesStatement.{u}) (hC : GW1ParamEvery.WalkConnectorClearanceStatement.{u}) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, IsRegularDriver (E spec k ω)) →
      ∀ᵐ ω ∂P, WalkChainFacts κ b jumps (-(Real.pi / 2))
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hR : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec) :=
    fun spec hs => stagedPiecesRegular_of_regular hT13 hκ hb (hE spec hs) (hreg spec)
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hR true,
    hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true] with ω hSω hTω hCω
  refine ⟨fun k c θ hl hseed => ?_, hCω⟩
  have hpr : ∀ j c θ, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps true)
      (fun j => E (GW1Z.walkSpec b jumps true) j ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E (GW1Z.walkSpec b jumps true) j ω).1
        (min (instrTime (GW1Z.walkSpec b jumps true) j) (E (GW1Z.walkSpec b jumps true) j ω).2) := by
    intro j c θ hj
    obtain ⟨f, α, C, hf, hC, h0, hW, hα, htr, hi, ha⟩ := hSω j c θ hj
    exact ⟨h0, hW, α, hα, htr⟩
  have hmaps := GW1WalkChain.maps_H_chart_run (κ := κ) (b := b) (jumps := jumps) (GW1Z.walkSpec b jumps true)
    (fun j => E (GW1Z.walkSpec b jumps true) j ω) hpr k
  obtain ⟨_, _, hc⟩ := eq_launch_of_launches (GW1Z.walkSpec b jumps true)
    (fun j => E (GW1Z.walkSpec b jumps true) j ω) hl
  have hmaps' : MapsTo c.2.1 QuantumZipper.H QuantumZipper.H := by rw [hc]; exact hmaps
  exact GW1WalkChain.pieceSimpleAt_of_isSimplePiece (hSω k c θ hl) hmaps' hseed (hTω k c θ hl).1 (hTω k c θ hl).2


/-- **`SB2LowerChainStatement` from Theorems 1.2–1.3**: GW1's per-step facts for the lower walk hold almost surely
under the retained kernel (GW1's clock route for piece simplicity, as in `Wire.walkProperRegStatements_of_thm12_thm13`;
tip coordinates and connector clearance from Theorem 1.3; regularization `StagedReg.regFam_spec`; the kernel tower). -/
theorem sb2LowerChainStatement_of_thm12_thm13 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerChainStatement.{u} := by
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
  have hreg := ae_walkChainFacts_of_reg hS h13 hT hC
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hP : ∀ᵐ ω ∂P, WalkChainFacts κ b jumps (-(Real.pi / 2))
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) := by
    filter_upwards [hreg κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hreg',
      hrun _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)] with ω hω hrω
    exact walkChainFacts_of_run_eq hrω hω
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hP] with ω₀ h₀
  intro _ _ _ _ _ _ _ _ _
  exact h₀


/-- **The range identity of SB2(2)'s lifted walk from the head-free data alone** (and Theorems 1.2–1.3). -/
theorem sb2LowerRelWalkRangeStatement_of_data_thm (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hD : SB2LowerRelDriverDataStatement.{u}) :
    SB2LowerRelWalkRangeStatement.{u} :=
  sb2LowerRelWalkRangeStatement_of_data hD (sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀)

/-- **SB2(2)'s combined target (R104a) from the head-free data and the conditional half** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_data (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hD : SB2LowerRelDriverDataStatement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_range h12 h13 h12₀ h13₀
    (sb2LowerRelWalkRangeStatement_of_data_thm h12 h13 h12₀ h13₀ hD) hcond

end InteractingSLE.Theorem14.SB.Lk
