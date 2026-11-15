/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafConn
import InteractingSLE.Spec.Supplement.GW4LeafPieceLaw
import InteractingSLE.Spec.Supplement.GW1WalkExitParam

/-!
# The counterflow visits both walks in strict reverse first-visit order

Packet PROVE-T14-GW4REG. Lemma GW1 (p. 618–620) and Theorem GW4's proof (p. 637: "GW1 puts both walks in that range",
"their first visits by `η` have strict reverse order on both"). This file proves
`GW4BarrierSelf.CounterflowWallOrderRegStatement` (**`counterflowWallOrderRegStatement_of_inputs`**) from

* GB6's restart law, Theorem 1.3 (both universes) and GW1's launch clocks (`GW1Z.WalkLaunchClockStatement`): the
  pieces (`walkPieceVisitStatement_of_clock`), the walk's run and its terminal state (GW1's proved run facts);
* Lemma GW2a's containment (`GW2aContainmentStatement`): every connector point is visited; then the real swallowing
  lemma orders the connectors (`connVisitOK_realArc`, `connVisitOK_realRay`);

through the run induction with first-visit data (`exists_reverseVisits_of_run`), and the reparametrization invariance of
reverse first visits (`reverseVisits_of_range_eq`). All five inputs are inputs of the current Theorem 1.4 wiring
(`Wire.theorem14Statement_current_expanded` derives GB6's restart law and the clocks from its leaves, and
`GW2aContainmentStatement` is one of its leaves).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

open GW1X GW1Bookkeep GW1WalkChain GW1Conn Exist Exist.Staged Exist.StagedLaw

/-! ### The direction of the connectors -/

theorem moveAlong_true_of_rFlowInv {κ : ℝ} {b : ℝ → ℝ} {θ : ℝ} {s : ExplState} {r : Bool} {x : ℝ}
    (h : RFlowInv κ b θ (ExplState.moveAlong s r x true)) : r = true := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  obtain ⟨-, -, -, hst⟩ := h
  cases r
  · simp [ExplState.moveAlong] at hst
  · rfl

theorem moveToEnd_true_of_rFlowInv {κ : ℝ} {b : ℝ → ℝ} {θ : ℝ} {s : ExplState} {r : Bool}
    (h : RFlowInv κ b θ (ExplState.moveToEnd s r)) : r = true := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  obtain ⟨harcs, -, -, -⟩ := h
  cases r
  · exfalso
    have hsub := harcs (Iic pt) (by simp [ExplState.moveToEnd])
    have hmem : pt - |pt| - 1 ∈ Iic pt := by
      simp only [mem_Iic]; linarith [abs_nonneg pt]
    have := hsub hmem
    simp only [mem_Ici] at this
    linarith [le_abs_self pt]
  · rfl

theorem moveAlong_false_of_lFlowInv {κ : ℝ} {b : ℝ → ℝ} {θ : ℝ} {s : ExplState} {r : Bool} {x : ℝ}
    (h : LFlowInv κ b θ (ExplState.moveAlong s r x true)) : r = false := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  obtain ⟨-, -, -, hst⟩ := h
  cases r
  · rfl
  · simp [ExplState.moveAlong] at hst

theorem moveToEnd_false_of_lFlowInv {κ : ℝ} {b : ℝ → ℝ} {θ : ℝ} {s : ExplState} {r : Bool}
    (h : LFlowInv κ b θ (ExplState.moveToEnd s r)) : r = false := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  obtain ⟨harcs, -, -, -⟩ := h
  cases r
  · rfl
  · exfalso
    have hsub := harcs (Ici pt) (by simp [ExplState.moveToEnd])
    have hmem : pt + |pt| + 1 ∈ Ici pt := by
      simp only [mem_Ici]; linarith [abs_nonneg pt]
    have := hsub hmem
    simp only [mem_Iic] at this
    linarith [neg_abs_le pt]

/-! ### The physical set grows along the run -/

theorem statePhysicalSet_run_subset (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {m n : ℕ} (hmn : m ≤ n) :
    statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D m) ⊆
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
  induction hmn with
  | refl => exact le_rfl
  | step _ ih =>
    exact ih.trans (GW1Z.prefixPhysSet_subset_succ (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D _)

/-! ### The connector data of the two walks -/

theorem realArc_mem_Icc {q x : ℝ} (hqx : q ≤ x) {t : ℝ≥0} (ht : t ≤ 1) :
    realArc q x t ∈ ((↑) : ℝ → ℂ) '' Icc q x := by
  refine ⟨q + (t : ℝ) * (x - q), ⟨?_, ?_⟩, (realArc_eq q x t).symm⟩
  · nlinarith [t.coe_nonneg]
  · have : (t : ℝ) ≤ 1 := by exact_mod_cast ht
    nlinarith [t.coe_nonneg]

theorem realArc_mem_Icc' {q x : ℝ} (hxq : x ≤ q) {t : ℝ≥0} (ht : t ≤ 1) :
    realArc q x t ∈ ((↑) : ℝ → ℂ) '' Icc x q := by
  refine ⟨q + (t : ℝ) * (x - q), ⟨?_, ?_⟩, (realArc_eq q x t).symm⟩
  · have : (t : ℝ) ≤ 1 := by exact_mod_cast ht
    nlinarith [t.coe_nonneg]
  · nlinarith [t.coe_nonneg]

/-- **The connector data of the right walk**, for one sample: from the walk's invariants (root seed bound, no
left-record threshold) and the visits of all its nonzero points. -/
theorem walkConnVisit_right {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hroot : PiecewiseConstantBoundaryData.leftLim b 0 + -(Real.pi / 2) * QuantumZipper.chiC κ < sleLambda κ)
    (hno : ∀ k, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D
      (k + 1)).2.2.2.2.2.1 ≠ GW1Conn.stThr (some false))
    (hvis : ∀ z ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D
        (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length), z ≠ 0 → ∃ t, γ t ≠ 0 ∧ -(γ t)⁻¹ = z) :
    WalkConnVisit (κ := κ) (b := b) (jumps := jumps) γ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D true := by
  intro k hk hodd
  have hRC := (rInv_run hroot D hno k hk.le).2 hodd
  have hF := rFlowInv_contStep (jumps := jumps) hRC (-(Real.pi / 2))
  set q := stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D k) with hqdef
  have hpt : 0 ≤ q := hRC.2.1
  have heq := GW1W.run_succ_walk_cont (κ := κ) (D := D) hk hodd
  have hsub := statePhysicalSet_run_subset κ b jumps (-(Real.pi / 2)) true D (Nat.succ_le_of_lt hk)
  refine ⟨fun r x hd hs => ?_, fun r hs => ?_⟩
  · rw [hs] at hF
    obtain rfl := moveAlong_true_of_rFlowInv hF
    simp only [↓reduceIte] at hd
    refine connVisitOK_realArc hW' hW'0 hγ (Or.inl ⟨hpt, hd⟩) fun t ht ht1 => hvis _ (hsub ?_) ?_
    · rw [heq, hs, statePhysicalSet_moveAlong]
      exact Or.inr (by simpa using realArc_mem_Icc hd.le ht1)
    · rw [realArc_eq]
      have h0 : (0 : ℝ) < t := ht
      have hne : q + (t : ℝ) * (x - q) ≠ 0 := by nlinarith
      exact_mod_cast hne
  · rw [hs] at hF
    obtain rfl := moveToEnd_true_of_rFlowInv hF
    refine connVisitOK_realRay hW' hW'0 hγ (Or.inl ⟨rfl, hpt⟩) fun t ht => hvis _ (hsub ?_) ?_
    · rw [heq, hs, statePhysicalSet_moveToEnd]
      exact Or.inr ⟨t, rfl⟩
    · have : (0 : ℝ) < t := ht
      simp only [realRay, ↓reduceIte, ne_eq, Complex.ofReal_eq_zero]
      linarith

/-- **The connector data of the left walk** (mirror of `walkConnVisit_right`). -/
theorem walkConnVisit_left {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hroot : -sleLambda κ < PiecewiseConstantBoundaryData.rightLim b 0 + Real.pi / 2 * QuantumZipper.chiC κ)
    (hno : ∀ k, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) D
      (k + 1)).2.2.2.2.2.1 ≠ GW1Conn.stThr (some true))
    (hvis : ∀ z ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) D
        (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length), z ≠ 0 → ∃ t, γ t ≠ 0 ∧ -(γ t)⁻¹ = z) :
    WalkConnVisit (κ := κ) (b := b) (jumps := jumps) γ (boundaryWalkSpec b jumps (Real.pi / 2) false) D false := by
  intro k hk hodd
  have hLC := (lInv_run hroot D hno k hk.le).2 hodd
  have hF := lFlowInv_contStep (jumps := jumps) hLC (Real.pi / 2)
  set q := stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false) D k) with hqdef
  have hpt : q ≤ 0 := hLC.2.1
  have heq := GW1W.run_succ_walk_cont (κ := κ) (D := D) hk hodd
  have hsub := statePhysicalSet_run_subset κ b jumps (Real.pi / 2) false D (Nat.succ_le_of_lt hk)
  refine ⟨fun r x hd hs => ?_, fun r hs => ?_⟩
  · rw [hs] at hF
    obtain rfl := moveAlong_false_of_lFlowInv hF
    simp only [Bool.false_eq_true, ↓reduceIte] at hd
    refine connVisitOK_realArc hW' hW'0 hγ (Or.inr ⟨hpt, hd⟩) fun t ht ht1 => hvis _ (hsub ?_) ?_
    · rw [heq, hs, statePhysicalSet_moveAlong]
      exact Or.inr (by simpa using realArc_mem_Icc' hd.le ht1)
    · rw [realArc_eq]
      have h0 : (0 : ℝ) < t := ht
      have hne : q + (t : ℝ) * (x - q) ≠ 0 := by nlinarith
      exact_mod_cast hne
  · rw [hs] at hF
    obtain rfl := moveToEnd_false_of_lFlowInv hF
    refine connVisitOK_realRay hW' hW'0 hγ (Or.inr ⟨rfl, hpt⟩) fun t ht => hvis _ (hsub ?_) ?_
    · rw [heq, hs, statePhysicalSet_moveToEnd]
      exact Or.inr ⟨t, rfl⟩
    · have : (0 : ℝ) < t := ht
      simp only [realRay, Bool.false_eq_true, ↓reduceIte, ne_eq, Complex.ofReal_eq_zero]
      linarith

/-! ### Each walk, almost surely -/

theorem exists_neg_inv_of_mem_completedRange {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W' ⊤ γ)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {z : ℂ} (hz : z ∈ counterflowCompletedRange W') (hz0 : z ≠ 0) :
    ∃ t, γ t ≠ 0 ∧ -(γ t)⁻¹ = z := by
  unfold counterflowCompletedRange at hz
  rw [CounterflowRange.tipSet_infinitySourceChart_top hγ hW' hW'0] at hz
  rcases hz with ⟨t, ht, rfl⟩ | hz
  · exact ⟨t, ht, rfl⟩
  · exact absurd hz hz0

/-- **Each boundary walk is first visited in strict reverse order** (GW1, GW4's proof), for staged families whose
drivers are regular at every sample: almost surely, for every generating trace `γ` of the counterflow, the walk has a
proper parametrization from `0` along which `γ` first visits the points in strict reverse order. -/
theorem ae_reverseVisits_walk (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (hClock : GW1Z.WalkLaunchClockStatement.{u})
    (hA : GW2aContainmentStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
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
  have hcont := hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _ hwR
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

theorem isCompleteSimpleFlow_of_isProperCurve {g : ℝ≥0 → ℂ} (hg : Supp9B.IsProperCurve g) (hg0 : g 0 = 0) :
    GB11.IsCompleteSimpleFlow g :=
  ⟨hg.1, hg.2.1, hg0, fun t => hg.2.2.1 t, hg.2.2.2⟩

/-- **The counterflow visits both walks in strict reverse first-visit order**
(`GW4BarrierSelf.CounterflowWallOrderRegStatement`),
from GB6's restart law, Theorem 1.3 (both universes), GW1's launch clocks and Lemma GW2a's containment. -/
theorem counterflowWallOrderRegStatement_of_inputs (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0}) (hClock : GW1Z.WalkLaunchClockStatement.{u})
    (hA : GW2aContainmentStatement.{u}) : GW4BarrierSelf.CounterflowWallOrderRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hreg
  have hpi := Real.pi_pos
  filter_upwards [ae_reverseVisits_walk hGB6 h13 h13₀ hClock hA hκ hκ4 hb hh hcf hζ' hE' hreg' true,
    ae_reverseVisits_walk hGB6 h13 h13₀ hClock hA hκ hκ4 hb hh hcf hζ' hE' hreg' false,
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

/-- **The contact order of the two walks** (`GW4BarrierSelf.WalkContactOrderRegStatement`) from the same inputs. -/
theorem walkContactOrderRegStatement_of_inputs (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0}) (hClock : GW1Z.WalkLaunchClockStatement.{u})
    (hA : GW2aContainmentStatement.{u}) : GW4BarrierSelf.WalkContactOrderRegStatement.{u} :=
  walkContactOrderRegStatement_of_wallOrder h13 (counterflowWallOrderRegStatement_of_inputs hGB6 h13 h13₀ hClock hA)

end GW4Leaf

end Theorem14

end InteractingSLE
