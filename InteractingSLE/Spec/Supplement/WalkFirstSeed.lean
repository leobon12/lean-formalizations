/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFirstSeedGeometry
import InteractingSLE.Spec.Restart.FCK2TermSource
import InteractingSLE.Spec.Sec7.StripWallStage0

/-! # The first walk exit has a blocked original seed for arbitrary boundary data -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.WalkFirstSeed

open Exist.Staged Exist.StagedLaw GW1WalkExit GW1WalkFinish WalkSeedFinite
open PiecewiseConstantBoundaryData (leftLim rightLim)

/-- At a flow-line seed, zero lifetime implies inadmissibility and positive
lifetime implies admissibility, for the original force word. -/
theorem ae_seed_test_of_isFlowLineDriver {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b jumps θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)) :
    ∀ᵐ ω ∂P,
      ((D ω).2 = 0 → ¬ ExplState.IsAdmissibleSeed κ (leftLim b 0) (rightLim b 0) θ) ∧
      ((D ω).2 ≠ 0 → ExplState.IsAdmissibleSeed κ (leftLim b 0) (rightLim b 0) θ) := by
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  filter_upwards [hC.1.ae_isIntegratedSLEPath] with ω hp
  constructor
  · intro hz
    exact (GW1.thresholdCondition_flowLine_zero_iff hκ b jumps θ).1
      (hp.isForcePath.threshold_of_eq_zero hz)
  · intro hz
    by_contra hbad
    have hthr := (GW1.thresholdCondition_flowLine_zero_iff hκ b jumps θ).2 hbad
    have hnt := hp.isForcePath.not_threshold (t := 0) (pos_iff_ne_zero.2 hz)
    apply hnt
    simpa only [hp.isForcePath.w_zero, hp.isForcePath.vL_zero, hp.isForcePath.vR_zero] using hthr

/-- A real threshold of the first piece inherits the bad original incident
height on its actual recorded side. No ambient side bound is used. -/
theorem seedBlocked_of_incident_at_first_threshold {κ θ : ℝ} {b : ℝ → ℝ}
    {right : Bool} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hP : GW1P.PieceRegular D.1 D.2)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    (hseed : ExplState.IsAdmissibleSeed κ (leftLim b 0) (rightLim b 0) θ)
    (hthr : stStatus (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = stThr (some right))
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace D.1 D.2 α)
    (hbad : (α D.2.toNNReal).im = 0 ∧
      (((α D.2.toNNReal).re ≤ 0 ∧ sleLambda κ ≤ leftLim b (α D.2.toNNReal).re + θ * chiC κ) ∨
        (0 ≤ (α D.2.toNNReal).re ∧ rightLim b (α D.2.toNNReal).re + θ * chiC κ ≤ -sleLambda κ))) :
    SeedBlocked κ b θ (ExplState.launch (ExplState.init 0) 0 D θ ⊤) := by
  have htip := trace_endpoint_eq_launch_point hreg hP hgood hfin hthr hα
  rw [htip] at hbad
  simp only [Complex.ofReal_im, Complex.ofReal_re] at hbad
  have hrec := outwardRecord_le_launch (ownProfile_init right) 0 θ hreg hgood hfin
  have hpt : sideCoord right (stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤)) =
      outwardRecord right (ExplState.launch (ExplState.init 0) 0 D θ ⊤) := by
    cases right
    · exact congrArg Neg.neg (GW1W.launch_thr_false hfin hthr).2.2.1
    · exact (GW1W.launch_thr_true hfin hthr).2.2.1
  have hside : 0 ≤ sideCoord right (stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤)) := by
    rw [hpt]
    simpa only [outwardRecord, stRecR, stRecL, ExplState.init, neg_zero, ite_self] using hrec
  right
  intro ha
  cases right
  · change 0 ≤ -stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) at hside
    rcases hbad.2 with ⟨-, hL⟩ | ⟨hpos, hR⟩
    · have hA := ha.1
      rw [heights_eq, hthr] at hA
      exact (not_lt_of_ge hL) hA
    · have hz : stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = 0 := by linarith only [hside, hpos]
      rw [hz] at hR
      exact (not_le_of_gt hseed.2) hR
  · change 0 ≤ stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) at hside
    rcases hbad.2 with ⟨hneg, hL⟩ | ⟨-, hR⟩
    · have hz : stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = 0 := by linarith only [hside, hneg]
      rw [hz] at hL
      exact (not_le_of_gt hseed.1) hL
    · have hA := ha.2
      rw [heights_eq, hthr] at hA
      exact (not_lt_of_ge hR) hA

/-- The first launched piece of either walk always leaves a terminal state
or an inadmissible original seed. This includes both zero and positive finite
lifetimes, with arbitrary boundary data and arbitrary angle. -/
theorem ae_first_seedBlocked (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ ω, IsRegularDriver (E 0 ω)) :
    ∀ᵐ ω ∂P, SeedBlocked κ b θ
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) 1) := by
  let W : ℝ≥0 → Ω → ℝ := fun t ω => (E 0 ω).1 t
  let ζ : Ω → ℝ≥0∞ := fun ω => (E 0 ω).2
  let α := GW2aSingle.chosenTrace W ζ
  have hfl := hE.isFlowLineDriver_first hκ hb hh rfl (GW1P.boundaryWalkSpec_prog b jumps θ right)
  have hα := GW2aSingle.ae_chosenTrace h13 hκ hfl
  have hη : IsFlowLine κ b jumps 0 θ P h α ζ :=
    Sec7.StripWall.isFlowLine_of_isFlowLineDriver hfl (hα.mono fun _ hω => hω.1)
  have hbad := Restart.FCPlumb.ae_original_terminal_bad_incident hκ hb hη
  have hP := GW1P.ae_pieceRegular_first h13 hκ hb hh hE rfl
    (GW1P.boundaryWalkSpec_prog b jumps θ right)
  have hgood := ae_isDrvGood_of_isFlowLineDriver hκ ⊤ hreg hfl
  filter_upwards [hbad, hα, hP, hgood, ae_seed_test_of_isFlowLineDriver hκ hfl]
    with ω hbω hαω hPω hgω hseed
  have hp : GW1P.PieceRegular (E 0 ω).1 (E 0 ω).2 := by
    simpa only [instrTime, GW1P.boundaryWalkSpec_prog, List.getElem?_cons_zero,
      min_top_left] using hPω
  have hr : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) 1 =
      ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ ⊤ := by
    rw [show 1 = 0 + 1 from rfl, GW1W.run_succ_walk_flow
      (by rw [boundaryWalk_length]; omega) (by rfl)]
    rfl
  rw [hr]
  by_cases ht : (E 0 ω).2 = ⊤
  · exact Or.inl (isTerminal_launch_of_top _ 0 (E 0 ω) θ ⊤ (by rw [ht]; rfl))
  have hg : LocalExt.IsDrvGood (recHist (recOf ⊤ (E 0 ω))) := hgω (GW1W.min_top_ne_top ht)
  by_cases hz : (E 0 ω).2 = 0
  · obtain ⟨hs, hpt, -⟩ := GW1W.launch_zero (s := ExplState.init 0) (k := 0) (θ := θ) hz
      (by intro he; cases he)
    right
    intro ha
    apply hseed.1 hz
    rw [heights_eq, hs] at ha
    change ExplState.IsAdmissibleSeed κ
      (leftLim b (stPt (ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ ⊤)))
      (rightLim b (stPt (ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ ⊤))) θ at ha
    rw [hpt] at ha
    exact ha
  have hi := hbω (E 0 ω).2.toNNReal (ENNReal.toNNReal_pos hz ht) (ENNReal.coe_toNNReal ht)
  have hα' : IsGeneratingTrace (E 0 ω).1 (E 0 ω).2 (α ω) := hαω.1
  rcases GW1W.launch_status_of_pos (s := ExplState.init 0) (k := 0) (θ := θ) ht hz with hs | hs | hs
  · exact seedBlocked_of_incident_at_first_threshold (hreg ω) hp hg ht (hseed.2 hz) hs hα' hi
  · exact seedBlocked_of_incident_at_first_threshold (hreg ω) hp hg ht (hseed.2 hz) hs hα' hi
  · exact Or.inl (Or.inr hs)

end InteractingSLE.Theorem14.WalkFirstSeed
