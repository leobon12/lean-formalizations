/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExit

/-! # GW1: classified stage exits and their measurable events -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw Restart GW1WalkFinish
open PiecewiseConstantBoundaryData (leftLim rightLim)

/-- The outward original height forces a boundary continuation after a finite exit. -/
def BadOutwardHeight (κ : ℝ) (b : ℝ → ℝ) (right : Bool) (s : ExplState) : Prop :=
  if right then rightLim b (stPt s) + stAngle s * chiC κ ≤ -sleLambda κ
  else sleLambda κ ≤ leftLim b (stPt s) + stAngle s * chiC κ

/-- In addition to the exit direction, retain the height needed for the next restart. -/
def ClassifiedExit (κ : ℝ) (b : ℝ → ℝ) (right : Bool) (s t : ExplState) : Prop :=
  ForwardExit κ b right s t ∧ (stStatus t ≠ stDone → BadOutwardHeight κ b right t)

theorem measurableSet_badOutwardHeight {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type*} [MeasurableSpace Ω]
    {S : Ω → ExplState} (hS : IsMeasState S) (right : Bool) :
    MeasurableSet {ω | BadOutwardHeight κ b right (S ω)} := by
  cases right
  · exact measurableSet_le measurable_const
      (((measurable_leftLim_of_pcbd hb).comp hS.2.1).add (hS.2.2.1.mul_const _))
  · exact measurableSet_le
      (((measurable_rightLim_of_pcbd hb).comp hS.2.1).add (hS.2.2.1.mul_const _)) measurable_const

theorem measurableSet_outwardThreshold {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type*} [MeasurableSpace Ω]
    {S : Ω → ExplState} (hS : IsMeasState S) (right : Bool) :
    MeasurableSet {ω | OutwardThreshold κ b right (S ω)} := by
  have hB := measurableSet_badOutwardHeight (κ := κ) hb hS right
  cases right
  · have hR : MeasurableSet {ω | -sleLambda κ <
        rightLim b (stPt (S ω)) + stAngle (S ω) * chiC κ} :=
      measurableSet_lt measurable_const
        (((measurable_rightLim_of_pcbd hb).comp hS.2.1).add (hS.2.2.1.mul_const _))
    exact (hS.1 _).union ((hS.1 _).inter (hR.inter hB))
  · exact (hS.1 _).union ((hS.1 _).inter hB)

theorem measurableSet_classifiedExit {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type*} [MeasurableSpace Ω]
    {S T : Ω → ExplState} (hS : IsMeasState S) (hT : IsMeasState T) (right : Bool) :
    MeasurableSet {ω | ClassifiedExit κ b right (S ω) (T ω)} := by
  have hle : MeasurableSet {ω | sideCoord right (stPt (S ω)) ≤ sideCoord right (stPt (T ω))} := by
    cases right
    · exact measurableSet_le hS.2.1.neg hT.2.1.neg
    · exact measurableSet_le hS.2.1 hT.2.1
  have himp : MeasurableSet {ω | stStatus (T ω) ≠ stDone →
      BadOutwardHeight κ b right (T ω)} :=
    ((hT.1 stDone).union (measurableSet_badOutwardHeight (κ := κ) hb hT right)).congr (by
      ext ω
      simp only [mem_union, mem_ofPred_eq]
      tauto)
  exact ((hT.1 _).union (hle.inter (measurableSet_outwardThreshold hb hT right))).inter himp

theorem classifiedExit_launch_right {κ θ : ℝ} {b : ℝ → ℝ} {s : ExplState}
    (hs : GW1W.RProf s) (hready : GW1W.RReady s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hpos : D.2 ≠ ⊤ → D.2 ≠ 0 →
      stStatus (ExplState.launch s k D θ ⊤) = stThr (some true))
    (hzero : D.2 = 0 → rightLim b (stPt s) + θ * chiC κ ≤ -sleLambda κ)
    (hbad : stStatus (ExplState.launch s k D θ ⊤) = stThr (some true) →
      rightLim b (stRecR (ExplState.launch s k D θ ⊤)) + θ * chiC κ ≤ -sleLambda κ) :
    ClassifiedExit κ b true s (ExplState.launch s k D θ ⊤) := by
  by_cases htop : D.2 = ⊤
  · have hd := (launch_eq_of_top s k D θ ⊤ (by rw [htop]; exact min_self _)).2.2.2.2.1
    exact ⟨Or.inl hd, fun hn => False.elim (hn hd)⟩
  by_cases hz : D.2 = 0
  · have hnt : stStatus s ≠ .inr (.inl ()) := by
      rcases hready.1 with h | h <;> rw [h] <;> intro he <;> cases he
    obtain ⟨hst, hpt, hang⟩ := GW1W.launch_zero (k := k) (θ := θ) hz hnt
    have hb : BadOutwardHeight κ b true (ExplState.launch s k D θ ⊤) := by
      change rightLim b _ + _ ≤ _
      rw [hpt, hang]
      exact hzero hz
    exact ⟨Or.inr ⟨by rw [hpt], Or.inr ⟨hst, hb⟩⟩, fun _ => hb⟩
  have hst := hpos htop hz
  obtain ⟨-, -, hpt, hang⟩ := GW1W.launch_thr_true htop hst
  have hb : BadOutwardHeight κ b true (ExplState.launch s k D θ ⊤) := by
    change rightLim b _ + _ ≤ _
    rw [hpt, hang]
    exact hbad hst
  refine ⟨Or.inr ⟨?_, Or.inl hst⟩, fun _ => hb⟩
  change stPt s ≤ stPt (ExplState.launch s k D θ ⊤)
  rw [hpt, hready.2]
  exact recR_le_launch hs k θ hreg (hgood htop) htop

theorem classifiedExit_launch_left {κ θ : ℝ} {b : ℝ → ℝ} {s : ExplState}
    (hs : GW1W.LProf s) (hready : GW1W.LReady s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hpos : D.2 ≠ ⊤ → D.2 ≠ 0 →
      stStatus (ExplState.launch s k D θ ⊤) = stThr (some false))
    (hzero : D.2 = 0 → -sleLambda κ < rightLim b (stPt s) + θ * chiC κ ∧
      sleLambda κ ≤ leftLim b (stPt s) + θ * chiC κ)
    (hbad : stStatus (ExplState.launch s k D θ ⊤) = stThr (some false) →
      sleLambda κ ≤ leftLim b (stRecL (ExplState.launch s k D θ ⊤)) + θ * chiC κ) :
    ClassifiedExit κ b false s (ExplState.launch s k D θ ⊤) := by
  by_cases htop : D.2 = ⊤
  · have hd := (launch_eq_of_top s k D θ ⊤ (by rw [htop]; exact min_self _)).2.2.2.2.1
    exact ⟨Or.inl hd, fun hn => False.elim (hn hd)⟩
  by_cases hz : D.2 = 0
  · have hnt : stStatus s ≠ .inr (.inl ()) := by
      rcases hready.1 with h | h <;> rw [h] <;> intro he <;> cases he
    obtain ⟨hst, hpt, hang⟩ := GW1W.launch_zero (k := k) (θ := θ) hz hnt
    have hbad0 := hzero hz
    have hb : BadOutwardHeight κ b false (ExplState.launch s k D θ ⊤) := by
      change _ ≤ leftLim b _ + _
      rw [hpt, hang]
      exact hbad0.2
    refine ⟨Or.inr ⟨by rw [hpt], Or.inr ⟨hst, ?_⟩⟩, fun _ => hb⟩
    change -sleLambda κ < rightLim b _ + _ ∧ _
    rw [hpt, hang]
    exact hbad0
  have hst := hpos htop hz
  obtain ⟨-, -, hpt, hang⟩ := GW1W.launch_thr_false htop hst
  have hb : BadOutwardHeight κ b false (ExplState.launch s k D θ ⊤) := by
    change _ ≤ leftLim b _ + _
    rw [hpt, hang]
    exact hbad hst
  refine ⟨Or.inr ⟨?_, Or.inl hst⟩, fun _ => hb⟩
  change -stPt s ≤ -stPt (ExplState.launch s k D θ ⊤)
  rw [hpt, hready.2]
  exact neg_le_neg (launch_le_recL hs k θ hreg (hgood htop) htop)

end InteractingSLE.Theorem14.GW1WalkExit
