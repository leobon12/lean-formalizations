/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513BridgeFrameCentered
import InteractingSLE.Spec.Sec5.Prop513TargetBoundary

/-!
# The source Q-word gives precisely the M-parameter word

The coordinate identity is checked on the boundary with the inherited lifts.
This supplies the deterministic word premise for the source's centred strip
coupling, without an additional boundary-data hypothesis.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.Prop513Bridge
open Sec4 Sec7.StripSysField

/-- The real Q inverse after inversion equals the real M inverse. -/
theorem q_realInv_negInv {q y : ℝ} (hy : y ≠ 0) (hy1 : y ≠ -1) :
    Prop513Target.realInv q (-y⁻¹) = Prop513Field.realInv q y := by
  have hd : y + 1 ≠ 0 := fun he => hy1 (eq_neg_of_add_eq_zero_left he)
  dsimp only [Prop513Target.realInv, Prop513Field.realInv]
  field_simp
  ring

/-- Exact deterministic word identity, including the inherited argument branch. -/
theorem counterflowData_stripQHData {κ q y : ℝ} (hκ : 0 < κ) (hq : 0 < q)
    (hy : y ≠ 0) (hy1 : y ≠ -1) (hyq : y ≠ q) (bL bU : ℝ → ℝ) :
    counterflowData κ (stripQHData κ q bL bU) y =
      stripCounterflowData κ 0 q bL bU y := by
  have hr1 : -y⁻¹ ≠ 1 := by
    intro he
    apply hy1
    have hm := congrArg (fun x : ℝ => x * y) he
    rw [neg_mul, inv_mul_cancel₀ hy, one_mul] at hm
    exact hm.symm
  have hrq : -y⁻¹ ≠ -(1 / q) := by
    intro he
    apply hyq
    have he' : y⁻¹ = q⁻¹ := by simpa only [one_div, neg_inj] using he
    exact inv_injective he'
  have hQ := Prop513Target.data_eq hq (κ := κ) (bL := bL) (bU := bU) hr1 hrq
  rw [q_realInv_negInv hy hy1] at hQ
  have hmid : Prop513Target.realMiddle q (-y⁻¹) = (1 + q) * y / (y + 1) := by
    have hd : y + 1 ≠ 0 := fun he => hy1 (eq_neg_of_add_eq_zero_left he)
    dsimp only [Prop513Target.realMiddle]
    field_simp
    ring
  have hcoef := chiC_sixteen_div hκ
  simp only [counterflowData, inverseData, returnData, cfOffset, cfCoeff, hcoef] at ⊢
  rw [← hQ]
  change -(_ + chiC κ * liftBoundary (Prop513Target.realMiddle q (-y⁻¹))) +
    (-(π * chiC κ) - 2 * π * -chiC κ) + - -chiC κ * liftBoundary y = _
  rw [hmid]
  rcases lt_or_gt_of_ne hy1 with hleft | hright
  · have hyneg : y < 0 := by linarith
    have hmpos : 0 < (1 + q) * y / (y + 1) :=
      div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by linarith) hyneg) (by linarith)
    simp only [liftBoundary, ite_eq_left hyneg, ite_eq_right hmpos.not_gt,
      stripCounterflowData, ite_eq_right (not_lt.2 hleft.le)]
    dsimp only [Prop513Field.realInv]
    ring
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · have hmneg : (1 + q) * y / (y + 1) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) hyneg) (by linarith)
      simp only [liftBoundary, ite_eq_left hyneg, ite_eq_left hmneg,
        stripCounterflowData, ite_eq_left hright]
      dsimp only [Prop513Field.realInv]
      ring
    · have hmpos : 0 < (1 + q) * y / (y + 1) :=
        div_pos (mul_pos (by linarith) hypos) (by linarith)
      simp only [liftBoundary, ite_eq_right hypos.not_gt, ite_eq_right hmpos.not_gt,
        stripCounterflowData, ite_eq_left hright]
      dsimp only [Prop513Field.realInv]
      ring

/-- The three exceptional parameter positions of Fig. 5.1. -/
theorem parameterJumps_fig51 (x₀ : ℝ) :
    Prop513Field.jumps (Real.exp (π * x₀)) (stripHJumps {0} {x₀}) =
      {-1, 0, Real.exp (π * x₀)} := by
  have hq := Real.exp_pos (π * x₀)
  have he : -1 - (1 + Real.exp (π * x₀)) / (-Real.exp (π * x₀) - 1) = 0 := by
    have hd : -Real.exp (π * x₀) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have he' : -1 - (1 + Real.exp (π * x₀)) / -1 = Real.exp (π * x₀) := by ring
  ext x
  simp [Prop513Field.jumps, stripHJumps, he, he', Finset.mem_insert,
    or_assoc, or_comm, or_left_comm]

/-- The canonical source Q-word discharges the boundary identification premise. -/
theorem counterflowData_fig51_eq_off_union {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) :
    ∀ y ∉ counterflowJumps (stripQHJumps (Real.exp (π * x₀)) {0} {x₀}) ∪
      Prop513Field.jumps (Real.exp (π * x₀)) (stripHJumps {0} {x₀}),
      counterflowData κ (stripQHData κ (Real.exp (π * x₀))
        (fig51Lower a b) (fig51Upper x₀ a' b')) y =
      stripCounterflowData κ 0 (Real.exp (π * x₀))
        (fig51Lower a b) (fig51Upper x₀ a' b') y := by
  intro y hy
  have hn : y ∉ Prop513Field.jumps (Real.exp (π * x₀)) (stripHJumps {0} {x₀}) :=
    fun hm => hy (Finset.mem_union.mpr (Or.inr hm))
  rw [parameterJumps_fig51] at hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  exact counterflowData_stripQHData hκ (Real.exp_pos _) hn.2.1 hn.1 hn.2.2 _ _

/-- The concrete frame of the source's Fig. 5.1 Q-field on its original sample
space. No boundary identification or random-field frame hypothesis remains. -/
theorem exists_frame_of_centered_fig51 {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h
      (stripQHData κ (Real.exp (π * x₀)) (fig51Lower a b) (fig51Upper x₀ a' b'))
      (stripQHJumps (Real.exp (π * x₀)) {0} {x₀}))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) :
    ∃ F : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC κ))
        (chiC (16 / κ)) (h ω) (F ω)) ∧
      IsFlowLineDriver (16 / κ)
        (counterflowData κ (stripQHData κ (Real.exp (π * x₀))
          (fig51Lower a b) (fig51Upper x₀ a' b')))
        (counterflowJumps (stripQHJumps (Real.exp (π * x₀)) {0} {x₀})) 0 P F W ζ ∧
      IsStripGFF κ P (fig51Source κ x₀ F)
        (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} ∧
      IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P (fig51Source κ x₀ F) W ζ ∧
      ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * x₀))) (-1)
        (-(π * chiC κ)) (chiC (16 / κ)) (fig51Source κ x₀ F ω) (F ω) := by
  exact exists_frame_of_centered_word hκ
    (isPiecewiseConstantBoundaryData_stripQHData (Real.exp_pos _)
      (isPiecewiseConstantBoundaryData_fig51Lower a b)
      (isPiecewiseConstantBoundaryData_fig51Upper x₀ a' b')) hh hcf
    (counterflowData_fig51_eq_off_union hκ)

end InteractingSLE.Sec5.Prop513Bridge
