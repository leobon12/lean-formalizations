/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma47AnglePass
/-!
# Lemma 4.7 at a relative angle: admissibility and junction bounds

The counterflow's partial sums follow from `CfThetaBounds`. The two new total
weights are `(3/2 ∓ θ/π)(8/κ - 2)`, so both retain the nonhitting bound on the
closed interval of allowed angles. Prefix transport and `prefix_snoc` are reused.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real
universe u
namespace InteractingSLE.Sec5.Lemma47Angle
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar WholeField CrossCond.Theta
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
section Weights
variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
theorem hasAdmissiblePartialSums_q_angle (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) :
    Sec4.HasAdmissiblePartialSums (16 / κ) (qρLT κ θ ρL ρR xL xR) (qρRT κ θ ρL ρR xL xR) (qxLT κ θ ρL ρR xL xR)
      (qxRT κ θ ρL ρR xL xR) := by
  have hk' : 0 < 16 / κ := by positivity
  have hb := Cond44Ref.isPiecewiseConstant_forceData κ ρL ρR xL xR (-(θ * QuantumZipper.chiC κ))
  obtain ⟨hbL, hbR⟩ := hθb
  have hbd := CfRegQ.counterflowData_bounds hκ
    (g := fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * QuantumZipper.chiC κ))
    (fun x hx => hbL x hx) (fun x hx => hbR x hx)
  exact Sec4.hasAdmissiblePartialSums_flowLine hk' (Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hb)
    (fun x hx _ => hbd.1 x hx) (fun x hx _ => hbd.2 x hx)

theorem strictAnti_qxL_angle (κ θ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    StrictAnti (qxLT κ θ ρL ρR xL xR) := fun _ _ h => Theorem14.GW0.flowLineXL_lt _ _ 0 h

theorem strictMono_qxR_angle (κ θ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    StrictMono (qxRT κ θ ρL ρR xL xR) := fun _ _ h => Theorem14.GW0.flowLineXR_lt _ _ 0 h

open Finset in
/-- The counterflow word's left prefix sums are at least `8/κ − 2`. -/
theorem prefix_qρL_angle (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) :
    ∀ m : ℕ, 1 ≤ m → m ≤ flowLineNL (Sec7.StripSysField.counterflowData κ (bDataT ρL ρR xL xR θ κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0 →
      16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin _ => i.val < m), qρLT κ θ ρL ρR xL xR i :=
  prefixL_of_hasAdmissiblePartialSums (hasAdmissiblePartialSums_q_angle hκ hθb) (strictAnti_qxL_angle κ θ ρL ρR xL xR)
    (fun i => Theorem14.GW3Word.flowLineXL_nonpos _ _ i)

open Finset in
/-- The counterflow word's right prefix sums are at least `8/κ − 2`. -/
theorem prefix_qρR_angle (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) :
    ∀ m : ℕ, 1 ≤ m → m ≤ flowLineNR (Sec7.StripSysField.counterflowData κ (bDataT ρL ρR xL xR θ κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0 →
      16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin _ => i.val < m), qρRT κ θ ρL ρR xL xR i :=
  prefixR_of_hasAdmissiblePartialSums (hasAdmissiblePartialSums_q_angle hκ hθb) (strictMono_qxR_angle κ θ ρL ρR xL xR)
    (fun i => Theorem14.GW3Word.flowLineXR_nonneg _ _ i)

/-- The coefficient of either junction is at least one at the corresponding extreme. -/
theorem junction_factor_bound (hκ : 0 < κ) (hκ4 : κ < 4) {a : ℝ} (ha : 1 ≤ a) :
    16 / κ / 2 - 2 ≤ a * (16 / κ / 2 - 2) := by
  have h8 : 0 ≤ 16 / κ / 2 - 2 := by
    rw [sub_nonneg, div_div, le_div_iff₀ (by positivity)]
    linarith only [hκ4]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ha h8

open Finset in
/-- Left image prefix sums retain the nonhitting bound. -/
theorem prefix_iwL_angle (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ ≤ π / 2)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) :
    ∀ m : ℕ, 1 ≤ m → m ≤ flowLineNL
      (Sec7.StripSysField.counterflowData κ (bDataT ρL ρR xL xR θ κ))
      (Sec7.StripSysField.counterflowJumps (forceJumpFinset xL xR)) 0 + 1 →
      16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin _ => i.val < m), iwLT κ θ ρL ρR xL xR i := by
  refine prefix_snoc (prefix_qρL_angle hκ hθb) ?_
  rw [CrossRestart.slitJunctionL_eq]
  have hdiv : θ / π ≤ 1 / 2 := (div_le_iff₀ Real.pi_pos).2 (by linarith only [hθ])
  have ht := junction_factor_bound hκ hκ4 (show 1 ≤ 3 / 2 - θ / π by linarith only [hdiv])
  linarith only [ht]

open Finset in
/-- Right image prefix sums retain the nonhitting bound. -/
theorem prefix_iwR_angle (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : -(π / 2) ≤ θ)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) :
    ∀ m : ℕ, 1 ≤ m → m ≤ flowLineNR
      (Sec7.StripSysField.counterflowData κ (bDataT ρL ρR xL xR θ κ))
      (Sec7.StripSysField.counterflowJumps (forceJumpFinset xL xR)) 0 + 1 →
      16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin _ => i.val < m), iwRT κ θ ρL ρR xL xR i := by
  refine prefix_snoc (prefix_qρR_angle hκ hθb) ?_
  rw [CrossRestart.slitJunctionR_eq]
  have hdiv : -(1 / 2) ≤ θ / π := (le_div_iff₀ Real.pi_pos).2 (by linarith only [hθ])
  have ht := junction_factor_bound hκ hκ4 (show 1 ≤ 3 / 2 + θ / π by linarith only [hdiv])
  linarith only [ht]

end Weights

end InteractingSLE.Sec5.Lemma47Angle
