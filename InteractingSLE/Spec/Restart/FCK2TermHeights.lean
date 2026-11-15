/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Src

/-!
# Original terminal incident heights at arbitrary real seeds

The source force word is centered at its original seed, which need not be
zero. Closed collision cuts, including an original jump, still read its
physical one-sided boundary height.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData FlowStopIdentLL MartChar.RealFlow

/-- The closed left collision-prefix identity at an arbitrary original seed. -/
theorem sum_collisionL_eq_leftLim_seed {κ θ x : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {y w : ℝ} (hy : y ≤ x) {vL : Fin (flowLineNL b J x) → ℝ}
    (hc : ∀ i, vL i = w ↔ y - x ≤ flowLineXL b J x i) :
    (∑ i ∈ univ.filter (fun i => vL i = w), flowLineRhoL κ b J x θ i) =
      Sec4.cumWeightLeft κ (leftLim b y + θ * chiC κ) := by
  classical
  obtain ⟨a, -, hay, haF, hcut⟩ := exists_left_cut isOpen_univ (mem_univ y) (insert x J)
  have haJ : a ∉ J := fun ha => haF (mem_insert_of_mem ha)
  have he : leftLim b y = b a := by
    apply Sec4.leftLim_eq_of_forall hay
    intro z hz
    apply Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hz.1.le
    intro v hv hvJ
    by_cases hva : v = a
    · exact haJ (hva ▸ hvJ)
    · have hav : a < v := lt_of_le_of_ne hv.1 (Ne.symm hva)
      exact (not_le_of_gt (hv.2.trans_lt hz.2)) ((hcut v (mem_insert_of_mem hvJ)).1 hav)
  change _ = -(leftLim b y + θ * chiC κ) / sleLambda κ - 1
  rw [sum_collisionL_eq_height hκ hb (hay.trans_le hy) haJ]
  · rw [he]
  · intro i
    rw [hc i]
    have hi := hcut _ (physical_flowLineXL_mem b J x i)
    constructor
    · intro h
      have : a < x + flowLineXL b J x i := hi.2 (by linarith only [h])
      linarith only [this]
    · intro h
      have : y ≤ x + flowLineXL b J x i := hi.1 (by linarith only [h])
      linarith only [this]

/-- The closed right collision-prefix identity at an arbitrary original seed. -/
theorem sum_collisionR_eq_rightLim_seed {κ θ x : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {y w : ℝ} (hy : x ≤ y) {vR : Fin (flowLineNR b J x) → ℝ}
    (hc : ∀ i, vR i = w ↔ flowLineXR b J x i ≤ y - x) :
    (∑ i ∈ univ.filter (fun i => vR i = w), flowLineRhoR κ b J x θ i) =
      Sec4.cumWeightRight κ (rightLim b y + θ * chiC κ) := by
  classical
  obtain ⟨a, -, hya, haF, hcut⟩ := exists_right_cut isOpen_univ (mem_univ y) (insert x J)
  have haJ : a ∉ J := fun ha => haF (mem_insert_of_mem ha)
  have he : rightLim b y = b a := by
    apply Sec4.rightLim_eq_of_forall hya
    intro z hz
    symm
    apply Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hz.2.le
    intro v hv hvJ
    exact (not_le_of_gt (hz.1.trans_le hv.1)) ((hcut v (mem_insert_of_mem hvJ)).1 hv.2)
  change _ = (rightLim b y + θ * chiC κ) / sleLambda κ - 1
  rw [sum_collisionR_eq_height hκ hb (hy.trans_lt hya) haJ]
  · rw [he]
  · intro i
    rw [hc i]
    have hi := hcut _ (physical_flowLineXR_mem b J x i)
    constructor
    · intro h
      have : x + flowLineXR b J x i ≤ a := hi.2 (by linarith only [h])
      linarith only [this]
    · intro h
      have : x + flowLineXR b J x i ≤ y := hi.1 (by linarith only [h])
      linarith only [this]

end InteractingSLE.Restart.FCPlumb
