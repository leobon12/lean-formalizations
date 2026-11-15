/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22ChartEFlow
import InteractingSLE.Spec.Exist.FlowField

/-!
# Local boundary-height readings of the actual flow-line word

Continuation of PROVE-T14-GW2ROOT2. The force-word reconstruction theorem
is reused at arbitrary angles. Each prefix can be read at a boundary point
arbitrarily close to its last mark. This retains spatial restrictions on
inner labels while allowing inadmissible far attracting groups.
-/

set_option autoImplicit false

noncomputable section

open Finset Set

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH10

/-- The existing right-prefix representative can be chosen before any
specified larger point, without losing avoidance of a finite set. -/
theorem exists_right_prefix_eq_before {n : ℕ} (x : Fin n → ℝ)
    (E : Finset ℝ) {q hi : ℝ} (hhi : q < hi) :
    ∃ y, q < y ∧ y < hi ∧ y ∉ E ∧
      univ.filter (fun i => x i ≤ y) = univ.filter (fun i => x i ≤ q) := by
  obtain ⟨z, hqz, _, hz⟩ := Sec4.exists_right_prefix_eq x E q
  obtain ⟨y, hqy, hy, hyE⟩ := Sec4.exists_mem_Ioo_not_mem E (lt_min hqz hhi)
  refine ⟨y, hqy, hy.trans_le (min_le_right _ _), hyE, ?_⟩
  apply le_antisymm
  · intro i hi
    apply hz.subset
    exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2.trans
      (hy.trans_le (min_le_left _ _)).le⟩
  · intro i hi
    exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2.trans hqy.le⟩

/-- A left cumulative weight of the angle-`θ` word is the boundary-height
conversion at a point in any prescribed interval just left of the mark. -/
theorem exists_left_prefix_height {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (θ : ℝ) {lo p : ℝ} (hlo : lo < p) (hp : p ≤ 0) :
    ∃ y, lo < y ∧ y < p ∧ y ∉ J ∧
      (∑ i ∈ univ.filter (fun i => p ≤ flowLineXL b J 0 i),
        flowLineRhoL κ b J 0 θ i) =
        Sec4.cumWeightLeft κ (b y + θ * QuantumZipper.chiC κ) := by
  obtain ⟨y, hy1, hy2, hyE, heq⟩ :=
    Sec5.Aux22ChartE.exists_left_le_prefix_eq (flowLineXL b J 0) J hlo
  have hy0 : y < 0 := hy2.trans_le hp
  refine ⟨y, hy1, hy2, hyE, ?_⟩
  rw [← heq, ← Sec4.cumWeightLeft_forceBoundaryData hκ
    (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0) hy0,
    Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hy0.ne
      (by simpa only [add_zero] using hyE), add_zero]

/-- The right cumulative weight can likewise be read before any larger
point, using the actual angle-dependent flow-line weights. -/
theorem exists_right_prefix_height {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (θ : ℝ) {q hi : ℝ} (hq : 0 ≤ q) (hhi : q < hi) :
    ∃ y, q < y ∧ y < hi ∧ y ∉ J ∧
      (∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ q),
        flowLineRhoR κ b J 0 θ i) =
        Sec4.cumWeightRight κ (b y + θ * QuantumZipper.chiC κ) := by
  obtain ⟨y, hy1, hy2, hyE, heq⟩ :=
    exists_right_prefix_eq_before (flowLineXR b J 0) J hhi
  have hy0 : 0 < y := hq.trans_lt hy1
  refine ⟨y, hy1, hy2, hyE, ?_⟩
  rw [← heq, ← Sec4.cumWeightRight_forceBoundaryData hκ
    (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
    (flowLineXL b J 0) (flowLineXR b J 0) hy0.le,
    Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hy0.ne'
      (by simpa only [add_zero] using hyE), add_zero]

end InteractingSLE.Theorem14.GW2TipSystem.RootH10
