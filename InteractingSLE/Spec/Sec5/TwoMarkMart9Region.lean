/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkAdapt8First

/-!
# Compact regular regions for the local first-mark Itô argument

Before first-mark separation both original marks are strictly right of the
driver. Restrict the existing compact retargeting box to ordered right marks;
the whole coordinate density is continuous there and hence uniformly bounded.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Mart9

open Zhan.Retarget

variable {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}

/-- The initial first-mark coordinate is in the existing observable region. -/
theorem initial_mem_region (ha : 0 < a) (hab : a < b) :
    rInit xL ![a, b] a ∈ obsRegion κ xL ![a, b] ρL ρR 0 := by
  have hd : drv κ xL ![a, b] ρL ρR (rInit xL ![a, b] a) = 0 := by
    simp only [drv, rInit, sub_self, mul_zero, Finset.sum_const_zero]
  refine ⟨?_, fun i => i.elim0, ?_⟩
  · change 0 < a - drv κ xL ![a, b] ρL ρR (rInit xL ![a, b] a)
    rw [hd, sub_zero]
    exact ha
  · intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact sub_ne_zero.2 hab.ne

/-- The existing compact box restricted to ordered original right marks. -/
def orderedBox (κ : ℝ) (xL ρL : Fin 0 → ℝ) (ρR : Fin 2 → ℝ) (a b : ℝ) (n : ℕ) :
    Set (RCoord 0 2 × ℝ) :=
  rKc κ xL ![a, b] ρL ρR 0 a n ∩ {p | p.1.2.1 0 ≤ p.1.2.1 1}

/-- The ordered box is compact. -/
theorem isCompact_orderedBox (n : ℕ) : IsCompact (orderedBox κ xL ρL ρR a b n) :=
  (isCompact_rKc κ xL ![a, b] ρL ρR 0 a n).inter_right
    (isClosed_le (by fun_prop) (by fun_prop))

/-- No original force denominator vanishes anywhere in this compact box. -/
theorem force_gap_ne_on_orderedBox (ha : 0 < a) (hab : a < b) {n : ℕ}
    {p : RCoord 0 2 × ℝ} (hp : p ∈ orderedBox κ xL ρL ρR a b n) (i : Fin 2) :
    p.1.2.1 i - drv κ xL ![a, b] ρL ρR p ≠ 0 := by
  have hr := rKc_subset_obsRegion κ xL ![a, b] ρL ρR 0 a (initial_mem_region ha hab) n hp.1
  have ht : drv κ xL ![a, b] ρL ρR p < p.1.2.1 0 := sub_pos.1 hr.1
  fin_cases i
  · exact sub_ne_zero.2 ht.ne'
  · exact sub_ne_zero.2 (ht.trans_le hp.2).ne'

/-- On an ordered box the existing full retargeting density is continuous. -/
theorem continuousOn_density (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ContinuousOn (dens κ xL ![a, b] ρL ρR 0) (orderedBox κ xL ρL ρR a b n) := by
  have hq : ∀ p ∈ orderedBox κ xL ρL ρR a b n, qOf κ xL ![a, b] ρL ρR 0 p ≠ 0 :=
    fun p hp => (rKc_subset_obsRegion κ xL ![a, b] ρL ρR 0 a (initial_mem_region ha hab) n hp.1).1.ne'
  have hqc : ContinuousOn (qOf κ xL ![a, b] ρL ρR 0) (orderedBox κ xL ρL ρR a b n) :=
    (contDiff_qOf κ xL ![a, b] ρL ρR 0 (n := 0)).continuous.continuousOn
  have hα : ContinuousOn (fun p : RCoord 0 2 × ℝ => -2 * p.1.2.2.1)
      (orderedBox κ xL ρL ρR a b n) := by fun_prop
  have hC : ContinuousOn (fun p : RCoord 0 2 × ℝ => p.1.2.2.1 ^ 2)
      (orderedBox κ xL ρL ρR a b n) := by fun_prop
  unfold dens
  refine (continuousOn_pi.2 fun i => i.elim0).prodMk ((continuousOn_pi.2 fun i => ?_).prodMk
    ((hα.div (hqc.pow 2) (fun p hp => pow_ne_zero 2 (hq p hp))).prodMk
      ((hα.div (hqc.pow 3) (fun p hp => pow_ne_zero 3 (hq p hp))).prodMk
        (hC.div (hqc.pow 4) (fun p hp => pow_ne_zero 4 (hq p hp))))))
  exact continuousOn_const.div ((by fun_prop : Continuous fun p : RCoord 0 2 × ℝ => p.1.2.1 i).sub
    (contDiff_drv κ xL ![a, b] ρL ρR (n := 0)).continuous).continuousOn
    (fun _ hp => force_gap_ne_on_orderedBox ha hab hp i)

/-- A uniform nonnegative bound on the density on each ordered box. -/
theorem exists_bound_density (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ orderedBox κ xL ρL ρR a b n,
      ‖dens κ xL ![a, b] ρL ρR 0 p‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_orderedBox (κ := κ) (xL := xL) (ρL := ρL) (ρR := ρR)
    (a := a) (b := b) n).exists_bound_of_continuousOn (continuousOn_density ha hab n)
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩

end InteractingSLE.Sec5.TwoMark.Mart9
