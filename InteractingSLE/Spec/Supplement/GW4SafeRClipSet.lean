/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRNextLines

/-!
# GW4: the canonical hull at a safe physical line

The set is the relative filled hull inside `H` while the physical line is safe,
and all of `H` afterwards. Its hitting measurability in the physical filtration
and its open complement are proved here, without a conditional locality input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets Supp8.RelSafe Supp8.GB6LineL

/-- The actual relative hull on the safe interval, and the full domain off it. -/
def safeHull (F : Frame) {Ω : Type*} (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  if lineClock F Wd GT V t ω < V ω then
    H ∩ fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal
  else H

theorem safeHull_subset_H (F : Frame) {Ω : Type*} (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) :
    safeHull F Wd GT R V t ω ⊆ H := by
  unfold safeHull
  split
  · exact inter_subset_left
  · exact Subset.rfl

theorem H_diff_safeHull_of_lt (F : Frame) {Ω : Type*} (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω)
    (hlt : lineClock F Wd GT V t ω < V ω) :
    H \ safeHull F Wd GT R V t ω =
      H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal := by
  simp only [safeHull, ite_eq_left hlt, Set.sdiff_self_inter]

/-- A nonempty subset of `H` avoids the clipped hull exactly on the safe
interval and when it avoids the actual hull. -/
theorem disjoint_safeHull_iff (F : Frame) {Ω : Type*} (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω)
    {D : Set ℂ} (hDH : D ⊆ H) (hD : D.Nonempty) :
    Disjoint D (safeHull F Wd GT R V t ω) ↔
      lineClock F Wd GT V t ω < V ω ∧ Disjoint D
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal) := by
  by_cases hlt : lineClock F Wd GT V t ω < V ω
  · simp only [safeHull, hlt, true_and]
    constructor
    · intro hd
      exact Set.disjoint_left.2 fun z hzD hzK => Set.disjoint_left.1 hd hzD ⟨hDH hzD, hzK⟩
    · intro hd
      exact hd.mono_right inter_subset_right
  · simp only [safeHull, hlt, false_and, iff_false]
    intro hd
    obtain ⟨z, hz⟩ := hD
    exact Set.disjoint_left.1 hd hz (hDH hz)

namespace Frame

variable {F : Frame} {Ω : Type*} [mΩ : MeasurableSpace Ω] {ν : Measure Ω}
  {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}

/-- The canonical set has open complement at every sample, also off the safe interval. -/
theorem isOpen_H_diff_safeHull (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (t : ℝ≥0) (ω : Ω) : IsOpen (H \ safeHull F Wd GT R V t ω) := by
  by_cases hlt : lineClock F Wd GT V t ω < V ω
  · rw [H_diff_safeHull_of_lt F Wd GT R V t ω hlt]
    exact QuantumZipper.FwdHolo.isOpen_compl_fwdHull
      ((hver.1.1.2.1 ω).comp continuous_real_toNNReal) (NNReal.coe_nonneg _)
  · simp only [safeHull, ite_eq_right hlt, sdiff_self, isOpen_empty]

/-- No random-set witness remains: the canonical safe hull itself is
hitting-measurable in the physical filtration. -/
theorem measurable_safeHull (hF : F.IsOk)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V) (t : ℝ≥0) :
    Measurable[physFilt measurable_gw4Rec hWm ν t, hittingSigma]
      (safeHull F Wd GT R V t) := by
  refine Sec5.Aux61ULoc.measurable_hitting_of_avoid fun U hU hUH => ?_
  have he : {ω | Disjoint (safeHull F Wd GT R V t ω) U} =
      ⋂ p : ℚ × ℚ × ℚ, ⋂ (_ : 0 < p.2.2),
        ⋂ (_ : closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U),
          {ω | Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
            (safeHull F Wd GT R V t ω)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    exact disjoint_iff_forall_posRatDisc hU
  rw [he]
  refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun hp =>
    MeasurableSet.iInter fun hsub => ?_
  have hrad : (0 : ℝ) ≤ (p.2.2 : ℝ) := by exact_mod_cast hp.le
  have hne : (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ)).Nonempty :=
    ⟨_, mem_closedBall_self hrad⟩
  have he' : {ω | Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
        (safeHull F Wd GT R V t ω)} =
      {ω | lineClock F Wd GT V t ω < V ω ∧
        Disjoint (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
          (fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal)} := by
    ext ω
    exact disjoint_safeHull_iff F Wd GT R V t ω (hsub.trans hUH) hne
  rw [he']
  exact measurableSet_lineSafe hF hGT hWm hGTm hGTae hver isClosed_closedBall t

end Frame

end InteractingSLE.Theorem14.GW4Fix
