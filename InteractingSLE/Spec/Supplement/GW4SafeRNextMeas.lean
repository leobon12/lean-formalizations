/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FixPhysLine
import InteractingSLE.Spec.Supplement.GB6LineL4

/-!
# GW4: measurable safe events at the physical lines

Continuation of PROVE-GW4-SAFER. The closed-set hull measurability and random-time
reader are reused from GB6. The path-rule identity handles the boundary event
where the physical clock equals the version stop.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull drive)

namespace InteractingSLE.Theorem14.GW4Fix

open Supp8.RelSafe Supp8.GB6LineL GW4Rel

/-- The physical relative clock stopped at the version stop. -/
abbrev lineClock (F : Frame) {Ω : Type*} (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (V : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  min (F.physClockG Wd GT t ω) (V ω)

/-- A path rule sees whether it has stopped by a level from the path frozen at
that level, including equality at the stop. -/
theorem pathRule_le_iff_freeze {ρ : (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule₀ ρ)
    (w : ℝ≥0 → ℝ) (a : ℝ≥0∞) :
    ρ w ≤ a ↔ ρ (fun u => w (min u a.toNNReal)) ≤ a := by
  by_cases ha : a = ⊤
  · simp only [ha, le_top]
  · have hcoe := ENNReal.coe_toNNReal ha
    constructor
    · intro h
      have he : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ w →
          w u = w (min u a.toNNReal) := fun u hu => by
        rw [min_eq_left (ENNReal.coe_le_coe.1 (by rw [hcoe]; exact hu.trans h))]
      rw [hρ w _ he]
      exact h
    · intro h
      have he : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ (fun u => w (min u a.toNNReal)) →
          w (min u a.toNNReal) = w u := fun u hu => by
        rw [min_eq_left (ENNReal.coe_le_coe.1 (by rw [hcoe]; exact hu.trans h))]
      rw [hρ _ w he]
      exact h

namespace Frame

variable {F : Frame} {Ω : Type*} [mΩ : MeasurableSpace Ω] {ν : Measure Ω}
  {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}

/-- Every safe avoidance event of a closed set is physical for a path-rule
version of the GW4 traversal. -/
theorem measurableSet_lineSafe (hF : F.IsOk)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V) {D : Set ℂ} (hD : IsClosed D) (t : ℝ≥0) :
    MeasurableSet[physFilt measurable_gw4Rec hWm ν t]
      {ω | lineClock F Wd GT V t ω < V ω ∧ Disjoint D
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal)} := by
  have ha := measurable_min_physClockG hF hGT hWm hGTm hGTae hver t
  obtain ⟨hvS, ρ, hρm, hρ, hVρ⟩ := hver
  have hv := hvS.1
  have hver' : IsGW4RelVersionR ν Wd F.c F.C R V := ⟨hvS, ρ, hρm, hρ, hVρ⟩
  have ha' : Measurable[physFilt measurable_gw4Rec hWm ν t]
      fun ω => (lineClock F Wd GT V t ω).toNNReal := ENNReal.measurable_toNNReal.comp ha
  have hY : ∀ u, Measurable[physFilt measurable_gw4Rec hWm ν t]
      (fun ω => R (min u (lineClock F Wd GT V t ω).toNNReal) ω) := fun u =>
    measurable_apply_randTime hv.2.1 (a := lineClock F Wd GT V t) (measurable_const.min ha')
      (fun ω => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans ENNReal.coe_toNNReal_le_self)
      (fun d B hB => measurableSet_le_min_inter_drv hF hGT hWm hGTm hGTae hver' t le_rfl hB)
  have hYc : ∀ ω, Continuous fun u => R (min u (lineClock F Wd GT V t ω).toNNReal) ω :=
    fun ω => (hv.2.1 ω).comp (continuous_id.min continuous_const)
  have hDis : MeasurableSet[physFilt measurable_gw4Rec hWm ν t] {ω | Disjoint D
      (fwdHull (drive 1 (fun u ω => R (min u (lineClock F Wd GT V t ω).toNNReal) ω) ω)
        ((lineClock F Wd GT V t ω).toNNReal : ℝ))} :=
    measurableSet_disjoint_fwdHull_rand hYc hY (measurable_coe_nnreal_real.comp ha')
      (fun _ => NNReal.coe_nonneg _) hD
  have hhull : ∀ ω, fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal =
      fwdHull (drive 1 (fun u ω => R (min u (lineClock F Wd GT V t ω).toNNReal) ω) ω)
        ((lineClock F Wd GT V t ω).toNNReal : ℝ) := fun ω => by
    refine LocalExt.fwdHull_congr_of_continuousOn
      ((hv.2.1 ω).comp continuous_real_toNNReal).continuousOn
      (QuantumZipper.NonSwallow.continuous_drive_ns hYc 1 ω).continuousOn
      (NNReal.coe_nonneg _) (lt_add_one _) ?_
    intro r hr
    simp only [drive, Real.sqrt_one, one_mul]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  have hpath : Measurable[physFilt measurable_gw4Rec hWm ν t]
      fun ω => fun u => R (min u (lineClock F Wd GT V t ω).toNNReal) ω :=
    (@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) (physFilt measurable_gw4Rec hWm ν t) _ _).2 hY
  have hStop : MeasurableSet[physFilt measurable_gw4Rec hWm ν t] {ω |
      ρ (fun u => R (min u (lineClock F Wd GT V t ω).toNNReal) ω) ≤
        lineClock F Wd GT V t ω} := measurableSet_le (hρm.comp hpath) ha
  have he : ∀ᵐ ω ∂ν, (lineClock F Wd GT V t ω < V ω ↔
      ¬ ρ (fun u => R (min u (lineClock F Wd GT V t ω).toNNReal) ω) ≤
        lineClock F Wd GT V t ω) := by
    filter_upwards [hVρ] with ω hω
    rw [← not_le, hω]
    exact not_congr (pathRule_le_iff_freeze hρ _ _)
  have hEm : MeasurableSet {ω | lineClock F Wd GT V t ω < V ω ∧ Disjoint D
      (fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal)} := by
    have h1 := measurableSet_lt (ha.mono ((physFilt measurable_gw4Rec hWm ν).le t) le_rfl)
      hv.2.2.2.1
    have h2 := (physFilt measurable_gw4Rec hWm ν).le t _ hDis
    simp only [← hhull] at h2
    exact h1.inter h2
  refine measurableSet_of_ae_eq ((physFilt measurable_gw4Rec hWm ν).le t)
    (nullSets_le_physFilt measurable_gw4Rec hWm ν t) hEm (hStop.compl.inter hDis) ?_
  filter_upwards [he] with ω hω
  show (ω ∈ {ω | _}) = (ω ∈ _ ∩ _)
  simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, hhull ω, hω]

end Frame

end InteractingSLE.Theorem14.GW4Fix
