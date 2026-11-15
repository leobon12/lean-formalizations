/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetBoundary

/-! # The canonical bounded harmonic mean in chart Q -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Target
open QuantumZipper Sec4 Sec7.StripSysField Prop513Schedule

/-- The transported harmonic mean has precisely the canonical Q boundary
limits, with the argument branch inherited from the chart composition. -/
theorem harmonicExtension {κ q : ℝ} (hq : 0 < q)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (stripHData κ bL bU) (stripHJumps JL JU) u) :
    IsBoundedHarmonicExtension (stripQHData κ q bL bU) (stripQHJumps q JL JU)
      (fun z => u ((targetChart q).2.1 z) +
        chiC κ * (targetChart q).2.2 ((targetChart q).2.1 z)) := by
  have hc := targetChart_isConformal hq
  have hcomp := LQGMetric.harmonicOnNhd_comp_holo isOpen_H isOpen_H hu.1 hc.1 hc.2.1
  have hm : DifferentiableOn ℂ (middle q) H :=
    (Prop513Field.isConformal hq).1.comp (differentiableOn_id.sub_const _) fun z hz => by
      simpa [H] using hz
  have hlift := LQGMetric.harmonicOnNhd_comp_holo isOpen_H isOpen_H
    harmonicOnNhd_infinitySourceChart_lift hm (fun z hz => middle_mem_H hq hz)
  obtain ⟨C, hC⟩ := hu.2.1
  refine ⟨fun z hz => ?_, ⟨C + |chiC κ| * (2 * π), fun z hz => ?_⟩, fun x hx => ?_⟩
  · simp_rw [lift_inv_eq]
    exact (hcomp z hz).add ((hlift z hz).const_smul (c := chiC κ))
  · calc
      _ ≤ |u ((targetChart q).2.1 z)| +
          |chiC κ| * |(targetChart q).2.2 ((targetChart q).2.1 z)| := by
        simpa only [abs_mul] using abs_add_le (u ((targetChart q).2.1 z))
          (chiC κ * (targetChart q).2.2 ((targetChart q).2.1 z))
      _ ≤ C + |chiC κ| * (2 * π) := by
        gcongr
        · exact hC _ (hc.2.1 hz)
        · rw [lift_inv_eq]
          exact abs_infinitySourceChart_lift_le _
  · have hx1 : x ≠ 1 := fun he => hx (by
      exact Finset.mem_coe.2 (Finset.mem_insert_of_mem
        (Finset.mem_insert.2 (Or.inl he))))
    have hxq : x ≠ -(1 / q) := fun he => hx (Finset.mem_insert.2 (Or.inl he))
    rw [← data_eq (κ := κ) hq hx1 hxq]
    simp_rw [lift_inv_eq]
    exact ((hu.2.2 _ (realInv_notMem hq hx)).comp (tendsto_inv_H hq hx1)).add
      (((tendsto_infinitySourceChart_lift (realMiddle_ne_zero hq hx1)).comp
        (tendsto_middle_H hq hx1)).const_mul (chiC κ))

end InteractingSLE.Sec5.Prop513Target
