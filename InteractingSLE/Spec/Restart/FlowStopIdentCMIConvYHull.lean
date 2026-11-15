/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYEnlarge

/-! # The finite terminal hull is the filling of the earlier hulls -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H fwdHull)

/-- Capacity continuity identifies the filling at a finite limit time, including
pockets swallowed exactly at that time. No trace or probabilistic input is used. -/
theorem fwdHull_eq_fillH_iUnion {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s : ℕ → ℝ≥0} {t : ℝ≥0} (hst : ∀ n, s n ≤ t)
    (hlim : Tendsto (fun n => (s n : ℝ≥0∞)) atTop (𝓝 (t : ℝ≥0∞))) :
    fwdHull W t = fillH (⋃ n, fwdHull W (s n)) := by
  let A : Set ℂ := ⋃ n, fwdHull W (s n)
  have hKt := isHPHull_fwdHull hW (NNReal.coe_nonneg t)
  have hAn : ∀ n, IsHPHull (fwdHull W (s n)) := fun n =>
    isHPHull_fwdHull hW (NNReal.coe_nonneg _)
  have hAK : A ⊆ fwdHull W t := iUnion_subset fun n =>
    (QuantumZipper.fwdHull_mono (W := W)).1 (NNReal.coe_le_coe.2 (hst n))
  have hAb : Bornology.IsBounded A := hKt.2.1.subset hAK
  have hpc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) := by
    have hp := isPreconnected_iUnion
      (s := fun n => fwdHull W (s n) ∪ {z : ℂ | z.im ≤ 0})
      ⟨0, mem_iInter.2 fun _ => Or.inr (by simp only [mem_ofPred_eq, Complex.zero_im, le_refl])⟩
      (fun n => (hAn n).isPreconnected_union_lowerHalf)
    simpa only [A, iUnion_union] using hp
  have hAf := isHPHull_fillH_of_isPreconnected hAb hpc
  have hsub : fillH A ⊆ fwdHull W t := by
    simpa only [hKt.fillH_eq] using fillH_mono hAK
  have hge : ∀ n, 2 * (s n : ℝ) ≤ HPHull.hcap ⟨fillH A, hAf⟩ := by
    intro n
    rw [← hcap_fwdHull hW hW0 (NNReal.coe_nonneg (s n))]
    apply HPHull.hcap_mono
    intro z hz
    exact mem_fillH_of_mem_closure ((hAn n).1 hz) (subset_closure (mem_iUnion.2 ⟨n, hz⟩))
  have hr : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (t : ℝ)) := by
    simpa only [ENNReal.coe_toReal, Function.comp_def] using
      (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlim
  have hcap : HPHull.hcap ⟨fwdHull W t, hKt⟩ ≤ HPHull.hcap ⟨fillH A, hAf⟩ := by
    rw [hcap_fwdHull hW hW0 (NNReal.coe_nonneg t)]
    exact le_of_tendsto (hr.const_mul 2) (Eventually.of_forall hge)
  exact (TraceClose.eq_of_subset_of_hcap_le
    (A := ⟨fillH A, hAf⟩) (B := ⟨fwdHull W t, hKt⟩) hsub hcap).symm

end InteractingSLE.Restart.FlowStopIdentCMI
