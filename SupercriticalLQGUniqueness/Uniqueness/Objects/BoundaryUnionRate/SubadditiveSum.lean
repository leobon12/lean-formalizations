import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AnnulusRate
import Mathlib.Analysis.MeanInequalitiesPow




 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem rpow_tsum_le_tsum_rpow {ι : Type*} (f : ι → ENNReal)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑' i, f i) ^ p ≤ ∑' i, f i ^ p := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  change (ENNReal.orderIsoRpow p hp) (⨆ s : Finset ι, ∑ i ∈ s, f i) ≤ _
  rw [OrderIso.map_iSup]
  refine iSup_le fun s => ?_
  change (∑ i ∈ s, f i) ^ p ≤ ∑' i, f i ^ p
  calc
    _ ≤ ∑ i ∈ s, f i ^ p := by
      induction s using Finset.induction_on with
      | empty => simp [ENNReal.zero_rpow_of_pos hp]
      | @insert i s his ih =>
          rw [Finset.sum_insert his, Finset.sum_insert his]
          exact (ENNReal.rpow_add_le_add_rpow _ _ hp.le hp1).trans
            (add_le_add_right ih _)
    _ ≤ _ := ENNReal.sum_le_tsum s

theorem lintegral_tsum_rpow_le_tsum_lintegral_rpow
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ι → Ω → ENNReal)
    (hf : ∀ i, AEMeasurable (f i) μ)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫⁻ ω, (∑' i, f i ω) ^ p ∂μ) ≤
      ∑' i, ∫⁻ ω, f i ω ^ p ∂μ := by
  calc
    _ ≤ ∫⁻ ω, ∑' i, f i ω ^ p ∂μ :=
      lintegral_mono fun ω => rpow_tsum_le_tsum_rpow
        (fun i => f i ω) hp hp1
    _ = _ := lintegral_tsum fun i => (hf i).pow_const p


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
