/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWAAContact

/-! # The excursion endpoint is the actual first contact

The shifted path remains in the counterflow domain until the given
excursion endpoint and reaches its complement exactly there.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow20
open Aux61FibData

/-- Exact first contact of a shifted excursion, with no chart or clock
normalization assumption. -/
theorem hitTime_shift_eq {η : ℝ → ℂ} {ρ : ℝ≥0 → ℂ} {D : Set ℂ} {r : ℝ≥0} {e : ℝ}
    (hre : (r : ℝ) < e) (hρ : ∀ v, ρ v = η (r + (v : ℝ)))
    (hstart : ρ 0 ∈ D) (hin : ∀ v ∈ Ioo (r : ℝ) e, η v ∈ D) (hend : η e ∉ D) :
    hitTime (fun _ : Unit => ρ) (fun _ => Dᶜ) () = ((e - r).toNNReal : ℝ≥0∞) := by
  have he : 0 < e - r := sub_pos.2 hre
  have hsum : (r : ℝ) + ((e - r).toNNReal : ℝ) = e := by
    rw [Real.coe_toNNReal _ he.le]
    ring
  apply le_antisymm
  · exact iInf₂_le (e - r).toNNReal (by
      change ρ (e - r).toNNReal ∉ D
      rw [hρ, hsum]
      exact hend)
  · refine le_iInf₂ fun v hv => ?_
    by_contra h
    have hv' : (v : ℝ) < e - r := by
      have := ENNReal.coe_lt_coe.1 (not_le.1 h)
      simpa only [← NNReal.coe_lt_coe, Real.coe_toNNReal _ he.le] using this
    change ρ v ∉ D at hv
    rcases eq_or_lt_of_le (show 0 ≤ v from zero_le) with hv0 | hv0
    · rw [← hv0] at hv
      exact hv hstart
    · have hD := hin (r + (v : ℝ)) ⟨by exact lt_add_of_pos_right _ (NNReal.coe_pos.2 hv0), by linarith⟩
      exact hv (by rw [hρ]; exact hD)

/-- The real physical clock approaches its endpoint from the left when
the nonnegative restart clock does. -/
theorem tendsto_add_coe_nhdsLT (r T : ℝ≥0) :
    Tendsto (fun v : ℝ≥0 => (r : ℝ) + (v : ℝ)) (𝓝[<] T) (𝓝[<] ((r : ℝ) + (T : ℝ))) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (continuousAt_const.add NNReal.continuous_coe.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with v hv
    change (r : ℝ) + (v : ℝ) < (r : ℝ) + (T : ℝ)
    linarith only [NNReal.coe_lt_coe.2 hv]

end InteractingSLE.Sec5.Aux61GWindow20
