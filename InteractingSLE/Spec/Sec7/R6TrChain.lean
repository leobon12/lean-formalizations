/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrData

/-! # Standard one-chain consequences for the real R.6 window -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Tr.InnerChain

variable {V P : Set ℂ} {I : ℝ → Chart} {p : ℂ}

theorem time_mem (M : InnerChain V P I p) : M.time ∈ Ico M.time (M.time + M.horizon) :=
  ⟨le_rfl, lt_add_of_pos_right _ M.horizon_pos⟩

/-- Antitonicity uses the selected relative chain's hull, with no
identification of an outer current domain with an ambient complement. -/
theorem dom_subset (M : InnerChain V P I p) {q : ℝ} (hq : q ∈ Ico M.time (M.time + M.horizon)) :
    ((I q).dom : Set ℂ) ⊆ (I M.time).dom := by
  rw [M.dom_eq q hq, M.dom_eq M.time M.time_mem]
  exact fun w hw => ⟨hw.1, hw.2.1, fun hk => hw.2.2 ((QuantumZipper.fwdHull_mono.1 hq.1) hk)⟩

/-- The bound for the forward chart is a consequence of bounded
inverse displacement; it is not an extra face input. -/
theorem norm_bound (M : InnerChain V P I p) {q : ℝ} (hq : q ∈ Ico M.time (M.time + M.horizon)) :
    ∃ B : ℝ, ∀ w ∈ ((I q).dom : Set ℂ), ‖(I q).1 w‖ ≤ ‖M.coord w‖ + B := by
  have hq0 : 0 ≤ q := M.time_pos.le.trans hq.1
  obtain ⟨B, hB⟩ := exists_norm_fwdMapInv_sub_le M.driver_cont M.driver_zero hq0
  refine ⟨B, fun w hw => ?_⟩
  have hw' := hw
  rw [M.dom_eq q hq] at hw'
  have hzH := (M.conformal q hq).fwd_mem hw
  have hInv : fwdMapInv M.driver q ((I q).1 w) = M.coord w := by
    rw [M.forward_eq q hq w hw'.1]
    exact QuantumZipper.RS.fwdMapInv_fwdMap M.driver_cont M.driver_zero hq0 hw'.2
  have hb := hB _ hzH
  rw [hInv] at hb
  have hn := norm_sub_norm_le ((I q).1 w) (M.coord w)
  rw [norm_sub_rev] at hn
  linarith

theorem continuousAt_left_mark (M : InnerChain V P I p) :
    ContinuousAt (fun q => WangWu.chartAL M.driver q) M.time := by
  exact ((MartChar.RealFlow.continuousOn_rightImg M.driver_cont.neg 0).continuousAt
    (Ici_mem_nhds M.time_pos)).neg.sub M.driver_cont.continuousAt

/-- All surviving physical forward coordinates change by uniformly
little during a sufficiently short real increment. -/
theorem forward_change_small (M : InnerChain V P I p) {a : ℝ} (ha : 0 < a) :
    ∃ θ > 0, ∀ q : ℝ, M.time < q → q < M.time + θ →
      q ∈ Ico M.time (M.time + M.horizon) →
      ∀ w ∈ ((I q).dom : Set ℂ), ‖(I q).1 w - (I M.time).1 w‖ ≤ a := by
  obtain ⟨θ, hθ, hsmall⟩ := uniform_forward_increment_small M.driver_cont M.driver_zero M.time_pos.le ha
  refine ⟨θ, hθ, fun q hlo hhi hq w hw => ?_⟩
  have hw' := hw
  rw [M.dom_eq q hq] at hw'
  rw [M.forward_eq q hq w hw'.1, M.forward_eq M.time M.time_mem w hw'.1]
  exact (hsmall q hlo hhi _ hw'.2).le

end InteractingSLE.Sec7.R6Tr.InnerChain
