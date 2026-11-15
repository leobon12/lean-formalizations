/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapVisits

/-!
# The zero gate at a fresh contact of an infinite pocket arm

PROVE-R7-GAPEQ. A positive-time fresh contact lies in the open half-plane:
the proper arm's only possible real point is the already visited origin.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 PocketJordan R7InfinityChart

/-- Pocket geometry supplies the fresh-tip interior condition locally. No global
assumption that all positive-time trace points lie in `H` is needed. -/
theorem lastVisit_gate_zero_of_pocket {W : ℝ → ℝ} {η A₁ A₂ b : ℝ → ℂ}
    {C : Set ℂ} {a p q v : ℝ} (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ha : 0 ≤ a)
    (hrev : IsReverseVisitOrderInf A₁ fun t => η '' Icc 0 t)
    (hv : v ∈ Ici (0 : ℝ)) (hp : η a = A₁ v) (hfresh : η a ∉ η '' Ico 0 a)
    (hb : IsLastVisitArm W η A₁ a p q b) : q = 0 := by
  have hu := lastVisit_eq_of_fresh hC.cont₁ hC.inj₁ hC.tendsto₁ hη.2.1 hrev ha hv hp hfresh
  have hq : trMap W 0 a q = η a := hb.2.2.2.2.2.2.trans ((congrArg A₁ hu).trans hp.symm)
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · rw [← ha0, YuanSimpleApprox.trMap_self hW 0 (ofReal_mem_Hbar q), hη.1] at hq
    exact ofReal_eq_zero.1 hq
  · have hH : η a ∈ H := by
      rcases eq_or_lt_of_le (show 0 ≤ v from hv) with hv0 | hv0
      · have he : η a = A₁ 0 := by simpa only [← hv0] using hp
        rcases hC.mem_y with hyH | hy0
        · exact he ▸ hyH
        · exact False.elim (hfresh ⟨0, ⟨le_rfl, ha0⟩, hη.1.trans (he.trans hy0).symm⟩)
      · rw [hp]
        exact hC.mem_H₁ v hv0
    exact fresh_tip_fibre hη hW hW0 ha0 hH hfresh hq

end InteractingSLE.Sec7.R7InfinityGap
