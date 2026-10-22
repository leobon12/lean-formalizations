import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Param.Interval

/-!
# Subcritical parameter windows

The interval and gap estimates from the parameterization give the window interfaces
used by the positive-parameter construction and the near-zero exponent bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open HigherDimLQGMetric

namespace HigherDimLQGContinuity

/-- Every interval ending at a subcritical parameter has a uniform gap. -/
theorem marginWindow_of_mem {d : ℕ} (hd : 2 ≤ d) {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hlohi : lo < hi) (hhi : hi ∈ subcritSet d) : MarginWindow d lo hi := by
  refine ⟨hlo, hlohi, gapXi d hi, (mem_subcritSet_iff_gapXi_pos hhi.1).1 hhi,
    fun ξ hξ hξ0 => ?_⟩
  obtain ⟨-, -, -, -, hsub, -⟩ := gap24 hd hhi
  have hmem : ξ ∈ Ioc 0 hi := ⟨hξ0, hξ.2⟩
  refine ⟨(hsub hmem).2, ?_⟩
  rw [← gapXi_of_pos hξ0]
  exact gapXi_antitone hd hξ.2

/-- Each positive subcritical parameter lies in a window with a uniform gap. -/
theorem subcritLocal_holds {d : ℕ} (hd : 2 ≤ d) : SubcritLocal d := by
  intro ξ hξ hsub
  have hmem : ξ ∈ subcritSet d := ⟨hξ, hsub⟩
  rw [subcritSet_eq_Ioo hd] at hmem
  refine ⟨ξ / 2, (ξ + xiCrit d) / 2, by linarith, by linarith,
    by linarith [hmem.2], ?_⟩
  refine marginWindow_of_mem hd (by linarith) (by linarith [hmem.2]) ?_
  rw [subcritSet_eq_Ioo hd]
  exact ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.2]⟩

/-- The exponent differs from its zero-parameter limit by at most `√(2d) ξ`. -/
theorem phiRate_holds {d : ℕ} (hd : 2 ≤ d) : PhiRate d := by
  refine ⟨1, one_pos, fun ξ hξ => ?_⟩
  have h := phiXi_lipschitz hd ξ 0
  rwa [phiXi_of_pos hξ.1, phiXi_zero, sub_zero, abs_of_pos hξ.1] at h

end HigherDimLQGContinuity
