/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PwWrap
import InteractingSLE.Spec.Sec5.StagedRepLaterScale

/-!
# The export's window clause, deterministic core: the dilated stage driver is the relative driver

Packet PROVE-GW2-STAGEMEAN, R122 round (D46 export, step E5). If the stage driver `D` is the Brownian rescaling of the
kernel's relative driver `Rk` on `[0, Q]` (`D s = Rk (λ² s) / λ`, `GW2Omx.sample_driver_scale`), the dilated stage
driver `scD λ D` IS `Rk` on `[0, λ² Q]`, so it generates the same hulls there:

* `scD_eqOn_of_scale`;
* **`fwdHull_scD_eq_of_scale`**: `fwdHull (scD λ D) r = fwdHull Rk r` for `0 ≤ r ≤ λ² Q`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open QuantumZipper (fwdHull)

namespace InteractingSLE.Theorem14.GW2Pw

open Sec5.CrossCond.StagedRepLater

/-- **The dilated stage driver is the kernel's relative driver** on `[0, λ² Q]`. -/
theorem scD_eqOn_of_scale {lam : ℝ} (hlam : 0 < lam) {D Rk : ℝ → ℝ} {Q : ℝ}
    (hrel : EqOn D (fun s => Rk (lam ^ 2 * s) / lam) (Icc 0 Q)) :
    EqOn (scD lam D) Rk (Icc 0 (lam ^ 2 * Q)) := by
  intro s hs
  have hl2 : 0 < lam ^ 2 := by positivity
  have hmem : s / lam ^ 2 ∈ Icc 0 Q :=
    ⟨div_nonneg hs.1 hl2.le, (div_le_iff₀ hl2).2 (by linarith [hs.2, mul_comm Q (lam ^ 2)])⟩
  show lam * D (s / lam ^ 2) = Rk s
  rw [hrel hmem]
  have h1 : lam ^ 2 * (s / lam ^ 2) = s := by field_simp
  show lam * (Rk (lam ^ 2 * (s / lam ^ 2)) / lam) = Rk s
  rw [h1]
  field_simp

/-- **The dilated stage driver generates the kernel's relative hulls** up to `λ² Q`. -/
theorem fwdHull_scD_eq_of_scale {lam : ℝ} (hlam : 0 < lam) {D Rk : ℝ → ℝ} (hD : Continuous D)
    (hRk : Continuous Rk) {Q : ℝ} (hrel : EqOn D (fun s => Rk (lam ^ 2 * s) / lam) (Icc 0 Q)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ lam ^ 2 * Q) : fwdHull (scD lam D) r = fwdHull Rk r := by
  have hsc : Continuous (scD lam D) := continuous_const.mul (hD.comp (continuous_id.div_const _))
  refine LocalExt.fwdHull_congr_of_continuousOn (t' := r + 1) hsc.continuousOn hRk.continuousOn hr0 (by linarith)
    fun s hs => scD_eqOn_of_scale hlam hrel ⟨hs.1, hs.2.trans hr⟩

end InteractingSLE.Theorem14.GW2Pw
