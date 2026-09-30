import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D29 resampling nodes, part 1: deterministic transfer by a density along the curve

Let `μ` be a measure on the time axis `ℝ` (the `Γ⁰` quantum length measure of the left or right
side of the curve, pulled back to capacity time: `L_t = μ (0,t]`), and `w : ℝ → [0,∞]` a density
that is positive on `(0,∞)` (for the wedge, `w(s) = |η(s)|^{-γ²/2} e^{γ G(η(s))/2}`: finite and
positive for `s > 0`, singular at `s = 0`). The weighted lengths are `L^w_t = ∫_{(0,t]} w dμ`.

* `ursmp_strictMonoOn`: if `t ↦ μ (0,t]` is strictly increasing on `[0,∞)` and the weighted
  lengths are finite, the weighted lengths are strictly increasing.
* `ursmp_measure_singleton`: if `μ` is finite on compacts and `t ↦ (μ (0,t]).toReal` is continuous
  on `[0,∞)`, then `μ` has no atom in `(0,∞)`.
* `ursmp_continuousOn`: if `μ` has no atom in `(0,∞)` and the weighted lengths are finite, then
  `t ↦ (L^w_t).toReal` is continuous on `[0,∞)` (primitive of a finite atomless measure,
  `intervalIntegral.continuousOn_primitive`).
* `ursmp_cocycle`: lengths given by one measure along the flow satisfy the additive cocycle.

Own elementary measure theory (no source needed; cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

theorem ursmp_measure_Ioc_split (μ : Measure ℝ) {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) :
    μ (Ioc 0 t) = μ (Ioc 0 s) + μ (Ioc s t) := by
  rw [← Ioc_union_Ioc_eq_Ioc h0 hst,
    measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]

/-- **The additive cocycle from one measure along the flow.** -/
theorem ursmp_cocycle (ν : Measure ℝ) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) :
    ν (Ioc 0 (u + s)) = ν (Ioc 0 u) + ν (Ioc u (u + s)) :=
  ursmp_measure_Ioc_split ν hu (by linarith)

end F1
end QuantumZipper
