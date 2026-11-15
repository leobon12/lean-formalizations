-- Frozen anchor (definition, spec_continuationThreshold_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
import InteractingSLE.Frozen.Spec.ForceWord_ThresholdCondition

set_option autoImplicit false

noncomputable section

open scoped NNReal ENNReal

namespace InteractingSLE

/-- **The continuation threshold** of the coordinates `(w, vL, vR)` with weights `(ρL; ρR)` (Specification p. 3, the
display defining `T_*`; Definition 2.1, p. 20): the infimum of the times `t` at which, for some side `q`, the weights of
the force points with `v^{i,q}_t = w_t` sum to at most `-2` (`ForceWord.ThresholdCondition`; an empty sum is `0`);
`∞` if there is no such time. -/
def continuationThreshold {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun j => vR j t)),
    (t : ℝ≥0∞)

end InteractingSLE
