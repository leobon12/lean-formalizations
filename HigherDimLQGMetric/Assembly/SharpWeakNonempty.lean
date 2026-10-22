import HigherDimLQGMetric.Main.Inputs
import HigherDimLQGMetric.Main.Existence
import HigherDimLQGMetric.ShellDec.Bridge

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.sharpWeak_nonempty`

`sharpWeak_nonempty_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/SharpWeakNonempty.lean` verbatim (the sharp
weak class at `Q(ξ)` is nonempty; [S] Lemma 10.1 and the existence half of Theorem 1.2). Proof: L10a's
`sharpWeak_nonempty_of_inputs` (`Main/Existence.lean`) with the unconditional inputs of `Main/Inputs.lean` (L8's [1]
Theorem 1.3, L9c's [1] Theorem 1.6), L5b's `realEpsAdapterShape` and G3b's `shellDecouplingFun_rd`. This module imports no
frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `sharpWeak_nonempty`, proved. -/
theorem sharpWeak_nonempty_impl :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ D : DistRd d → ContMetric d, IsSharpWeakExpMetric d ξ (distExp d ξ) D := by
  exact sharpWeak_nonempty_of_inputs b3Goal' DGZ.realEpsAdapterShape theorem16Shape' shellDecouplingFun_rd

end HigherDimLQGMetric
