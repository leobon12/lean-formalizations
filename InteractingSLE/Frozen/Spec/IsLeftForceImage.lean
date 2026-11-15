-- Frozen anchor (definition, spec_IsLeftForceImage_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
import QuantumZipper.Loewner.Forward

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace InteractingSLE

/-- **`v` is the geometric image of the left force point `x ≤ 0`** (`x = 0` is `0⁻`) under the Loewner evolution of the
continuous driver `w` with `w 0 = 0` (Specification §2.3, L815; the mirror image of `IsRightForceImage`):
`V_t = sup {g_t(y) : y < x, y not swallowed by time t}`, i.e. `g_t(x)` while `x` is not swallowed and the `g_t` image
of the left endpoint of `ℝ ∩ K_t` otherwise. -/
def IsLeftForceImage (w : ℝ≥0 → ℝ) (x : ℝ) (v : ℝ≥0 → ℝ) : Prop :=
  Continuous w ∧ w 0 = 0 ∧ x ≤ 0 ∧
    ∀ t : ℝ≥0, v t = w t + sSup {c : ℝ | ∃ y : ℝ, y < x ∧
      (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) (t : ℝ) u) ∧
      c = (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) (t : ℝ) (y : ℂ)).re}

end InteractingSLE
