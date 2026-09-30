import QuantumZipper.Common.Basic

/-!
# Hölder continuity on a set

`IsHolderOn F S`: `F` is Hölder continuous on `S` with some positive exponent `α` and some
constant `C` (no bound on `α`, no sign condition on `C`; used by `Blueprint.RevMapHolder`,
DECISIONS D6).
-/

namespace QuantumZipper

/-- `F` is Hölder continuous on `S` with some exponent `α > 0`. -/
def IsHolderOn (F : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∃ α C : ℝ, 0 < α ∧ ∀ z ∈ S, ∀ w ∈ S, ‖F z - F w‖ ≤ C * ‖z - w‖ ^ α

end QuantumZipper
