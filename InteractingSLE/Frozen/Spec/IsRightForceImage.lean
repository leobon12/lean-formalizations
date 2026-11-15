-- Frozen anchor (definition, spec_IsRightForceImage_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
import QuantumZipper.Loewner.Forward

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace InteractingSLE

/-- **`v` is the geometric image of the right force point `x` under the Loewner evolution of the driver `w`**
(Specification §2.3, L815: "If we are given any process `W_t` with `W_0 = 0` we can define the Loewner evolution
`g_t`. If we are also given … points … `x^{i,R} ≥ 0` then … if `x^{i,q}` has not yet been absorbed by the Loewner hull
`K_t` then `V_t^{i,q} = g_t(x^{i,q})`, and otherwise `V_t^{i,R}` is the `g_t` image of the right endpoint of
`ℝ ∩ K_t`"). The carrier is the source's: `w` continuous with `w 0 = 0` and `x ≥ 0` (`x = 0` is `0⁺`). The value is
`V_t = inf {g_t(y) : y > x, y not swallowed by time t}`, `g_t(y) = w_t + f_t(y)`, `f_t = QuantumZipper.fwdMap` the
centred Loewner map, `y` not swallowed by time `t` when the centred real flow from `y` exists on `[0, t]`
(`QuantumZipper.IsForwardSol`). The module `InteractingSLE.Spec.Sec2.T2426Cert` proves that this is `g_t(x)` while `x`
is not swallowed, the right limit of `g_t` at the right end of the swallowed real set otherwise, and `x` at time
`0`. -/
def IsRightForceImage (w : ℝ≥0 → ℝ) (x : ℝ) (v : ℝ≥0 → ℝ) : Prop :=
  Continuous w ∧ w 0 = 0 ∧ 0 ≤ x ∧
    ∀ t : ℝ≥0, v t = w t + sInf {c : ℝ | ∃ y : ℝ, x < y ∧
      (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) (t : ℝ) u) ∧
      c = (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) (t : ℝ) (y : ℂ)).re}

end InteractingSLE
