/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.TraceCoding
import InteractingSLE.Spec.Sec7.CounterflowProb2Coding

/-!
# The trace codings, unconditionally

Packet PROVE-TRACECODE. PROVE-T14-IN proves PROVE-SEC7-D2's named input `Sec7.StoppedTraceCodingStatement`
(`Sec7.Coding.stoppedTraceCodingStatement`, `Spec/Sec7/CounterflowProb2Coding.lean`). With
`topTraceCodingStatement_of_stopped` (`TraceCoding.lean`) this discharges PROVE-SEC7-A4's named inputs
`Sec7.TopTraceCodingStatement` and `Sec7.TransientTraceCodingStatement`.
-/

set_option autoImplicit false

namespace InteractingSLE

namespace Sec7

/-- **The measurable coding of a continuous generating trace on `[0, ∞)`** (named input of PROVE-SEC7-A4; Corollary
LP11's proof, pp. 488–489, and Aux. lemma 126's proof, pp. 399–400). -/
theorem topTraceCodingStatement : TopTraceCodingStatement :=
  topTraceCodingStatement_of_stopped Coding.stoppedTraceCodingStatement

/-- **The measurable coding of a continuous generating trace on `[0, ∞)` tending to infinity** (PROVE-SEC7-A4). -/
theorem transientTraceCodingStatement : TransientTraceCodingStatement :=
  transientTraceCodingStatement_of_top topTraceCodingStatement

end Sec7

end InteractingSLE
