/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCKDisintMain
import InteractingSLE.Spec.Supplement.RLCKLiftProof

/-!
# Lemma G8 (with G9): the remaining inputs

Packet PROVE-RLC-K. `RLC.G8FrameStatement` from Lemma 7.5, Proposition 7.4's complete ordered reference, G7's
retained-pair restart conditionally on the retained histories and G8's positivity input: `g8FrameStatement_of_parts`
with Lemma G9 discharged (`g9LiftStatement`).
-/

set_option autoImplicit false

universe u

namespace InteractingSLE

namespace RLC

/-- **Lemma G8 (with G9)**, `G8FrameStatement`, from Lemma 7.5, Proposition 7.4's complete ordered reference, G7
conditionally on the retained histories and G8's positivity (Lemma G9 is proved: `g9LiftStatement`). -/
theorem g8FrameStatement_of_cond_pos (h75 : Theorem15.Lemma75Statement.{0})
    (href : Sec7.Prop74Order.Prop74RefStatement.{u}) (hR : RetainedPairRestartCondStatement.{u})
    (hPos : G8PositivityStatement.{u}) : G8FrameStatement.{0} :=
  g8FrameStatement_of_parts h75 href hR hPos g9LiftStatement

end RLC

end InteractingSLE
