/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2TermAccess

/-!
# First-contact determination with physical terminal access discharged

The only additional source input is the forward marked field-kernel law
`FirstContactK2ForwardKernelsStatement`. Its two instances are protected
Gaussian pairings and complement-member pairings in the actual retained
capacity filtration. Thus a general conditional first-exit/restart field law
can supply it without a terminal or maximal-lifetime clause: those source
checks are proved here. The precise kernel and censoring types remain the
committed `FCK2CapForwardInputs` and `HasFCK2CapForwardKernel` interfaces.
-/
set_option autoImplicit false
noncomputable section

namespace InteractingSLE.Restart.FCPlumb
universe u

/-- Physical terminal access and all collision checks are discharged.
Only the general restart law's source forward-kernel instance remains. -/
theorem firstContactCanonCondDetStatement_of_forwardKernels_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u})
    (hForward : FirstContactK2ForwardKernelsStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_source_forwardKernels_physicalTerminalAccess
    h12 h13 h12₀ h13₀ h76 hForward
    (firstContactK2PhysicalTerminalAccessStatement
      (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76))

end InteractingSLE.Restart.FCPlumb
