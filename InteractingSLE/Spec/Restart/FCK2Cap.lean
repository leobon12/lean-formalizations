/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2CapInputs
import InteractingSLE.Spec.Restart.FCK2CapRead

/-!
# First-contact determination from forward kernels and endpoint access

The two explicitly named source constructions remain unproved. This file
records their complete consequences without identifying them with theorems.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCPlumb
universe u

/-- Forward marked kernels supply the unchanged capacity safe-law statement. -/
theorem firstContactK2CapacitySafeLawsStatement_of_forwardKernels
    (hForward : FirstContactK2ForwardKernelsStatement.{u}) :
    FirstContactK2CapacitySafeLawsStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨K₁, K₂⟩ := hForward κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  exact ⟨bdrySafeInputs_of_fcCapForwardInputs (hd.measurable_chartField κ hh.1) K₁,
    bdrySafeInputs_of_fcCapForwardInputs (hd.measurable_chartField κ hh.1) K₂⟩

/-- Terminal access and the actual incident heights supply all endpoint
collision checks, including a possible zero endpoint. -/
theorem firstContactK2TerminalCollisionStatement_of_terminalAccess
    (hAccess : FirstContactK2TerminalAccessStatement.{u}) :
    FirstContactK2TerminalCollisionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨A₁, A₂⟩ := hAccess κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  exact ⟨terminalInputs_of_fcCapTerminalAccess hκ hc₁ hz₁
      (hg.mono fun _ hω hM => (hω hM).1) A₁,
    terminalInputs_of_fcCapTerminalAccess hκ hc₂ hz₂
      (hg.mono fun _ hω hM => (hω hM).2) A₂⟩

/-- The current conditional determination theorem. The forward-kernel and
endpoint-access hypotheses are not discharged by the per-seed CMI converse
or by the general-angle martingale-law theorem. -/
theorem firstContactCanonCondDetStatement_of_forwardKernels_terminalAccess_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u})
    (hForward : FirstContactK2ForwardKernelsStatement.{u})
    (hAccess : FirstContactK2TerminalAccessStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_capacitySafeLaws_terminalCollision_thm12_thm13_lemma76
    h12 h13 h12₀ h13₀ h76
    (firstContactK2CapacitySafeLawsStatement_of_forwardKernels hForward)
    (firstContactK2TerminalCollisionStatement_of_terminalAccess hAccess)

end InteractingSLE.Restart.FCPlumb
