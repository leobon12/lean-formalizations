/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2FinalInputs

/-!
# First-contact assembly with all pre-lifetime collision checks discharged
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.FCPlumb
universe u

/-- The boundary input now requires only the finite-terminal check. All
positive pre-lifetime real and interior checks follow from the source coupling. -/
theorem firstContactK2BoundaryCollisionStatement_of_terminalCollision
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u})
    (hterminal : FirstContactK2TerminalCollisionStatement.{u}) :
    FirstContactK2BoundaryCollisionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨T₁, T₂⟩ := hterminal κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  have hp := ae_canon_positive_prelife_nonThreshold h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hu₀ hsort hmean hcanon hc₁ hc₂ hz₁ hz₂ hg
  exact ⟨⟨fun a => (hp.1 a).mono (fun _ hω hB q hq hqU _ => hω hB q hq hqU), T₁.terminal⟩,
    ⟨fun a => (hp.2 a).mono (fun _ hω hB q hq hqU _ => hω hB q hq hqU), T₂.terminal⟩⟩

/-- Determination with the actual remaining mathematical inputs: capacity
safe laws and finite-terminal collision. Every pre-lifetime collision and
both incident seed checks are discharged. -/
theorem firstContactCanonCondDetStatement_of_capacitySafeLaws_terminalCollision_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u})
    (hSafe : FirstContactK2CapacitySafeLawsStatement.{u})
    (hterminal : FirstContactK2TerminalCollisionStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_capacitySafeLaws_boundaryCollision_thm12_thm13_lemma76
    h12 h13 h12₀ h13₀ h76 hSafe
    (firstContactK2BoundaryCollisionStatement_of_terminalCollision
      (lemma75Statement_of_thm12_thm13 h12 h13)
      (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76)
      firstContact_retainedRangeEntranceStatement hterminal)

end InteractingSLE.Restart.FCPlumb
