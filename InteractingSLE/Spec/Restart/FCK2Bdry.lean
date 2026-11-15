/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2BdryInputs

/-!
# First-contact boundary assembly with source seeds discharged

The old boundary-input statement follows from capacity safe laws and the
boundary collision checks. The supplied source word has admissible seeds
on every branch, including collapsed sides, by the proved source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCPlumb
universe u

/-- Conditional assembly of the unchanged boundary-input statement. The
collapsed-side seed obligation is proved from the source data. -/
theorem firstContactK2BoundaryInputsStatement_of_safeLaws_boundaryCollision
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u})
    (hSafe : FirstContactK2CapacitySafeLawsStatement.{u})
    (hCollision : FirstContactK2BoundaryCollisionStatement.{u}) :
    FirstContactK2BoundaryInputsStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨S₁, S₂⟩ := hSafe κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨C₁, C₂⟩ := hCollision κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  have ha := ae_admissible_of_boxMean_all_sides h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hu₀ hsort hmean
  exact ⟨⟨ha.mono (fun _ hω hM _ => (hω hM).1), S₁.safe_law, S₁.safe_members,
      C₁.boundary, C₁.terminal⟩,
    ⟨ha.mono (fun _ hω hM _ => (hω hM).2), S₂.safe_law, S₂.safe_members,
      C₂.boundary, C₂.terminal⟩⟩

/-- Determination from Theorems 1.2–1.3, Lemma 7.6 and precisely the remaining
capacity safe-law and boundary-collision statements. No collapsed seed input
or ordinary-pair assertion at first contact is assumed. -/
theorem firstContactCanonCondDetStatement_of_capacitySafeLaws_boundaryCollision_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u})
    (hSafe : FirstContactK2CapacitySafeLawsStatement.{u})
    (hCollision : FirstContactK2BoundaryCollisionStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_boundaryInputs_thm12_thm13_lemma76 h12 h13 h12₀ h13₀ h76
    (firstContactK2BoundaryInputsStatement_of_safeLaws_boundaryCollision
      (lemma75Statement_of_thm12_thm13 h12 h13)
      (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76)
      firstContact_retainedRangeEntranceStatement hSafe hCollision)

end InteractingSLE.Restart.FCPlumb
