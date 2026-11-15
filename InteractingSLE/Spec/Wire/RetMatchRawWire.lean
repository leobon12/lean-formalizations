/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchRawLocal
import InteractingSLE.Spec.Wire.RetMatchPredictWire

/-!
# Retained determination from canonical stopping-rule regularization

Doob–Dynkin and the bounded positive announcements are proved independently
of regularization. The only new named hypothesis concerns Galmarino versions
of canonical augmented stopping times under the model's history law.
-/

set_option autoImplicit false
noncomputable section

namespace InteractingSLE.Wire.RetMatchRaw

/-- The unchanged retained model determination target follows from canonical
regularization and the permitted Theorem 1.3. -/
theorem retStoppedTypeDeterminationStatement_of_canonicalRegularization
    (h13 : Exist.Theorem13Statement.{0}) (hC : CanonicalPrelifeRegularizationStatement) :
    RetStoppedTypeDeterminationStatement :=
  RetMatchPredict.retStoppedTypeDeterminationStatement_of_positiveBoundedPrelifeRules h13
    (positiveBoundedPrelifeRuleStatement_of_canonicalRegularization hC)

universe v

/-- The unchanged retained Lemma 7.6, with arbitrary outer universe, follows
from canonical regularization and the permitted source inputs. -/
theorem lemma76DetRStatement_of_canonicalRegularization
    (h13 : Exist.Theorem13Statement.{0}) (hC : CanonicalPrelifeRegularizationStatement)
    (h75 : Theorem15.Lemma75Statement.{v}) : Sec7.Lemma76DetRStatement.{v} :=
  RetMatchPredict.lemma76DetRStatement_of_positiveBoundedPrelifeRules h13
    (positiveBoundedPrelifeRuleStatement_of_canonicalRegularization hC) h75

end InteractingSLE.Wire.RetMatchRaw
