/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCIOrder
import InteractingSLE.Spec.Wire.Thm15Inputs5

/-!
# Lemma G2a's order from the established inputs of Theorem 1.5

Packet PROVE-RLC-I (wiring only, no new mathematics). `RLC.g2aOrderStatement_of_parts` with its inputs discharged as in
PROVE-WIRE5 (`Spec/Wire/Thm15Inputs5`): Lemma 7.5 and Lemma 7.7 (`Wire.lemma75Statement_of_open5`,
`Wire.lemma77Statement_of_open5`), the first-contact word kernel from the word-measurable Theorem 1.2, Theorem 1.3 and
the first-contact canonical conditional determination (`Restart.firstContactWordKernelStatement_of_param`,
`Exist.Param12.theorem12ParamStatement_of_thm12_thm13`), and the half-plane Proposition 5.5 at universe `0` from
Propositions 4.11 and 5.1 in chart `Q` (`Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q`). Theorems 1.2
and 1.3 enter only as the types of their frozen anchors (this serves Theorem 1.5 only; R43/R48 do not apply).
Conditional helpers with distinct names; none is a provider.
-/

set_option autoImplicit false

universe u

namespace InteractingSLE

namespace RLC

/-- **The order of Lemma G2a** from G2a's other parts and the established open inputs of Theorem 1.5: Theorems 1.2–1.3
at universe `0` (frozen types); at universe `u`: Propositions 4.11 and 5.1 in chart `Q`, Lemma 7.1's fixed-time pocket
clause, (R1) + heights + (Det) of Lemma 7.6 and the first-contact canonical conditional determination; at universe `0`:
Propositions 4.11 and 5.1 in chart `Q`. -/
theorem g2aOrderStatement_of_open5 (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hcl : Sec7.Lemma72E.PocketClauseStatement.{u}) (hD76 : Sec7.Lemma76CondDetHeightsStatement.{u})
    (hFCD : Restart.FirstContactCanonCondDetStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hP : G2aPartsStatement.{u}) : G2aOrderStatement.{u} :=
  g2aOrderStatement_of_parts (Wire.lemma75Statement_of_open5 h411 h51 hcl)
    (Wire.lemma77Statement_of_open5 h12₀ h13₀ h411 h51 hcl hD76)
    (Restart.firstContactWordKernelStatement_of_param (Wire.lemma75Statement_of_open5 h411 h51 hcl)
      (Wire.lemma77Statement_of_open5 h12₀ h13₀ h411 h51 hcl hD76)
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hFCD)
    (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411₀ h51₀) hP

/-- **Lemma G2a** (`G2aReferenceStatement`) from its other parts and the same inputs. -/
theorem g2aReferenceStatement_of_open5 (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hcl : Sec7.Lemma72E.PocketClauseStatement.{u}) (hD76 : Sec7.Lemma76CondDetHeightsStatement.{u})
    (hFCD : Restart.FirstContactCanonCondDetStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hP : G2aPartsStatement.{u}) : G2aReferenceStatement.{u} :=
  g2aReferenceStatement_of_parts_order hP
    (g2aOrderStatement_of_open5 h12₀ h13₀ h411 h51 hcl hD76 hFCD h411₀ h51₀ hP)

end RLC

end InteractingSLE
