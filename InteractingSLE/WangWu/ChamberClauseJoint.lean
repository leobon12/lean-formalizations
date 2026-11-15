/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberClauseLand
import InteractingSLE.WangWu.Lemma421Seed
import InteractingSLE.WangWu.Prop419Proof

/-!
# `Chamber4JointStatement` from Proposition 4.19 alone

Packet PROVE-WW-B28. With the chamber clause (J5) proved (`SeedThree.chamberClauseStatement`) and Lemma 4.21 for seed
lines proved (PROVE-WW-B24, `lemma421SeedStatement`), PROVE-WW-B24's assembly `chamber4JointStatement_of_prop419_clause`
leaves Proposition 4.19 (the order of the seed lines, `SeedField.Prop419Statement`) as the only input of Proposition
4.24's joint statement at `κ = 4`:

* **`chamber4JointStatement_of_prop419'`** : `Prop419Statement → Chamber4.Chamber4JointStatement`;
* `twoSeedGraphInput_four_of_prop419'` : `Prop419Statement → LP.TwoSeedGraphInput 4`;
* `chamber4JointStatement_of_seedTailSmall`, `twoSeedGraphInput_four_of_seedTailSmall`: the same from PROVE-WW-B25's
  remaining input of Proposition 4.19 (`SeedField.SeedTailSmallStatement`, `prop419Statement_of_seedTailSmall`).

Conditional helpers (on Proposition 4.19); they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.WangWu.ChamberCond

open SeedField

/-- **Proposition 4.24's joint statement at `κ = 4` from Proposition 4.19 alone** (the chamber clause and Lemma 4.21
for seed lines are proved). Conditional helper. -/
theorem chamber4JointStatement_of_prop419' (h419 : Prop419Statement.{u}) : Chamber4.Chamber4JointStatement.{u} :=
  chamber4JointStatement_of_prop419_clause h419 SeedThree.chamberClauseStatement

/-- **`LP.TwoSeedGraphInput 4` from Proposition 4.19 alone.** Conditional helper. -/
theorem twoSeedGraphInput_four_of_prop419' (h419 : Prop419Statement.{u}) : LP.TwoSeedGraphInput.{u} 4 :=
  twoSeedGraphInput_four_of_prop419_clause h419 SeedThree.chamberClauseStatement

/-- **Proposition 4.24's joint statement at `κ = 4` from the small-gap seed-tail input of Proposition 4.19**
(PROVE-WW-B25's `prop419Statement_of_seedTailSmall`). Conditional helper. -/
theorem chamber4JointStatement_of_seedTailSmall (hS : SeedTailSmallStatement.{u}) :
    Chamber4.Chamber4JointStatement.{u} :=
  chamber4JointStatement_of_prop419' (prop419Statement_of_seedTailSmall hS)

/-- **`LP.TwoSeedGraphInput 4` from the small-gap seed-tail input of Proposition 4.19.** Conditional helper. -/
theorem twoSeedGraphInput_four_of_seedTailSmall (hS : SeedTailSmallStatement.{u}) : LP.TwoSeedGraphInput.{u} 4 :=
  twoSeedGraphInput_four_of_prop419' (prop419Statement_of_seedTailSmall hS)

end InteractingSLE.WangWu.ChamberCond
