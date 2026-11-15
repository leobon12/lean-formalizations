/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9DFrame
import InteractingSLE.Spec.Supplement.G12Statement
import InteractingSLE.Spec.Sec4.Aux25Term

/-!
# Theorem W5 from its remaining inputs, with Aux. 25 discharged and W0a from the source form of G12

Packet PROVE-W5-REST2. PROVE-W5-REST's assembly `Supp9D.w5Statement_of_inputs''` takes Aux. 25, W0a, W0b, Lemma 7.7,
the two retained-pair carriers and W5's common-seed comparison. Aux. lemma 25 is now a theorem
(`Theorem15.aux25Statement`, `Spec/Sec4/Aux25Term.lean`), and W0a follows from Lemma G12 in the source's evolution
form (`Supp7.w0aStatement_of_g12Evol`, `G12Statement.lean`). The remaining inputs of `Theorem15.W5Statement` are:

* `Supp7.G12EvolStatement` (Lemma G12, supplement §7.9);
* `Supp9.W0bStatement` (Lemma W0b);
* `Supp10.Lemma77Statement` (Lemma 7.7);
* `Supp9D.JointRetainedPairStatement` and `Supp9D.RetainedLocalCompletionStatement` (G7 for both tips; G3/G7a/G8/G2a,
  G9–G10 and the gluing at a retained pair);
* `Supp9.W5CommonSeedStatement` (W5's common-seed comparison).
-/

set_option autoImplicit false

universe u

namespace InteractingSLE

namespace Supp9D

/-- **Theorem W5** (Theorem 1.5's interface 3) from G12 (source form), W0b, Lemma 7.7, the two retained-pair carriers
and the common-seed comparison; Aux. 25 and W0a are discharged. -/
theorem w5Statement_of_g12Evol (hG12 : Supp7.G12EvolStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hL : RetainedLocalCompletionStatement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u}) :
    Theorem15.W5Statement.{u} :=
  w5Statement_of_inputs'' Theorem15.aux25Statement (Supp7.w0aStatement_of_g12Evol hG12) hW0b h77 hJ hL hCS

end Supp9D

end InteractingSLE
