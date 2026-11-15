/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb6Positive
import InteractingSLE.Spec.Sec7.ContinuityProb6Seed
import InteractingSLE.Spec.Theorem13Inputs

/-!
# §7.3: the reductions of Aux. lemmas 106 and 113 with the inputs proved in this packet

Packet PROVE-SEC7-C6. Discharges, in the landed reductions of PROVE-SEC7-C4/C5, the named inputs proved here:

* `ExistsEvolutionStatement` is the landed `Theorem13.existsEvolutionStatement` (PROVE-T13-ASM);
* `aux106TransienceStatement_of_aux102`: `Aux106TransienceStatement` from the one-force inputs and Aux. lemma 102
  with its band switches (`Aux106PositiveStatement` is `Positive.aux106PositiveStatement`);
* `aux106Statement_of_aux102`: `Sec7.Aux106Statement` (the input of the κ < 4 induction) from the same;
* `aux113PrefixStatement_of_transience`, `lpAux113PrefixStatement_of_transience`: the prefix parts of Aux. lemma 113
  from transience without merger alone (the seed entrance is `Positive.seedEntranceStatement`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE

namespace Sec7

/-- **Aux. lemma 106's transience from the one-force inputs and Aux. lemma 102 with its band switches.** -/
theorem aux106TransienceStatement_of_aux102 (h1 : SeedOneForceTraceStatement.{u}) (h99 : Aux99Statement.{u})
    (h102 : Aux102BandStatement.{u}) : Aux106TransienceStatement.{u} :=
  aux106TransienceStatement_of_inputs Theorem13.existsEvolutionStatement h1 h99 h102 Positive.aux106PositiveStatement

/-- **`Sec7.Aux106Statement` from the one-force inputs and Aux. lemma 102 with its band switches.** -/
theorem aux106Statement_of_aux102 (h1 : SeedOneForceTraceStatement.{u}) (h99 : Aux99Statement.{u})
    (h102 : Aux102BandStatement.{u}) : Aux106Statement.{u} :=
  aux106Statement_of_separated (aux106SeparatedStatement_of_inputs Theorem13.existsEvolutionStatement h1 h99
    (aux106TransienceStatement_of_aux102 h1 h99 h102))

/-- **The prefix part of Aux. lemma 113 from transience without merger** (and Proposition 7.3's two-seed statement). -/
theorem aux113PrefixStatement_of_transience (h73 : Prop73TraceStatement.{u})
    (htr : Aux113TransienceStatement.{u}) : Aux113PrefixStatement.{u} :=
  aux113PrefixStatement_of_inputs Theorem13.existsEvolutionStatement h73
    (fun _ hκ _ => Positive.seedEntranceStatement hκ) htr

/-- **The prefix part of Aux. lemma 113 in LP10's form from transience without merger**, every `κ > 0`. -/
theorem lpAux113PrefixStatement_of_transience {κ : ℝ} (hκ : 0 < κ) (htr : LPAux113TransienceStatement.{u} κ) :
    LPAux113PrefixStatement.{u} κ :=
  lpAux113PrefixStatement_of_inputs hκ Theorem13.existsEvolutionStatement (Positive.seedEntranceStatement hκ) htr

end Sec7

end InteractingSLE
