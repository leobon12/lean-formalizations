/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb7Aux102
import InteractingSLE.Spec.Theorem13Inputs
import InteractingSLE.WangWu.Theorem18

/-!
# The consumers of Aux. lemma 102, without the input

Packet PROVE-SEC7-C7. `Sec7.Aux102BandStatement` is now a theorem (`Sec7.aux102BandStatement`,
`ContinuityProb7Aux102.lean`). This file restates the landed reductions that took it as a hypothesis, with the
hypothesis discharged (same conclusions, one input fewer):

* `C7.aux106Statement_of_oneForce`: Aux. lemma 106 in LP form, every `κ > 0`, from the one-force statement
  (`WangWu.Theorem18.aux106Statement_of_oneForce`, PROVE-WW-C2);
* `C7.lpAux113TransienceStatement_of_high`, `C7.aux113TransienceStatement_of_high`: Aux. lemma 113's transience from
  its third sector alone (`WangWu.LowSide`, PROVE-WW-C2);
* `C7.revisedInductionLtFourStatement_of_open`: Theorem 1.3's `κ < 4` range without `Aux102BandStatement`
  (`Theorem13.revisedInductionLtFourStatement_of_open`, PROVE-T13-ASM);
* `C7.wwTheorem18DistinctStatement_of_high`: Wang–Wu's Theorem 1.8 (`κ = 4`) without `Aux102BandStatement`.
-/

set_option autoImplicit false

universe u

namespace InteractingSLE

namespace Sec7

namespace C7

/-- **Aux. lemma 106 (LP form), every `κ > 0`, from the one-force statement** (Aux. 102 discharged). -/
theorem aux106Statement_of_oneForce {κ : ℝ} (hκ : 0 < κ) (h1 : LP.OneForceStatement.{u} κ) :
    LP.Aux106Statement.{u} κ :=
  WangWu.Theorem18.aux106Statement_of_oneForce hκ h1 aux102BandStatement

/-- **Aux. lemma 113's transience (LP10's form) from its third sector** (Aux. 102 discharged). -/
theorem lpAux113TransienceStatement_of_high {κ : ℝ} (hκ : 0 < κ)
    (hhigh : WangWu.LowSide.LPAux113HighTransienceStatement.{u} κ) : LPAux113TransienceStatement.{u} κ :=
  WangWu.LowSide.lpAux113TransienceStatement_of_high hκ aux102BandStatement hhigh

/-- **Aux. lemma 113's transience (`κ < 4`) from its third sector** (Aux. 102 discharged). -/
theorem aux113TransienceStatement_of_high (h73 : Prop73TraceStatement.{u})
    (hhigh : WangWu.LowSide.Aux113HighTransienceStatement.{u}) : Aux113TransienceStatement.{u} :=
  WangWu.LowSide.aux113TransienceStatement_of_high h73 aux102BandStatement hhigh

/-- **Theorem 1.3, `0 < κ < 4`, from the open inputs other than Aux. lemma 102.** -/
theorem revisedInductionLtFourStatement_of_open
    (h71 : Lemma71.Lemma71MappedSegmentStatement.{0})
    (h99 : ∀ κ : ℝ, 0 < κ → κ < 4 → Aux99StoppedStatement.{u} κ)
    (h106 : Aux106PositiveStatement.{u})
    (hseed : ∀ κ : ℝ, 0 < κ → κ < 4 → SeedEntranceStatement.{u} κ)
    (h113 : Aux113TransienceStatement.{u}) (h1s : OneSidedPrefixStatement.{u}) :
    LP.RevisedInductionLtFourStatement.{u} :=
  Theorem13.revisedInductionLtFourStatement_of_open h71 h99 aux102BandStatement h106 hseed h113 h1s

/-- **Wang–Wu's Theorem 1.8 (`κ = 4`) without Aux. lemma 102.** -/
theorem wwTheorem18DistinctStatement_of_high (h2 : LP.TwoSeedComplete.{u} 4)
    (hna : WangWu.Lemma51.OneRightNonAdmissibleStatement.{u} 4)
    (hhigh : WangWu.LowSide.LPAux113HighTransienceStatement.{u} 4) (h9 : LP9PrefixStatement.{u} 4) :
    LP.WWTheorem18DistinctStatement.{u} :=
  WangWu.Theorem18.wwTheorem18DistinctStatement_of_high h2 hna aux102BandStatement hhigh h9

end C7

end Sec7

end InteractingSLE
