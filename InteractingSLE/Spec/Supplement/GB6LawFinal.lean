/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LawMain
import InteractingSLE.Spec.Supplement.GB6LifeEndMain
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# Proposition GB6: the conditional-law half from (d), the canonical codes and Theorem 1.3 at `16/κ`

Packet PROVE-GB6D. With step (e) proved (`gb6EndpointStatement`: the deterministic endpoint argument from the base
statement `gb6BaseStatement`, and the GB5 tails under the conditional law, `gb6_kernel`), GB6's conditional-law half
(PROVE-GB6C's hull form `GB6RelativeLawStatement`, hence `GB6RestartStatement` and the first-contact assertion
`GB6FirstContactStatement`) follows from exactly:

* `GB6CondDetStatement` — step (d), the conditional law of the relative exploration before contact (named input);
* `CompleteSixteenDivStatement` — Theorem 1.3 at `16/κ` (from its twelve landed open inputs,
  `completeSixteenDivStatement_of_open`);
* the canonical driver codes, `Restart.CanonicalDriverCodeStatement` — proved by PROVE-CONDDET from Theorem 1.2 in R44's
  word-measurable form (`Exist.Staged.Theorem12ParamStatement`) and Theorem 1.3 (`Exist.Theorem13Statement`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart

/-- **GB6, step (e), deterministic half** (proved). -/
theorem gb6EndpointStatement : GB6EndpointStatement := gb6EndpointStatement_of_base gb6BaseStatement

/-- **GB6's conditional-law half (hull form)** from (d), canonical driver codes and Theorem 1.3 at `16/κ` (conditional
helper). -/
theorem gb6RelativeLawStatement_of_condDet_complete (hcode : CanonicalDriverCodeStatement)
    (hC : CompleteSixteenDivStatement) (hD : GB6CondDetStatement.{u}) : GB6RelativeLawStatement.{u} :=
  gb6RelativeLawStatement_of_condDet hcode hC gb6EndpointStatement hD

/-- **GB6's conditional-law half (hull form)** from (d), Theorem 1.2 (R44 form), Theorem 1.3 and Theorem 1.3 at `16/κ`
(conditional helper). -/
theorem gb6RelativeLawStatement_of_param_complete (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hC : CompleteSixteenDivStatement) (hD : GB6CondDetStatement.{u}) :
    GB6RelativeLawStatement.{u} :=
  gb6RelativeLawStatement_of_param h12p h13 hC gb6EndpointStatement hD

/-- **GB6's conditional-law half** (`GB6RestartStatement`) from the same inputs (conditional helper). -/
theorem gb6RestartStatement_of_param_complete (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hC : CompleteSixteenDivStatement) (hD : GB6CondDetStatement.{u}) :
    GB6RestartStatement.{u} :=
  gb6RestartStatement_of_relativeLaw (gb6RelativeLawStatement_of_param_complete h12p h13 hC hD)

/-- **GB6's first-contact assertion** from the same inputs (conditional helper). -/
theorem gb6FirstContactStatement_of_param_complete (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hC : CompleteSixteenDivStatement) (hD : GB6CondDetStatement.{u}) :
    GB6FirstContactStatement.{u} :=
  gb6FirstContactStatement_of_relativeLaw (gb6RelativeLawStatement_of_param_complete h12p h13 hC hD)

end GB6

end Supp8

end InteractingSLE
