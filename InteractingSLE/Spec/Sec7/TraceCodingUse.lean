/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.TraceCodingTop
import InteractingSLE.Spec.Sec7.TwoForceMain3Prop73
import InteractingSLE.Spec.Sec2.JacobiExists

/-!
# The trace codings and the Jacobi diffusion, discharged in their §7 consumers

Packet PROVE-TRACECODE2. The measurable codings of the trace event are proved:

* `Sec7.topTraceCodingStatement`, `Sec7.transientTraceCodingStatement` (`T = ∞`, PROVE-TRACECODE,
  `Foundations/Loewner/TraceCodingTop.lean`), the named inputs of PROVE-SEC7-A4;
* `Sec7.Coding.stoppedTraceCodingStatement` (buffered stops, PROVE-T14-IN, `Spec/Sec7/CounterflowProb2Coding.lean`),
  the named input of PROVE-SEC7-D2.

The other input these consumers share, `JacobiDiffusionExistsStatement`, is PROVE-YW-JACOBI's
`Sec2.Jacobi.exists_isJacobiDiffusion` (`Spec/Sec2/JacobiExists.lean`); `jacobiDiffusionExistsStatement` restates it
in the named form.

This file gives the consumers' conclusions with both inputs removed. Each wrapper keeps only the inputs that are still
open (the embedded reference of Lemma 7.1, the reference of Lemma 7.25, the change of measure of Aux. lemma 126, the
§7.3 inputs of the κ < 4 induction). They are conditional helpers and replace no source theorem.

| Consumer | Wrapper |
|---|---|
| `prop73TraceStatement_of_inputs`, `prop73TraceStatement_of_lemma71` | `prop73TraceStatement_of_reference` |
| `isCompleteForceWord_seedRight` | `isCompleteForceWord_seedRight_of_prop73Trace` |
| `seedOneForceTraceStatement_of_prop73` | `seedOneForceTraceStatement_of_prop73Trace` |
| `seedOneForceTraceStatement_of_inputs`, `seedOneForceTraceStatement_of_lemma71` | `seedOneForceTraceStatement_of_reference` |
| `revisedInductionLtFourStatement_of_lemma71` | `revisedInductionLtFourStatement_of_reference` |
| `aux126StoppedTraceStatement_of_inputs`, `Coding.aux126StoppedTraceStatement_of_girsanov` | `aux126StoppedTraceStatement_of_aux126Girsanov` |
| `lemma725TraceStatement_of_girsanov`, `Coding.lemma725TraceStatement_of_three` | `lemma725TraceStatement_of_reference_girsanov` |
-/

set_option autoImplicit false

open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Sec7

/-- **Existence of the two-sided Jacobi diffusion** in the named form `JacobiDiffusionExistsStatement` (Theorem 2.2's
proof, p. 23), from PROVE-YW-JACOBI's `Sec2.Jacobi.exists_isJacobiDiffusion`. -/
theorem jacobiDiffusionExistsStatement : JacobiDiffusionExistsStatement :=
  fun _ _ _ hκ ha hb => Sec2.Jacobi.exists_isJacobiDiffusion hκ ha hb

/-! ### §7.1: Proposition 7.3 and the one-force seed case -/

/-- **Proposition 7.3, trace part** (p. 242), `Prop73TraceStatement`, from the embedded reference of Lemma 7.1 alone:
`prop73TraceStatement_of_inputs` with the coding and the Jacobi diffusion discharged. -/
theorem prop73TraceStatement_of_reference (href : Lemma71TraceReferenceStatement.{v}) :
    Prop73TraceStatement.{u} :=
  prop73TraceStatement_of_inputs jacobiDiffusionExistsStatement transientTraceCodingStatement href

/-- **The one-force seed case on the right, from Proposition 7.3** (p. 378): `isCompleteForceWord_seedRight` with the
coding and the Jacobi diffusion discharged. -/
theorem isCompleteForceWord_seedRight_of_prop73Trace (h73 : Prop73TraceStatement.{0}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (xL : Fin 0 → ℝ) (xR : Fin 1 → ℝ) (ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ)
    (hxR : ∀ i, xR i = 0) (hρR : ∀ i, -2 < ρR i) : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR :=
  isCompleteForceWord_seedRight jacobiDiffusionExistsStatement transientTraceCodingStatement h73 hκ hκ4 xL xR ρL ρR
    hxR hρR

/-- **The one-force seed case from Proposition 7.3**, `SeedOneForceTraceStatement`:
`seedOneForceTraceStatement_of_prop73` with the coding and the Jacobi diffusion discharged. -/
theorem seedOneForceTraceStatement_of_prop73Trace (h73 : Prop73TraceStatement.{0}) :
    SeedOneForceTraceStatement.{u} :=
  seedOneForceTraceStatement_of_prop73 jacobiDiffusionExistsStatement transientTraceCodingStatement h73

/-- **The one-force seed case from the embedded reference of Lemma 7.1** alone:
`seedOneForceTraceStatement_of_inputs` with the coding and the Jacobi diffusion discharged. -/
theorem seedOneForceTraceStatement_of_reference (href : Lemma71TraceReferenceStatement.{v}) :
    SeedOneForceTraceStatement.{u} :=
  seedOneForceTraceStatement_of_inputs jacobiDiffusionExistsStatement transientTraceCodingStatement href

/-- **The revised κ < 4 induction** (`LP.RevisedInductionLtFourStatement`) from the embedded reference of Lemma 7.1 and
the four §7.3 inputs (Aux. 99, 106, 113 and the one-sided step): `revisedInductionLtFourStatement_of_lemma71` with the
coding and the Jacobi diffusion discharged. -/
theorem revisedInductionLtFourStatement_of_reference (href : Lemma71TraceReferenceStatement.{v})
    (h99 : Aux99Statement.{u}) (h106 : Aux106Statement.{u}) (h113 : Aux113Statement.{u})
    (h1s : OneSidedStepStatement.{u}) : LP.RevisedInductionLtFourStatement.{u} :=
  revisedInductionLtFourStatement_of_lemma71 jacobiDiffusionExistsStatement topTraceCodingStatement href
    h99 h106 h113 h1s

/-! ### §7.4: Aux. lemma 126 and Lemma 7.25 -/

/-- **Aux. lemma 126, the stopped transfer** (`Aux126StoppedTraceStatement`) from the change of measure of Aux. lemma
126 alone: `aux126StoppedTraceStatement_of_inputs` with the stopped coding and the Jacobi diffusion discharged. -/
theorem aux126StoppedTraceStatement_of_aux126Girsanov (hGir : Aux126GirsanovStatement.{v}) :
    Aux126StoppedTraceStatement.{u, v} :=
  aux126StoppedTraceStatement_of_inputs jacobiDiffusionExistsStatement Coding.stoppedTraceCodingStatement hGir

/-- **Lemma 7.25, finite-time continuity** (p. 413), `LP.Lemma725TraceStatement`, from the reference of Lemma 7.25
(Aux. lemmas 130, 125, 127) and the change of measure of Aux. lemma 126: `lemma725TraceStatement_of_girsanov` with the
stopped coding and the Jacobi diffusion discharged. -/
theorem lemma725TraceStatement_of_reference_girsanov (hRef : Lemma725ReferenceStatement.{v})
    (hGir : Aux126GirsanovStatement.{v}) : LP.Lemma725TraceStatement.{u} :=
  lemma725TraceStatement_of_girsanov jacobiDiffusionExistsStatement hRef hGir Coding.stoppedTraceCodingStatement

end Sec7

end InteractingSLE
