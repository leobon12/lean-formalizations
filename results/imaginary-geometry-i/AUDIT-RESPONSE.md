# Response to the external audit of 15 November 2026

An independent audit of the first public snapshot of this release (commit `94b0484`) checked the formal statements
against Miller and Sheffield's paper, looked for vacuity, hidden axioms and circularity, and recompiled a 462-module
subset.
- **Verdict:** substantive, apparently nonvacuous mathematics, with no fake SLE/GFF encoding, inconsistent extra
  premise, admitted proof or circular substitution in the chains it inspected.
- **Requests:** six items, mostly about the exact correspondence between the advertised results and the frozen
  statements.

This ledger answers each item in the audit's requested form. "New anchor" means a new frozen, sealed theorem file,
added beside the original 17, which stay unchanged. "Supplementary" means a public theorem whose statement passed an
independent statement audit but is not a frozen anchor.

## Summary

| Item (audit priority) | Status | Where |
| --- | --- | --- |
| 1. Crossing predicate permits merging (1) | **Resolved**: new anchor | `IsFlowLine.crosses_of_lt_of_contact` |
| 2. Contact clauses fire only on interior contacts (1) | **Resolved** for merging and crossing (new anchors). **Open, disclosed**: critical-angle non-intersection at real points | `IsFlowLine.merges_of_contact`, `IsFlowLine.crosses_of_lt_of_contact` |
| 3. Theorem 2.6 normalization (2) | **Resolved** in the documentation; the statement was already correct | [Errata A3](ERRATA.md) |
| 4a. Counterflow frame (2) | **Resolved**: supplementary bridge theorems | `AuditFix.literalCounterflowBridge_holds` and corollaries |
| 4b. Frontier meaning (2) | **Resolved**: new anchor in the paper's case; supplementary general bridge | `IsCenteredCounterflowDriver.boundaryWalks_outerBoundaries` |
| 5. Markov sentence of Theorem 2.2 (3) | **Resolved**: new anchor (strong Markov); supplementary simple and increment forms | `exists_strongMarkovKernel_isIntegratedSLEEvolution` |
| 6. Verification evidence (3) | **Resolved**; the public workflow run is pending | [Specification](specification/), [Correspondence](CORRESPONDENCE.md), the guide's "How it was checked" |

The audit also judged the Theorem 2.4 horizon correction justified, already disclosed, and not a hidden gap. Nothing
was changed there.

## 1. Crossing (priority 1)

- **Finding: confirmed.** `CrossesFromRightAt` asks only that, after the first contact, every pair of strict outgoing
  prefixes has ordered proper completions. `HasOrderedProperCompletions` admits identical curves, so the frozen
  Theorem 1.5 (iii) conclusion did not exclude merging after the contact. The audit's two examples show this: identical
  vertical rays, and curves that merge after a first contact at i.
- **Change.** A new anchor, `InteractingSLE.IsFlowLine.crosses_of_lt_of_contact`
  ([`InteractingSLE/Frozen/Spec/IsFlowLine_crosses_of_lt_of_contact.lean`](../../InteractingSLE/Frozen/Spec/IsFlowLine_crosses_of_lt_of_contact.lean)).
  At the first contact it adds that no open arc of either outgoing available path lies on the other outgoing available
  path. This is the specification's "no common nontrivial open outgoing arc" (Theorem 7.12C) and the paper's "crosses".
- **Mathematical argument.**
  - The conditional outgoing paths are flow lines of the conditional field in the first-contact chart.
  - The project's W0b theorem (distinct-angle flow lines share no open subarc, from Lemma 7.5) applies to them.
  - The no-arc event is measurable, so it transfers from the conditional law back to the original curves.
  - The transfer goes through the chart and the increasing clocks, using Lemma 7.7's confinement.
  - Baire's theorem upgrades the conclusion from finite prefixes to whole outgoing paths
    (`Spec/AuditFix/StrongCross*.lean`).
  - A deterministic lemma, `AuditFix.Cross.not_agreeAsCurvesAfter_of_noCommonOutgoingArc`, shows the new clause
    excludes `AgreeAsCurvesAfter` once both curves continue past the contact.
- **Verification.**
  - The statement audit AUD-AF-T15 compiled the audit's examples: both satisfy the old conclusion and fail the new one.
  - The new anchor implies the original `IsFlowLine.crosses_of_lt`.
  - Both seal keys (AUD-SEAL-AF), the axioms (`propext`, `Classical.choice`, `Quot.sound`) and an exact kernel replay.
- **Remaining qualification.**
  - The incoming order is not restated; it follows from x₂ < x₁ and Theorem 1.5 (i).
  - A finite lifetime's endpoint is not counted as part of the other path.

## 2. Contact scope (priority 1)

- **Finding: confirmed.** The frozen merging, crossing and critical-angle clauses were triggered only by contacts in
  the open half-plane strictly before both lifetimes. The paper's Proposition 7.12 and Lemma 7.8 (pp. 137, 141) also
  treat a first contact on the real line.
- **Change.**
  - **Merging:** new anchor `InteractingSLE.IsFlowLine.merges_of_contact`. Merging holds at every contact of the closed
    available paths: interior or real, at a common starting point, or at a terminal time.
  - **Crossing:** the new crossing anchor above fires on every available contact, interior or real.
- **Mathematical argument.** The interior trigger was a restriction of the frozen statements only. Lemma 7.7, W8, the
  first-contact restart and Theorem 7.12C already cover first contacts on the boundary
  (`Spec/AuditFix/BoundaryContact*.lean`).
- **Verification.** AUD-AF-T15, both seal keys, the axioms and kernel replay. Both new anchors imply their originals.
- **Open, and disclosed.** The critical-angle clauses ("otherwise the paths almost surely do not intersect, except
  possibly at their starting point", p. 30) are proved only for contacts in the open half-plane. That is at any
  parameter, terminal times included: `AuditFix.criticalOrderedNoInteriorPoint_holds` and
  `AuditFix.criticalCrossingNoLaterInteriorPoint_holds`, which are supplementary.
  - **Why the real-point claim is not proved:** the project's critical-angle argument excludes first hits inside the
    half-plane only. The specification restricts these clauses in the same way (spec pp. 5, 543–544).
  - **What it would need:** a first-hit exclusion at points where one curve touches the real line, and a junction lemma
    at random boundary points under the conditional law. Neither is available.
  - **A note on the paper's wording.** A hand-checked example (not formalized) shows that a terminal contact at one
    path's starting point can occur almost surely. So "except possibly at their starting point" must mean a starting
    point of either path, not only a common one.

## 3. Theorem 2.6 normalization (priority 2)

- **Finding: confirmed as a documentation item.** The frozen theorem uses the physical conditional mean 𝔥_t(z) of
  Theorem 1.1, with bracket log(crad(ℍ, z)/crad(ℍ ∖ K_t, z)) and no factor κ, on the horizon σ = min(τ_z, T∗). The paper
  prints "√κ times a Brownian motion".
- **Change.** [Errata A3](ERRATA.md) and the [correspondence](CORRESPONDENCE.md) explain the relation:
  - in the proof of Theorem 2.4, the paper's analytic expression (2.12) (p. 43) has imaginary part (π/λ)𝔥_t = √κ𝔥_t;
  - that rescaled function is √κ times a Brownian motion, and 𝔥_t itself is a standard one (pp. 74–75);
  - the statement mixes the two normalizations.

  The frozen statement keeps the correct bracket. No Lean change.
- **Verification.** A hand computation, which agrees with the audit's own computation.

## 4a. Counterflow frame (priority 2)

- **Finding: confirmed as a convention.** The frozen Theorem 1.4 uses the centred counterflow line CF_d(h), the angle-0
  flow line at κ′ of −h∘R + πχ − 2χ arg w in the chart R(z) = −1/z. The paper's literal definition (pp. 19–20) gives
  −h∘R + 2πχ − 2χ arg w with the compatible lift.
- **Change (supplementary).** `IsLiteralCounterflowDriver` is defined, faithful to the paper's definition with the
  branch of the specification's chart (FD12.1, n = 0). The following are proved:
  - **Bridge** (`AuditFix.literalCounterflowBridge_holds`): for the same driver and lifetime, `IsCenteredCounterflowDriver`
    for h is equivalent to `IsLiteralCounterflowDriver` for the shifted field h + πχ. This is a shift of the fixed field
    at every sample point, not an equality in law.
  - **Branches** (`literalCounterflowBranch_holds`): for branch n the shift is (1 − 2n)πχ, so no branch removes the
    half-turn. The paper's suggested branch, n = 1, gives CF_d(h) = CF_lit(h − πχ).
  - **The shifted field** is again a GFF with piecewise-constant data b + πχ (`shiftedField_holds`).
  - **Theorem 1.4 in the literal frame:** its three conclusions (light cone, frontiers, component kernels) for the
    literal counterflow line of h + πχ (`literalCounterflow{LightCone,Frontiers,ComponentKernels}_holds`).

  Files: `Spec/AuditFix/LiteralCounterflow*.lean`.
- **Verification.** The statement audit AUD-AF-T14 (6 PASS, 8 PASS-WITH-NOTES, 0 FAIL), the axioms and kernel replay.
- **Remaining qualification.** The staged-history hypotheses stay in the frame of h. Relabelling angles by θ ↦ θ − π
  is proved for single flow lines only. No case is hidden, because every literal background with piecewise-constant
  data has the form h + πχ.

## 4b. Frontiers (priority 2)

- **Finding: confirmed as a terminology item.** The frozen frontier statement says the walks lie in the counterflow
  range and the range has no point strictly beyond them. It did not identify a topological frontier.
- **Change.**
  - **New anchor** `InteractingSLE.IsCenteredCounterflowDriver.boundaryWalks_outerBoundaries`. In the paper's case,
    when η′ is nowhere boundary filling (p. 22: "the left and right boundaries of η′"):
    - each walk is a single complete flow line;
    - R = frontier(rightSideOf K) ∩ K = closure(frontier(rightSideOf K) ∩ ℍ), and likewise L;
    - R ∪ L is the outer boundary of the range K in both senses.
  - **Supplementary** `AuditFix.frontierBridge_holds`, in general:
    - R and L are simple curves from 0 to ∞;
    - the region strictly right of R is exactly the right complementary region of K, and R ∩ ℍ is its boundary
      relative to ℍ;
    - R is recovered from K alone, together with the real points of K on [0, ∞).
- **Verification.** AUD-AF-T14, both seal keys for the anchor, the axioms and kernel replay.
- **Remaining qualification.**
  - All sets are subsets of ℂ; the point at infinity is left out on both sides.
  - In general (R ∪ L) ∩ ℍ lies in the frontier of K, but the reverse inclusion is not claimed.
  - That the first walk piece is the flow line of h comes from the staged-history hypothesis.

## 5. Markov sentence of Theorem 2.2 (priority 3)

- **Finding: confirmed.** The frozen Theorem 2.2 exported existence and killed-state uniqueness, but not the paper's
  last sentence (p. 40): the values W_t, B_t and V_t "are a continuous multidimensional Markovian process". A restart
  law was proved internally.
- **Change.**
  - **New anchor** `InteractingSLE.exists_strongMarkovKernel_isIntegratedSLEEvolution`. For a > 0 and weights ρ there
    is one time-homogeneous kernel Q on finite-time cylinder events of the state (W, V^L, V^R, B) such that:
    - Q at a state is the killed-state law of every evolution started there;
    - Q is measurable on separated states;
    - the state paths are continuous before ζ;
    - the strong Markov property holds at every finite stopping time, T = 0 and unseparated (entrance) words included.
  - **Supplementary:** the simple Markov property at fixed times, for the evolution's filtration and the natural one,
    and the increment form (`AuditFix.integratedSLEMarkov_holds`, `integratedSLEIncrementStrongMarkov_holds`).
- **Verification.**
  - AUD-AF-T22 (PASS-WITH-NOTES): the auditor derived the Markov identity with an independently defined restart law, so
    Q cannot be chosen to make the statement true.
  - Both seal keys, the axioms and kernel replay.
- **Remaining qualification.**
  - Q is measurable only on separated states; the only unseparated state is the deterministic initial one.
  - Future events are finite-time cylinders, the convention of the frozen uniqueness theorem.
  - Stopping times are finite.
  - There is no Mathlib `Kernel`/semigroup packaging; the integrated Chapman–Kolmogorov identity follows from the
    stated clauses.

## 6. Verification evidence (priority 3)

- **Finding: confirmed at the audited snapshot.**
- **Change.**
  - The 671-page specification is published with its transcription, in [`specification/`](specification/).
  - A [correspondence](CORRESPONDENCE.md) gives the source-to-statement map, and the [errata](ERRATA.md) list the
    paper's errors.
  - The guide separates semantic review, compilation and kernel replay.
- **Verification performed.**
  - all 8,618 modules of the closure compiled afresh from the exported files;
  - an exact kernel replay of each of them;
  - `leanchecker --fresh` of the whole import closure of all frozen modules, Mathlib included;
  - the focused certificate on the fresh build: every reported axiom is one of `propext`, `Classical.choice` and
    `Quot.sound`;
  - for this response, the 26 new modules (18 proof modules, four anchors, four providers) compiled afresh and
    replayed exactly;
  - the seal-closure check now includes Theorems 2.4, 2.6 and the four new anchors among its roots.
- **Pending.** The public workflow runs for this release.
