# Conformal weldings of random surfaces: the quantum zipper

Lean formalization of the **eight named results in Section 1**, with the statement conventions below, from Scott Sheffield, [*Conformal weldings of random surfaces: SLE and the quantum gravity zipper*, arXiv:1012.4797v2](https://arxiv.org/abs/1012.4797v2).

The release covers Theorems 1.1–1.4, Corollary 1.5, Propositions 1.6–1.7 and Theorem 1.8, together with their local proof dependencies. Proposition 1.6 retains an additional boundary-regularity assumption; this release does not claim its literal full domain generality.

## Results and proof entrypoints

Every declaration below is in the `QuantumZipper` namespace. Each proof has exactly the linked statement as its type, without additional unproved literature hypotheses.

| Result | Statement | Proof |
| --- | --- | --- |
| 1.1: forward SLE/GFF coupling, including the `4 < κ < 8` addendum | [`theorem1_1`](../../QuantumZipper/Statements/Thm11.lean) | [`Thm11Asm.theorem1_1_proved`](../../QuantumZipper/Proofs/Thm11/Final.lean) |
| 1.2: reverse SLE/GFF coupling modulo additive constants | [`theorem1_2`](../../QuantumZipper/Statements/Thm12.lean) | [`theorem1_2_holds`](../../QuantumZipper/Proofs/Thm12/Main.lean) |
| 1.3: equality of quantum boundary lengths along the welding | [`theorem1_3`](../../QuantumZipper/Statements/Thm13.lean) | [`theorem1_3_proved`](../../QuantumZipper/Proofs/Zipper/FieldLawler4Final.lean) |
| 1.4: the welding determines the curve | [`theorem1_4`](../../QuantumZipper/Statements/Thm14.lean) | [`theorem1_4_proved`](../../QuantumZipper/Proofs/MainResults13.lean) |
| 1.5: capacity-zipper stationarity and group law | [`theorem1_5`](../../QuantumZipper/Statements/Thm15.lean) | [`theorem1_5_proved`](../../QuantumZipper/Proofs/MainResults13.lean) |
| 1.6: zooming at a boundary-length-typical point gives a quantum wedge | [`theorem1_6`](../../QuantumZipper/Statements/Prop16.lean) | [`theorem1_6_proved`](../../QuantumZipper/Proofs/Section5/Prop1617Proved.lean) |
| 1.7: quantum-length stationarity of a quantum wedge | [`theorem1_7`](../../QuantumZipper/Statements/Prop17.lean) | [`theorem1_7_proved`](../../QuantumZipper/Proofs/Section5/Prop1617Proved.lean) |
| 1.8: independent wedge decomposition, matching lengths and length-zipper stationarity | [`Paper18.theorem1_8PaperMO`](../../QuantumZipper/Statements/Thm18PaperMO.lean) | [`theorem1_8_proved`](../../QuantumZipper/Proofs/MainResults18.lean) |

Three companion results are also included:

- [`theorem1_5_full_proved`](../../QuantumZipper/Proofs/Zipper/Cor15FullMain.lean) proves [`theorem1_5_full`](../../QuantumZipper/Statements/Thm15Full.lean), including existence and uniqueness of the welding driver used by the capacity zipper.
- [`theorem1_6_general_proved`](../../QuantumZipper/Proofs/Section5/Prop16GenMain.lean) proves [`theorem1_6_general`](../../QuantumZipper/Statements/Prop16General.lean), deriving positivity of the expected boundary mass instead of assuming it.
- [`Prop16Lit.theorem1_6_literal_proved`](../../QuantumZipper/Proofs/Section5/Prop16LitDilQ.lean) proves the [conformal-chart companion](../../QuantumZipper/Statements/Prop16Literal.lean) of Proposition 1.6.

## Correspondence with the paper

**Proposition 1.6.** The domain contains a half-disc around every point in the interior of its real boundary segment. This excludes some slit domains admitted by the paper's printed assumptions. All three formal versions retain this condition. The original and conformal-chart versions assume a positive, finite expected boundary mass; the general version proves positivity from the remaining hypotheses. The conformal-chart companion additionally requires a measurable family of conformal charts from the upper half-plane onto the translated domain, so its hypotheses require simply connected domains with those charts.

**Parameters and laws.** The quantum-surface statements use `0 < γ < 2`; the degenerate case `γ = 0` is excluded. Wedges use the range `α < Q`. Fields in the reverse coupling are compared modulo additive constants. Theorem 1.8 compares the two pieces through field data off the interface, and its zipper acts on those pieces. Canonical descriptions use unit quantum area to fix dilation.

**Almost-sure quantifiers.** The zipper group identities are almost sure for each fixed pair of times: `∀ s t, ∀ᵐ ω, …`. The release does not assert one common exceptional set simultaneously for all real times.

The linked statement modules specify the definitions, normalizations and hypotheses. Those statements and proof entrypoints define this release's claims.

## Verification and non-vacuity

See the repository's [verification instructions](../../VERIFICATION.md) and [certificate](../../Certificate.lean). The certificate checks the exact headline types, absence of proof placeholders, and axiom dependencies. The accepted axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

The included supporting certificates construct independent Brownian-motion/GFF and Brownian-motion/wedge setups, certify a genuine nonzero boundary measure and nontrivial welding in Theorem 1.3, and check non-degeneracy of the laws and maps used in Theorem 1.8. The [literal-chart certificate](../../QuantumZipper/Proofs/Section5/Prop16LitCert.lean) supplies explicit charts for the upper half-disc; it concerns those chart hypotheses specifically.

The [verification record](../../VERIFICATION.md) distinguishes current source checks from earlier builds and kernel replays. Kernel checking establishes the Lean proofs; correspondence with the paper is a separate question, and the qualifications above are part of this release's scope.

The pinned Lean and Mathlib versions and all local proof dependencies are included in this public snapshot. No access to the private development repository is required to build it.

[All released formalizations](../../README.md)
