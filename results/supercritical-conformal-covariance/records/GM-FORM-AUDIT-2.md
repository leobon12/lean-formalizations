# Public extract of the second independent statement audit of the Gwynne–Miller-form results

A second auditor, independent of the first and of the provers, audited the 22 public declarations of the final `GMForm` interface (after ruling A21) against Gwynne–Miller arXiv:1905.00384v2, with Lean probes. It pinned the audited files by SHA-256; an independent release review later checked that the landed statements are identical to the audited ones. This was a statement audit, not a seal: the `GMForm` theorems are supporting theorems, not frozen and not sealed. Its verdict line is `GMSA2: PASS`. Source: development audit file, SHA-256 `fb4795cb6245feb0f1c647914985193160670ad9cb18655bd59cdd39d2164494`.

## Source comparison and five-bin binder tables

The tables are a reusable expansion: each row is one binder or one field of a project-owned Prop binder. The declaration matrix following them identifies precisely which rows occur in each theorem. SOURCE refers to the supercritical statement or GM source as indicated; RULED to the numbered adopted ruling; TYPING to carriers and probability-law formation; STANDING is unused; EXCESS is absent. A source mathematical assumption carried by a helper remains an input to that helper, and is proved or constructed at the base-theorem call site.

| ID | Expanded binder | Bin | Basis |
|---|---|---|---|
| A1 | ξ : {x : ℝ // 0 < x} | TYPING | DG parameter; paper 17 |
| A2 | hξ : ξcrit < ξ | SOURCE | paper 17 |
| A3 | Q : ℝ | TYPING | paper 17 |
| A4 | hQ : IsLFPPExponent ξ Q | SOURCE | Q = Q(ξ), paper 17 |
| A5 | D : DistC → LSCMetric | TYPING | DG strong metric, paper 18 |
| A6a | hD: Measurable D | SOURCE | DG Def. 1.7, paper 18, A15 C4 |
| A6b | hD: length-space axiom | SOURCE | DG Def. 1.7, paper 18 |
| A6c | hD: locality axiom | SOURCE | DG Def. 1.7, paper 18 |
| A6d | hD: Weyl axiom | SOURCE | DG Def. 1.7, paper 18 |
| A6e | hD: affine-coordinate axiom | SOURCE | DG Def. 1.7, paper 18 |
| A6f | hD: finite-compact-distance axiom | SOURCE | DG Def. 1.7, paper 18 |
| B1 | U : Opens ℂ | TYPING | paper 22; GM 272, 325 |
| B2 | V : Opens ℂ | TYPING | paper 22; GM Axiom IV |
| B3 | hUc : IsConnected U | SOURCE | “domain”, paper 22; GM 325 |
| B4 | hVc : IsConnected V | SOURCE, redundant | paper 22; follows from B3+B7 |
| B5 | hUg : IsGreenian U | RULED | A14 |
| B6 | hVg : IsGreenian V | RULED, redundant | A14; follows from B5+B7 |
| B7 | φ : ℂ → ℂ | TYPING | only restriction to U is used |
| B8a | hφ: DifferentiableOn ℂ φ U | SOURCE | conformal map, paper 22; GM Axiom IV |
| B8b | hφ: BijOn φ U V | SOURCE | bijection, paper 22; GM Axiom IV |
| C1 | Ω : Type | TYPING | random field carrier |
| C2 | MeasurableSpace Ω | TYPING | random field carrier |
| C3 | P : Measure Ω | TYPING | field law |
| C4 | IsProbabilityMeasure P | TYPING | “almost surely” |
| Z1 | h : Ω → DistOn U | TYPING | GM 264–265 |
| Z2 | z : Ω → DistOn U | TYPING | GM 264–265 |
| Z3 | f : Ω → C(U,ℝ) | TYPING | GM 264–265 |
| Z4 | hh : Measurable h | TYPING | random distribution |
| Z5a | hz: Measurable z | SOURCE | zero-boundary GFF, GM 264 |
| Z5b | hz: Gaussian process of test pairings | SOURCE | zero-boundary GFF, GM 264 |
| Z5c | hz: centered process | SOURCE | zero-boundary GFF, GM 264 |
| Z5d | hz: zero-boundary Green covariance | SOURCE | zero-boundary GFF, GM 264 |
| Z6 | hf : Measurable f | TYPING | random continuous function |
| Z7 | heq : ∀ᵐ ω, h ω = z ω + f ω as distributions | SOURCE | GM 264–265 |
| R1 | h : Ω → DistOn U | TYPING | paper 23, A10.2 |
| R2 | h₀ : Ω → DistC | TYPING | A10.2 |
| R3 | f : Ω → C(U,ℝ) | TYPING | A10.2 |
| R4a | hr: Measurable h | SOURCE | paper 23, A10.2 |
| R4b | hr: h₀ is a whole-plane GFF plus continuous | SOURCE | paper 23, A10.2 |
| R4c | hr: Measurable f | SOURCE | paper 23, A10.2 |
| R4d | hr: ∀ᵐ h = h₀ restricted + f | SOURCE | paper 23, A10.2 |
| K1 | ι : Type | TYPING | indexed family |
| K2 | Countable ι | RULED | A13.1; countable-law limit |
| K3 | Ω : ι → Type | TYPING | family carrier |
| K4 | ∀ i, MeasurableSpace (Ω i) | TYPING | family carrier |
| K5 | P : ∀ i, Measure (Ω i) | TYPING | family law |
| K6 | ∀ i, IsProbabilityMeasure (P i) | TYPING | family law |
| E1 | Ω′ : Type | TYPING | arbitrary extension |
| E2 | MeasurableSpace Ω′ | TYPING | extension |
| E3 | P′ : Measure Ω′ | TYPING | extension |
| E4 | π : Ω′ → Ω | TYPING | extension |
| E5 | MeasurePreserving π P′ P | RULED | A10.2 realization interpretation |
| E6 | a₀ or b₀ : Ω′ → DistC | TYPING | realization |
| E7 | a or b : Ω′ → C(domain,ℝ) | TYPING | realization |
| E8a–d | IsDomainRealization: measurable field; whole-plane GFF plus continuous; measurable correction; a.e. decomposition | RULED | A10.2, A15 C3 |

The E rows occur *inside the conclusion* of Base's universal version clauses; they are not assumptions on the theorem. Product-existence clauses additionally prevent these universal implications from being vacuous.

| Declaration | Complete outer binder-row expansion | Extra inner logical inputs | Bin result |
|---|---|---|---|
| `gm_direction_of_root` | A1–A6f; B1–B8b; C1–C4; R1–R4d | E1–E8d in conclusion; product realization exists | SOURCE/TYPING/RULED only |
| `exists_realization_of_zeroBoundary` | B1,B5; C1–C4; Z1–Z7 | none | SOURCE/TYPING/RULED only |
| `gmCorrection` | A3; B1,B2,B7,B8a,b; f : C(U,ℝ) TYPING | literal body f∘φ⁻¹ + Q log|(φ⁻¹)′| | BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS |
| `measurable_gmCorrection` | A3; B1,B2,B7,B8a,b; C1,C2; f : Ω→C(U,ℝ), hf : Measurable f TYPING | none | SOURCE/TYPING only |
| `gm_class_pullback` | A3; B1,B2,B7,B8a,b; C1–C3; Z1–Z3,Z5a–d,Z6,Z7 | h measurability is intentionally supplied by caller | SOURCE/TYPING only |
| `metric_agrees_on_common_refinement` | A1,A3,A4,A5,A6a–f; B1; Ω,Ω₁,Ω₂,Ωc and four measurable spaces; P₁,P₂,Pc, IsProbabilityMeasure Pc; π₁,π₂,σ₁,σ₂; MeasurePreserving σ₁/σ₂; a.e. base agreement; h,a₀,a,b₀,b; two R4a–d realizations | all coupling data are the lemma's mathematical antecedent, and callers construct them | SOURCE/TYPING only |
| `gm_zeroBoundary_covariance_on_extension` | A1–A6f; B1–B8b; C1–C4; Z1–Z7 | product/extension witnesses in conclusion | SOURCE/TYPING/RULED only |
| `exists_measurable_metric_for_all_realizations_on_space` | A1,A3,A4,A5,A6a–f; B1; C1–C4; R1–R4d | second R2,R3,R4a–d inside “every realization” conclusion | SOURCE/TYPING only |
| `exists_measurable_metric_of_zeroBoundary` | A1,A3,A5,A6a–f; B1,B5; C1–C4; Z1–Z7 | realization witness and version in conclusion | SOURCE/TYPING/RULED only |
| `exists_fieldwise_gm_axiomIV_on_extension` | A1–A6f; B1–B8b; C1–C4; Z1–Z7 | two realization witnesses, two version equalities, all-pairs identity | SOURCE/TYPING/RULED only |
| `exists_countably_universal_domain_metric` | A1,A3,A5,A6a–f; B1; K1–K6; families h,g,f TYPING; ∀i R4a–d SOURCE | version for each i | SOURCE/TYPING/RULED only |
| `exists_countably_universal_metric_of_zeroBoundary` | A1,A3,A5,A6a–f; B1,B5; K1–K6; ∀i Z1–Z7 | realization and version for each i | SOURCE/TYPING/RULED only |
| `exists_countably_universal_gm_axiomIV_on_extensions` | A1–A6f; B1–B8b; K1–K6; ∀i Z1–Z7 | common maps before i; extensions after i | SOURCE/TYPING/RULED only |
| `ae_of_ae_fst` | Ω,X, measurable spaces, StandardBorelSpace X, Nonempty X, P, μ, IsFiniteMeasure μ, MeasurePreserving fst μ P, q:Ω→Prop, ∀ᵐp q(p.1) | pure measure-theory helper; all inputs are typing or its explicit antecedent | SOURCE/TYPING only |
| `isZeroBoundaryGFF_comp` | B1; Ω,Ω′, measurable spaces, P,P′,π, MeasurePreserving π P′ P; z, its Z5a–d certificate | pure pullback-of-law helper | SOURCE/TYPING only |
| `exists_prod_realization_of_zeroBoundary` | B1,B5; C1–C4; Z1–Z7 | product realization in conclusion | SOURCE/TYPING/RULED only |
| `product_common_refinement` | Ω,Ω′,X, measurable spaces, StandardBorelSpace X, Nonempty X; P, IsProbabilityMeasure P; P₁, IsProbabilityMeasure P₁, MeasurePreserving fst P₁ P; P′, IsProbabilityMeasure P′; π, MeasurePreserving π P′ P | common product measure in conclusion; no empty extension possible | SOURCE/TYPING only |
| `version_on_all_extensions` | A1,A3,A4,A5,A6a–f; B1; C1–C4; h; P₁, IsProbabilityMeasure P₁, MeasurePreserving fst P₁ P; a₀,a, R4a–d; Φ; its a.e. version equality | E1–E8d in conclusion | SOURCE/TYPING/RULED only |
| `base_data` | A1–A6f; B1–B8b; C1–C4; Z1–Z7 | two product realizations and root equality in conclusion | SOURCE/TYPING/RULED only |
| `target_hyps` | B1–B3,B5,B7,B8a,b | conclusion is connected and Greenian V | SOURCE/TYPING/RULED only |
| `gm_axiomIV_on_base` | A1–A6f; B1–B3,B5,B7,B8a,b; C1–C4; Z1–Z7 | two E1–E8d clauses, two product existences, base a.s. all-pairs identity | SOURCE/TYPING/RULED only |
| `exists_countably_universal_gm_axiomIV_on_base` | A1–A6f; B1–B3,B5; K1–K6; φ:ι→(ℂ→ℂ) TYPING; ∀i B8a,b SOURCE; ∀i Z1–Z7 | for each i two E1–E8d clauses, two product existences, base a.s. all-pairs identity | SOURCE/TYPING/RULED only |

Expanded assumptions contain no EXCESS gate. In particular `hD` is DG's six-part *definition* of a strong LQG metric, rather than a bundle of the desired conformal covariance; `hr` is a field realization, not a proof of coordinate change. `IsGreenian` is the actual finite Green-energy condition, not an existential placeholder. `IsConformalBijection` is holomorphic-on-U plus bijective U→V. `domainMetric` is `weylScaleOn ξ f (D h₀)`, an infimum of exp-weighted lengths of curves in the domain; no fallback branch occurs. `gmCorrection` has the exact inverse derivative. None uses an unproved placeholder.

## Vacuity decision for every existential conclusion

| Declaration(s) | Trivial-witness decision |
|---|---|
| `gm_direction_of_root`; `exists_realization_of_zeroBoundary`; `gm_zeroBoundary_covariance_on_extension` | An empty extension cannot preserve a probability measure. The witness includes a genuine `IsDomainRealization` (a whole-plane GFF plus continuous), and the coordinate conclusion compares its metric. |
| `exists_measurable_metric_for_all_realizations_on_space` | Φ=0 fails for any realized field on a domain containing distinct points: `version_forces_nonzero` below. An arbitrary map must agree with the actual domain metric a.s. |
| `exists_measurable_metric_of_zeroBoundary`; `exists_countably_universal_metric_of_zeroBoundary` | The required realization and a.e. version equality rule out Φ=0 in the disk/Unit instance. The existential realization cannot be empty. |
| `exists_fieldwise_gm_axiomIV_on_extension`; `exists_countably_universal_gm_axiomIV_on_extensions` | Both maps are tied to the two realized metrics on a common extension. Zero fails on a nondegenerate disk, even though the all-pairs identity is only on that extension. |
| `exists_countably_universal_domain_metric` | For ι=Empty, the theorem correctly has no field to serve and its proof takes Φ=0. For ι=Unit with the disk GFF, the version equality forbids zero. This is an empty-family edge case, not a false assertion about a field. |
| `exists_prod_realization_of_zeroBoundary`; `product_common_refinement`; `base_data` | Every witness measure projects to a probability law and is itself probability; its realization or common-refinement equation is substantive. Empty or zero measures cannot witness them. |
| `gm_axiomIV_on_base`; `exists_countably_universal_gm_axiomIV_on_base` | Each side has a product realization, and each map equals the corresponding domain metric for **every** measure-preserving extension and realization. The conclusion then asserts the all-pairs identity `∀ᵐ ω ∂P` on the original field space. The generic nonzero probe refutes both zero maps on the disk. For the countable theorem, ι=Empty is vacuous, but ι=Unit is certified nonvacuous by the same probe. |
| `gmCorrection`; `measurable_gmCorrection`; `gm_class_pullback`; `metric_agrees_on_common_refinement`; `ae_of_ae_fst`; `isZeroBoundaryGFF_comp`; `version_on_all_extensions`; `target_hyps` | No existential conclusion requiring a separate witness. Their premises are concrete maps, laws, field classes, or realizations, and are satisfied by the disk construction or, for the measure-theory helpers, by identity/product couplings. |

Transporting Φ_U to Φ_V by φ cannot bypass the V-version clause. With that choice, the clause itself becomes the nontrivial equality between the transported U metric and the realized V metric. Likewise, choosing a “probability extension” with no realization cannot satisfy either product-existence conjunct. The old A21 counterexample Φ_U=Φ_V=0 is eliminated by the exact final statement.

**Satisfiable premises.** On the unit disk, take ξ=ξcrit+1, the proved Q(ξ) and strong metric D; the disk is connected, bounded and Greenian, φ=id is a conformal bijection, and Markov decomposition of an existing whole-plane GFF supplies a genuine zero-boundary GFF z. Set h=z and f=0. The equation h=z+f holds by `Function.extend` of zero and `Distribution.ofFun_zero`. For countable forms take ι=Unit and this same field and identity map. The resulting product realizations are real probability spaces. Thus the hypotheses do not hide an inconsistency.

**Nonzero argument.** For distinct x,y in the disk, the DG metric sample is an extended metric a.s.; `SupercriticalConformalCovariance.Domain.eq_of_weylScaleOn_eq_zero` implies a domain metric value zero forces x=y. A version equality Φ(h)=domainMetric therefore implies Φ(h)(x,y)≠0 a.s. Since P is a probability measure, the all-zero Φ would imply both zero and nonzero on a nonempty conull set, contradiction. The probe tests the single-field and Unit-indexed Base conclusions separately. It also covers the V side by applying the generic statement to its product realization on V.

## Difference from Gwynne–Miller

| Issue | Exact audited form | Source relation |
|---|---|---|
| Direction | h on U; h^φ=h∘φ⁻¹+Q log|(φ⁻¹)′| on V; compare D_h(u,v) with D_h^φ(φu,φv) | GM Axiom IV direction; inverse of supercritical paper Theorem 1.1 |
| Law scope | One Φ_U and Φ_V after a chosen law, or after a specified countable family of laws and maps φ_i with fixed U,V | Weaker than GM Definition 1.1 footnote's one map per domain for every law; A13.1/A21 leave this open |
| Map scope | Countable Base theorem chooses maps before `∀i`, including varying φ_i | Stronger than the older extension countable theorem, where φ was fixed before choosing maps; still does not give all maps at once |
| Domains | Connected Greenian U; V connected and Greenian derived from φ | “Domain” gives connectedness; Greenian is A14 restriction. Disconnected open sets and the whole plane are outside these theorems; affine whole-plane result is separate |
| Metric carrier | D: distributions→lsc extended metrics; domainMetric: U×U→[0,∞]; Φ values are arbitrary functions off the tested field laws | Supercritical replacement for GM continuous metrics; +∞ and singular points retained. The maps are metric-valued a.s. on the specified laws, not asserted to land in an LSCMetric subtype on every distribution |
| Original space | Base pair satisfies `∀ᵐ ω ∂P, ∀u v`; extension versions quantify over **all** measure-preserving extensions and realized metrics; actual product realizations are also exhibited | Base conclusion matches the a.s. location of GM Axiom IV for the supplied field. Extension theorems are strictly weaker as stand-alone claims |
| Field class | A specified z and measurable f on Ω with h=z+f a.s.; f may depend on z | GM permits “can be coupled” and does not require the displayed decomposition on the original Ω. The proved form covers any supplied coupling on its own space. An arbitrary original-space coupling transfer is not separately claimed |
| Axioms I–III | Not in these GMForm conclusions | Domain-metric analogues are separate `Domain.Axioms` theorems; do not call this module alone a proof of all GM Definition 1.1 |
| Normalization/event | Exact factor 1; all u,v simultaneously; event may depend on fixed φ | Matches Axiom IV and paper 28–31 |

## Verdict by public declaration

| Declaration | Verdict | Reason |
|---|---|---|
| `gm_direction_of_root` | WEAKER-AS-DISCLOSED | realization formulation of forward Axiom IV; derives from sealed root |
| `exists_realization_of_zeroBoundary` | FAITHFUL | genuine whole-plane realization of the zero-boundary class |
| `gmCorrection` | FAITHFUL | literal inverse-coordinate continuous correction |
| `measurable_gmCorrection` | FAITHFUL | measurability of that literal correction |
| `gm_class_pullback` | FAITHFUL | transformed zero-boundary field and correction, conditional on supplied class data |
| `metric_agrees_on_common_refinement` | FAITHFUL | independence on a supplied common coupling |
| `gm_zeroBoundary_covariance_on_extension` | WEAKER-AS-DISCLOSED | equality on an extension |
| `exists_measurable_metric_for_all_realizations_on_space` | WEAKER-AS-DISCLOSED | one law and one space, all realizations there |
| `exists_measurable_metric_of_zeroBoundary` | WEAKER-AS-DISCLOSED | one law, chosen realization extension |
| `exists_fieldwise_gm_axiomIV_on_extension` | WEAKER-AS-DISCLOSED | maps are per law, equality on extension |
| `exists_countably_universal_domain_metric` | WEAKER-AS-DISCLOSED | countably many realized laws |
| `exists_countably_universal_metric_of_zeroBoundary` | WEAKER-AS-DISCLOSED | countably many zero-boundary laws |
| `exists_countably_universal_gm_axiomIV_on_extensions` | WEAKER-AS-DISCLOSED | fixed φ, countable laws, equality on extension |
| `ae_of_ae_fst` | FAITHFUL | product-space a.e. descent, even for nonmeasurable predicate |
| `isZeroBoundaryGFF_comp` | FAITHFUL | law-preserving pullback of GFF process |
| `exists_prod_realization_of_zeroBoundary` | FAITHFUL | product realization with real probability projection |
| `product_common_refinement` | FAITHFUL | conditional-kernel common refinement |
| `version_on_all_extensions` | FAITHFUL | fixed product version transfers to every realization extension |
| `base_data` | FAITHFUL | two product realizations and root identity |
| `target_hyps` | FAITHFUL | connectedness and Greenianity transport |
| `gm_axiomIV_on_base` | WEAKER-AS-DISCLOSED | actual base-space Axiom IV for one represented law, with both universal version clauses; laws not universal |
| `exists_countably_universal_gm_axiomIV_on_base` | WEAKER-AS-DISCLOSED | actual base-space Axiom IV for specified countable fields/maps; fixed U,V, not all laws |
| `Audit.lean` | N/A | import-only file; no declaration |

**Release-guide paragraph.** For the supercritical LQG metric with ξ>ξcrit and Q=Q(ξ), on connected Greenian domains U and V related by a deterministic conformal bijection φ, a zero-boundary GFF on U plus a measurable random continuous function has a domain metric obtained from a whole-plane realization. For any specified such field, there are measurable functions of the field on U and V that agree with the metric on every realization extension and satisfy Gwynne–Miller's Axiom IV on the field's original probability space, almost surely for all endpoint pairs at once, with exact constant one and infinite distances allowed. One pair of functions works for any specified countable family of fields and conformal maps between the same domains. The construction does not yet give one function per proper domain valid for every field law, and it assumes the field decomposition is supplied on the probability space under discussion.
