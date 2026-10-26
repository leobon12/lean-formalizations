# Public extract of the first independent statement audit of the Gwynne–Miller-form results

An auditor who was not a prover, lander or reviewer of any audited declaration compared the frozen root and the public `GMForm` statements of that time with Gwynne–Miller arXiv:1905.00384v2 (Definition 1.1 with its footnote, Axioms I–IV, the domain-field paragraph and Theorem 1.3), under the `lean-statement-audit` procedure. It was made at development commit `ce98d4325`, when the frozen root still had its registered draft body, and before ruling A21; the statements it audited were then corrected, and the second audit ([GM-FORM-AUDIT-2.md](GM-FORM-AUDIT-2.md)) covers the final ones. Its verdict line is `GMSA: FINDINGS 6`. Source: development audit file, SHA-256 `3307c0af5925b5fd8e54b845d9344fafb9210e3b845f07785346dee05589e7d3`.

Ruling A21 settled the six findings as follows (the corrected statements are the ones released):

| Finding | Ruling A21 |
| --- | --- |
| F1: the Axiom IV identity held only on an extension of the probability space | accepted in substance; the auditor's replacement statements were **rejected** (three of them tie neither map to the metric, so zero maps satisfy them, and a fourth ties only Φ_U); the released base-space forms `gm_axiomIV_on_base` and `exists_countably_universal_gm_axiomIV_on_base` add version clauses for **both** maps, the existence of realizations on a product extension, and Axiom IV almost surely on the field's own space, moved down from the extension by disintegration |
| F2: in the countable form the maps were chosen after the conformal map | accepted: the maps are now chosen once, before a countable family of conformal maps φ_i |
| F3: the guide called U = ℂ uncovered | accepted (guide wording): `Rotation.ae_complex_affine_covariance` gives Gwynne–Miller's Axiom IV′ for complex-affine maps of ℂ, with D itself as the one map for every law |
| F4: the hypotheses on V are redundant | accepted: V = φ(U) is connected and Greenian when U is; the base-space forms assume them on U only, while the frozen root keeps the paper's hypotheses |
| F5: two unused binders of `metric_agrees_on_common_refinement` | accepted; the landed declaration keeps its signature |
| F6: the GM-form layer restates Axiom IV and measurability only | accepted (disclosure): the domain forms of Axioms I–III are in `Domain.Axioms` |

## Verdict summary

| Target | Statement fidelity (against its source) | EXCESS | Vacuity | Axioms |
|---|---|---|---|---|
| Root `SupercriticalConformalCovariance.conformal_covariance` (DRAFT_SORRY) | PASS against paper Thm 1.1, under A10.2, A14 and A15 | 0 | non-vacuous (probe 3a and the existence conjunct) | DRAFT: `sorryAx` from the body only. The provider `Implementation.conformal_covariance_impl` has the `rfl`-equal type and uses only standard axioms |
| `gm_direction_of_root` | PASS: equivalent to the root by φ ↔ φ⁻¹; GM Axiom IV for the realization class | 0 | non-vacuous | standard axioms through the provider |
| `gm_zeroBoundary_covariance_on_extension`, `exists_fieldwise_gm_axiomIV_on_extension`, `exists_countably_universal_gm_axiomIV_on_extensions` | PASS for what they state. **Weaker than GM Axiom IV:** the a.s. event lives on an extension (F1), and the maps are chosen after φ (F2) | 0 | non-vacuous (probe 3a fires them) | standard axioms through the provider |
| `exists_measurable_metric_for_all_realizations_on_space`, `exists_measurable_metric_of_zeroBoundary`, `exists_countably_universal_domain_metric`, `exists_countably_universal_metric_of_zeroBoundary` | PASS as per-law and countable-law forms of GM Def. 1.1's "measurable function of the field" (A13.1) | 0 | non-vacuous | standard axioms |
| `exists_realization_of_zeroBoundary`, `gm_class_pullback`, `measurable_gmCorrection`, `metric_agrees_on_common_refinement` | PASS (interface lemmas). `metric_agrees_…` has two unused binders (F5) | 0 | non-vacuous | standard axioms |
| def `gmCorrection` | BODY_MATCH OK (f∘φ⁻¹ + Q log\|(φ⁻¹)′\|); PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A (`invFunOn` is determined on V by injectivity); DEFINITION_VERDICT PASS | — | — | — |

No finding is an EXCESS premise or an unfaithful conclusion. Each of the six is one of three things: the GM-form layer states less than is provable, a binder is redundant or unused, or the release guide describes the result inaccurately. Each has an exact fix, and the fixes for F1, F2 and F4 were proved in the audit's own Lean probe (probe 3).

## Findings

**F1 (medium): the GM-form Axiom IV theorems still carry an extension clause, which A13 asked to remove, and the base-space form is provable.**
- *Where:* `gm_zeroBoundary_covariance_on_extension`, `exists_fieldwise_gm_axiomIV_on_extension` and `exists_countably_universal_gm_axiomIV_on_extensions` (`SCC/GMForm/{ZeroBoundaryCovariance,Functional,Countable}.lean`).
- *What they say:* the identity Φ_U(h)(u,v) = Φ_V(h^φ)(φu,φv) for all u, v holds only `∀ᵐ ω ∂P₂` on an existentially chosen measure-preserving extension `π₁ ∘ π₂ : Ω₂ → Ω`.
- *What GM says:* GM Axiom IV (l. 288–290) and Thm 1.3 (l. 328–331) assert it almost surely for the field h itself. Ruling A13 asks for "GM's Axiom IV with no extension clause".
- *Why the two differ:* the event "∀ u v, …" is an uncountable intersection, and it need not be measurable in the cylinder or product σ-algebras. An a.s. statement on an extension does not imply one on the base for such events.
  - Counterexample to the general implication: let Ω = [0,1] with Borel sets and Lebesgue P, and let A be a Bernstein set (inner measure 0, outer measure 1).
  - Take Ω₂ = A with the trace measure P₂(A ∩ B) := P(B), π the inclusion, and q := 1_A.
  - Then π is measure-preserving and q ∘ π ≡ true, but {¬q} = Aᶜ has outer measure 1.
- *Fix (proved in probe 3; standard axioms with the provider, `sorryAx` only through the DRAFT root):* add the base-space theorems `gm_axiomIV_on_base` and `exists_countably_universal_gm_axiomIV_on_base`, with the exact statements in "Details" below. Their supporting lemmas are:
  - `ae_of_ae_fst`: lifting along Ω × X, X standard Borel;
  - `isZeroBoundaryGFF_comp`;
  - `exists_prod_realization_of_zeroBoundary`: the live proof of `exists_realization_of_zeroBoundary` with the extension exposed as `Ω × DistC`, π = `Prod.fst`;
  - `base_data`.
- *Fix to the guide:* change item 3 of the guide's "(a) Countable-law form" from "on which … almost surely" to "almost surely on the probability space of h_i". The extension then remains only in items 1–2, which describe what Φ_U(h_i) and Φ_V(h_i^φ) are.

**F2 (low): in the countable form, Φ_U and Φ_V are chosen after φ.**
- *The issue:* in `exists_countably_universal_gm_axiomIV_on_extensions` the quantifier order is `∀ φ hφ, ∀ family, ∃ Φ_U Φ_V`. In GM Def. 1.1 the map h ↦ D_h on each open set is fixed before any conformal map. The guide says "The maps may depend on the family" but does not say they may depend on φ.
- *Fix:* index the maps with the family, `(φ : ι → ℂ → ℂ) (hφ : ∀ i, IsConformalBijection (φ i) U V)`. One Φ_U and one Φ_V then serve countably many (field, map) pairs.
- *Status:* proved in probe 3 as `exists_countably_universal_gm_axiomIV_on_base_maps`, which also drops hVc and hVg (see F4).
- *Fix to the guide:* "The maps may depend on the (countable) family of fields and maps."

**F3 (low): the guide's claim that U = ℂ is "not covered here" is inaccurate.**
- *The guide's text:* "On ℂ itself, Gwynne–Miller use the whole-plane GFF instead, and that case is not covered here."
- *What exists:* the landed theorem `SupercriticalConformalCovariance.Rotation.ae_complex_affine_covariance` (`Rotation/Affine.lean:16`). It states, for every strong D, every whole-plane GFF plus continuous function h and every a ≠ 0 and b, that a.s. for all u, v, D_h(au+b, av+b) = D_{h(a·+b)+Q log|a|}(u, v). That is GM Axiom IV′ (l. 304–306) with complex a, and so GM Thm 1.3 for U = ℂ.
  - The field there is written `addConst (rotDist (a/|a|) (affineComp |a| b h)) (Q log|a|)`.
  - I checked `rotDist β k = k(β·)` (`testRot_apply`: ⟨rotDist β k, ψ⟩ = ⟨k, ψ(β⁻¹·)⟩) and `affineComp r b h = h(r·+b)` (`affineComp` = r⁻²·h∘affMap). Together these give h(a·+b).
- *Two further points:*
  - In the whole-plane case, GM's literal "one measurable map for every law" holds trivially: D itself is a measurable map (`IsStrongLQGMetric`, first conjunct).
  - The classical fact that every conformal bijection from ℂ onto a domain is affine (an injective entire function is a degree-1 polynomial) is not formalized: no hit in `quantum_zipper`, `small_gamma_geodesics`, `lqg_metric` or this project.
- *Fix to the guide:* replace the sentence with: "On ℂ itself, Gwynne–Miller's field class is the whole-plane GFF plus a continuous function, and the conformal maps of ℂ onto a domain are the complex-affine maps. That case is GM Axiom IV′. It is proved for every strong metric, including rotations, as `Rotation.ae_complex_affine_covariance`, and there the literal 'one map for every law' holds with the map D itself. That every conformal map of ℂ onto a domain is affine is classical and is not formalized here." Optional: add a GMForm corollary that restates `ae_complex_affine_covariance` under a GM name.

**F4 (low): the target-domain hypotheses hVc and hVg are redundant in every GM-form theorem.**
- *Why:* V = φ(U) is connected because U is, and Greenian because U is.
- *Proof (probe 3, `target_hyps`):* connectedness is `hφ.2.image_eq ▸ hUc.image φ hφ.1.continuousOn`; Greenian is `GPull.isGreenian_of_conf (Reversal.inverse_conformal hφ) hUg`.
- *Comparison with GM:* GM Thm 1.3 assumes the hypotheses only on U. The extra binders lose no generality, but they make the statement look stronger than GM's.
- *Fix:* drop `hVc` and `hVg` from `gm_direction_of_root`, `gm_zeroBoundary_covariance_on_extension`, `exists_fieldwise_gm_axiomIV_on_extension` and `exists_countably_universal_gm_axiomIV_on_extensions` (and their base-space successors), and derive them with `target_hyps`. Proved shape: `gm_axiomIV_on_base_sourceOnly`. The frozen root keeps both under A15 C4; there they are redundant too, but ruled.

**F5 (low): `metric_agrees_on_common_refinement` has unused binders `hπ₁` and `hπ₂`.**
- *Evidence:* the linter warns at `Independence.lean:30–31`, and the build log of the corollary proofs shows the same warnings.
- *Fix:* delete both binders, which strengthens the theorem; the proof is unchanged. The landed copy (`SupercriticalConformalCovariance.GMForm.metric_agrees_on_common_refinement`) is identical, so the fix belongs in a later landing.

**F6 (low, disclosure): only Axiom IV and measurability are restated; Φ's codomain is raw functions.**
- *What GM claims:* Thm 1.3's second sentence says the map h ↦ D_h "is a γ-LQG metric in the sense of Definition 1.1": continuous-metric values and Axioms I–IV on every open set.
- *What the GM-form layer has:*
  - The maps have type `DistOn U → (U × U → ℝ≥0∞)` and are measurable for the product σ-algebra.
  - No GM-form theorem says that Φ_U(h) is a.s. an extended length metric, or that it satisfies domain locality or Weyl scaling.
  - Those facts are proved for the domain metric in `SupercriticalConformalCovariance.Domain.Axioms`: `ae_domainMetric_isLength`, `ae_domainMetric_add`, `ae_domainMetric_restrict`, `ae_domainMetric_eq_of_restrictOn_eq` and `exists_measurable_domainMetric`. They transfer to Φ_U through the a.s. identity, but this is not stated.
- *Fix (guide):* add to "Scope differences": "Only GM's Axiom IV and the measurability of the field-to-metric map are restated in Gwynne–Miller form. The domain versions of Axioms I–III are proved for the domain metric in `Domain.Axioms`, not repackaged for Φ_U. Φ_U takes values in all functions U × U → [0, ∞], and is a.s. the (lower-semicontinuous-in-the-confined-sense, possibly infinite) domain metric."
- *Optional:* a corollary `ae_isLength_PhiU`.

## Five-bin binder tables

Citations: P = paper text; GM = 1905.00384v2 TeX lines; DG = 2110.00177v3. For the GM-form theorems the comparison is with GM Thm 1.3 and Axiom IV, and, for the functional theorems, with Def. 1.1 and its footnote and l. 316–321. The parameter block (ξ, Q, D) replaces GM's γ-LQG metric by the paper's supercritical setting (A13: "the proof of §2–§7 is shared; only the interface is new").

**Block A, parameters (6 binders).**

| Binder | Bin | Citation |
|---|---|---|
| `ξ : Set.Ioi 0` | TYPING | DG ξ > 0 |
| `hξ : xiCrit < ξ` | SOURCE | P l. 17 |
| `Q : ℝ` | TYPING | |
| `hQ : IsLFPPExponent ξ Q` | SOURCE | P l. 17, "Q = Q(ξ)" |
| `D : DistC → LSCMetric` | TYPING | P l. 18, "metrics allowed +∞" |
| `hD : IsStrongLQGMetric ξ Q D` (6 conjuncts) | SOURCE | P l. 18 and DG Def. 1.7 / Thm 1.8 ("one normalization" = every strong metric, A15 C4) |

**Block B, domains and map (8 binders).**

| Binder | Bin | Citation |
|---|---|---|
| `U V : Opens ℂ` | TYPING (2) | P l. 22; GM l. 326 |
| `hUc : IsConnected U` | SOURCE | "domain", P l. 22 and GM l. 326 |
| `hVc : IsConnected V` | SOURCE (P); for GM, implied by hUc and hφ (F4) | P l. 22, A15 C4 |
| `hUg : IsGreenian U` | RULED | A14 |
| `hVg : IsGreenian V` | RULED (A14); implied by hUg and hφ (F4) | A14 |
| `φ : ℂ → ℂ` | TYPING | values off U irrelevant |
| `hφ : IsConformalBijection φ U V` (2 conjuncts) | SOURCE | P l. 22; GM l. 288, 326 (printed "φ : ℂ → U" read as U → Ũ; SGG ER1 / guide) |

**Block C, probability space (4).** `Ω`, `[MeasurableSpace Ω]`, `P`, `[IsProbabilityMeasure P]`: TYPING (4).

**Block R, the paper's realization class (4).**

| Binder | Bin |
|---|---|
| `h` | TYPING |
| `h₀` | TYPING |
| `f` | TYPING |
| `hr : IsDomainRealization …` (4 conjuncts) | SOURCE (P l. 23: "GFF plus continuous in the local sense"), encoded per RULED A10.2 / A15 C3 |

**Block Z, GM's zero-boundary class (7).**

| Binder | Bin | Citation |
|---|---|---|
| `h z : Ω → DistOn U`, `f` | TYPING (3) | |
| `hh : Measurable h` | TYPING | "random distribution" |
| `hz : IsZeroBoundaryGFF U z P` | SOURCE | GM l. 264 |
| `hf : Measurable f` | TYPING | "random continuous function" |
| `heq : ∀ᵐ, h = z + f` | SOURCE | GM l. 264. The coupling is on Ω; this is equivalent, see the difference table |

**Block K, countable family (6).**

| Binder | Bin |
|---|---|
| `ι` | TYPING |
| `[Countable ι]` | RULED (A13.1: the countable-law form) |
| `Ω : ι → Type` | TYPING |
| `[∀ i, MeasurableSpace]` | TYPING |
| `P` | TYPING |
| `[∀ i, IsProbabilityMeasure]` | TYPING |

**Block E, the inner antecedents of a universal "for every extension and realization" clause (8).**

| Binder | Bin |
|---|---|
| `Ω'` | TYPING |
| `[MeasurableSpace Ω']` | TYPING |
| `P'` | TYPING |
| `π` | TYPING |
| `MeasurePreserving π P' P` | RULED (A10.2: realizations exist only after coupling) |
| `g₀` | TYPING |
| `k` | TYPING |
| `IsDomainRealization … g₀ k` | RULED (A10.2: the meaning of the other side's domain metric) |

**Counts per declaration** (outer binders; EXCESS = 0 everywhere):

| Declaration | Blocks | SOURCE | STANDING | TYPING | RULED | EXCESS | Total |
|---|---|---|---|---|---|---|---|
| root `conformal_covariance` | A+B+C+R (+E inner) | 7 | 0 | 13 (+6) | 2 (+2) | 0 | 22 (+8) |
| `gm_direction_of_root` | A+B+C+R (field on U) (+E) | 7 | 0 | 13 (+6) | 2 (+2) | 0 | 22 (+8) |
| `gm_zeroBoundary_covariance_on_extension` | A+B+C+Z | 8 | 0 | 15 | 2 | 0 | 25 |
| `exists_fieldwise_gm_axiomIV_on_extension` | A+B+C+Z | 8 | 0 | 15 | 2 | 0 | 25 |
| `exists_countably_universal_gm_axiomIV_on_extensions` | A+B+K+Z (families) | 8 | 0 | 16 | 3 | 0 | 27 |
| `exists_measurable_metric_for_all_realizations_on_space` | ξ,Q,hQ,D,hD,U + C + R(h,a₀,a,ha); inner ∀ b₀ b, IsDomainRealization (TYPING 2, RULED 1) | 3 | 0 | 11 | 0 | 0 | 14 |
| `exists_measurable_metric_of_zeroBoundary` | ξ,Q,D,hD,U,hUg + C + Z | 3 | 0 | 13 | 1 | 0 | 17 |
| `exists_countably_universal_domain_metric` | ξ,Q,D,hD,U + K + (h,g,f,hr) | 2 | 0 | 12 | 1 | 0 | 15 |
| `exists_countably_universal_metric_of_zeroBoundary` | ξ,Q,D,hD,U,hUg + K + Z | 3 | 0 | 14 | 2 | 0 | 19 |
| `exists_realization_of_zeroBoundary` | C + U,hU + Z | 2 | 0 | 10 | 1 | 0 | 13 |
| `gm_class_pullback` | Q,φ,U,V,hφ + Ω,mΩ,P + Z minus hh | 3 | 0 | 11 | 0 | 0 | 14 |
| `measurable_gmCorrection` | Q,φ,U,V,hφ,Ω,mΩ,f,hf | 1 | 0 | 8 | 0 | 0 | 9 |
| `metric_agrees_on_common_refinement` | ξ,Q,hQ,D,hD,U; 4 types + 4 σ-algebras; P,[prob],P₁,P₂,Pc,[prob]; π₁,π₂,σ₁,σ₂; hπ₁,hπ₂ (**unused**, F5), hσ₁,hσ₂,hbase; h,a₀,a,b₀,b; ha,hb | 4 (hQ,hD,ha,hb; GMU Rem. 1.5) | 0 | 32 (incl. 2 unused) | 0 | 0 | 36 |

Notes on the table:
- ξ > ξ_crit is not assumed by the four locality theorems, and hQ not by two of them. Those theorems hold for every strong metric, which strengthens them.
- Conclusion-side existentials are not binders. Their content:
  - the root's first conjunct (RULED A15 C2: existence of a realization of the pulled-back field);
  - "∃ extension, realization" in the GM-form theorems (RULED A10.2 / A13.2);
  - "∃ Φ_U Φ_V measurable" (GM Def. 1.1);
  - the a.s. identity, the conclusion of Axiom IV.
- Implicitness and order: every source premise is an explicit binder, and constants appear in the source order (ξ, Q, D, then domains, then the field). The existential maps follow ∀ φ (F2).
- Normalization: the Q log|(φ⁻¹)′| term matches GM (1.9) exactly. The multiplicative constant is exactly one; there is no hidden C.

**Base-space successors (probe 3)**, same bins:

| Declaration | Bins |
|---|---|
| `gm_axiomIV_on_base` | as `exists_fieldwise_…`: SOURCE 8, TYPING 15, RULED 2, EXCESS 0 |
| `gm_axiomIV_on_base_sourceOnly` | SOURCE 7, TYPING 15, RULED 1, EXCESS 0 (no hVc/hVg) |
| `exists_countably_universal_gm_axiomIV_on_base` | as the countable form, 27 |
| `exists_countably_universal_gm_axiomIV_on_base_maps` | ι-indexed φ, no hVc/hVg: SOURCE 7 (hφ is ι-indexed), TYPING 17 (φ is a family), RULED 2 (hUg, [Countable ι]), EXCESS 0 |

## Difference table (Lean form versus GM Thm 1.3 / Axiom IV / Def. 1.1)

| Difference | Classification | Why |
|---|---|---|
| Paper's inverse convention: D_h(φu,φv;V) = D_{h∘φ+Q log\|φ′\|}(u,v;U), with h on V | **Equivalent reformulation** | GM's form is the paper's applied to φ⁻¹ : V → U (`Reversal.inverse_conformal`), since φ⁻¹(φz) = z. This is exactly the proof of `gm_direction_of_root` (probe 2), and the converse is symmetric. GM's h^φ = h∘φ⁻¹ + Q log\|(φ⁻¹)′\| is literally `confPullbackField Q (inverse_conformal hφ) h` |
| Extension and realization quantifiers instead of "D_h as a measurable function of h" | **Equivalent for the meaning of D_h; weaker for the Φ-identity as currently stated (F1)** | GM defines D_{h̊^U+f} through h|_U = h̊^U + 𝔥^U (l. 316–321), i.e. through a whole-plane realization; GM l. 821–822 use couplings too. The paper's class and GM's agree after extension: GM-class ⊆ realization class (`exists_realization_of_zeroBoundary`, Greenian), and the converse holds by Markov. Realization independence (sealed) makes D_h a.s. a function of h. The per-law Borel map is `exists_measurable_domainMetric`. The current Φ theorems state the Axiom IV identity only on an extension; the base-space form is proved in probe 3 |
| Countable families of laws instead of GM's one map for all laws (Def. 1.1 and footnote) | **Weakening (A13.1)** | The coin mixture handles countably many laws. GM's own footnote concedes D_h is constructed only a.s. per law. The literal form is OPEN (below). The countable form with maps chosen before φ is proved (probe 3, F2) |
| Connected Greenian domains (A14) instead of "open domain" | **Thm 1.3:** "domain" = connected, so connectedness is equivalent and Greenian is a restriction that GM's zero-boundary class presupposes on proper domains (on ℂ ∖ {closed polar} no ZB GFF exists, so GM's class is undefined). **Def. 1.1 ("each open set"):** a weakening (disconnected open sets are excluded; disclosed in the guide) | ℂ itself: see the U = ℂ row. hVc and hVg are redundant (F4) |
| lsc, possibly infinite metrics instead of continuous metrics | **Forced by the supercritical setting** (not comparable) | Supercritical metrics have singular points and are not continuous (DG). D_h ∈ `LSCMetric`, and the domain metric has values in [0,∞] (paper l. 18–20). Φ maps into all functions U×U → [0,∞] (F6) |
| GFF class: whole-plane realization h = h₀\|_V + f (root) versus zero-boundary GFF plus continuous (GMForm) | **Root:** equivalent to GM's class on Greenian domains, up to extension (both inclusions above). **GMForm:** GM's class literally (z on Ω with h = z + f a.s., f an arbitrary measurable random continuous function, any dependence) | GM's "can be coupled" puts f on an extension. Taking the coupling on Ω loses nothing: given a coupling, put f on Ω × C(U) by the conditional law of f given h (C(U,ℝ) is Polish), and lift the a.s. conclusion with `ae_of_ae_fst` |
| φ-dependence of the a.s. event | **Equivalent** | GM: "deterministic conformal map … a.s."; Lean: ∀ φ, ∀ᵐ. Paper l. 28 says so explicitly |
| U = ℂ | **Excluded from GMForm and the root by A14; covered elsewhere (F3)** | `Rotation.ae_complex_affine_covariance` is GM Axiom IV′ with complex a, for every strong D. That needed a proof, because DG's Axiom IV has only real dilations and translations; GM inherited rotations from GMU. The literal one-map-for-all-laws form holds there with D. "Conformal ℂ → Ũ ⇒ affine" is not formalized |
| GM Thm 1.3's printed "φ : ℂ → U" | **Erratum; the coherent reading U → Ũ** | Literally, ℂ → U conformal forces U = ℂ and φ affine, which is the U = ℂ row. SGG ruling G9/ER1 records the same reading |
| Scope "That is, … a γ-LQG metric in the sense of Def. 1.1" (Axioms I–III on domains) | **Not restated (F6)** | Proved for `domainMetric` in `Domain.Axioms` |
| Weyl scaling class in GM Axiom III (bounded f) | **Strengthening** (not GM-form) | Realizations allow any continuous f (no boundedness) |

## Vacuity and nonvacuity (probe 3a)

- **Parameters** (`exists_params`): ξ := xiCrit + 1 > 0, by `Real.sInf_nonneg`. Q comes from the sealed `existsUnique_isLFPPExponent` and D from the sealed `exists_strongLQGMetric_lfppLimit`. Standard axioms.
- **Domains:** the unit disk is open, connected (convex, nonempty) and Greenian (`zbAdmissible_of_isBounded`). φ = id is a conformal bijection.
- **Field class:** `exists_zbGFF_disk` takes a whole-plane GFF (`GFFExist.exists_wholePlaneGFF`) and applies `Markov.exists_generated_joint_markov_general`, giving an `IsZeroBoundaryGFF disk` field with an honest covariance (Greenian, so not the junk covariance). With f = 0 and `extend_zero_eq` + `Distribution.ofFun_zero`, every hypothesis of the GM-form theorems holds.
- **Firing:** `gm_zeroBoundary_nonvacuous` instantiates all of them. An `example` then applies `gm_zeroBoundary_covariance_on_extension` and `exists_countably_universal_gm_axiomIV_on_extensions` (ι = Unit) to that data, and both fire.
- **Existence conjuncts are meaningful:**
  - each produced realization includes `IsGFFPlusCont`, a genuine whole-plane GFF;
  - each Φ is pinned a.s. to the domain metric of that realization;
  - the domain metric is not trivially ∞: `ae_domainMetric_zero_eq_internal` reduces it to D_{h₀}(·,·;V), and DG Axiom V (finite internal distances between compact sets in a connected U) applies.
- **Root's universal clause:** non-vacuous because its existence conjunct produces an extension and a realization (A15 C2). That conjunct is proved in the provider.

## The literal "one map for every law" form

- **The guide's OPEN is accurate** for proper Greenian domains. No Lean statement proves it or refutes it.
- **The argument has a real gap, not just a Lean gap:**
  - DG's Axiom II gives a locality functional per law.
  - The coin mixture handles countably many laws (`universalLocality_lsc`, as in SGG `universalLocality`, which is also countable only).
  - The LFPP construction gives convergence in probability per law, not along one sequence for all laws. GM's footnote itself defines D_h only a.s. per law.
  - The class (all ZB GFF + arbitrary random continuous corrections, on all spaces) contains uncountably many mutually singular laws, for example deterministic f outside the Cameron–Martin space.
  - So "OPEN" (not proved, not claimed false) is the correct status.
- **Exception, U = ℂ:** there it holds literally with Φ = D (F3).
- **Is the countable-law form the honest maximum? Not as currently stated.** What is proved, or provable here with the probes, is strictly more:
  1. the base-space Axiom IV identity (no extension clause; F1);
  2. one pair of maps for a countable family of (field, map) pairs, chosen before the maps (F2);
  3. hypotheses only on the source domain (F4);
  4. the whole-plane affine case, with the literal one-map form (F3).
  - The honest maximum is: countably universal, base-space GM Axiom IV on connected Greenian domains, plus the whole-plane affine case. The literal all-laws form on proper domains stays OPEN.

## Plain-language summary for the release guide

> In Gwynne–Miller's terms, the release proves the following for the supercritical metric (ξ > ξ_crit, Q = Q(ξ), any strong LQG metric D). Let U be a connected Greenian domain and φ : U → V a conformal bijection. Let h be a zero-boundary GFF on U plus a random continuous function, which may depend on the GFF arbitrarily. Then h^φ = h ∘ φ⁻¹ + Q log|(φ⁻¹)′| is again such a field on V. The metric D_h of h is the Weyl-scaled internal metric of a whole-plane realization, it does not depend on the realization, and it is almost surely a Borel function of h. For each such h, almost surely, simultaneously for all u, v ∈ U, D_h(u, v) = D_{h^φ}(φ(u), φ(v)), with exact constant one and +∞ values allowed. One Borel map on U and one on V serve any given countable family of such fields and maps at once. *[After F1 and F2 land: the identity then holds almost surely on each field's own probability space.]* The whole-plane case, with complex-affine maps of ℂ, is also proved, and there one map, D itself, serves every law. What is not proved, and stays open, is Gwynne–Miller's literal requirement of one map on each proper domain chosen before all the uncountably many laws. The probability-one event depends on φ. Disconnected open sets and non-Greenian proper domains are outside the scope.

(Before F1 and F2 land, replace the bracketed sentence with: "The identity holds almost surely on a measure-preserving extension of the probability space of h that carries the realizations; the maps may depend on φ.")
