# Imaginary Geometry I: correspondence between the paper and the Lean statements

This document compares the formal statements of the Lean 4 formalization of Jason Miller and Scott Sheffield,
*Imaginary geometry I: interacting SLEs*, Probability Theory and Related Fields 164 (2016), 553–705
(arXiv:1201.1496), with the paper. For each main theorem and each main definition it lists every difference between
the Lean statement and the paper's text, so that a reader can see exactly what the formal theorems say.

**Update after the external audit (15 November 2026).** An independent audit of the first publication led to four
more frozen theorems; see the [audit response](AUDIT-RESPONSE.md). They narrow these differences:
- **Theorem 1.5 (ii) and (iii)** now hold at every contact, real contacts included (`IsFlowLine.merges_of_contact`,
  `IsFlowLine.crosses_of_lt_of_contact`). The crossing excludes a common outgoing arc, so it no longer permits merging.
  The critical-angle non-intersection clauses remain interior-only.
- **Theorem 2.2's Markov sentence** is now stated, as a strong Markov property
  (`exists_strongMarkovKernel_isIntegratedSLEEvolution`).
- **Theorem 1.4's** "the left and right boundaries of η′" is now stated literally in the nowhere-boundary-filling case
  (`IsCenteredCounterflowDriver.boundaryWalks_outerBoundaries`). A bridge to the paper's literal counterflow
  definition is proved as a supplementary theorem.

The theorem-by-theorem entries below describe the original 17 statements, with a note where an added theorem changes
the comparison.

## How to read this document

**Sources.**
- *The paper*: arXiv:1201.1496v2 (27 February 2016). "p. n" is page n of its PDF, which is also the printed page
  number.
- *The specification*: the formal statements were frozen from *Imaginary Geometry I: mathematical specification*, a
  671-page edition of the paper prepared for this formalization (SHA-256 `88157ccbdb236054…`). It keeps the paper's
  section and theorem numbers, writes the statements out with all their hypotheses, corrects errors and adds
  supplementary arguments. "spec p. n" is its page n. It is included in this release: [`specification/`](specification/).
- *The Lean statements*: all names are in the namespace `InteractingSLE`. Each of the 17 frozen theorems and 96 frozen
  definitions is one file in `InteractingSLE/Frozen/Spec/`, named after the declaration with `.` replaced by `_`, and
  listed in `InteractingSLE/Frozen/frozen-anchors.json`. All 17 theorem files are sealed: each proof is a single
  `by exact` of a provider theorem with the same statement. The [result guide](README.md) prints the statements.
- *Records*: ruling (R…), audit (AUD-…) and errata-ledger (E…) labels name development records that are not part of
  the release; they are given so that each reading can be traced. Where the paper is wrong, this document names the
  correction; the argument is in the [errata document](ERRATA.md).

**Labels.** Each difference carries one label.
- **convention**: a choice of encoding, normalization or frame; the mathematical content is unchanged.
- **made precise**: the paper's words are informal, ambiguous or incomplete; the Lean states one exact reading, the
  one the specification gives.
- **stronger in Lean**: the Lean asserts more than the paper (more general hypotheses or an additional conclusion).
- **weaker in Lean**: the Lean asserts less than the paper's words.
- **correction**: the paper's statement is wrong as printed; the Lean states a corrected form.
- **scope**: a statement added on purpose (a companion theorem) or a sentence left out on purpose.

**Notation.** ℍ = {z : Im z > 0}. λ = π/√κ and χ = 2/√κ − √κ/2. For 0 < κ < 4: κ′ = 16/κ and Λ = λ − πχ/2 = π√κ/4
(the paper's λ′). g_t and K_t are the Loewner maps and hulls of (1.6) (p. 12), f_t = g_t − W_t, and
𝔥_t(z) = 𝔥⁰_t(f_t(z)) − χ arg f_t′(z) is the harmonic function of Theorem 1.1. T∗ is the continuation threshold and
τ_z the time at which z ∈ ℍ is swallowed.

## 0. Conventions common to all statements

These differences apply wherever the object occurs; the theorem sections do not repeat them.

- **G1, convention.** Force words are plain data: positions `xL : Fin nL → ℝ`, `xR : Fin nR → ℝ` and real weights
  `ρL`, `ρR`, with the order x_{k,L} ≤ ⋯ ≤ x_{1,L} ≤ 0 ≤ x_{1,R} ≤ ⋯ ≤ x_{ℓ,R} as the hypothesis `IsOrderedForceWord`.
  The side is the list a mark belongs to, so 0⁻ and 0⁺ are distinct. Coincident marks are separate entries whose
  weights add in every sum. The paper orders the marks strictly in §1.3 (p. 15) but allows coincident force points in
  §2.2 (p. 35). (R22; AUD-1b §4.1)
- **G2, convention.** κ (written a in Theorems 1.3 and 2.2) is an arbitrary real in the definitions; κ > 0, and κ < 4
  where flow lines are involved, are hypotheses of each theorem. (R15 Q5; R19 (2))
- **G3, made precise.** The lifetime ζ of an evolution is the continuation threshold read as the *maximal lifetime*:
  the threshold condition fails at every time before ζ; ζ = 0 exactly when the seed is inadmissible; and if
  0 < ζ < ∞, every limit of the state as t ↑ ζ satisfies the threshold condition. Read literally, the printed
  infimum (p. 35) evaluates the state at and after the time where the evolution stops being defined, and it admits
  fake short lifetimes. That no coordinate explodes at a finite ζ is a theorem (spec Aux. lemma 3, p. 24) established
  in the proofs, not part of the definition. (R15 Q1; errata ledger E1; AUD-1b §6.1, note N1)
- **G4, convention.** An evolution may use any filtration in which B is a Brownian motion and W, V are adapted before
  ζ, instead of σ(B_s, W_s, V_s : s ≤ t) (p. 35) or its usual augmentation (spec p. 4); both classes give the same
  theorems. B is a Brownian motion for all times, extended independently after ζ as the specification's proofs do.
  (R15 Q2; AUD-1b §4.6, §6.2)
- **G5, made precise.** Where the paper says "the function which is harmonic in ℍ with boundary values …", the Lean
  quantifies over every *bounded* harmonic extension (harmonic and bounded on ℍ, with the given boundary limits off a
  finite set). Companion theorems prove that one exists and that any two agree on ℍ, so these clauses are neither
  vacuous nor dependent on a choice. (spec p. 2; R19 (1); AUD-2 §5.1; AUD-3c §5)
- **G6, made precise.** A field is a random distribution h : Ω → 𝓓′(ℍ), measurable for the cylinder σ-algebra.
  "h⁰ is a zero-boundary GFF" means that h⁰ is a centred Gaussian process on test functions whose covariance is the
  Dirichlet Green form for (f, g)_∇ = (2π)⁻¹ ∫ ∇f · ∇g, the paper's normalization (p. 53); the predicate is reused
  from the LQGMetric library. (R19 (6), (7); AUD-2 §3, §4.14)
- **G7, made precise.** "A continuous curve generating the Loewner chain on [0, T]" is `IsGeneratingTrace`: η(0) = 0,
  η is continuous on [0, T] (on [0, ∞) if T = ∞), and for every t < T, ℍ ∖ K_t is the unbounded component of
  ℍ ∖ η([0, t]). No hull identity is asserted at T itself, where η(T) is the continuous limit. (spec p. 3; AUD-1b
  §4.8)

## 1. Theorem by theorem

### Theorem 1.1: coupling of SLE_κ(ρ) with the GFF (paper pp. 17–18; spec p. 9)

**Paper.** Fix κ > 0 and weights (ρ^L; ρ^R); let (W, V^{i,q}) solve (1.10)–(1.11) and let 𝔥⁰_t be "the function
which is harmonic in ℍ with boundary values" −λ(1 + Σ_{i=0}^{j} ρ^{i,L}) on [V_t^{j+1,L}, V_t^{j,L}) and
λ(1 + Σ_{i=0}^{j} ρ^{i,R}) on [V_t^{j,R}, V_t^{j+1,R}), where x^{0,L} = 0⁻ and x^{0,R} = 0⁺. With (F_t) "the
filtration generated by (W, V^{i,q})", "there exists a coupling (K, h) where h̃ is a zero boundary GFF on ℍ and
h = h̃ + 𝔥₀" such that for every F_t-stopping time τ that almost surely occurs before the continuation threshold,
"K_τ is a local set for h and the conditional law of h|_{ℍ∖K_τ} given F_τ is equal to the law of 𝔥_τ + h̃ ∘ f_τ".

**Lean.** `InteractingSLE.exists_isOptionalHullCoupling`: for κ > 0 and every ordered force word there are a
probability space, a filtration, an integrated evolution (W, V^L, V^R, B) with lifetime ζ, and a random distribution h
on ℍ, satisfying `IsOptionalHullCoupling`. Companion:
`InteractingSLE.existsUnique_isBoundedHarmonicExtension_forceBoundaryData`.

**Differences** (besides G1–G6).
- **made precise.** The boundary data are taken at the centred positions V̂ = V − W, with V̂^{0,L} = V̂^{0,R} = 0
  (`forceBoundaryData`): at x < 0 the value is −λ(1 + the total weight of the left marks to the right of x), at x ≥ 0
  it is λ(1 + the total weight of the right marks at or to the left of x). The paper's display uses V_t, with
  x^{0,L} = 0⁻ and x^{0,R} = 0⁺, while 𝔥⁰_t is composed with the centred map f_t and Figure 1.11 (p. 18) is drawn
  centred. (spec p. 9; AUD-2 §4.4)
- **made precise.** arg f_t′ comes from the continuous branch of log f_t′ that vanishes at t = 0 (`couplingMean`).
  (spec p. 9; AUD-2 §4.7)
- **made precise.** (F_t) is the usual augmentation of the filtration generated by the driving process (W, V) killed
  at ζ (`drivingFiltration`), without B, as the theorem says. A Lean filtration can adjoin only measurable null sets,
  which changes no statement. (spec p. 9; R19 (3); AUD-2 N1)
- **made precise.** "Local set" is `IsLocalSet`, the paper's two-step definition (p. 62) on ℍ; see §2. (R19 (5);
  AUD-2 §4.12)
- **made precise.** The conditional law is stated by conditional characteristic functions: for every test function
  φ, almost surely on {supp φ ∩ K_τ = ∅}, E[exp(i(h, φ)) | F_τ] = exp(i(𝔥_τ, φ) − ½ E_τ(φ)), where
  E_τ(φ) = ∬ φ(y) G(f_τ(y), f_τ(z)) φ(z) dy dz, with G(y, z) = log|y − z̄| − log|y − z|, is the variance of
  (h̃ ∘ f_τ, φ). The null set may depend on τ and φ. This is the form the specification's proof establishes
  (spec p. 82). (AUD-2 §4.13, §5.2)
- **convention.** "There exists a coupling" is stated as the existence of one probability space carrying the
  evolution and the field. It is equivalent to "for the driving process there is a coupling" by the uniqueness in
  law of Theorem 2.2. (AUD-2 note N2)
- **scope.** The companion, which is not in the paper, states that for every real κ, all weights and all centred
  positions the force data have a bounded harmonic extension, unique on ℍ. (R19 (1); AUD-2 §5.1)

### Theorem 1.2: the field determines the curve (paper p. 20; spec p. 4)

**Paper.** "Suppose that h is a GFF on ℍ and that η ∼ SLE_κ(ρ). If (η, h) are coupled as in the statement of
Theorem 1.1, then η is almost surely determined by h."

**Lean.** `InteractingSLE.exists_measurable_lifetime_trace_eq_comp_field`: for κ > 0, an ordered force word and every
coupling, on any probability space, that satisfies `IsOptionalHullCoupling`, there is a measurable map
Φ : 𝓓′(ℍ) → [0, ∞] × (paths [0, ∞) → ℂ) such that almost surely Φ(h)₁ = ζ and Φ(h)₂(t) = η(min(t, ζ)) for all t and
for every continuous generating trace η of W on [0, ζ].

**Differences** (besides G1–G7).
- **made precise.** "Determined by h" means "almost surely equal to a measurable function of h": measurable for the
  cylinder σ-algebra on 𝓓′(ℍ) and the product σ-algebra on paths, which for continuous traces is equivalent to the
  Borel σ-algebra of continuous paths. Φ is chosen after the coupling. (spec p. 4; R19 (7); AUD-2 note N4, §5.3)
- **made precise.** The determined object is the pair formed by the lifetime ζ and the capacity-parametrized curve
  stopped at ζ, including its endpoint when ζ is finite. (spec p. 4; R19 (4))
- **made precise.** The curve clause is asserted for every continuous generating trace; that one exists is
  Theorem 1.3, which applies to the evolution of the same coupling. (R19 (4); AUD-2 note N3)

### Theorem 1.3: continuity and transience of the trace (paper p. 22; spec p. 4)

**Paper.** "Suppose that κ > 0. If η ∼ SLE_κ(ρ) on ℍ from 0 to ∞ then η is almost surely a continuous path, up to
and including the continuation threshold. On the event that the continuation threshold is not hit before η reaches
∞, we have a.s. that lim_{t→∞} |η(t)| = ∞."

**Lean.** `InteractingSLE.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`: for a > 0, an ordered force word and
every integrated evolution (W, V^L, V^R, B) with lifetime ζ on any filtered probability space, almost surely: if the
seed is inadmissible, then ζ = 0; and W has a continuous generating trace η on [0, ζ], with |η(t)| → ∞ when ζ = ∞.

**Differences** (besides G1–G4, G7).
- **stronger in Lean.** "η ∼ SLE_κ(ρ)", the law of Theorem 2.2, becomes every integrated evolution on every filtered
  probability space; by Theorem 2.2 they all have that law. (R15 Q4; errata ledger E4; AUD-1b §5.1)
- **made precise.** "η is a continuous path, up to and including the continuation threshold" is the existence of a
  continuous generating trace of the driver on [0, ζ] (G7); when ζ = ∞ it is continuous on [0, ∞). (AUD-1b §4.8,
  §5.1)
- **made precise.** "The continuation threshold is not hit before η reaches ∞" is the event {ζ = ∞}. (spec p. 4;
  AUD-1b §5.1)
- **made precise.** An inadmissible seed gives ζ = 0, and the trace is then the single point 0. (spec p. 4; AUD-1b
  §5.1)

### Theorem 1.4: light cone, frontiers and component laws (paper p. 22; spec pp. 4–5)

**The paper is informal here.** It says (p. 22): "Theorem 1.4 below is stated somewhat informally. As mentioned
earlier, precise statements will appear in Proposition 5.9 and in Section 7.4.3."

**Paper.** Let h be a GFF on ℍ with piecewise constant boundary data, let η′ be "the counterflow line of h starting
at ∞ targeted at 0", and assume that its continuation threshold is almost surely not hit. Then (a) "the range of η′ is
almost surely equal to the set of points accessible by SLE_κ trajectories of h starting at 0 whose angles are
restricted to be in [−π/2, π/2] but may change in time"; (b) with η_L and η_R the flow lines of h from 0 with angles
π/2 and −π/2, almost surely, if η′ is nowhere boundary filling (η′ ∩ ℝ has empty interior), then η_L and η_R do not
hit the continuation threshold before reaching ∞ and are the left and right boundaries of η′. The precise versions
named there are Proposition 5.9 (p. 104: strip data without boundary intersection) and §7.4.3 (pp. 163–166: general
piecewise-constant data, the boundary-filling case of Figure 7.22, and Proposition 7.30).

**How the formal statements make it precise.** The specification states Theorem 1.4 (pp. 4–5) in the form of its
Corollary GW6 (p. 643): the completed range of η′ is the closed countable boundary-continued light cone of Lemmas GW2
(p. 621) and GW2a (p. 623); the frontiers are the finite boundary walks of Lemma GW1 (p. 618); and, as an added
conclusion, the component field–path laws are the finite-word kernels of Theorem GW4 (p. 637). The Lean has three
statements and a companion:
- `InteractingSLE.IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone` (part (a));
- `InteractingSLE.IsCenteredCounterflowDriver.boundaryWalks_frontiers` (part (b));
- `InteractingSLE.IsCenteredCounterflowDriver.componentKernels` (the GW4 conclusion);
- the companion `InteractingSLE.exists_isStagedHistory`.

Common hypotheses: 0 < κ < 4; b locally constant off a finite set; a standard Borel probability space carrying a GFF
h with data b; W′ and ζ′ with `IsCenteredCounterflowDriver κ P h W' ζ'`; ζ′ = ∞ almost surely; and a realization E
of the staged histories (items 4–6). Theorem 1.4 counts as proved only with all four statements (R29).

**Differences** (besides G1–G7).
1. **made precise.** 0 < κ < 4 is explicit, and the boundary data are finite piecewise constant (finitely many
   jumps). (spec p. 4; AUD-4 §1)
2. **convention.** η′ is the *centred* counterflow CF_d(h) = CF_lit(h + πχ), coupled with −h − πχ and run from ∞ to 0
   with the lift L_R(z) = −2 Log z of R(z) = −1/z: in the chart R, its driver W′ is the Theorem 1.1 driver, at
   κ′ = 16/κ, of the field −h ∘ R + πχ − 2χ arg w, whose finite boundary data are existential (they are fixed by its
   law). The paper couples a counterflow line with −h and leaves the branch of arg ψ′ to its figures (Remark, p. 19).
   The literal and centred frames differ by the odd shift πχ, which no change of branch (a multiple of 2πχ) absorbs;
   the specification reads the paper's figures of a flow line with its reverse counterflow, and their extremal angles
   ±π/2, in the centred frame. (spec pp. 2, 12, 16–17, FD11.1–FD12.5; AUD-4 §1, §4.1)
3. **made precise.** "The range of η′" is its completed range: the tip points R(γ(t)), t ≥ 0, obtained as radial
   limits (γ the trace of W′), together with the terminal point 0. The initial point ∞ is left out of both sides of
   every set identity. (AUD-4 §4.1, note N4)
4. **made precise.** A trajectory "whose angles may change in time" is a staged history: a root on ℝ and a finite
   program of flow instructions (angle θ for own capacity time t, t = ∞ allowed) and boundary-continuation
   instructions, each ordinary piece launched in the current unbounded domain with the inherited derivative lift. Its
   physical set is its root, its pieces up to their stops, and its boundary connectors. (spec p. 136, GW1, GW2a;
   AUD-4 §4.2)
5. **made precise.** The statements quantify over every realization E (a driver and a lifetime for each history and
   instruction) satisfying `IsStagedHistory`: the drivers are measurable, the retained histories are events, the
   value at a finite positive lifetime is the continuous limit, and under the regular conditional law given the
   retained history each launched piece is the angle-θ flow line of the conditional field. E is constrained for every
   root but only for histories whose angles lie in [−π/2, π/2], the ones the specification uses. The companion provides such
   an E on every standard Borel space carrying h, so the statements are not vacuous. (R25, R29; AUD-4 §4.3, note N5;
   AUD-4b §1.3, §1.5, Q3)
6. **made precise.** E must also satisfy `StagedPiecesRegular` (version 2 of the statements): almost surely every
   launched piece has a continuous driver from 0 and a continuous generating trace up to its stop, tending to ∞ if it
   never stops. Conditional laws cannot see path regularity; the paper's pieces are curves, and the companion supplies
   such realizations. (R51; AUD-T14-R51 §1, §3, B3, B8)
7. **convention.** The probability space is standard Borel, which regular conditional laws require; no law-level
   content is lost. (R25; AUD-4 note N2, §8)
8. **made precise.** Light cone (a): for every countable dense Θ ⊂ (−π/2, π/2) there is a countable dense set Q of
   positive times such that, for every such E, almost surely the completed range is the closure of {0} and the GW2
   family. The family consists of the physical sets of all finite Θ-schedules from 0 with strictly increasing switch
   and terminal times in Q, each kept only up to its first threshold; and, if the angle −π/2 seed at 0 is inadmissible
   on the right (b(0⁺) − πχ/2 ≤ −λ), of the segments [0, v] and the same schedules from v, for every rational v in the
   first low right boundary arc. (spec GW2, p. 621; AUD-4 §1, §4.4, note N9)
9. **made precise.** The closed angle interval and boundary continuation: adding the physical sets of any fixed
   countable collection of histories from 0 whose ordinary angles lie in [−π/2, π/2], continued along ℝ after a
   threshold by the GW2a rule, gives almost surely the same closed set, with one null set per collection. (spec GW2a,
   p. 623; AUD-4 §1, §3)
10. **weaker in Lean.** The time set Q is existential: it is chosen after Θ and before E, and may depend on the
    probability space and the field. The paper's light cone (p. 100) uses positive rational switch times, and its
    Proposition 5.9 (p. 104) lets the times range over any dense set; the Lean identity is asserted for one Q, while
    containment (item 9) holds for every countable family of histories. (spec GW2: "There is a deterministic countable
    dense schedule set Q"; AUD-4 note N3)
11. **stronger in Lean.** The frontier statement (b) holds on every event, not only when η′ is nowhere boundary
    filling: almost surely the right walk R lies in the completed range and no point of the range lies strictly to
    its right, and the left walk L lies in it with no point of the range strictly to its left. R starts at 0 at angle
    −π/2, flows through its available lifetime, and at a finite threshold follows ℝ to the right to the next original
    jump at which the angle is admissible and relaunches there; L is the mirror walk at angle π/2. The paper treats
    the boundary-filling case only informally (p. 26; Figure 7.22, p. 164). (spec GW1, p. 618, GW4; AUD-4 §1, §4.4)
12. **made precise.** "Left and right boundaries" are meant in GW4's side-boundary sense: z is strictly to the right
    of a set A if z ∈ ℍ ∖ A and the closure of its component in ℍ ∖ A contains a positive real point not in A (to the
    left: a negative one). (AUD-4 §1, §4.4)
13. **made precise.** "η_L and η_R do not hit the continuation threshold before reaching ∞" is: if the range meets ℝ
    in a set with empty interior, the first piece of each walk has infinite lifetime, so each walk is the single flow
    line η_R or η_L. (AUD-4 §1)
14. **stronger in Lean.** Component kernels are not in the paper's Theorem 1.4; the specification adds "the actual
    component field–path laws are the complete finite-word kernels of GW4". For almost every ω₀, given the retained
    data of both walks, every component C of ℍ ∖ (R ∪ L) lying between them has a component chart, and for every
    choice of charts: h written in the chart of C is, under the conditional law, a GFF whose finite boundary word is
    −Λ on the ordinary pieces of R, +Λ on those of L and the original boundary value on the connectors (GW3.1); its
    centred counterflow has infinite lifetime, and η′ traverses C as that counterflow after a continuous increasing
    time change; and the field–driver pairs of different components are independent. When both arcs are ordinary the
    word is (d, d) with d = κ′/2 − 4 (spec GW4), the law of the paper's Proposition 7.30 (p. 163). (spec p. 5,
    GW3–GW4, pp. 636–637; R25; AUD-4 D1; AUD-4b §1.4)
15. **scope.** The companion `exists_isStagedHistory` (spec GW1, p. 618) is not in the paper. (R25, R29, R51)

### Theorem 1.5: interaction of flow lines (paper p. 30; spec p. 5)

**Paper.** h is a GFF on ℍ with piecewise constant boundary data, η^x_θ is its flow line from x ∈ ∂ℍ with angle θ,
and x₁ ≥ x₂. (i) If θ₁ < θ₂, η^{x₁}_{θ₁} almost surely stays to the right of η^{x₂}_{θ₂}; if θ₂ − θ₁ < πκ/(4 − κ) the
paths can bounce off each other, "otherwise the paths almost surely do not intersect (except possibly at their
starting point)". (ii) If θ₁ = θ₂, the paths may intersect and, "upon intersecting, the two curves merge and never
separate". (iii) If θ₂ + π > θ₁ > θ₂, η^{x₁}_{θ₁} may intersect η^{x₂}_{θ₂} and, upon intersecting, "crosses and then
never crosses back"; if θ₁ − θ₂ < πκ/(4 − κ) they can bounce off each other, "otherwise the paths almost surely do not
subsequently intersect". The paper calls this statement "somewhat imprecise" (p. 29).

**Lean.** `InteractingSLE.IsFlowLine.stays_right_of_lt` (i), `InteractingSLE.IsFlowLine.merges` (ii) and
`InteractingSLE.IsFlowLine.crosses_of_lt` (iii); companions `InteractingSLE.exists_isFlowLine` and
`InteractingSLE.IsPiecewiseConstantBoundaryData.existsUnique_isBoundedHarmonicExtension`. Setting: 0 < κ < 4; b
locally constant off a finite set; a probability space carrying a GFF h with data b; (η₁, ζ₁) and (η₂, ζ₂) satisfying
`IsFlowLine` for (x₁, θ₁) and (x₂, θ₂), with x₂ ≤ x₁ in (i)–(ii) and x₂ < x₁ in (iii). Theorem 1.5 counts as proved
only together with `exists_isFlowLine` (R26).

**Differences** (besides G1–G7).
- **made precise.** 0 < κ < 4 is explicit (the paper defines flow lines only for κ ∈ (0, 4), p. 18), and the
  boundary data are finite piecewise constant. (spec p. 5; AUD-3 §1, §3.2)
- **convention.** A flow line is any pair (η, ζ) satisfying `IsFlowLine` (see §2), not "the" flow line. This is
  faithful because such curves are almost surely functions of the field (Theorem 1.2); `exists_isFlowLine` shows that
  they exist on the field's own probability space, so the three clauses are not vacuous. (AUD-3 §3.6; AUD-3c §4.2,
  §5; R26)
- **made precise.** "Stays to the right" is Convention W0, required for every pair of prefixes strictly before the
  lifetimes: η₁([0, a]) and η₂([0, c]) extend to continuous injective curves to ∞ in the closed half-plane, the second
  in the closed left side of the first. The closed relation between the terminal limits is not included. (spec W0,
  p. 528, W5, p. 533; AUD-3 §1, §2.1, note N4)
- **made precise.** "Intersecting" is an interior available contact: η₁(s) = η₂(t) ∈ ℍ with s < ζ₁ and t < ζ₂. Merging
  in (ii) and crossing in (iii) are asserted after such contacts. (spec p. 5; AUD-3 §2.1, §3.9) *Added after the
  external audit:* `IsFlowLine.merges_of_contact` and `IsFlowLine.crosses_of_lt_of_contact` assert them after every
  contact, real ones included, as in the paper's Proposition 7.12 (p. 141). (R122; AUD-AF-T15)
- **weaker in Lean.** The non-intersection clauses of (i) and (iii) exclude only interior available contacts: common
  real points and common terminal points are not covered, where the paper says that the paths do not intersect
  except possibly at their starting point. (spec p. 5: "Common terminal points are excluded from nonintersection
  conclusions"; AUD-3 §2.1, §3.9)
- **made precise.** Merging (ii): after every interior available contact η₁(s) = η₂(t), an increasing bijection from
  [s, a] onto [t, c], with a = ζ₁ or c = ζ₂, carries η₁ to η₂; "never separate" means while both are available.
  (AUD-3 §2.2, §3.11)
- **made precise.** Crossing (iii): if there is an interior available contact, there is a first contact (s₀, t₀),
  attained at one common point, which may be real and may precede the given contact; there η₁ crosses η₂ from right
  to left and never back: in a conformal chart of the unbounded component left by both incoming prefixes, sending the
  contact point to 0 and ∞ to ∞, every pair of strict outgoing prefixes has ordered completions with the image of η₁
  on the left. Only the outgoing order is encoded; the incoming order follows from x₂ < x₁. (spec Theorem 7.12C,
  pp. 461, 542; AUD-3 note N5, §3.14) This weak order alone permits merging. *Added after the external audit:*
  `IsFlowLine.crosses_of_lt_of_contact` adds that no open arc of either outgoing path lies on the other, which is
  Theorem 7.12C's "no common open outgoing arc". (R122; AUD-AF-T15)
- **made precise.** "Do not subsequently intersect" in (iii) is "every interior available contact is the first
  contact". (AUD-3 §2.3)
- **made precise.** (iii) assumes x₂ < x₁, as the specification does; for x₁ = x₂ the pair is covered by (i) with the
  two curves exchanged. (spec p. 5)
- **scope.** The sentences allowing bouncing or contact are not assertions and are not formalized. (spec p. 5; AUD-3
  §1, B11)
- **scope.** The companions are not in the paper: `exists_isFlowLine` (every such field carries its flow lines) and
  the existence and uniqueness on ℍ of the bounded harmonic extension of finite piecewise-constant data. (R26; AUD-3c)

### Theorem 2.2: existence and uniqueness of SLE_κ(ρ) (paper p. 40; spec p. 21)

**Paper.** "Given the vector ρ and the initial values V_0^{i,q}, Definition 2.1 uniquely determines a joint law for
W_t, B_t, and the V_t^{i,q} — each defined for all t up to the continuation threshold. Under this law, the values W_t,
B_t, and V_t^{i,q} taken together are a continuous multidimensional Markovian process indexed by t."

**Lean.** `InteractingSLE.exists_isIntegratedSLEEvolution` (existence) and
`InteractingSLE.IsIntegratedSLEEvolution.measure_killedState_eq` (uniqueness in law).

**Differences** (besides G1–G4).
- **convention.** The theorem is split into existence and uniqueness in law. (R15 Q4; R22)
- **made precise.** "Definition 2.1" is the formal definition `IsIntegratedSLEEvolution`; see §2.
- **made precise.** Existence is stated explicitly: for a > 0 and every ordered force word there are a probability
  space (in the lowest universe), a filtration and an integrated evolution with its lifetime. The paper's "uniquely
  determines a joint law" presupposes it. (AUD-1a §4.2; AUD-1b §5.2)
- **made precise.** Uniqueness: any two integrated evolutions, on any two filtered probability spaces, give the same
  probability to every event {t_j < ζ and (W, V^L, V^R, B)(t_j) ∈ A_j for j = 1, …, n} (all times t_j, all Borel sets
  A_j). These events form a π-system that determines the law of the state killed at ζ, including the law of ζ.
  (AUD-1b §5.3, §6.6)
- **made precise.** The law also depends on κ, which the paper's sentence does not list; the statement fixes it.
  (errata ledger E6)
- **scope.** The last sentence, the Markov property, was not part of the original frozen statements (R15 Q4; R17).
  *Added after the external audit:* `exists_strongMarkovKernel_isIntegratedSLEEvolution` states it as a strong Markov
  property, with one time-homogeneous kernel at every finite stopping time. Time zero and entrance words are included.
  The kernel is measurable on separated states, and future events are finite-time cylinders. (R122; AUD-AF-T22)

### Theorem 2.4: martingale characterization (paper p. 43; spec pp. 34–35)

**Paper.** Given "a random continuous curve η on ℍ̄ from 0 to ∞ whose Loewner driving function W_t is almost surely
continuous", points x^{i,q} with weights ρ^{i,q}, the images V^{i,q} of the x^{i,q} (g_t(x^{i,q}) before x^{i,q} is
absorbed, afterwards the g_t-image of the left or right endpoint of ℝ ∩ K_t), and 𝔥_t as in Theorem 1.1: "W_t and the
V_t^{i,q} can be coupled with a standard Brownian motion B_t to describe an SLE_κ(ρ) process (up to the continuation
threshold) if and only if 𝔥_t(z) evolves as a continuous local martingale in t for each fixed z ∈ ℍ until the time z
is absorbed by K_t."

**Lean.** `InteractingSLE.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore`.

**Differences** (besides G1–G5, G7).
- **correction.** The martingale side is stopped at min(τ_z, T∗), not at τ_z. With the printed horizon the forward
  direction is false (see the errata document); min(τ_z, T∗) is the horizon of the specification's own proof and of
  Theorem 2.6. (R109; AUD-T2426A §7; AUD-T2426B F1; AUD-T2426C note N1)
- **made precise.** The curve is a measurable process η with a measurable driver W such that, almost surely, W is
  continuous with W₀ = 0, η is a continuous generating trace of W on [0, ∞), η stays in the closed half-plane and
  |η(t)| → ∞. The closed half-plane condition matters: a curve allowed into the lower half-plane is not determined by
  its hulls. (AUD-T2426C §4.1; AUD-T2426A B9)
- **made precise.** The force points are measurable inputs V^L, V^R that are almost surely the geometric images,
  defined by one infimum (right marks) or supremum (left marks) formula over unswallowed real points; proved lemmas
  show that this is g_t(x) before x is swallowed and the image of the extreme endpoint of ℝ ∩ K_t afterwards. (The
  paper's sentence before the theorem writes x^{i,q} where V_t^{i,q} is meant.) (AUD-T2426A-v2 §4.1, §5.1;
  AUD-T2426C §3.1)
- **made precise.** "Can be coupled with a standard Brownian motion" is: on an extension of the probability space (a
  measure-preserving map Ω′ → Ω) there are a filtration and a Brownian motion B with which W and V form an integrated
  evolution whose lifetime is T∗, computed from (W, V) by `continuationThreshold`. After T∗ the Brownian motion needs
  fresh randomness. (AUD-T2426A §7; AUD-T2426C §4.2)
- **made precise.** The martingale side quantifies over every choice of bounded harmonic extensions of the force data
  at V_t − W_t, for each sample and time (G5), and over every z ∈ ℍ. (R19 (1); AUD-T2426C §4.2)
- **made precise.** Its filtration is the usual augmentation of the natural filtration of η, which the theorem does
  not name; the specification names it in the proof. (AUD-T2426C §4.2)
- **made precise.** "Continuous local martingale until σ" is `IsContLocalMartingaleBefore`: almost surely continuous
  on [0, σ), with localizing stopping times, each equal to 0 or strictly below σ, that eventually exceed every time
  before σ, the stopped processes 1_{σ_n > 0} X_{t∧σ_n} being martingales. Only values before σ enter; that σ can be
  announced is a proof obligation, not a hypothesis. (AUD-T2426C §3.3, note N-M1; AUD-T2426A-v2 §4.4)

### Theorem 2.6: one-point characterization (paper pp. 52–53; spec p. 40)

**Paper.** In the setting of Theorem 2.4, if "for some fixed z ∈ ℍ the correspondingly defined 𝔥_t(z) is given by √κ
times a Brownian motion when time is parameterized by minus the log of the conformal radius", then "these processes
describe an SLE_κ(ρ) evolution at least up to the first time that z is swallowed by the path". The paper only sketches
the proof: "Although we will not use it in this paper, we remark (and sketch a proof)" (p. 52).

**Lean.** `InteractingSLE.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius`.

**Differences** (besides the setting items of Theorem 2.4).
- **correction.** There is no factor √κ for the harmonic function 𝔥_t of Theorem 1.1, which the statement names. The
  printed factor belongs to the √κ-rescaled analytic function (2.12) of the proof of Theorem 2.4, whose imaginary part
  is √κ 𝔥_t (errata A3). The formal hypothesis is the bracket identity
  ⟨𝔥(z)⟩_t = log(crad(ℍ, z)/crad(ℍ ∖ K_t, z)), so that 𝔥_t(z) − 𝔥₀(z) is a standard Brownian motion in the time
  −log crad (spec p. 40: "no factor √κ occurs in that parameterization"). (AUD-T2426A §7; AUD-T2426C F5)
- **made precise.** The hypothesis is stated through its defining property: for every choice of extensions, 𝔥_t(z) is
  a continuous local martingale before σ, and there is a process A, almost surely equal before σ to
  log(crad(ℍ, z)/crad(ℍ ∖ K_t, z)), such that 𝔥_t(z)² − A_t is a continuous local martingale before σ. This is proved
  equivalent to the explicit Loewner form of the bracket. (AUD-T2426A-v2 §5.2; AUD-T2426C §4.3, F5)
- **made precise.** The horizon of both the hypothesis and the conclusion is σ = min(τ_z, T∗); the paper names only
  the swallowing time. The specification prints this horizon, so no ruling was needed. (spec p. 40; AUD-T2426C note N1)
- **made precise.** crad(D, z) = |φ′(0)| for a conformal bijection φ of the unit disc onto D with φ(0) = z
  (`IsConformalRadius`, a relation proved to be single-valued); for ℍ ∖ K_t it is taken in the component containing
  z, which is all of ℍ ∖ K_t. (spec p. 157; AUD-T2426C §3.4)
- **made precise.** "These processes describe an SLE_κ(ρ) evolution up to σ" is: on an extension of the probability
  space there is an integrated evolution (W′, V′, B, ζ) whose driver and force points agree almost surely with W and V
  at all times before σ. (AUD-T2426C note N3)

## 2. Definitions

The frozen files are in `InteractingSLE/Frozen/Spec/`, named after the declarations. `QuantumZipper.…` and
`LQGMetric.…` objects are reused from already released libraries and are not frozen files.

| Object | Paper | Lean | Differences |
|---|---|---|---|
| GFF and boundary data | (1.3), p. 10; §3.1, p. 53; harmonic extension in Theorem 1.1, p. 17; piecewise-constant data, pp. 22, 30 | `IsGFFWithBoundaryData`, `IsBoundedHarmonicExtension`, `IsPiecewiseConstantBoundaryData` with `PiecewiseConstantBoundaryData.leftLim`, `.rightLim`, `.jumpSet`, `upperHalfPlaneOpens`; `LQGMetric.IsZBGFFProcess` | G5, G6. Fields live on ℍ; other domains enter only through charts. "Piecewise constant" is "locally constant off a finite set", so there are finitely many jumps; the values at the jumps are never read. h − m is a zero-boundary GFF for every bounded harmonic extension m of b. (AUD-3 §3.2, §8) |
| Local sets | pp. 61–62 | `IsLocalSet`, `hittingSigma`, `IsHarmonicDistOn`, `IsCondZeroBoundaryGFF` | Defined on ℍ only: a relatively closed A ⊆ ℍ stands for the paper's A ∪ ∂ℍ ∈ Γ. The σ-algebra on sets is generated by the hitting events {A ∩ U ≠ ∅}, U ⊆ ℍ open, which on Γ is the paper's Hausdorff-metric Borel σ-algebra. "Given (A, h₁), h₂ is a zero-boundary GFF on ℍ ∖ A" is stated by conditional characteristic functions with the Dirichlet covariance of ℍ ∖ A; "a sample with the law of (A, h) can be produced by" is an equality of laws with a pair built on an auxiliary probability space. (R19 (5); AUD-2 §4.9–§4.12) |
| SLE_κ(ρ) (Definition 2.1) | (1.10)–(1.11), pp. 16–17; Definition 2.1, p. 35 | `IsIntegratedSLEEvolution`, `IsIntegratedSLEPath` (version 2), `IsFilteredBrownianReal`, `AdaptedBefore`, `IsOrderedForceWord` | G1–G4. The paper's Conditions 1–3 (local strong solutions between collisions, instantaneous reflection, the integral equation for V) are replaced by the integrated equations (1.10)–(1.11) for all t < ζ, which the paper says are equivalent (p. 35); the strong-solution property becomes a consequence (spec p. 21). Stated explicitly: the side order V^{k,L} ≤ ⋯ ≤ V^{1,L} ≤ W ≤ V^{1,R} ≤ ⋯ ≤ V^{ℓ,R}, absolute integrability of every 1/(W − V) on compact intervals before ζ, Lebesgue-null collision sets, continuity on [0, ζ), and adaptedness of the processes killed at ζ. (spec p. 20; AUD-1b §4.3–§4.6; version 2: R28, AUD-4b §2) |
| Continuation threshold | p. 17 (description); p. 35 (definition) | `ForceWord.ThresholdCondition`; the lifetime clauses of `IsIntegratedSLEPath`; `continuationThreshold` | G3. The condition sums the weights of all marks of one side that coincide with W, as on p. 35, not a prefix sum as in the description on p. 17; the two differ only when marks coincide. An empty sum is 0. `continuationThreshold` is the literal infimum; it is used only for the given processes of Theorems 2.4 and 2.6, where it is consistent with the maximal-lifetime clauses. (R15 Q1; E1; AUD-1b §4.2; AUD-T2426C §3.2, §6) |
| Force points | p. 15 (configurations and weights); p. 35 (coincident points); pp. 42–43 (images under the Loewner flow) | `IsOrderedForceWord`, `forceBoundaryData`, `forceJumpSet`, `IsLeftForceImage`, `IsRightForceImage`; flow-line words `flowLineNL`, `flowLineNR`, `flowLineXL`, `flowLineXR`, `flowLineRhoL`, `flowLineRhoR` | G1. Boundary data at the centred positions V − W (Theorem 1.1). Geometric images by one infimum or supremum formula, for continuous drivers from 0 and marks on the correct side, proved equal to g_t(x) before x is swallowed and to the image of the extreme endpoint of ℝ ∩ K_t afterwards. (AUD-2 §4.4; AUD-T2426C §3.1) |
| Loewner chain, trace and the coupling of Theorem 1.1 | (1.6)–(1.7), p. 12; §2.1, p. 33; Theorem 1.1, pp. 17–18 | `QuantumZipper.fwdHull`, `.fwdMap`, `.logDerivFwd`; `IsFilling`, `IsGeneratingTrace`, `couplingMean`, `loewnerGreenEnergy`, `IsOptionalHullCoupling`, `Chart.tipSet` | G7. K_t is the set of points of ℍ swallowed by time t; driver, hull and trace are separate objects. arg f_t′ comes from the branch of log f_t′ vanishing at t = 0. For counterflows and staged pieces the physical points are radial limits lim_{y↓0} of the inverse maps at iy. The coupling predicate is described under Theorem 1.1. (AUD-1b §4.7–§4.8, §6.5; AUD-2 §4.7, §4.8, §4.13; AUD-4 §4.1) |
| Flow lines of angle θ | Definition, p. 18; "flow line of angle θ", p. 19 | `IsFlowLine`, `IsFlowLineDriver`, `IsTranslateAddConst`, `sleLambda` | In ℍ from a real point x, through the chart z ↦ z − x (derivative argument 0): the field h(· + x) + θχ; the force word read off b, namely seed marks 0⁻ and 0⁺ of weights −(b(x⁻) + θχ)/λ − 1 and (b(x⁺) + θχ)/λ − 1 (kept even when 0) and a mark at y − x of weight (b(y⁺) − b(y⁻))/λ for each genuine jump y; an integrated evolution of that word coupled with the field as in Theorem 1.1; and η − x its generating trace on [0, ζ]. ζ is the available lifetime, and every curve with these properties counts. Flow lines in other domains appear only inside staged histories, through charts. (AUD-3 §1, §3.5, §3.6) |
| Counterflow lines | Definition, pp. 19–20 | `IsCenteredCounterflowDriver`, `infinitySourceChart`, `IsChartTransport` (version 2), `Chart`, `Chart.id`, `Chart.recenter`, `Chart.loewner`, `counterflowCompletedRange` | Only from ∞ to 0 in ℍ, in the centred frame with the lift −2 Log z (Theorem 1.4, item 2); the parameter field's boundary data are existential; the completed range omits ∞. In component charts the same predicate is applied to the transported field. (spec FD11.1–FD12.5; AUD-4 §4.1, note N4; AUD-4b §1.4; version 2: R32) |
| Light cones and staged histories | angle-varying flow lines and the light cone, p. 100; Proposition 5.9, p. 104; §7.4.3, p. 163 | `Instr`, `ExplSpec`, `ExplStatus`, `ExplState` and its steps `ExplState.init`, `.heights`, `.IsAdmissibleSeed`, `.launch`, `.moveAlong`, `.moveToEnd`, `.contStep`, `.flowStep`, `.step`, `.run`, `.physSet`; `pastSigma`, `IsStagedHistory`, `StagedPiecesRegular`, `scheduleProgram`, `IsSchedule`, `lowerArcRoots`, `boundaryLightConeFamily`, `IsBoundaryContinuedProgram` | Programs with deterministic switch times in each piece's own capacity clock, where the paper's angle-varying flow lines use stopping times; boundary continuation after a threshold (GW2a), which the paper does not describe; in the GW2 family a history is kept only up to its first threshold; each piece is characterized by its regular conditional law given the retained history; realizations are universally quantified, with the regularity hypothesis of R51; only histories with angles in [−π/2, π/2] are constrained. (Theorem 1.4, items 4–10; AUD-4 §4.2–§4.4) |
| Boundary walks | p. 26; Figure 7.22, p. 164 | `boundaryWalkSpec`, `rightSideOf`, `leftSideOf`, `ExplState.physSet` | The walk is the program of (number of jumps + 1) rounds of [flow at the extreme angle through the available lifetime; continue along ℝ], restarting at the first later original jump at which the angle's seed is admissible (GW1): the algorithm of Figure 7.22 with its restart point specified. The sides of a set A are defined through the components of ℍ ∖ A whose closure meets the positive (or negative) real axis outside A. (spec GW1, p. 618; AUD-4 §4.4) |
| Component charts and kernels | Proposition 7.30, p. 163 (conditional law given both boundaries, nowhere boundary filling) | `betweenComponents`, `IsComponentChart`, `IsComponentBoundaryData`, `IsComponentTraversal`, `ExplState.ordinarySet` | The paper has no general definition; the Lean follows GW3–GW4 (spec pp. 636–637). Components of ℍ ∖ (R ∪ L) neither right of R nor left of L; a chart is a conformal bijection C → ℍ whose inverse has boundary limits on R at positive reals and on L at negative reals, with a continuous branch of the argument of its derivative (charts differ by scalings; the branch is pinned by the boundary word); the boundary word is −Λ or +Λ on ordinary pieces and the original values on connectors; the traversal is a continuous increasing time change that matches the tips. (AUD-4b §1.2, Q1, Q2) |
| Interaction of two curves | Theorem 1.5, p. 30 | `seedRayClosure`, `closedLeftSide`, `IsProperCompletion`, `HasOrderedProperCompletions`, `IsInteriorAvailableContact`, `IsFirstContact`, `AgreeAsCurvesAfter`, `unboundedPart`, `activeDomain`, `IsActiveChart`, `CrossesFromRightAt` | Theorem 1.5 uses "stays to the right", "intersect", "merge" and "cross" without a formal definition; the Lean follows the specification's W0, W5 and Theorem 7.12C (pp. 528, 533, 461, 542), as described under Theorem 1.5. (AUD-3 §3.7–§3.14) |
| Filtrations, local martingales, conformal radius | Theorem 1.1, p. 18; Theorem 2.4, p. 43; Theorem 2.6, p. 52 | `killedDrivingSigma`, `IsMeasurableKilledDriving`, `killedDrivingFiltration`, `drivingFiltration`, `usualAugmentation`, `nullSigma`, `IsContLocalMartingaleBefore`, `IsConformalRadius` | The driving filtration is generated by the killed events {r < ζ, (W_r, V_r) ∈ A} and augmented with the measurable null sets and right limits. Local martingales before a random time use localizing times equal to 0 or strictly below it. The conformal radius is the relation r = |φ′(0)|. (AUD-2 §4.1–§4.2; AUD-T2426C §3.3–§3.4) |

## 3. What is not formalized

### 3.1 The fan statements: Proposition 7.33 and Theorem OT1 (rulings R16, R17)

The paper states that the fan, the union of the flow lines from the starting point with fixed angles in [−π/2, π/2],
is almost surely a strict subset of the range of the counterflow line (Figure 1.12, p. 21; Figure 1.16, p. 26;
Figure 1.18 (d), p. 28). Its Proposition 7.33 (p. 167), for strip data without boundary intersection, asserts that
P[η′(τ′) ∈ F] = 0 for every stopping time τ′ of the counterflow line with η′(τ′) ≠ 0 almost surely, where F is the
closure of the fan, so that F has Lebesgue measure zero. The specification's paragraph "Fan statements" after
Theorem 1.5 (spec p. 5) keeps Proposition 7.33 (spec p. 426) with an added hypothesis, that the tip η′(τ′) is an
interior point and fresh, η′(τ′) ∉ η′([0, τ′)); its Theorem OT1 (spec pp. 666–667) disproves the extension without
freshness in the specification's centred coupling. That correction belongs to the errata document. Neither statement
is formalized: R16 removed Theorem OT1 from the targets (it alone needs the interior flow lines of Imaginary
Geometry IV), and R17 limited the targets to the main theorems, leaving out Proposition 7.33 and the fan statements.

### 3.2 The Markov sentence of Theorem 2.2

"Under this law, the values W_t, B_t, and V_t^{i,q} taken together are a continuous multidimensional Markovian process
indexed by t" (p. 40) was not part of the original frozen statements. It was added after the external audit as
`exists_strongMarkovKernel_isIntegratedSLEEvolution`. (R15 Q4; R17; R122)

### 3.3 Other claims of Sections 1 and 2

Sections 1.1 and 1.2 are an overview and background. The other claims of §§1.3, 1.4 and 2 that are not among the 17
statements are these.
- p. 17: the continuation threshold is almost surely infinite if and only if every partial sum of weights on each side
  exceeds −2 (the specification's precise form is Lemma GW0, p. 617).
- pp. 18–20: flow lines and counterflow lines in general simply connected domains. Only the forms in ℍ are frozen;
  other domains enter through charts inside staged histories and component kernels.
- pp. 20–22, the outline of the proofs, for example that the conditional law of η given η_{θ₁} and η_{θ₂} is
  SLE_κ(ρ^L(θ₁); ρ^R(θ₂)) independently in the components between them.
- p. 21, Figure 1.12: Duplantier duality, i.e. the flow lines of angles −π/2 and π/2 merge into the right and left
  boundaries of η′, is covered by `boundaryWalks_frontiers` in the setting of Theorem 1.4; that each flow line of
  angle θ ∈ [−π/2, π/2] lies in the range of η′ follows from the second part of
  `completedRange_eq_closure_lightCone`. The fan statement of the same caption is §3.1.
- p. 25, Figure 1.15: SLE_64(ρ₁; ρ₂) processes are boundary filling only when ρ₁, ρ₂ ≤ 28.
- p. 26: when η′ fills boundary segments, "η_L and η_R hit their continuation thresholds before reaching ∞"; the rest
  of that sentence (they extend to the entire boundaries, Figure 7.22) is covered by `boundaryWalks_frontiers`.
- p. 27: the right (left) boundary of any SLE_{16/κ}(ρ′) process from ∞ to 0 is the flow line of angle −π/2 (π/2).
  `boundaryWalks_frontiers` covers this, in the walk form, for counterflow lines of fields with finite
  piecewise-constant boundary data that almost surely do not hit their continuation threshold.
- p. 28, Figure 1.18: the conditional law of η′ given the zero-angle flow line (independent SLE_6(−3/2) processes).
- p. 29: the conditional law of η′ given η_L or η_R alone, and given the boundaries of its parts before and after it
  hits a boundary point (Proposition 7.31, p. 164). The conditional law given both walks is `componentKernels`.
- p. 29, Figure 1.19: hitting properties of the flow lines of angles π and −π started from a point of a flow line.
- pp. 30–31, Figure 1.20 and the text after Theorem 1.5: the conditional law of one flow line given another.
- p. 32: the regime θ₁ ≥ θ₂ + π, which the paper does not explore.
- p. 33, §2.1: background on SLE_κ (existence of the trace, the filling); pp. 33–34: Bessel processes and the
  one-force-point construction (2.3).
- pp. 35–40: the argument that Conditions 1–3 of Definition 2.1 imply the integrated equations (the Lean definition
  is the integrated form).
- p. 42, Remark 2.3: if every partial sum is at least κ/2 − 2, the driver does not hit the force points and the
  process is continuous. The continuity is a case of Theorem 1.3; the non-collision claim is not stated.
- p. 43, after Theorem 2.4: a curve with a continuous driving function does not trace itself or ∂ℍ and does not enter
  the bounded components it draws (Proposition 6.12).
- p. 50, Lemma 2.5: for such a curve the set {t : η(t) ∈ ℝ} has Lebesgue measure zero.

## 4. Numbering

Lean names are in the namespace `InteractingSLE`; "spec" pages refer to the specification.

| Paper result | Paper page | Spec page | Lean |
|---|---|---|---|
| Theorem 1.1 | 17–18 | 9 | `exists_isOptionalHullCoupling`; companion `existsUnique_isBoundedHarmonicExtension_forceBoundaryData` (spec p. 9) |
| Theorem 1.2 | 20 | 4 | `exists_measurable_lifetime_trace_eq_comp_field` |
| Theorem 1.3 | 22 | 4 | `IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace` |
| Theorem 1.4 | 22 | 4–5; GW1 618, GW2 621, GW2a 623, GW3 636, GW4 637, GW6 643 | `IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`, `IsCenteredCounterflowDriver.boundaryWalks_frontiers`, `IsCenteredCounterflowDriver.componentKernels`, `IsCenteredCounterflowDriver.boundaryWalks_outerBoundaries` (added after the external audit); companion `exists_isStagedHistory` (spec p. 618) |
| Theorem 1.5 | 30 | 5; W0 528, W5 533, Theorem 7.12C 461 and 542 | `IsFlowLine.stays_right_of_lt` (i), `IsFlowLine.merges` (ii), `IsFlowLine.crosses_of_lt` (iii); at every contact: `IsFlowLine.merges_of_contact`, `IsFlowLine.crosses_of_lt_of_contact` (added after the external audit); companions `exists_isFlowLine`, `IsPiecewiseConstantBoundaryData.existsUnique_isBoundedHarmonicExtension` (spec p. 5) |
| Definition of a flow line | 18–19 | 10–11 | `IsFlowLine`, `IsFlowLineDriver` |
| Definition of a counterflow line | 19–20 | 11–12; frames FD11.1–FD12.5, 12–17 | `IsCenteredCounterflowDriver`; the paper's literal definition: `IsLiteralCounterflowDriver`, with the bridge `AuditFix.literalCounterflowBridge_holds` (supplementary) |
| Definition 2.1 and the continuation threshold | 35 | 20, 3 | `IsIntegratedSLEEvolution`, `IsIntegratedSLEPath`, `ForceWord.ThresholdCondition`, `continuationThreshold` |
| Theorem 2.2 | 40 | 21 | `exists_isIntegratedSLEEvolution`, `IsIntegratedSLEEvolution.measure_killedState_eq`; the Markov sentence: `exists_strongMarkovKernel_isIntegratedSLEEvolution` (added after the external audit) |
| Remark 2.3 | 42 | 32 | not formalized |
| Theorem 2.4 | 43 | 34–35 | `exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore` |
| Lemma 2.5 | 50 | 38 | not among the frozen statements |
| Theorem 2.6 | 52–53 | 40 | `exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius` |
| Proposition 5.9 | 104 | 139 | not among the frozen statements; named on p. 22 as a precise version of Theorem 1.4 |
| Proposition 7.30 | 163 | 421 | not among the frozen statements; its law is the (d, d) case of `componentKernels` |
| Proposition 7.33 | 167 | 426 | not formalized (R16, R17) |
| (none) | — | Theorem OT1, 666–667 | not formalized (R16, R17) |
| claim on p. 17 | 17 | Lemma GW0, 617 | not among the frozen statements |
