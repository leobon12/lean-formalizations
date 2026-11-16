# Imaginary geometry I: the formal target in one page

This page states the eight main theorems of Miller–Sheffield, *Imaginary geometry I* (arXiv:1201.1496v2), as they are
formalized, in the paper's notation. Each item names its frozen Lean declarations; all are in the namespace
`InteractingSLE`, with files in `InteractingSLE/Frozen/Spec/`. The [correspondence](CORRESPONDENCE.md) and the
[errata](ERRATA.md) give the details and the sources of every reading below.

## Conventions used by every statement

- **Domain.** Every field and curve lives on ℍ = {z : Im z > 0}. Other domains enter only through conformal charts.
- **Boundary data.** Finite piecewise-constant data b: b is locally constant off a finite set, so it has finitely many
  jumps; its values at the jumps are never read.
- **Parameters.** λ = π/√κ, χ = 2/√κ − √κ/2, κ′ = 16/κ, Λ = λ − (π/2)χ = π√κ/4 (the paper's λ′).
- **κ.** κ is an arbitrary real in the definitions; κ > 0, and κ < 4 where flow lines occur, is a hypothesis of each
  theorem.
- **Force words.** Left marks x_{n,L} ≤ … ≤ x_{1,L} ≤ 0 and right marks 0 ≤ x_{1,R} ≤ … ≤ x_{m,R} with arbitrary real
  weights. A left mark at 0 is 0⁻ and a right mark at 0 is 0⁺. Coincident marks stay separate and their weights add.
- **Centred force points.** The force data are taken at the centred positions V̂_t = V_t − W_t, with V̂ = 0 for 0⁻ and
  0⁺ ([errata A5](ERRATA.md)).
- **Harmonic extensions.** "The harmonic extension" is read as "every bounded harmonic extension". Companion theorems
  prove that one exists and that any two agree on ℍ.
- **GFF.** A field is a measurable random distribution on ℍ (cylinder σ-algebra). h has data b if h − m is a
  zero-boundary GFF for every bounded harmonic extension m of b, with the Dirichlet normalization (2π)⁻¹ ∫ ∇f · ∇g.
- **SLE_κ(ρ) (Definition 2.1).** `IsIntegratedSLEEvolution`: the integrated form of the equations,
  W_t = √κ B_t + Σ ∫₀ᵗ ρ/(W_s − V_s) ds and V_t = x + ∫₀ᵗ 2/(V_s − W_s) ds for t < ζ. The side order holds, each
  1/(W − V) is integrable on compact intervals before ζ, and collision times have measure zero.
- **Lifetime.** ζ is the continuation threshold T∗ read as the maximal lifetime: the state is admissible before ζ;
  ζ = 0 exactly when the seed is inadmissible; if 0 < ζ < ∞, no limit of the state at ζ from below is admissible
  ([errata A4](ERRATA.md)).
- **Filtrations.** An evolution may use any filtration in which B is a Brownian motion and W, V are adapted before ζ.
- **Traces.** A continuous generating trace η of W on [0, T] has η(0) = 0, is continuous on [0, T], and ℍ ∖ K_t is
  the unbounded component of ℍ ∖ η([0, t]) for every t < T.
- **Flow lines.** `IsFlowLine`: η is a flow line of angle θ from x ∈ ℝ with available lifetime ζ if an integrated
  evolution of the flow-line force word of (b, x, θ), coupled with h(· + x) + θχ as in Theorem 1.1, has η − x as its
  continuous generating trace on [0, ζ]. Every such curve counts, not only "the" flow line.
- **Counterflow lines.** `IsCenteredCounterflowDriver`: η′ = CF_d(h) runs from ∞ to 0. In the chart R(z) = −1/z with
  lift −2 Log z, it is the angle-0 flow line at parameter κ′ of −h∘R + πχ − 2χ arg w. So
  CF_d(h) = CF_lit(h + πχ) ([errata A2](ERRATA.md)).
- **What the frame changes for angles.** In this frame the boundaries of η′ are the flow lines of h of angles ±π/2,
  as in the paper's figures; with the printed definition the angles are off by π, whatever branch is chosen.
- **Completed range.** The range of η′ is the set of its tip points together with the terminal point 0. The initial
  point ∞ is left out of every set compared with it.

## The eight theorems

### Theorem 1.1: coupling of SLE_κ(ρ) with the GFF

- For κ > 0 and every ordered force word there are a probability space, a filtration, an integrated SLE_κ(ρ)
  evolution (W, V, B) with lifetime ζ, and a field h, such that h − 𝔥₀ is a zero-boundary GFF.
- For every stopping time τ < ζ of the usual augmentation (𝓕_t) of the filtration of (W, V) killed at ζ: K_τ is a
  local set of h, and for every test function φ, almost surely on {supp φ ∩ K_τ = ∅},
  E[exp(i(h, φ)) | 𝓕_τ] = exp(i(𝔥_τ, φ) − ½ E_τ(φ)), with 𝔥_τ = 𝔥⁰_τ∘f_τ − χ arg f_τ′ and E_τ the Green energy in
  the chart f_τ.
- Declarations: `exists_isOptionalHullCoupling`; companion `existsUnique_isBoundedHarmonicExtension_forceBoundaryData`.

Differences from the printed paper:
- Boundary data at the centred force points ([errata A5](ERRATA.md)).
- arg f_t′ is the branch of log f_t′ that vanishes at t = 0.
- The conditional law is stated by conditional characteristic functions of single test functions, the form the
  specification's proof establishes; the null set may depend on τ and φ.
- "There exists a coupling" is the existence of one probability space carrying evolution and field; this is
  equivalent by the uniqueness in law of Theorem 2.2.

### Theorem 1.2: the field determines the curve

- For κ > 0, an ordered force word and every coupling satisfying the conclusion of Theorem 1.1, there is a measurable
  Φ from distributions on ℍ to [0, ∞] × (paths [0, ∞) → ℂ) with, almost surely, Φ(h) = (ζ, t ↦ η(min(t, ζ))) for
  every continuous generating trace η of W on [0, ζ].
- Declaration: `exists_measurable_lifetime_trace_eq_comp_field`.

Differences from the printed paper:
- "Determined by h" is "almost surely equal to a measurable function of h"; the determined object is the pair of the
  lifetime and the curve stopped at it. Existence of the trace is Theorem 1.3.

### Theorem 1.3: continuity and transience of the trace

- For a > 0, an ordered force word and every integrated SLE_a(ρ) evolution with lifetime ζ, on any filtered
  probability space, almost surely: an inadmissible seed gives ζ = 0; W has a continuous generating trace η on [0, ζ];
  and |η(t)| → ∞ when ζ = ∞.
- Declaration: `IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`.

Differences from the printed paper:
- Stated for every integrated evolution, not for "η ∼ SLE_κ(ρ)"; this is stronger, and all of them have the law of
  Theorem 2.2.

### Theorem 1.4: light cone, frontiers and component laws

- **Setting.** 0 < κ < 4; finite piecewise-constant b; a standard Borel probability space carrying a GFF h with data b;
  η′ = CF_d(h) with ζ′ = ∞ almost surely; and every realization E of the staged histories with angles in
  [−π/2, π/2] satisfying `IsStagedHistory` and `StagedPiecesRegular`.
- **Light cone.** For every countable dense Θ ⊂ (−π/2, π/2) there is a countable dense Q ⊂ (0, ∞) such that, for every
  E, almost surely the completed range of η′ equals the closure of {0} ∪ the GW2 family (finite Θ-schedules from 0
  with switch and terminal times in Q, each kept through its first threshold, plus the forced boundary roots).
  Adding the physical sets of any fixed countable collection of histories from 0 with angles in [−π/2, π/2] gives
  almost surely the same closed set.
- **Light cone, prescribed switching times.** Both identities hold for every deterministic countable dense
  Q ⊂ (0, ∞) fixed in advance, for instance the positive rationals.
- **Frontiers.** Almost surely the right walk R lies in the range with no point of the range strictly to its right,
  and likewise the left walk L on the left. If the range meets ℝ in a set with empty interior, the first piece of each
  walk has infinite lifetime.
- **Outer boundaries.** If the range K meets ℝ in a set with empty interior, almost surely each walk is a single
  complete flow line, R = frontier(rightSideOf K) ∩ K, L = frontier(leftSideOf K) ∩ K, and R ∪ L is the outer boundary
  of K.
- **Component kernels.** Given both walks, each component C between them carries, in its chart, a GFF with boundary
  word −Λ on R, +Λ on L and the original values on connectors; η′ traverses C as the centred counterflow of that field;
  and the pairs for different components are conditionally independent.
- Declarations: `IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`,
  `IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone_of_schedule` (prescribed switching times),
  `IsCenteredCounterflowDriver.boundaryWalks_frontiers`, `IsCenteredCounterflowDriver.boundaryWalks_outerBoundaries`,
  `IsCenteredCounterflowDriver.componentKernels`; companion `exists_isStagedHistory`.

Differences from the printed paper:
- Switching times:
  - `completedRange_eq_closure_lightCone_of_schedule` holds for every countable dense set. That includes the paper's
    positive rational times (p. 100), and the countable sets among Proposition 5.9's dense time sets (p. 104).
  - The original anchor `completedRange_eq_closure_lightCone` asserts the identity only for some set chosen after the
    law.
- η′ is the centred counterflow CF_d(h) = CF_lit(h + πχ) ([errata A2](ERRATA.md)). The supplementary
  `AuditFix.literalCounterflowBridge_holds` restates the three conclusions for the literal counterflow line of h + πχ.
- The GW2a addition clause, with boundary continuation along ℝ after a threshold, is from the specification; the
  paper does not describe boundary continuation.
- The paper is informal here (p. 22); the statements follow the specification's Corollary GW6, GW1–GW4.
- Angle-varying trajectories are staged histories with deterministic switch times in each piece's capacity clock,
  quantified over all realizations E; the companion shows such an E exists.
- The probability space is standard Borel, which regular conditional laws require.
- The frontier statement holds on every event, not only when η′ is nowhere boundary filling; "frontier" is read in
  the side-boundary sense.
- Forced boundary roots are used only when the lower seed (angle −π/2) is inadmissible on the right
  ([errata B3](ERRATA.md)).
- The component-kernel statement is an addition of the specification (GW4), not in the paper's Theorem 1.4.

### Theorem 1.5: interaction of flow lines

- **Setting.** 0 < κ < 4; finite piecewise-constant b; a GFF h with data b; η₁ a flow line of angle θ₁ from x₁ with
  lifetime ζ₁, η₂ one of angle θ₂ from x₂ with lifetime ζ₂.
- **(i)** If x₂ ≤ x₁ and θ₁ < θ₂: almost surely, for all a < ζ₁ and c < ζ₂, η₁([0, a]) and η₂([0, c]) have ordered
  proper completions with η₂ on the left (W0).
- **(i), critical.** If moreover θ₂ − θ₁ ≥ πκ/(4 − κ): almost surely every common point η₁(s) = η₂(t) with s ≤ ζ₁,
  t ≤ ζ₂ is the common starting point (x₁ = x₂, s = t = 0) or terminal for both paths (s = ζ₁, t = ζ₂).
- **(ii)** If x₂ ≤ x₁ and θ₁ = θ₂: almost surely, after every contact η₁(s) = η₂(t) with s ≤ ζ₁, t ≤ ζ₂, the curves
  agree as ordered unparametrized curves until the shorter available portion ends.
- **(iii)** If x₂ < x₁ and θ₂ < θ₁ < θ₂ + π: almost surely, if there is a contact with s < ζ₁, t < ζ₂, the first
  contact is attained at one common point, η₁ crosses η₂ there from right to left and never crosses back, and no open
  arc of either outgoing path lies on the other.
- **(iii), critical.** If moreover θ₁ − θ₂ ≥ πκ/(4 − κ): almost surely every common point with s ≤ ζ₁, t ≤ ζ₂ is the
  first contact or terminal for both paths.
- Declarations: `IsFlowLine.stays_right_of_lt`, `IsFlowLine.merges`, `IsFlowLine.crosses_of_lt` (the original
  anchors, interior contacts only); `IsFlowLine.merges_of_contact`, `IsFlowLine.crosses_of_lt_of_contact` (every real
  or interior contact); `IsFlowLine.start_or_terminal_of_contact_of_critical`,
  `IsFlowLine.first_or_terminal_of_contact_of_critical` (critical clauses at every contact); companions
  `exists_isFlowLine` and `IsPiecewiseConstantBoundaryData.existsUnique_isBoundedHarmonicExtension`.

Differences from the printed paper:
- Merging and crossing hold at real contacts as well as interior ones, as in the paper's Proposition 7.12
  (`merges_of_contact`, `crosses_of_lt_of_contact`).
- The critical-angle clauses hold at every contact, with a point terminal for both paths allowed: two critical flow
  lines can end at a common real point almost surely ([errata A9](ERRATA.md)).
- "Their starting point" is read as the common one; a contact at an unshared starting point has probability zero
  when both lifetimes are positive.
- "Stays to the right" is ordering of strict pre-lifetime prefixes (Convention W0); the relation of the terminal
  limits is not included.
- (iii) assumes x₂ < x₁, as the specification does; for x₁ = x₂ the pair is covered by (i) with the curves exchanged.
- In (iii) the crossing is asserted at the first contact, which may be real and may precede the given contact; only
  the outgoing order is encoded.
- The sentences allowing bouncing are not assertions and are not formalized.

### Theorem 2.2: existence and uniqueness in law of SLE_κ(ρ)

- **Existence.** For a > 0 and every ordered force word there are a probability space, a filtration and an
  integrated SLE_a(ρ) evolution with its lifetime.
- **Uniqueness in law.** Any two integrated evolutions with the same data give the same probability to every event
  {t_j < ζ and (W, V^L, V^R, B)(t_j) ∈ A_j, j = 1, …, n}; so the laws of the state killed at ζ, and of ζ, coincide.
- **Strong Markov.** There is one time-homogeneous Q on finite-time cylinder events of the state such that Q at a
  state is the killed-state law of every evolution started there, and at every finite stopping time T the future
  killed state is distributed by Q at the state at time T.
- Declarations: `exists_isIntegratedSLEEvolution`, `IsIntegratedSLEEvolution.measure_killedState_eq`,
  `exists_strongMarkovKernel_isIntegratedSLEEvolution`.

Differences from the printed paper:
- The lifetime is the maximal lifetime, not the literal infimum, which admits spurious short lifetimes
  ([errata A4](ERRATA.md)).
- The Markov sentence is a strong Markov property on finite cylinders at finite stopping times. Q is measurable only
  on separated states. It is not packaged as a Mathlib `Kernel` or semigroup.
- The law depends on κ, which the paper's sentence does not list; the statement fixes it.

### Theorem 2.4: martingale characterization of SLE_κ(ρ)

- **Setting.** κ > 0, an ordered force word; almost surely W is continuous with W₀ = 0, η is a continuous generating
  trace of W on [0, ∞) in the closed half-plane with |η(t)| → ∞, and V is the geometric image of the marks.
- **Statement.** On some extension of the probability space, W, V and a Brownian motion form an integrated SLE_κ(ρ)
  evolution with lifetime T∗, if and only if, for every choice of extensions and every z ∈ ℍ, 𝔥_t(z) is a continuous
  local martingale before min(τ_z, T∗) in the usual augmentation of the filtration of η.
- Declaration: `exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore`.

Differences from the printed paper:
- The horizon is min(τ_z, T∗), not τ_z. As printed, the forward direction fails (κ = 4, W ≡ 0, one mark at 0⁺ of
  weight −3) ([errata A1](ERRATA.md)).
- "Can be coupled with a standard Brownian motion" means on a measure-preserving extension Ω′ → Ω.
- The curve stays in the closed half-plane; a curve allowed into the lower half-plane is not determined by its hulls.
- The filtration of the martingale side is named; the paper names it only in the proof.

### Theorem 2.6: one-point martingale characterization

- Same setting as Theorem 2.4; fix z ∈ ℍ and σ = min(τ_z, T∗).
- Suppose that 𝔥_t(z) is a continuous local martingale before σ and that there is a process A with
  A_t = log(crad(ℍ, z)/crad(ℍ ∖ K_t, z)) almost surely for t < σ, such that 𝔥_t(z)² − A_t is a continuous local
  martingale before σ.
- Then, on some extension, there is an integrated SLE_κ(ρ) evolution whose driver and force points agree almost surely
  with W and V before σ.
- crad(D, z) = |φ′(0)| for a conformal bijection φ of the unit disc onto D with φ(0) = z.
- Declaration: `exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius`.

Differences from the printed paper:
- The bracket is log(crad(ℍ, z)/crad(ℍ ∖ K_t, z)) with coefficient 1, not √κ times a Brownian motion; the factor √κ
  belongs to the rescaled function (2.12) ([errata A3](ERRATA.md)).
- The horizon of hypothesis and conclusion is σ = min(τ_z, T∗); the paper names only the swallowing time.
- The bracket is stated by its defining property, proved equivalent to the explicit Loewner form.

## Outside the scope

- The fan statements after Theorem 1.5: Proposition 7.33 and Theorem OT1.
- Public declarations for flow lines and counterflow lines in general simply connected domains; other domains enter
  only through conformal charts inside the proofs and the staged histories.
- Proposition 5.9 (p. 104), which the paper names as a precise version of Theorem 1.4, is not a frozen declaration.
