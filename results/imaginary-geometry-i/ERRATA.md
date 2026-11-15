# Errata: Miller and Sheffield, *Imaginary geometry I: interacting SLEs*

This note lists the errors in

> J. Miller and S. Sheffield, *Imaginary geometry I: interacting SLEs*, Probab. Theory Related Fields 164 (2016),
> 553–705, arXiv:1201.1496,

that came to light while its main theorems were formalized in Lean 4, together with related problems in the
specification the formalization was built from and in works that the specification cites.

## Scope

**Version checked.** arXiv:1201.1496v2 (27 February 2016), 173 pages. Page numbers ("p. 43") are pages of this PDF;
they coincide with the printed page numbers. The journal version was not compared.

**The formalization.** The formal statements were frozen from a 671-page mathematical specification of the paper,
prepared outside the project and cited here as "spec p. n". It keeps the paper's section and theorem numbers, writes
out the hypotheses on domains, force points, lifetimes, filtrations and field frames, and adds supplementary arguments
with their own labels (Aux. n, LP10, GW1–GW6, S1–S7, …). Theorems 1.1–1.5, 2.2, 2.4 and 2.6 and three companion
statements are proved in Lean from the three standard axioms. Where an item below changes a statement, the proved
statement is the corrected one.

**What is listed.**
- **A. Errors in the paper.** The claim or step is in arXiv v2; it is quoted and located. Some of these were already
  repaired by the specification, and this is said where it applies; the specification reproduces the others.
- **B. Errors of the specification.** Introduced by the specification, or contained in its supplementary arguments,
  and not present in the paper.
- **C. Cited works.** Gaps and slips in works that the specification cites.

**What is not listed.** False intermediate statements of the project's own proof plan and defects of its own formal
definitions, which were corrected by rulings and say nothing about the paper; true steps that a source asserts
without proof (the formalization supplies them, and the project records them as deviations, not errata); and repairs
that the specification makes to passages the project did not examine against the paper. Two examples of the last
kind: the specification states Theorem 1.5 (iii) only for x₁ > x₂, where the paper fixes x₁ ≥ x₂ for all three parts
(p. 30); and its supplement (spec pp. 450–451) replaces the "exact conditions" (5.4)–(5.5) of p. 101 by sufficient
conditions.

**Companion documents.** The specification is included in this release, in [`specification/`](specification/), and the
[correspondence](CORRESPONDENCE.md) lists every difference between the Lean statements and the paper. The
[result guide](README.md) gives the formal statements and how they were checked.

**Labels.** E… are entries of the project's errata ledger, R… its rulings and AUD-… its independent statement audits.
Other labels (ARCH-…, PROVE-…, SRC-…, GX-SPEC-…, GLOSSARY-…) are hand-offs of work packages. Supplementary notes
received during the project are cited as "Astra", with the ruling that adopted them and their section, for example
"Astra (R71) §1". These are development records; they are not part of the public release.

**Notation.** κ > 0, λ = π/√κ, χ = 2/√κ − √κ/2, κ′ = 16/κ and λ′ = π√κ/4 = λ − (π/2)χ. The g_t are the Loewner maps,
f_t = g_t − W_t, K_t the hulls and V_t the force points; T∗ is the continuation threshold, τ_z the time at which z is
swallowed, and C(z; D) the conformal radius of D seen from z.

## Summary

| Item | Location (arXiv v2) | Problem | Kind |
|---|---|---|---|
| A1 | Theorem 2.4, p. 43 | the martingale side must stop at T∗ | false as stated |
| A2 | Definition of counterflow lines, pp. 19–20; Theorem 1.4, p. 22 | the conformal definition is off by πχ from the normalization of the paper's figures and of Theorem 1.4 | imprecise statement (normalization) |
| A3 | Theorem 2.6, pp. 52–53 | spurious factor √κ | typo (wrong constant) |
| A4 | Definition 2.1, p. 35; Theorem 2.2, p. 40 | circular threshold; unspecified Markov property | imprecise statement |
| A5 | Theorem 1.1, p. 17 | uncentred force points in the boundary data | typo |
| A6 | Proposition 5.1, p. 99 | the no-wrap step misses two endings | gap in a proof |
| A7 | Lemma 6.2, pp. 112–113 | hypothesis applied at first-entrance times | imprecise statement; gap in a proof |
| A8 | Proposition 3.3, p. 57 | the closure of K must be excluded | imprecise statement |
| B1 | spec Lemma S5, p. 582 | the inside clause is false as printed | false as stated |
| B2 | spec pp. 3–4, 20–21, 37 | wording of Section 2 and Theorem 1.3 | imprecise statement |
| B3 | spec Theorem 1.4, GW2–GW4 | wording of the light-cone statements | imprecise statement |
| B4 | spec references | missing reference, wrong labels and page references, a notation clash | typos and notation |
| C1 | Zhan 2010, Theorem 6.1 (iii)–(iv) | endpoint clause not reached by its proof | gap in a proof |
| C2 | Zhan 2008 and 2010 | five formula slips | typo |
| C3 | Schramm–Wilson 2005, Theorem 3 | used beyond its stated scope (no error in it) | scope note |
| C4 | inputs of the SLE₈ note | Alvisio–Lawler and Johansson Viklund–Lawler | gap in a proof; typos |

## A. Errors in the original paper

### A1. Theorem 2.4: the martingale condition must stop at the continuation threshold

- **Where.** §2.3, Theorem 2.4, p. 43.
- **Printed.** W_t and the V_t "can be coupled with a standard Brownian motion B_t to describe an SLE_κ(ρ) process
  (up to the continuation threshold) if and only if h_t(z) evolves as a continuous local martingale in t for each
  fixed z ∈ H until the time z is absorbed by K_t."
- **Why it is wrong.** The left side constrains the curve only before T∗, the right side until τ_z. After a finite T∗
  the curve is arbitrary, so the "only if" direction fails. Example: κ = 4 (so χ = 0 and λ = π/2), W ≡ 0 (the vertical
  slit η(t) = 2i√t, with g_t(z) = √(z² + 4t)), and one right force point at 0⁺ of weight −3. The seed is
  inadmissible, so T∗ = 0, and the left side holds trivially once a Brownian motion is adjoined on an extension. The
  force point moves as V_t = 2√t, and h_t = h⁰_t ∘ f_t, where h⁰_t has boundary values −λ on (−∞, 0), λ on (0, 2√t) and
  −2λ on (2√t, ∞). Since f_t(iy) = i√(y² − 4t),

      h_t(iy) = −(3λ/π) arctan(√(y² − 4t) / (2√t)),

  which increases strictly from −3λ/2 to 0 on [0, τ_iy) = [0, y²/4). (Since arg f_t′(iy) = 0, the same example works for every κ.) A deterministic, continuous, strictly increasing
  process is not a local martingale. The forward half of the proof ("can be seen by applying Itô's formula", p. 43)
  uses (1.10), which holds only below T∗ ("We will only construct SLE_κ(ρ) for t below the continuation threshold",
  p. 35). The remark on p. 17 that all results hold "up until (and including) the continuation threshold" concerns
  SLE_κ(ρ) processes and does not override the explicit horizon of the theorem.
- **Kind.** False as stated (the "only if" direction).
- **Correction and formal treatment.** Require the martingale property before min(τ_z, T∗); both directions then hold.
  The frozen Theorem 2.4 has this horizon and is proved. The specification prints the paper's wording (spec
  pp. 34–35), but its proof says "All statements below are stopped strictly before the continuation threshold" (spec
  p. 35) and its Theorem 2.6 states the minimum (spec p. 40). The two statement audits classified the printed form
  differently: an imprecision resolved by a standing convention of the specification (spec p. 9; AUD-T2426A), or
  false as printed (AUD-T2426B). In the paper only the remark of p. 17 quoted above comes close to such a convention.
- **Records.** R109; AUD-T2426A §7 (a) and N1; AUD-T2426B F1; AUD-T2426C N1; PROVE-T2426-STMT (D1). There is no
  errata-ledger entry (see the last section).

### A2. Counterflow lines: the conformal definition is off by πχ from the normalization used in Theorem 1.4

- **Where.** Definition of counterflow lines and the Remark on branches, §1.3, pp. 18–20; Theorem 1.4, p. 22; Figures
  1.12 (p. 21), 5.1 (p. 94) and 7.23 (p. 165).
- **Printed.** A counterflow line of h is an SLE_κ′(ρ) coupled "with a GFF −h" as in Theorem 1.1 (p. 19). On other domains it is defined through a conformal map ψ, "a branch of
  arg ψ′ that is defined continuously", and the field h ∘ ψ⁻¹ − χ arg(ψ⁻¹)′ (pp. 18–20). The Remark on p. 19 says "In some sense, changing the branch of arg ψ′ is
  equivalent to adding a multiple of 2πχ to the boundary data", that boundary data given by figures "will avoid any
  'multiple of 2πχ' ambiguity", and "This remark also applies to the definition of counterflow line given below." Theorem 1.4, for the
  counterflow line η′ of h from ∞ to 0: "ηL [is] the flow line of h with angle π/2 starting at 0 and ηR the flow line
  of h with angle −π/2", and if η′ is nowhere boundary filling, ηL and ηR "are the left and right boundaries of η′".
- **Why it is wrong.** With this definition the angles are off by π, equivalently the field by πχ, whatever branch is
  chosen. Take for η′ a plain SLE_κ′ from ∞ to 0 with 2 < κ < 4, which is nowhere boundary filling. With ψ(z) = −1/z
  and arg ψ′ = −2 arg z + 2πn (n ∈ ℤ), the definition forces h to have boundary values a = −λ′ + 2π(1 − n)χ on ℝ₋ and
  b = λ′ − 2πnχ on ℝ₊. The law of η′ is invariant under the reflection z ↦ −z̄, which exchanges the left and right
  boundaries of η′ and maps the angle-θ flow line of h to the angle-(−θ) flow line of −h(−z̄), a field with boundary
  values −b on ℝ₋ and −a on ℝ₊. If ηL and ηR were the two boundaries, ηL would be a non-trivial curve and the
  angle-π/2 flow line of −h(−z̄) would have the same law as ηL. The law of a non-trivial flow line from 0 determines
  the boundary values of the field, so this needs (−b, −a) = (a, b), that is, a + b = 0. But a + b = 2π(1 − 2n)χ ≠ 0:
  a change of branch moves the heights by multiples of 2πχ and cannot produce the odd multiple of πχ that is needed.
  Coupling η′ with −h − πχ instead (branch n = 0) gives a = −(λ′ − πχ) and b = λ′ − πχ, and the obstruction disappears.
  This is the normalization the paper uses wherever it draws a counterflow line together with flow lines from its
  target. In Figures 1.12 and 5.1 the outer boundaries of η′ carry −λ and λ: the heights on the left side of the
  angle-π/2 flow line and on the right side of the angle-(−π/2) flow line, as the caption of Figure 1.12 says. The
  definition shifts these heights by an odd multiple of πχ. The strip data λ′ − πχ and −λ′ of Figure 7.23 (p. 165) make
  η′ an SLE_κ′(κ′/2 − 4; κ′/2 − 4), as its caption states, only in this normalization; the definition would need a
  half-integer branch. The hypotheses a′, b′ ≥ λ′ + πχ and a, b ≥ λ′ of Proposition 5.1 (p. 94) are the non-hitting
  conditions in it.
- **Kind.** Imprecise definition (normalization). For a counterflow line aimed at the starting point of the flow lines,
  the conformal definition of pp. 19–20 does not give the normalization of the paper's figures, and, contrary to the
  Remark on p. 19, no choice of branch repairs this. Read with the printed definition, the identification of the
  boundary flow lines in Theorem 1.4 fails; read in the normalization of the figures, which the Remark makes
  authoritative, it holds.
- **Correction and formal treatment.** The specification introduces the centred frame CF_d(h) = CF_lit(h + πχ),
  coupled with −h − πχ (FD11.1–FD11.4, spec p. 12). It notes that a change of branch "cannot replace c = 0 by
  c = −πχ", reads the paper's figures that combine an upward flow line with its reverse counterflow in this frame, and
  states Theorem 1.4 for CF_d(h) (spec p. 4). The formal Theorem 1.4 does the same: in the chart R(z) = −1/z with
  lift −2 Log z, η′ is the angle-0 flow line at parameter κ′ of −h ∘ R + πχ − 2χ arg w (FD12.5, spec p. 17). AUD-4
  checked this transport, including its boundary values b′(0⁺) = −b(−∞) + πχ and b′(0⁻) = −b(+∞) − πχ.
- **Records.** AUD-4 §1 and §4.1; AUD-4b; AUD-T14-R51; ARCH-4 (D5). No ruling or errata-ledger entry; the symmetry check and the comparison with Figures 1.12, 5.1 and 7.23 were made for this note.

### A3. Theorem 2.6: there is no factor √κ

- **Where.** §2.3, Theorem 2.6, pp. 52–53.
- **Printed.** "… for some fixed z ∈ H the correspondingly defined h_t(z) is given by √κ times a Brownian motion when
  time is parameterized by minus the log of the conformal radius. Then these processes describe an SLE_κ(ρ) evolution
  at least up to the first time that z is swallowed by the path."
- **Why it is wrong.** In the paper's normalization (λ = π/√κ, p. 15; Dirichlet product (2π)⁻¹ ∫ ∇f · ∇g, p. 53),
  h_t(z) is a standard Brownian motion in the time −log C(z; H ∖ K_t). The paper computes this itself in the proof of
  Theorem 1.1: dh_t(z) = Im(2/f_t(z)) dB_t and "d⟨h_t(z), h_t(z)⟩ = −dC_t(z)", where C_t(z) is "(up to an additive
  constant) the log of the conformal radius of H ∖ K_t viewed from z" (pp. 74–75). Lemma 6.4 (p. 113) has the same
  normalization for the variance of a conditional mean. With the printed factor the bracket would be κ times as large,
  so for κ ≠ 1 the hypothesis is not met by SLE_κ(ρ) itself, and the theorem does not characterize it. 
- **Kind.** Typo (wrong constant).
- **Correction and formal treatment.** The specification's Theorem 2.6 (spec p. 40) has
  ⟨h(z)⟩_t = log(C(z; H)/C(z; H ∖ K_t)), remarks that "no factor √κ occurs", and works up to min(τ_z, T∗). The paper's statement does not say until when the hypothesis is assumed; the specification
  assumes it, and concludes, only before min(τ_z, T∗). The frozen
  Theorem 2.6 states the bracket by its defining property (with A_t this log ratio, h_t(z)² − A_t is a continuous local
  martingale before σ = min(τ_z, T∗)) and is proved.
- **Records.** AUD-T2426A §7 (c) (normalization checked, "with no √κ factor"); AUD-T2426B F5; AUD-T2426C F5. No ruling
  or errata-ledger entry.

### A4. Definition 2.1 and Theorem 2.2: the continuation threshold, and the Markov sentence

- **Where.** §2.2, Definition 2.1 and the definition of the continuation threshold, p. 35; Theorem 2.2, p. 40.
- **Printed.** "We define the continuation threshold to be the infimum of the t values for which either
  Σ_{i : V_t^{i,L} = W_t} ρ^{i,L} ≤ −2 or Σ_{i : V_t^{i,R} = W_t} ρ^{i,R} ≤ −2. We will only construct SLE_κ(ρ) for t
  below the continuation threshold." Definition 2.1 describes an evolution "up to some stopping time". Theorem 2.2:
  "Definition 2.1 uniquely determines a joint law for W_t, B_t, and the V_t^{i,q} — each defined for all t up to the
  continuation threshold. Under this law, the values W_t, B_t, and V_t^{i,q} taken together are a continuous
  multidimensional Markovian process indexed by t."
- **Why it is imprecise.** (i) The threshold is computed from the state at and after the time at which the evolution
  stops being defined. Read literally, it admits evolutions with spurious short lifetimes, and the uniqueness in
  Theorem 2.2 fails. Example (κ > 2): two right force points at 0⁺ with weights −3 and 2 form one group of weight
  −1 > −2. In the evolution of Theorem 2.2 they stay together, the threshold is never reached, and W returns to the
  group at arbitrarily large times. Let T₀ be the first such return after time 1, keep the processes on [0, T₀], and
  afterwards let the point of weight −3 move with W while the other moves away continuously. Conditions 1–3 hold up to
  the stopping time T₀, and the literal infimum is T₀, because after T₀ the point of weight −3 is alone at W.
  (ii) In the last sentence neither the filtration nor time-homogeneity is specified, and the proof relies on it ("By scale invariance and the Markovian property", p. 41).
- **Kind.** Imprecise or ambiguous statement; the intended meaning (the maximal lifetime) is clear.
- **Correction and formal treatment.** The lifetime ζ is part of the data of a formal evolution, with maximality
  conditions: the state is admissible before ζ; ζ = 0 exactly when the seed is inadmissible; and if 0 < ζ < ∞, no limit
  of the state at ζ from below is admissible. Explosion at a finite ζ is excluded by a theorem (Aux. 3 of the
  specification), not by the definition. Theorem 2.2 is frozen as existence and as uniqueness in law of the state
  killed at ζ. The Markov sentence is not part of the frozen statements; it is used inside proofs only. The
  specification has the same definition of the threshold (spec pp. 3, 20).
- **Records.** E1, E5; R15 (Q1, Q4), R17; AUD-1b §6.1 and N1; ARCH-1 (D2, §9).

### A5. Theorem 1.1: the boundary data are written with uncentred force points

- **Where.** §1.3, Theorem 1.1, p. 17; Figure 1.11, p. 18.
- **Printed.** h⁰_t is "harmonic in H with boundary values −λ(1 + Σ_{i=0}^{j} ρ^{i,L}) if s ∈ [V_t^{j+1,L}, V_t^{j,L}),
  λ(1 + Σ_{i=0}^{j} ρ^{i,R}) if s ∈ [V_t^{j,R}, V_t^{j+1,R})", and h_t(z) = h⁰_t(f_t(z)) − χ arg f_t′(z).
- **Why it is wrong.** The V_t^{i,q} are the uncentred force points of (1.11), while h⁰_t is evaluated at
  f_t(z) = g_t(z) − W_t (p. 12). The breakpoints must be the centred points f_t(x^{i,q}) = V_t^{i,q} − W_t, as in
  Figure 1.11 and in the proof, which uses "f_t(x^{i,q}) = V_t^{i,q} − W_t" (p. 74). As printed, every jump of the
  boundary data is displaced by W_t.
- **Kind.** Typo.
- **Correction and formal treatment.** The specification writes the data at V̂_t = V_t − W_t, with the centred positions
  of 0⁻ and 0⁺ set to 0 (spec p. 9). The formal Theorem 1.1 uses these centred positions.
- **Records.** AUD-2 (transcription of Theorem 1.1). No ruling or errata-ledger entry.

### A6. Proposition 5.1: the no-wrap step misses two endings

- **Where.** §5.1, proof of Proposition 5.1, p. 99; Lemma 5.4, p. 97; outline of the proof, p. 95.
- **Printed.** "If this is not the case, then after time τ, η must wrap around (but not hit) η′(τ′) and then hit the
  right side of η′([0, τ′]) (recall that η almost surely does not hit the side of ∂_U S which lies to the right of
  z0)." The contradiction is then drawn from Lemma 5.4: η "cannot hit the right side of η′([0, τ′]) or the part of
  ∂_U S which lies to the right of z0 before it hits the left side of η′([0, τ′]), the part of ∂_U S which lies to the
  left of z0, or tends to ∞ after time τ_δ".
- **Why it is incomplete.** After passing around the tip, η can leave η′(τ′) on its left in two further ways, without
  touching the right side of η′([0, τ′]) or the part of ∂_U S to the right of z0. (i) It tends to the right end +∞ of
  the strip. The hypothesis (5.1) allows this (η "accumulates in ∂_U S or tends to ±∞", p. 95), and the application of Lemma 5.4 on p. 99 lists it as an alternative ("or tends to ∞ after time τ_δ"); the
  statement of Lemma 5.4 on p. 97 does not mention it. (ii) It runs up between the right side of the hull K′_τ′ and the part of ∂_U S to the right of z0,
  and ends at z0 itself, approached from the east. (The proof of Lemma 5.4 rests on Lemma 5.2, which excludes only hits of
  open boundary arcs, so it does not reach the single point z0.) Deterministic configurations of both kinds satisfy the conclusion
  of Lemma 5.4 while η′(τ′) lies strictly to the left of η, so the claimed contradiction does not follow. The
  proposition itself is not in doubt.
- **Kind.** Gap in a proof.
- **Correction and formal treatment.** Both endings must be excluded separately. (i) Almost surely the flow line does
  not end at the right strip end, by the endpoint classification of strip flow lines (Aux. 22 of the specification).
  (ii) An excursion of η away from the hull, started at a rational time at positive distance from it, cannot end on an
  exposed eastern side of the hull, at the eastern access to z0, or on ∂_U S to the right of z0 (Astra (R71)
  follow-up 4 §1; a repair by a Cameron–Martin comparison through the endpoint is Astra (R53) part C). The formal
  proofs do not use the printed step: they either supply both endings in this way or argue from the counterflow line,
  which ends at a finite point where the side of approach is visible. The specification reproduces the printed step
  (spec p. 135).
- **Records.** R45, R50, R53 (C), R71 (1); PROVE-SEC5-K, PROVE-SEC5-P.

### A7. Lemma 6.2: the locality hypothesis is applied at first-entrance times

- **Where.** §6.1, Lemma 6.2 and its proof, pp. 112–113.
- **Printed.** Hypothesis 1: "η_i([0, τ]) is a local set for h for every η_i-stopping time τ"; τ_j is "a stopping time
  for the filtration F_t^j generated by η_1|[0,τ_1], …, η_{j−1}|[0,τ_{j−1}] and η_j(s) for s ≤ t". The proof lets
  τ_j^U be "the infimum of times in which η_j is in U", claims that η_j([0, τ_j^U]) is determined by h_{U^c}, and that
  "{τ_j ≤ τ_j^U} is almost surely determined by A_{j−1} and h_{U^c}".
- **Why it is incomplete.** (i) For an open U and the natural filtration of a continuous path, τ_j^U is in general only
  an optional time: the path can touch ∂U at time t and enter U immediately afterwards, so {τ_j^U ≤ t} is not determined
  by the path up to t. Hypothesis 1 is thus applied outside its scope, unless it is read for stopping times of the
  right-continuous filtration. (ii) The step on {τ_j ≤ τ_j^U} needs τ_j to be a stopping time of the natural filtration
  (Galmarino's test), as printed; it fails for right-continuous stopping times. For example, let τ_j be the first
  entrance time of an open set U′ disjoint from U, for a path that touches a common boundary point of U and U′ at time τ_j^U and enters U immediately afterwards:
  whether it also enters U′ immediately, which decides whether τ_j ≤ τ_j^U, is not determined by the path up to τ_j^U. (iii) The same step needs the stopped paths, while hypothesis 1 controls only their ranges. The specification
  already states the hypothesis for the stopped history (spec p. 155); points (i) and (ii) remain in it.
- **Kind.** Imprecise statement (the filtration in hypothesis 1 is not specified), and a gap in the proof.
- **Correction and formal treatment.** The formal version uses the locality hypothesis only at first-entrance times,
  which are stopping times of the right-continuous filtration. It takes the τ_j as path functionals with Galmarino's
  property, which is how the applications define them.
- **Records.** R37, R34; PROVE-SEC6-A2, PROVE-SEC6-A3.

### A8. Proposition 3.3: the closure of K must be excluded

- **Where.** §3.1, Proposition 3.3, p. 57.
- **Printed.** For "a deterministic closed subset of D", "a.s. lim_{D∖K ∋ z → z0} h1(z) = 0 for all z0 ∈ ∂D ∖ K". The
  proof begins: "Let U be a simply connected neighborhood of z0 such that the distance from U to K is positive."
- **Why it is imprecise.** If K is only relatively closed in D, a boundary point in the Euclidean closure of K has no
  such neighbourhood, and the conclusion can fail there. For D = H and K = {iy : 0 < y ≤ 1}, the centred Gaussian
  variable h1(x + iy) has variance
  log(C(x + iy; H)/C(x + iy; H ∖ K)), which tends to ∞ as x + iy → 0 with x/y → 0. The statement should exclude the
  closure of K. The paper's own use (proof of Proposition 3.8, p. 70) concerns only points at positive distance from
  the set.
- **Kind.** Imprecise statement.
- **Correction and formal treatment.** The specification states the limit for z0 ∈ ∂D outside the closure of K (spec
  p. 44), and the formalization uses this form.
- **Records.** Astra (R35) §6, item 3; R35.

## B. Errors introduced by the specification

### B1. Lemma S5: the inside clause is false as printed

- **Where.** Specification, supplement, Lemma S5 (one-sided physical gluing), spec p. 582; proof, spec pp. 582–583.
- **Printed.** "If the whole actual second prefix is contained in K_A, the same conclusion holds for every available
  own-domain extension of A, without constructing a nonempty second relative flow."
- **Why it is wrong.** The clause puts no condition on how the prefix moves inside K_A, but the proof treats only a
  prefix that "stops before the exit at L" (last paragraph, spec p. 583). A prefix contained in K_A that runs along the
  real base through L and then up an edge of A violates the conclusion; this counterexample is proved in Lean.
- **Kind.** False as stated (missing hypothesis).
- **Correction and formal treatment.** Add the hypothesis that the prefix does not visit L before its end. The
  corrected clause is derived from Lemma S2 and is the form that SB3 uses. Lemma S5 has no counterpart in the paper.
- **Records.** R49; PROVE-T14-SB3 (the counterexample), PROVE-T14-SB2 (the transcription).

### B2. Section 2 and Theorem 1.3: wording

- **"a Brownian motion B in their joint filtration"** (spec pp. 3, 20). The filtration must be that of (W, V, B),
  since B is continued independently after T∗ (spec pp. 22, 25). The paper is explicit:
  F_t = σ(B_s, W_s, V_s^{i,q} : s ≤ t) (p. 35). (E3.)
- **"the strong-solution clause in Definition 2.1"** (spec p. 37, proof of Theorem 2.4). The specification's
  Definition 2.1 (spec p. 20) has no such clause; strong solvability is listed among the derived properties (spec
  p. 21). In the paper, Condition 1 of Definition 2.1 does contain it (p. 35). (E2.)
- **"The canonical integrated SLE_a(ρ) evolution"** (spec p. 4, Theorem 1.3) is not defined; it means the law fixed by
  Theorem 2.2. The paper writes "η ∼ SLE_κ(ρ)" (p. 22). The formal Theorem 1.3 is stated for every integrated
  evolution, which is stronger. (E4.)
- **Kind.** Imprecise statements. **Formal treatment.** A formal evolution may use any filtration in which B is a
  Brownian motion, which gives the same theorems; strong solvability is derived; Theorem 1.3 holds for every evolution.
- **Records.** E2, E3, E4; R15 (Q2, Q4); ARCH-1 §9; AUD-1b.

### B3. Theorem 1.4 and GW2–GW4: wording of the light-cone statements

- **The forced roots** (spec p. 5, Theorem 1.4): "When an initial ordinary seed is inadmissible, include the forced
  original-boundary connectors … as in GW2." GW2 (spec p. 621) adds these roots only when the lower extreme seed, of
  angle −π/2, is inadmissible on its right; under the theorem's no-threshold hypothesis no other case occurs. The
  statement should name that seed.
- **GW2.** The clock of the "times in Q" is not named; it is the own capacity clock of the concatenated history, which
  agrees with the half-plane capacity clock. Q ⊂ (0, ∞) is needed but stated only in Proposition 5.9. A prescribed
  switch at exactly a threshold time is not addressed (it is read as not performed).
- **Undefined terms.** "Frontier" is not defined; GW4's proof uses it in the side-boundary sense. The "complete
  finite-word kernel" of GW4 and Theorem 1.4 is not defined as a law. GW3's normalization of the common-lift chart is
  stated only in its proof (spec p. 636), and Λ = λ − (π/2)χ is used without a local definition.
- **Kind.** Imprecise statements. **Formal treatment.** Each reading is recorded in the frozen statements and was
  checked by the audits (for example, forced roots only for the lower seed).
- **Records.** ARCH-4 §9 (Q5, E1–E5); ARCH-4b §9 (E-a–E-c); AUD-4 (N9; §8); AUD-4b §4.

### B4. References, cross-references and notation

- Schramm–Wilson, *SLE coordinate changes*, is cited at Corollary BR2 (spec p. 607) with title, theorem number and URL,
  but is missing from the reference list (spec p. 671). (E13; SRC-SW05.)
- The paper's Proposition 7.11 is called Theorem 7.11 in the specification but is still cited as "Proposition 7.11"
  elsewhere (spec pp. 218, 380 (Proposition 7.23), 576). (GX-SPEC-08.)
- Page references in the supplement point to old page numbers: "original pages 414–417" (proof of LP11, spec p. 488;
  the induction meant is on spec pp. 378–380) and "original pages 67–68" (spec p. 489; the force-point endpoint
  identities are on spec pp. 39–40). Theorem LP10 (spec p. 486) lists "Aux. 108–111" among its premises, although
  Aux. 109 is stated only for 0 < κ < 4 and LP10 concerns k > 4; the records do not settle whether LP10 needs a
  large-parameter analogue of Aux. 109. (GX-SPEC-05.)
- Notation: in BR4a (spec p. 610), χ_k = 2/√k − √k/2 is χ evaluated at the parameter k of the field there, which for
  k = κ′ is −χ; the formulas are consistent, but the clash with χ invites errors; "LaterContact" in G6
  (spec p. 495) is never defined; Theorem 7.12C is printed in a short form (spec p. 460) and a full form (spec p. 542);
  Aux. 114 and Aux. 116 are not printed (numbering gaps). (GLOSSARY-C, SRC-08.)
- **Kind.** Typos and notation.

## C. Gaps and slips in cited works

### C1. Zhan 2010, Theorem 6.1 (iii)–(iv): the endpoint clause

- **Where.** D. Zhan, *Duality of chordal SLE, II*, Ann. Inst. Henri Poincaré Probab. Stat. 46 (2010), 740–759,
  arXiv:0803.2223v2: Theorem 6.1 (arXiv p. 18) and its proof (pp. 19–21; the step in question is on p. 20).
- **Claim.** For SLE_κ, κ > 4, and a stopping time T, if γ(T) ∈ H then "the two curves f_t(x), c(T) < x ≤ ξ(T), and
  f_t(x), ξ(T) ≤ x < d(T), are both semi-crosscuts" (f_t there means f_T). In particular f_T is injective on
  (c(T), ξ(T)] and on [ξ(T), d(T)), including the driving point, so the tip has a single real preimage.
- **Why it is incomplete.** The proof of (iii)–(iv) reads "Using the same argument as in (i)". That argument (an
  independent SLE grown after T, and the first-swallow crosscut of duality) gives injectivity on the open arcs, but it
  does not reach the endpoint ξ(T). The project and its supplementary notes found no proof of this endpoint clause.
  This concerns the completeness of the cited proof; no claim is made that the clause is false.
- **Kind.** Gap in a proof (cited work).
- **Formal treatment.** The specification uses the clause at stopping times in Aux. 135–136 (spec pp. 439–442). The
  formalization does not prove it and does not use it: those uses are replaced (Astra (R41)), Theorems 1.2–1.5 are
  proved without Aux. 136 (R105), and a check of the constant dependencies of every sealed proof finds the clause in
  none of them (R105b).
- **Records.** R38, R39, R41, R105, R105a, R105b; Astra (R39) §4; the project's help request on this point (prompt D).

### C2. Formula slips in Zhan 2008 and Zhan 2010

- D. Zhan, *Duality of chordal SLE, II* (2010), arXiv:0803.2223v2:
  - Theorem 5.1 (p. 16) prints C₃ = 1 − C₄; the construction just before it and its applications use C₃ = 1/2 − C₄.
  - Proof of Lemma 6.1 (p. 19): h(x) = ∫₀ˣ cosh(s/2)^{2/κ−2} ds. The equation displayed with it,
    (κ/2)h″ + (κ/2 − 2) tanh(x/2) h′ = 0, requires the exponent 8/κ − 2. That exponent is still negative for κ > 4, so
    the conclusion stands.
  - §3 (p. 7), before Lemma 3.1: the strip driving function is written ξ(t) = B(t) + σt, without the factor √κ that
    the following formulas contain.
- D. Zhan, *Duality of chordal SLE*, Invent. Math. 174 (2008), 309–353, arXiv:0712.0332v3:
  - (4.24) (p. 24) prints the integrand of F as 2A_{1,1}A_{2,1}/E²; the next display (4.25) requires
    2A_{1,1}²A_{2,1}²/E⁴, as differentiation of the Schwarzian shows (Astra (R38) A.6).
  - In the seed-degeneration paragraph (p. 37) the auxiliary Ñ carries F^λ, whereas M̃ in (4.26) has F^{−λ}.
- **Kind.** Typos. **Formal treatment.** The corrected formulas are used. Each printed form was checked against the
  LaTeX sources of the two papers.
- **Records.** R38; Astra (R38) Part A.6.

### C3. Schramm–Wilson 2005, Theorem 3: scope

- **Where.** O. Schramm and D. B. Wilson, *SLE coordinate changes*, New York J. Math. 11 (2005), 659–669, Theorem 3
  (p. 662); cited at Corollary BR2 (spec p. 607).
- **Point.** Theorem 3 is stated up to the first time the driving function meets a force point (its Definition 2),
  for a seed distinct from the force points, and gives equality in law up to a time change and an unspecified positive
  stopping time. The specification uses the coordinate change through admissible collisions and with force points at
  the seed. It says so and supplies its own extension (identity (BR2.0), spec pp. 607–608). This is not an error in
  Schramm–Wilson; it is recorded so that Theorem 3 is not applied beyond its scope. The missing reference entry is B4.
- **Formal treatment.** The target-change identity for the integrated equations is proved in the library with Zhan's
  other inputs (R35).
- **Records.** E13; SRC-SW05; GX-SPEC-05.

### C4. Inputs of the SLE₈ note: Alvisio–Lawler and Johansson Viklund–Lawler

These concern the separate SLE₈ continuity note and are described with its release. In M. Alvisio and G. F. Lawler's
note on the existence and modulus of continuity of the SLE₈ curve, Corollary 1 is derived in one sentence from
Theorem 3, which controls only time 1, while the corollary needs every dyadic time; its convergent half is proved by a
repaired route (E7, R24). The smaller points are: a log-shifted threshold in §3.5 (harmless; E8), a missing citation of
Lemma 2.2 of Johansson Viklund–Lawler in Lemma 1 (E9), a sign and an offset in the inclusion V ⊂ E in the proof of
Lemma 2 (constants only; E10), and typos on pp. 10, 13 and 14 (E11). In F. Johansson Viklund and G. F. Lawler, *Almost
sure multifractal spectrum for the tip of an SLE curve*, the proof of Proposition 2.3 has two misprints ("|h′(x + 1)|"
for |h′(x + i)|, "h(x)" for h(i)), and (2.16) has "=" for "≤"; no statement changes. Kind: gap in a proof (E7);
typos. Records: E7–E11, R24; SRC-EXT-S8, SRC-JVL.

## How the items were confirmed

- **Against the paper.** Every A item was located in the arXiv v2 PDF and its text layer. Quotations are verbatim up to
  the typesetting of symbols, and the page numbers are those of the PDF. Where the specification reproduces or repairs
  an item, its page-addressed transcription was checked as well.
- **Evidence.** A1: an explicit computation, found by the drafter of the statement (PROVE-T2426-STMT, D1), recomputed
  independently by two statement audits (AUD-T2426A §7 (a), AUD-T2426B F1), and rechecked here. A2: the symmetry computation given there, consistent with the specification's remark that a change
  of branch moves heights only by multiples of 2πχ (FD11.2) and with the audit of the formal frame (AUD-4 §4.1), and with the heights drawn in Figures 1.12, 5.1 and 7.23. A3:
  the paper's own computation on pp. 74–75 and the audits' check of the normalization. A4: the project's example
  (ARCH-1), adapted here to continuous processes. A5 and A8: comparison of statement, figure and proof. A6:
  deterministic configurations recorded in PROVE-SEC5-K and PROVE-SEC5-P. A7: the counterexample to the step recorded
  in PROVE-SEC6-A3. B1: a Lean disproof. C1: the explicit statement in Astra (R39) §4 that the endpoint step is not
  supplied. C2: comparison with the LaTeX sources.
- **Formal side.** The corrected statements are the frozen, sealed ones; their proofs use only propext,
  Classical.choice and Quot.sound. No sealed proof depends on the clause of C1 (R105b).
- **Independent review.** Before publication, a separate refute-first review checked every A item again: each
  quotation page by page in the PDF, each counterexample recomputed, and Figures 1.12, 5.1, 7.18 and 7.23 read for the
  heights they draw. It confirmed A1–A8. It led to the present wording of A2 (a normalization remark about the
  definition, not an error of Theorem 1.4 as the paper uses it), the removal of a horizon claim from A3, and a
  correction of the attribution in A6. Section C was checked against the project's records, not against the cited
  papers.
- **Record keeping.** The project's errata ledger has entries E1–E13 only. It has no entry for A1, although ruling
  R109 calls the item an erratum and AUD-T2426C N1 asks for a ledger entry. A2, A3, A5, A6 (R45, R50), A7 (R37), A8
  and B1 (R49) have no ledger entries either; they are recorded only in rulings, audits, hand-offs or the
  specification, or, for the symmetry check in A2, only here. This note collects them.
- **Left out.** Problems recorded only against the project's own reformulations: for example R57 (strip heights
  applied to another chart; the ruling itself says that no source page changes), R59 (the counterflow line does not
  return to its starting point, a fact needed in the project's half-plane chart but not by the paper's strip
  argument), and corrections that supplementary notes made to the project's own proposals (R98). Also left out are
  steps that the sources assert without proof but that are true, recorded as source gaps in the dependency graph, for
  example the integrated target-change identity assumed by LP6, the measurability of half-plane capacity as a
  function of the hull in Aux. 18, and the measurability of the crossing event in Corollary 7.12E.
