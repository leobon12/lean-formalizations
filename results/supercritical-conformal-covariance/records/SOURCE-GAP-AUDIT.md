# Public extract of the independent source-gap audit

This is the record behind the guide's list of source repairs and its errata (ruling A22.6). An auditor who took no part in finding or
writing the repairs checked every SOURCE_GAP node of the source dependency graph against the pinned sources: the manuscript P (its pinned
text extraction, shipped in `source/`), Ding–Gwynne (DG) arXiv:2110.00177v3, Gwynne–Miller (GM) arXiv:1905.00384v2 and (GMU)
arXiv:1905.00383v3, Pfeffer (Pfe) arXiv:2104.04020v3 and Miller–Sheffield (IG4) arXiv:1302.4738v2. Literature line numbers are lines of the
arXiv TeX sources; “P l. N” is line N of the text extraction.

The audit was made at graph revision 5, which had 53 SOURCE_GAP nodes, before the Lean proof was complete. Its verdicts were then applied
to the graph. At revision 7, the revision the guide lists: the 15 NOT-A-GAP nodes became reading notes; graph review 3 reinstated one of
them, the Ding–Gwynne Prop 1.9 step (row 2), as a minor gap; and the gap the audit found missing was added as `prop-4.3#apply-tangent`.
That gives the guide's 40 gap nodes. This extract keeps the audit's verdict keys, its table and its detailed arguments. It omits the
auditor's process notes, its Lean spot-checks of statements that were then still in development (the Lean status is in the guide), its
recommendations to the graph (since applied) and its errata list (reproduced in the guide). Source: development file SHA-256
`88223ddbfc9018d2b38f8300a46a5f1c23063fdef2d4bd3522bad5c8a5fee891`.

**Verdict keys.**
- **GENUINE**: the printed source is wrong, or materially incomplete at that point.
- **GENUINE (minor)**: a real omission, repaired by a short standard argument.
- **NOT-A-GAP**: the printed text is correct, or it is covered by the paper's own conventions. The node records a formal expansion, a
  reading note, or a route choice. These items should not be listed as errata.

**Severity keys.**
- **F**: a false printed statement.
- **P**: a gap in a printed proof.
- **C**: an imprecise citation.
- **N**: a convention or notation issue.
- **X**: no source error (formal expansion, route choice or reading note).

## Table

| # | Node | Verdict | Sev. | Reason |
|---|---|---|---|---|
| 1 | `def:theta` | GENUINE (minor) | C | θ is DG Lemma 2.13's exponent (§2.6), not "§3.2". Pfeffer Props 1.10/1.12 are in §1.2, not §1.3. [1, L2.11] and [2, L2.26] are used for their proofs. Re-pointing the edges is correct. |
| 2 | `dg:prop-rotation#constant-one` | NOT-A-GAP | C/X | DG's law comparison of D_h(0,∂𝔻) is valid given the true, unstated fact that a fixed point is a.s. non-singular. The repair swaps in an axiom-level observable, across(A_{1,2}) ∈ (0,∞). The route is correct. |
| 3 | `disp-10#finite-family` | NOT-A-GAP | N | (10) with the continuum ∃ contains the finite-family event. l. 442–443 says which family is tested; reading it there is a convention. |
| 4 | `domain-affine` | GENUINE (minor) | C | (I1) cites DG for whole-plane fields only. P applies it to domain fields (l. 121–122, 223, 234, 344–348). The derivation through realizations is correct. |
| 5 | `domain-locality` | GENUINE (minor) | P | GM l. 319–320 asserts the domain axioms "by inspection". The domain form also needs universal locality. |
| 6 | `domain-measurable-functional` | GENUINE | P | "The metric is a measurable functional of that field" (l. 233) needs one Borel functional valid for h^{ψ_n} and h^a together. Axiom II gives one per law. |
| 7 | `domain-weyl` | GENUINE (minor) | P | GM "by inspection". Composing Weyl scalings with corrections unbounded at ∂V needs the Weyl length formula. Correct. |
| 8 | `g-pull` | GENUINE | P | P uses tacitly that h∘φ+Q log\|φ′\| and h^φ are again in the class (l. 26, 37, 544). GM argues it in one sentence (l. 361). The Greenian Markov, re-embedding and correction repair is correct and consistent with A14. |
| 9 | `gm:lem-tv-conv#as-conv` | GENUINE (minor) | N | Typo at GM l. 539: f∘φ_n → f(α⁻¹·), not f(α·). The display itself is right. G1 (supports) and G2 (real derivatives) are unstated routine details. |
| 10 | `gm:lem-tv-conv#cameron-martin` | GENUINE | P | The shift is random, so the deterministic Cameron–Martin density does not apply directly. Independence gives TV ≤ E min(1, √(e^{E(S)}−1)). The cutoff energy needs an L² bound on Y_n−(Y_n,f_r). |
| 11 | `gm:lem-tv-conv#decomposition` | GENUINE | P | Lemma 2.3 allows U_n = ℂ, where no zero-boundary GFF exists: use disks D_n. With (h,𝐟)=0 the Markov parts are not independent: recentre. Typo φ(U_n) → φ_n(U_n). |
| 12 | `gm:lem-tv-conv#harmonic-energy` | GENUINE | P/C | "Basic estimates (see the proof of IG4 2.10)" give only a sup bound, and that bound rests on IG4's unproved variance claim. Energy decay needs more. The repair keeps the cutoff in the source disk. |
| 13 | `gm:lem-tv-conv#normalization` | **GENUINE** | **F** | (h(α·))_{𝐟,\|α\|}(0) = h_{𝐟,\|α\|²}(0) ≠ 0, so (2.6) and (2.6-0) have TV distance 1 when \|α\| ≠ 1. The correct scale is \|α\|⁻¹. P already uses it (f_a, l. 213). See §2.1. |
| 14 | `ig4:prop::gff_convergence#variance-bound` | GENUINE | P | IG4 l. 1174 states Var(𝔥_n(y)−𝔥_n(0)) ≤ ε² as "not difficult to see". It gives no proof and no uniformity in y. The nested-disk bound −log(1−\|y\|²/L²) is correct and uniform. See §2.9. |
| 15 | `input-I2#escape-barrier` | GENUINE | C | (I2)'s "every finite metric-length path is Euclidean continuous" is attributed to Pfeffer Props 1.10/1.12, whose printed proofs presuppose it (an erratum also recorded by the SupercriticalLQGUniqueness release). The barrier argument (exact scaling, Q>0, h_{2^n}(0)/n→0, Borel–Cantelli) is correct. |
| 16 | `input-I2#escape-topology` | GENUINE (repair component) | C | Deterministic: D-convergence implies Euclidean convergence, by lsc plus positivity on bounded sets and the barrier at infinity. Correct, and the chordal counterexample shows the barrier is needed. |
| 17 | `input-I2#route-lsc-barrier` | GENUINE (repair route) | C | The audit-supplied route B is logically prior to Pfeffer's. It is sound and adopted (rulings A16 and A17.1). |
| 18 | `input-I2#weyl-transfer` | GENUINE (repair component) | C | Local continuity transfers through a locally bounded weight e^{ξf}. Correct. |
| 19 | `lem-1.2#metric-curve` | GENUINE (minor) | P | Lemma 1.2's proof never shows that the uniform limit is a D-curve, which the internal metric requires. The lsc argument D(P(t),P(s)) ≤ V(0,s)−V(0,t+) is correct. |
| 20 | `lem-2.1#endpoint-limit` | NOT-A-GAP | X | The printed argument (path compactness plus length lsc from Lemma 1.2, applied to h^φ on V) is valid and never claims e is lsc. The confined-metric closure is an equivalent formal route. |
| 21 | `lem-2.1#koebe-normalized` | NOT-A-GAP | X | The printed claim is correct. "After passage to a subsequence" is superfluous, and the uniformity in (U,φ) is true (proved) but never consumed. |
| 22 | `lem-2.1#lognormal-factor` | GENUINE (minor) | N | The factor exp(ξ((ĥ∘F_n⁻¹,𝐟)−ĥ_1(0))) has an n-dependent law, so "law independent of n" is false. It converges a.s. to a fixed log-normal law, so tightness, which is all that is used, holds. |
| 23 | `lem-2.1#loop-chaining` | GENUINE | P | Inherited from Pfeffer Lemma 2.26's proof (Pfe l. 1590–1611). Nested small loops need not intersect, and the terminal loop has no paid interval (t_{J+1} is undefined). The filled-set chain repair is correct. See §2.6. |
| 24 | `lem-2.1#strict-comparison` | NOT-A-GAP | X | Replacing ≤ C₀ by < 2C₀ (with across > 0 a.s.) is constant bookkeeping. |
| 25 | `lem-2.1#uniform-centres` | GENUINE (minor) | N | Slip: (4) and Lemma 5.1 are stated for z ∈ K, but lattice centres lie near K. Apply them to a compact neighbourhood. |
| 26 | `lem-3.1#repaired` | **GENUINE** | **F/P** | Ill-posed: the hypotheses are "arbitrary generalized functions", and the couplings need not carry f_n, f. Literally false "jointly with the fields" on a larger neighbourhood (g_n = g+ψ). Its locality step needs a common functional. Repair correct; Lean proves a stronger form. See §2.3. |
| 27 | `lem-3.2#barrier-event` | NOT-A-GAP | C | "Strictly less than half" is not DG's event, but it is true: the same tightness and iteration argument gives any constant factor. Strict around < across suffices. Imprecise citation only. |
| 28 | `lem-3.2#excursion-replacement` | NOT-A-GAP | X | The paper already applies the surgery to "distance-minimizing sequences" (l. 187). The node itself says "as printed". |
| 29 | `lem-3.2#infinite-distances` | NOT-A-GAP | X | The claim at l. 188 is true. Confined ≥ ambient makes the ∞ case trivial; the wording "the same argument" is loose. |
| 30 | `lem-3.3#distortion` | NOT-A-GAP | X | Standard univalent convergence, correctly invoked. The node records the formal theorem. |
| 31 | `lem-3.3#expanding-confinement` | GENUINE (minor) | P | **T2 is not a gap**: "approximates … uniformly in probability" is the standard approximation theorem (Billingsley Thm 3.2). **B2 is genuine**: the strict barrier event is not stable under the non-constant correction Q log\|(ψ_n⁻¹)′\|+Q log\|a\|, so a margin θ<1 is needed, and TV transfer needs a Borel, local event. D1 is a simplification. |
| 32 | `lem-3.3#fixed-confinement` | **GENUINE** | P | The maximal coupling plus Lemma 3.1 needs one locality functional for the different laws, and a gluing with h. Both routes (repaired printed route; transfer lemma) are correct. See §2.4. |
| 33 | `lem-3.3#joint-identification` | GENUINE (minor) | P | Same root cause as T1. The measurable-graph argument ((H,Ẽ) =ᵈ (h^a, D_{h^a}) ⇒ Ẽ = D_H a.s.) is correct. |
| 34 | `lem-3.3#pullback-epigraph` | NOT-A-GAP | X | ψ_n∘ψ_n⁻¹ = id on compacts eventually (Koebe ¼) is the trivial domain fact behind "transported by the inverse maps". |
| 35 | `lem-3.3#transfer-lemma` | GENUINE (repair component of T1) | P | A new lemma of the repair route, not a source error. Its proof sketch (L¹ approximation, TV bound, dominated convergence) is correct. |
| 36 | `lem-4.1#connector` | **GENUINE** | P | (6) pays u_n → ∂B_{s_j}, but the loop may sit near radius √s_j, and that radial segment is unpaid (single-scale counterexample). The two-scale repair (s_k, then √s_j < s_k) uses only (6). Statement unchanged. See §2.2. |
| 37 | `lem-4.2#ambient-metrics` | GENUINE (minor) | N | (8) tests balls and annuli that leave A_{αr,r}(z). The compact annulus of Lemma 4.2 must contain them (e.g. Ā_{1/2,2} rescaled), or ambient metrics must be used. |
| 38 | `lem-4.2#borel-witness` | GENUINE (minor) | P | (7) involves the circle average m_{z,r}, which is field data, not a metric coordinate: read d(u,v) ≤ M, as l. 305 and l. 356–358 do. The Borel claims for moving-centre around and point-to-circle distances need short arguments. |
| 39 | `lem-4.2#closed-annulus-trace` | NOT-A-GAP | N/X | Covered by P l. 41 ("Boundary endpoints are interpreted using paths in the closed annulus"). The development's feasibility analysis already called it a reading note. **Demote**, like SG-CC-REV-001. |
| 40 | `lem-4.2#geodesic-code` | NOT-A-GAP | X | Under "source distance at most M" the endpoint distance is finite. A Euclidean-continuous path of finite D-length is a D-curve by the `lem-1.2#metric-curve` lsc argument. A formalization detail. |
| 41 | `lem-4.2#parameter-space` | GENUINE (minor) | P | The set of lsc length metrics is not closed in the lsc-function space (cε → 0), and the paper does not show it is Polish. The standard Borel parameter space with measurable metric maps keeps the conclusion (universal measurability) unchanged. |
| 42 | `lem-5.1#locality` | GENUINE (minor) | N | F_{z,r} uses internal metrics of the closed annulus, which are determined by h near cl A, not by h on the open annulus (l. 416–417). It is universally measurable, not Borel. The enlarged-annulus iteration is correct. |
| 43 | `lem-5.1#shield` | NOT-A-GAP | X | The numerics are correct (2CkS = S/(2C) < S/C, and an escape crosses twice). The node asks only for a domain-metric statement of the surgery. |
| 44 | `lem-7.1#local-decomposition` | GENUINE (minor) | P | "Couple … with a whole-plane GFF" needs an extension of the probability space, with countably many couplings on one space. Standard (conditional kernels). |
| 45 | `lem-7.1#pathwise-weyl` | GENUINE (minor) | P | Transferring e ≤ d through a random weight needs the Weyl length formula and dλ_e ≤ dλ_d. "Path weights agree exactly" compresses this. |
| 46 | `markov-greenian` | NOT-A-GAP | X (N in GM) | A new formal step forced by the frozen existence conjunct (A14). P itself only decomposes on disks (l. 524). GM l. 313 says "for each deterministic open set U", tacitly Greenian. IG4 Prop 2.8 is stated for bounded W. See §2.10. |
| 47 | `prop-4.3#first-exit-confinement` | NOT-A-GAP | X | "All small endpoint annuli are contained in the rescaled domain" (l. 359–360) is the right justification. First-exit truncation and invariance of path length under confinement are standard. See §2.8. |
| 48 | `prop-4.3#skorokhod` | GENUINE (minor) | P | The state space is unspecified (𝒟′ is not metrizable; use countable coordinates). The failure flag mark and the transfer of the universally measurable failure event under equality of laws are only gestured at (l. 326–329). See §2.8. |
| 49 | `prop-6.1#endpoint-exclusion` | **GENUINE** | P | "Ignore the initial and terminal portions" (l. 474–476) does not give the invariant that l. 478–479 and 494–496 need: the G2/G4 loops are met on both sides only if P(0), P(T) ∉ B_{2r_j}(z_j). The corridor repair is correct. See §2.7. |
| 50 | `pullback-locality` | GENUINE (minor) | P | GM l. 362: "easily seen" without proof. Needs domain locality, universal locality and test-function transport. |
| 51 | `sec5#g1-probability` | **GENUINE** | P (inherited) | DG l. 1976 derives clause 1 (around ≤ δ^θ·across) from Lemma 2.13, which bounds around by δ^θ times *elapsed time*. That does not imply the ratio. Repaired by the sealed two-scale ratio estimate. See §2.5. |
| 52 | `sec5#g3-probability` | **GENUINE** | P (inherited) | DG Lemma 2.14 requires endpoints in the *open* U, away from η. The clause-3 geodesics end on ∂A, and enlarging U changes the carrier. Repaired by the sealed closed-endpoint extension, then α → 1. See §2.5. |
| 53 | `universal-locality` | GENUINE | P | P l. 169–170 and 233 compare metrics of different field laws through "determined by". Axiom II gives one functional per law. The coin-mixture repair is correct. See §2.4. |

Counts: GENUINE (any, including the repair components in rows 15–18 and 35) 38. NOT-A-GAP 15 (rows 2, 3, 20, 21, 24, 27, 28, 29, 30, 34,
39, 40, 43, 46, 47). Severity F: rows 13 and 26.
repair component of a genuine gap; treat it as part of row 32). Severity F: rows 13 and 26.

## Detailed arguments for the deep nodes

### 2.1 GM-L24-N1: the GM Lemma 2.4 normalization scale (row 13). GENUINE, F

**Source.** GM defines h_{𝐟,r}(z) := (h(r·+z), 𝐟) with 𝐟 radial and ∫𝐟 = 1 (GM l. 452–454), and normalizes h_{𝐟,1}(0) = 0 (l. 495).
Then:
- (2.6) (l. 519–520) subtracts (h∘φ_n⁻¹)_{𝐟,|α|}(0), with φ_n′(0) → 1/α;
- l. 549 asserts: "the field h(α·) is normalized so that (h(α·))_{𝐟,|α|}(0) is zero".

**Refutation attempt.** Let g = h(α·). Then g_{𝐟,s}(0) = ∫ h(αs w) 𝐟(w) dw. Write α = |α|e^{iθ}. Rotating w and using that 𝐟 is radial
gives h_{𝐟,s|α|}(0). So:
- (h(α·))_{𝐟,|α|}(0) = h_{𝐟,|α|²}(0), which is 0 only when |α| = 1;
- (h(α·))_{𝐟,|α|⁻¹}(0) = h_{𝐟,1}(0) = 0.

**(2.6) is false when |α| ≠ 1.** Take K containing supp 𝐟_{|α|}. Then the pairing against 𝐟_{|α|} is determined by the restriction to K.
- On the left side of (2.6) it is identically 0.
- On the right side it is h_{𝐟,|α|²}(0) − h_{𝐟,1}(0), a non-degenerate centred Gaussian (the logarithmic covariance is positive definite
  on mean-zero tests).
- So the TV distance is 1 for every n.

The same holds for (2.6-0). The claim is therefore a genuinely false printed statement. Its proof sketch is otherwise fine at the
corrected scale.

**The repair is correct and minimal.** Change |α| to |α|⁻¹ in (2.6) and (2.6-0).
- Normalizing by (·)_{𝐟,s}(0) is a function on distributions modulo constants. So the TV distance of the normalized laws is at most the
  TV distance modulo constants, which goes to 0 by IG4.
- The limit is normalized exactly at s = |α|⁻¹.

**Consumers.** The paper is consistent with the corrected scale.
- **Lemma 3.3.** At l. 213, f_a(w) = |a|⁻² 𝐟(w/a) with a = lim ψ_n′(0) = α⁻¹ (GM's φ_n = ψ_n). Then (g, f_a) = ∫ g(au) 𝐟(u) du,
  which equals g_{𝐟,|a|}(0) = g_{𝐟,|α|⁻¹}(0) by radial symmetry. For g = h(a⁻¹·) this is (h,𝐟) = 0 by l. 206.
- **Lemma 2.1.** It uses F_n′(0) = 1 (α = 1), where the two scales coincide.
- **GM's own use (l. 583–590)** needs only the convergence of the constants, which (2.5) gives at either scale.

**Effect on the root.** None. (I4) must be *cited* with the corrected scale.

**Same lemma, smaller items** (rows 9–12; T1 = `gm:lem-tv-conv#as-conv`, G3 and G4 = `gm:lem-tv-conv#decomposition`, G5 =
`gm:lem-tv-conv#harmonic-energy`, G6 and G7 = `gm:lem-tv-conv#cameron-martin`). All verified against GM l. 524–562.
- **T1.** φ_n → z/α, so f∘φ_n → f(α⁻¹·). The display is still right, since (h(α·), f) = (h, |α|⁻² f(α⁻¹·)).
- **G3.** Lemma 2.3 allows U_n = ℂ, and then φ_n is affine. There is no zero-boundary GFF there. Disks D_n ⊂ U_n suffice, because
  every observation uses h near the bounded set φ_n⁻¹(K).
- **G4.** With supp 𝐟 ⊂ U_n and the normalization (h,𝐟) = 0, the harmonic part absorbs −(h̊_n,𝐟). That constant is correlated with
  h̊_n, so the two parts are not independent. It is invisible after renormalization.
- **G6.** ∇(χ(Y−c)) contains (Y−c)∇χ, so the energy needs an L² (or Poincaré) bound, not just E(Y).
- **G7.** The shift is random. The law of h̊ + S_n is a mixture, and TV(mixture, law h̊) ≤ E[TV(h̊+s, h̊)]|_{s=S_n}. That is the
  stated bound.
- **G5.** IG4's proof gives only the sup of |𝔥−𝔥(0)| on B(0,R), and that rests on its own unproved variance claim (§2.9). Energy
  smallness additionally needs interior gradient estimates.

All are genuine, and all are minor except N1.

### 2.2 `lem-4.1#connector`: the Lemma 4.1 connector (row 36). GENUINE, P

**Printed argument (l. 275–278).** Choose a loop in A_{s_j,√s_j}(u_n) of d_n-length ≤ 2M s_j^θ, and a path from u_n to ∂B_{√s_j}
"whose initial segment to ∂B_{s_j} has length ≤ 2M s_j^θ … hence an e_n-connector from u_n to every point of the loop of cost
O(CM s_j^θ)".

**Refutation.** The loop lies outside B_{s_j}. So the path first reaches ∂B_{s_j}, which is paid, and only later meets the loop, which
may lie near radius √s_j. The segment in between is unpaid.

**Counterexample.** Take a metric whose weight is huge on A_{2s,√s/2}(u) and small elsewhere. Then:
- d(u, ∂B_s) and around(A_{s,√s}) are small (a cheap loop exists near radius √s);
- d(u, loop) ≥ across(A_{2s,√s/2}), which is huge.

So (6) at one scale does not bound the connector. The gap is genuine. The statement survives.

**Repair check.** (6) holds for **every fixed j** and all large n. Fix k, then j with √s_j < s_k.
- The loop γ ⊂ A_{s_j,√s_j}(u_n) ⊂ B_{s_k}(u_n) separates u_n from ∂B_{s_k}(u_n).
- So every path from u_n to ∂B_{s_k} meets γ, and d_n(u_n, γ) ≤ d_n(u_n, ∂B_{s_k}) ≤ M s_k^θ (in the infimum sense).
- Recovery endpoints a_n → u lie in B_{s_j}(u_n), inside γ, for large n. The recovery path Q_n ends near v, outside B_{√s_j}(u_n), so
  by Euclidean continuity it meets γ.
- Splicing gives e_n(u_n, v_n) ≤ len_{e_n}(Q_n) + C·O(M(s_k^θ + s_j^θ)). Only the distance comparison e_n ≤ C d_n and the triangle
  inequality are used.
- Let j → ∞, then k → ∞. The contradiction is then the printed one.
- Positivity 0 < d(u,v) (l. 268–272) is valid: epigraph liminf gives d(u,v) ≤ L ≤ M, and u ≠ v.

**Minimality and consumers.** No new hypothesis is added. Prop 4.3 supplies (6) from (8) on the dyadic scales (l. 359): every
δ ∈ Δ ∩ (0,(1−α)²] in rescaled units, so both scales are available.

### 2.3 `lem-3.1#repaired`: Lemma 3.1 as printed (row 26). GENUINE; F in a literal reading, otherwise P

**Printed (l. 163–167).** Random generalized functions g_n, g on a neighbourhood of K′, "which can be coupled so that g_n = g on K′
with probability → 1"; f_n, f continuous with ‖f_n−f‖ → 0 in probability; "the intrinsic metrics on K … converge jointly with the
fields, in probability".

**Refutation, item by item.**
- **(a) Arbitrary generalized functions have no D_g.** This is an implicit-hypothesis defect. The paper's context makes the intended
  class clear (fields locally GFF plus continuous), so this alone is a convention issue.
- **(b) "Jointly with the fields".** If "the fields" means the fields on the stated neighbourhood N of K′, the claim is false: take
  g_n = g + ψ with ψ ∈ C_c^∞(N∖K′), ψ ≠ 0. If it means the restrictions to (an open set inside) K′, it is true and trivial on the
  coupling event. The statement is ambiguous, and one literal reading is false.
- **(c) Pairwise couplings.** A per-n coupling suffices for convergence in law (Lemma 3.3's only use), with P_n[epi-dist > δ] → 0. This
  reading is meaningful (the formal proof proves it). It requires the coupling to carry f_n and f as well,
  which the statement does not say.
- **(d) The proof, l. 169–170.** "Locality identifies the metric functionals on K": D_{g_n}(·,·;U) = F_n(g_n|_U) and
  D_g(·,·;U) = F(g|_U) with law-dependent F_n ≠ F. Equality of the restrictions does not give equality of the metrics without one
  common functional. This is a genuine proof gap, repaired by universal locality (§2.4).

**Overall.** The printed statement is ill-posed and literally false in one reading. Under the natural reading it is true, with a proof
gap. The audit therefore describes it as "statement imprecise (implicit hypotheses; ambiguous joint convergence) and proof gap"
rather than flatly "false", with the g_n = g+ψ counterexample to the literal reading.

**Repair.** The repair is correct and as weak as needed: one common coupling; fields with realizations; P[g_n|_U = g|_U] → 1 for a
deterministic open U ⊇ K; jointly measurable corrections; joint convergence with the restrictions to U.
- The relaxations in the formal version (only K ⊆ K′ and K ⊆ U; only f measurable) are sound.
- It changes only an internal lemma. Its only consumer is the printed route of Lemma 3.3 (`lem-3.3#route-maxcoupling`). The root is
  untouched.

### 2.4 Lemma 3.3: T1, T2, B1, B2 (rows 6, 31–35, 53, and 27–29 for B1)

Here T1 is the one-functional gap of `lem-3.3#fixed-confinement` (with `domain-measurable-functional`, `lem-3.3#joint-identification`, `lem-3.3#transfer-lemma` and `universal-locality`); T2 is the limit interchange inside `lem-3.3#expanding-confinement`; B2 is the margin event of that node; B1 is the barrier event of `lem-3.2#barrier-event` and its neighbours; D1 is a simplification.

**T1: GENUINE, P.**
- **Printed step (l. 218–223).** "Under a maximal coupling of the normalized fields, they agree on a neighborhood of B_S with
  probability tending to one; Lemma 3.1 therefore gives joint convergence."
- **What it needs:**
  1. The transformed metric on B_S equals Φ(field|_N) for a functional Φ common to the law of the transformed field (which changes with
     n) and to h^a. This is the same defect as §2.3(d).
  2. The joint law with the original h, which needs a gluing of the per-n coupling with (h, h^{ψ_n}). This is standard on standard Borel
     spaces.
- **The identification (l. 231–236)** then works by the measurable-graph argument: if (H,Ẽ) =ᵈ (h^a, D(h^a)) with D a Borel map, then
  Ẽ = D(H) a.s. And H = h^a(h) a.s. by GM (2.5), which is deterministic. That argument is sound once joint convergence of
  (field, metric) is known.
- **The alternative route of the formal proof** replaces the coupling by the transfer lemma: X_n → Y a.s. and law X_n → law Y in TV imply
  Φ(X_n) → Φ(Y) in probability for Borel Φ into a compact metric space. I checked it. Embed the target in [0,1]^ℕ. For each coordinate
  pick a continuous g with E|Φ−g|(Y) < ε. Then E|Φ(X_n)−g(X_n)| ≤ E|Φ(Y)−g(Y)| + 2·TV_n, and g(X_n) → g(Y) a.s. The route is correct
  and avoids the coupling and the correction lift.
- **Both routes are correctly modelled as ROUTES.**

**Universal locality (row 53): the repair is correct.**
- Axiom II (frozen: `∃ F, ∀ᵐ ω, (D (h ω)).internal U = F (restrictTo U (h ω))`) is per law.
- Mix the countably many laws with an independent coin N. g_N is again a whole-plane GFF plus a continuous function: the GFF parts
  agree modulo constants, which `IsWholePlaneGFF` allows.
- Axiom II for g_N gives F. On {N = i}, which is independent of g_i and has positive probability, D_{g_i}(·;U) = F(g_i|_U) a.s.
- A simpler argument than the formal one therefore suffices, because h ↦ D_h is one deterministic measurable map: P(D_{g_i} ≠ F(g_i|_U))
  = P(D_{g_N} ≠ F(g_N|_U), N = i)/P(N = i) = 0.
- The formal proof's conditionally independent copies, Dirac conditional law and measurable atom are also valid. They are needed for the
  *pathwise-local observable* generalization (the barrier event).

**T2: NOT-A-GAP.** l. 224–230 says that, for each R and δ, S can be chosen with P(confined = unconfined on B_R) ≥ 1−δ, transferred to
the transformed field, "thus fixed-confinement convergence approximates expanding-confinement convergence uniformly in probability".
- This is precisely the hypothesis lim_S limsup_n P(d(X_n^S, X_n) > ε) = 0 of the standard approximation theorem (Billingsley,
  Convergence of Probability Measures, Thm 3.2), together with X_n^S ⇒ X^S and X^S ⇒ X.
- Locality of epigraph convergence on open B_R² makes agreement on B_R² sufficient.
- The formal proof's remark that "the a.s. subsequence argument at fixed S fails" is about its in-probability formalization, not
  about the paper. The diagonal S_n → ∞ is a valid formal alternative.
- What remains genuinely missing in that paragraph is B2.

**B2: GENUINE (minor), P.** "The same barrier event transfers to the transformed field by the preceding total-variation comparison."
- TV applies to the *normalized field* h∘ψ_n⁻¹ − c_n.
- The metric of h^{ψ_n} differs from the metric of that field by the Weyl weight Q log|(ψ_n⁻¹)′| + c_n. Its constant part scales
  around and across equally. Its non-constant part is o(1) uniformly on B̄_S but not 0.
- A strict inequality "around < across" is not stable under an o(1) multiplicative perturbation. A margin event "around < θ·across",
  θ < 1, whose probability is close to the strict one by continuity of measure, is needed.
- The barrier event must also be a Borel, pathwise-local functional of the field near B̄_S for TV to apply.
- The repair is correct and minimal.

**B1 (rows 27–29): NOT-A-GAP.**
- DG Lemma 2.11's proof event is E_s = {around(A_{s,2s}) < across(A_{2s,3s})} (DG l. 1371–1373), with no factor ½.
- P's "strictly less than half the cost of crossing a farther annulus" is a strengthening. It is still true, because the same
  tightness (Axiom V′) and iteration argument works with any constant factor, or because across of a far annulus → ∞ a.s.
- It is unnecessary: an excursion that leaves the outer disk crosses the far annulus between its first and last loop hits, so strict
  around < across suffices.
- The surgery on near-minimizing sequences is as printed (l. 187). Infinite distances are trivial (confined ≥ ambient).
- So: an imprecise citation, not an error.

**D1** (d_n → D_h a.s. without Lemma 3.2) is correct. Internal metrics on increasing closed disks decrease pointwise to D_h, since
finite paths have bounded trace. A decreasing pointwise limit of lsc functions to an lsc limit is an epigraph limit. Not a gap.

### 2.5 `sec5#g1-probability` and `sec5#g3-probability`: the gaps inherited from Ding–Gwynne (rows 51, 52, 1)

**`sec5#g1-probability`, DG l. 1976.**
- DG proves clause 1 of E_r(z) (l. 1890–1894: around(A_{δr,δ^{1/2}r}(x)) ≤ δ^θ·across(A_{δr,δ^{1/2}r}(x)) for every internal
  boundary geodesic hitting B_{δr}(x), x ∈ A_{3r/4,3r/2}) "by Lemma 2.13 with f ≡ 0".
- Lemma 2.13 (l. 1427–1446) concludes around(A_{εr,ε^χ r}(z)) ≤ ε^θ·s, where s is the geodesic time of the hit.
- s is a macroscopic quantity, of order r^{ξQ}e^{ξh_r}, while across of the small annulus is of order (√δ r)^{ξQ}e^{ξh_{√δr}(x)}.
  Typically across ≪ s, and across ≤ s gives no inequality in the needed direction.
- So the inference is invalid. The gap is **GENUINE** in DG and inherited by P l. 383–389 ("the source-only estimates of [1]").
- The repair is the sealed two-scale ratio theorem of SupercriticalLQGUniqueness. It gives the ratio form for every real δ ≤ δ₀, hence
  for the dyadic δ.
- I also checked that **one θ serves (8) and (G1)**. In §6, x = u = P(s_j), and the segment from u to v crosses A_{δr,√δr}(u) because
  |u−v| ≥ (1−α)r ≥ √δ r. So across ≤ D(u,v) = t_j − s_j, and around ≤ δ^θ D(u,v). For the point-to-circle part, the extended geodesic
  crosses the loop before and after x, so by minimality D(x, ∂B_{δr}(x)) ≤ around. This needs `prop-6.1#endpoint-exclusion`.
- Hence `def:theta` re-pointing to `slu:two-scale-ratio` is right. The citation of θ (DG §2.6, Lemma 2.13 with χ = ½, not §3.2) is a
  genuine citation slip.

**`sec5#g3-probability`, DG l. 1979–1984.**
- DG applies Lemma 2.14 (l. 1550–1562), with η the unit circle, to D_h(·,·;cl A_{r/2,2r})-geodesics "from a point of ∂B_{r/2} to a
  point of ∂B_r".
- Lemma 2.14 requires geodesics of D_{h−f}(·,·; r cl U) between points of r[U ∖ B_{ε^{1/2}}(η)], with U *open*. The endpoints lie on
  ∂(rU), not in rU. The printed "∂B_r" endpoint even lies on η itself, a typo.
- Enlarging U to U′ ⊋ cl A changes the carrier r cl U′. An internal geodesic of cl A need not be one of cl U′, so the lemma cannot be
  applied as printed. **GENUINE.**
- The closed-endpoint extension sealed in SupercriticalLQGUniqueness is the right repair. Pushing α → 1 after
  δ₀ follows DG's own order ("after possibly shrinking K_ann, in a manner depending on K_ep").

Both repairs are sealed in SupercriticalLQGUniqueness. Neither changes (G1), (G3), §6 or the root.

### 2.6 `lem-2.1#loop-chaining`: the loop chaining inherited from Pfeffer Lemma 2.26 (row 23). GENUINE, P

**Pfeffer's argument.** Pfeffer Lemma 2.26 (Pfe TeX l. 1577)
builds balls B_{r_j/2}(x_j) inductively along P, with t_{j+1} the first exit of B_{r_j}(x_j). It asserts "from topological
considerations … the union of the paths C_{r_j}(x_j) is connected". It then sums Σ_{j≤J} around ≤ C Σ_j across(A_{r_j/2,r_j}(x_j))
≤ C Σ_j (t_{j+1}−t_j) (Pfe l. 1590–1611).

**Both claims fail.**
1. **Connectivity.** P(t_{j+1}) ∈ ∂B_{r_j}(x_j) lies inside the loop C_j ⊂ A_{r_j,2r_j}(x_j). If r_{j+1} ≪ r_j, the loop C_{j+1} around
   P(t_{j+1}) can lie entirely inside the bounded component of ℂ∖C_j. Then the union is not connected.
2. **The terminal loop.** For j = J, P stays in B_{r_J/2}(x_J), so it never crosses A_{r_J/2,r_J}. t_{J+1} is undefined and that
   loop's cost is unpaid. In the supercritical case, the around cost of a tiny annulus near a possibly singular endpoint need not
   vanish, so "+o(1)" (P l. 142) is not justified as stated.

**Repair check.** Follow P and keep a filled-set invariant:
- either P later hits the current loop, and the segment up to the hit pays for it;
- or P stays inside the filled loop to its end, and the loop is only a connector to a point within O(ε) of P(T).
The endpoint limit then goes through Lemma 1.2 (row 20). Termination uses the positive minimum of finitely many grid crossings. This
is correct, and it is the sealed `l4_chain` pattern.

**Two further notes.**
- P cites [2, L2.26] for its *proof* (Pfeffer's hypotheses, conditionally iid metrics, do not apply to (d,e)), so the citation is
  imprecise. The gap is in Pfeffer's Lemma **2.26** (Pfe l. 1574–1614).

### 2.7 `prop-6.1#endpoint-exclusion`: the retained endpoints in Prop 6.1 (row 49). GENUINE, P

**Printed (l. 471–479).** Start at t_{j−1}, take a good ball with P(t_{j−1}) ∈ B_{r_j/2}(z_j), set t_j = next exit, and s_j = last
preceding time on ∂B_{αr_j}. "Ignore the initial and terminal portions corresponding to balls meeting the endpoints of P." Then:
"Restrict P between its surrounding hits of ∂A_{r_j/2,2r_j}(z_j). This is an internal geodesic … The short outer loop from (G2) meets
the extended geodesic on both sides."

**What the later steps need.**
- (G1)–(G3) apply to geodesics *between two boundary points* of A. The (G2) and (G4) minimality arguments (l. 481 and (14)) need the
  geodesic to hit the respective loops before s_j or t_{j−1}, and after t_j.
- If P(0) ∈ B_{2r_j}(z_j), the "extended geodesic" may start inside A, or inside B_{r_j/2}, and the loops need not be hit before.
- "Balls meeting the endpoints" (endpoint in B_{r_j}) is the wrong exclusion radius (it must be 2r_j). It also does not say how the
  chain is restarted so that the retained steps are consecutive.

**Repair check.** Use the last exit τ₀ from B_{3ε}(P(0)) and the first entry σ₀ into B_{3ε}(P(T)). For t_{j−1} ∈ [τ₀, σ₀] and
r_j ≤ ε:
- |z_j − P(0)| ≥ 3ε − r_j/2 > 2r_j, and likewise for P(T). So both endpoints lie outside B_{2r_j}(z_j), and the extended geodesic enters
  and leaves A.
- The discarded times τ₀ → 0 and T − σ₀ → 0, because a nonconstant finite geodesic is injective and continuous, hence a homeomorphism
  onto its image (l. 500–503). Their e-cost is at most C*·(source length).

**Algebra.** (12)–(14) combine as printed. With a = s_j − t_{j−1} ≤ A₀ b and b = t_j − s_j:
C*a + (1+η)b ≤ [(1+η) + (A₀/(A₀+1))(C*−1−η)](a+b) = C_new(a+b).

### 2.8 `prop-4.3#first-exit-confinement`, `prop-4.3#skorokhod` (rows 47, 48) and `prop-4.3#apply-tangent`

**`prop-4.3#first-exit-confinement`: NOT-A-GAP.** Lemma 4.1 is applied to the confined metrics d_n, and needs (6) for d_n.
- The costs in (8) are D(x, ∂B_{δ}(x)) and around(A_{δ,√δ}(x)) in rescaled units.
- If the closed ball B̄_{√δ}(x) lies in the confinement disk, then:
  - a point-to-circle path stopped at its first exit stays in B̄_δ(x), so the cost is the same for the confined metric;
  - a loop inside the annulus has the same length for the ambient and the internal metric (the length of a path in K for D(·,·;K)
    equals its D-length).
- P's sentence "All small endpoint annuli are contained in the rescaled domain for large n" (l. 359–360) is exactly this premise. The
  node is a formal expansion.

**`prop-4.3#skorokhod`: GENUINE (minor).** "Apply a Skorokhod subsequence representation … together with these selected endpoint variables on the
event of failure" (l. 364–366).
- Skorokhod needs a separable metric state space. 𝒟′(ℂ) is not metrizable; countable coordinates fix this.
- The failure event must enter as a mark (a Boolean flag), together with the endpoints.
- A universally measurable event transfers under equality of laws only through completion. P mentions completion (l. 326–329) but not
  for the flag.
- All are standard, so the repair is correct.

**`prop-4.3#apply-tangent`: a gap missing from the graph at the time of the audit.** Lemma 3.3 is stated for *one* whole-plane GFF h and maps ψ_n. In Prop 4.3 the fields
ĥ_n = h(z_n + r_n·) − h_{f,r_n}(z_n) vary with n, although they have one law (l. 344–345).
- To apply Lemma 3.3 one needs the joint law of (ĥ_n, d_n, e_n) to be the same Borel image of the law of ĥ_n as for h.
- That requires the metrics, including the realization of the zoomed transformed field, to be law-determined Borel functionals.
- The paper leaves this implicit. The formal proof supplies it (a varying-field form of the tangent limit in law).
- The graph has since recorded this gap at `prop-4.3#apply-tangent` (minor). P's zoom identity at l. 345–349 is correct; the auditor
  checked (ĥ_n)^{ψ_n} = (h^φ)∘B − c.

### 2.9 The IG4 variance repair (row 14). GENUINE, P (literature)

**Source.** IG4 l. 1172–1174: sup_{B(0,R)}|𝔥_n − 𝔥_n(0)| ≤ (C/R)∫_{∂B(0,2R)}|𝔥_n(y) − 𝔥_n(0)|dy (the Poisson kernel on B(0,2R) is
≤ 1/(πR) for |z| ≤ R; correct). Then "it is not difficult to see that … Var(𝔥_n(y) − 𝔥_n(0)) ≤ ε² for n ≥ n₀". There is no proof,
and n₀ must not depend on y for the integral bound.

**Repair check.**
- Markov on D_n ⊇ B(0,L), then on B(0,L) applied to the zero-boundary part, gives 𝔥_{B_L} = 𝔥_{D_n} + H′ with independent summands.
- So Var(𝔥_{D_n}(y) − 𝔥_{D_n}(0)) ≤ Var(𝔥_{B_L}(y) − 𝔥_{B_L}(0)).
- From G_{B_L}(x,w) = log|L² − x w̄| − log L − log|x−w|, the harmonic correction gives −H(y,y) − H(0,0) + 2H(0,y) = −log(1 − |y|²/L²).
- This is uniform for |y| ≤ S < L and → 0 as L → ∞.

The claim is true and the repair is correct and minimal. It is a gap in a printed proof of the cited literature, not a false statement.

**Scope.** The Lean theorem `SupercriticalConformalCovariance.TV.ig4_prop210_zeroBoundary_bounded` assumes bounded D_n
containing B(0,L_n), L_n → ∞. That is narrower than IG4 2.10(i) (harmonically non-trivial boundary, unbounded allowed), but it is all
that GM Lemma 2.4 needs after its repair by disks.

### 2.10 Markov on Greenian domains (row 46). NOT-A-GAP (new formal step)

**P.** P never decomposes on a general domain. Lemma 7.1 uses bounded disks B′ (l. 524), which IG4 Prop 2.8 (bounded W, IG4 l. 1111)
covers.

**Why the step exists.** The frozen root includes the existence conjunct (A14/A15 C2): the class of fields with a realization is
closed under conformal pullback between Greenian U, V. That needs Markov on arbitrary Greenian domains, including unbounded domains
with no circle in the complement.

**GM.** GM l. 313 asserts h|_U = h̊^U + 𝔥^U "for each deterministic open set U". That is false or meaningless for U = ℂ or ℂ minus a
polar set (no zero-boundary GFF), so it tacitly assumes non-polar complement. This is a convention issue in GM, and A14 makes exactly
that hypothesis explicit.
