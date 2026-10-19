# A small-parameter limit for higher-dimensional LFPP

Lean formalization of **Theorem 1.1** of *A small-parameter limit for higher-dimensional Liouville first
passage percolation* (18 October 2026; [AI research
paper](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/higher-dimensional-lfpp-limit.pdf),
AI-generated and unrefereed), developed under Leonardo Bonanno's direction with AI assistance.

The formalization covers **the whole theorem, in every dimension d ≥ 2, with no assumptions**: (A_{n,d})
is finite and subadditive, A_{n,d}/(n log 2) → κ_d, κ_d > 0, the LFPP exponent λ_d(ζ) exists for all
small ζ > 0, and λ_d(ζ)/ζ^{4/3} → κ_d. The paper imports the existence of λ_d from Ding–Gwynne–Zhuang
[DGZ, Proposition 1.1] and derives κ_d > 0 from a planar LFPP lower bound. Both are proved here. Proving
the DGZ input meant filling a gap in its argument: a percolation duality in ℤ^d that DGZ use without
proof. Six companion theorems are also proved: the dimension comparison (1.8), κ₂ = a*/log 16, the
variance normalization, non-vacuity, and two corollaries in dimension two that remove the hypotheses of
the [small-parameter LQG dimension](../small-gamma-dimension/) release's main theorem.

[Exact statement](../../HigherDimLFPP/Frozen/MainTheorem.lean#L31-L41) · [Frozen
definitions](../../HigherDimLFPP/Frozen/) · [Proof](../../HigherDimLFPP/Assembly/Main.lean) · [Existence
of the exponent](../../HigherDimLFPP/Exist/Exponent.lean#L100) · [Percolation
duality](../../HigherDimLFPP/Perc/) · [Focused certificate](Check.lean) · [Verification
record](verification.json)

## The theorem

Fix d ≥ 2 and a smooth, nonnegative, compactly supported, radial kernel κ on ℝ^d with ‖κ‖₂ = 1. Put
K_t(z) = t^{−(d+1)/2} κ(z/t), let W be white noise on ℝ^d × (0,∞), and for 0 < a < b let

> H_{a,b}(z) = ∫_a^b ∫ K_t(z − y) W(dy, dt).

Then Var H_{ε,1}(z) = log ε⁻¹. With U = (−2,2)^d and e₁ = (1,0,…,0), the LFPP distance D^ζ_{ε,d} is the
infimum, over paths from 0 to e₁ in U, of ∫ e^{ζ H_{ε,1}(z)} times arclength, and λ_d(ζ) is the exponent
with log D^ζ_{ε,d} / log ε → λ_d(ζ) in probability as ε ↓ 0. Let V_{n,d} be the continuous functions f :
[0,1] → ℝ^{d−1} that vanish at 0 and 1 and are affine on every dyadic interval of length 2⁻ⁿ, let E(f) =
½∫₀¹ ‖f′‖², let G_d be the centered Gaussian process with covariance π∫₀¹ (‖f‖ + ‖g‖ − ‖f − g‖) dx, and
put A_{n,d} = E sup_{f ∈ V_{n,d}} (G_d(f) − E(f)). For each d ≥ 2:

- (A_{n,d}) is **finite** and **subadditive**;
- A_{n,d}/(n log 2) → **κ_d** := inf_{n≥1} A_{n,d}/(n log 2), and **κ_d > 0**;
- the exponent **λ_d(ζ) exists** for all sufficiently small ζ > 0;
- **λ_d(ζ)/ζ^{4/3} → κ_d** as ζ ↓ 0.

The proof declaration is `HigherDimLFPP.theorem11`. Its statement, copied from
[`HigherDimLFPP/Frozen/MainTheorem.lean`](../../HigherDimLFPP/Frozen/MainTheorem.lean#L31-L41) (inside
`namespace HigherDimLFPP`, with `open MeasureTheory ProbabilityTheory Filter Topology Set`), is:

```lean
theorem theorem11 : ∀ d : ℕ, 2 ≤ d →
    (∀ n : ℕ, A n d ≠ ⊥ ∧ A n d ≠ ⊤) ∧
    (∀ n r : ℕ, A (n + r) d ≤ A n d + A r d) ∧
    Tendsto (fun n : ℕ => (A n d).toReal / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d)) ∧
    0 < kappa d ∧
    ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, ∃ lam : ℝ, IsLFPPExponent H P ζ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, IsLFPPExponent H P ζ (lam ζ)) →
        Tendsto (fun ζ => lam ζ / ζ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa d)) :=
```

Its proof is `by exact HigherDimLFPP.theorem11_impl`. The statement holds for every admissible kernel,
every white noise on any probability space and every family of continuous versions of H_{ε,1}. The
statement was frozen and audited independently against the paper before the proof was complete. Sealing
changed only the one-line proof body, the import of its provider and comment markers; a hash of the
elaborated statement confirms that it is unchanged. [`Check.lean`](Check.lean) restates it verbatim and
checks that `theorem11` proves it. It also derives, from `field_exists` and `theorem11`, that an exponent
exists for an actual field in every dimension d ≥ 2, so the hypotheses can be met.

## All results

Each result is a frozen theorem in its own file under
[`HigherDimLFPP/Frozen/`](../../HigherDimLFPP/Frozen/), proved by a one-line `by exact` of its provider.

| Result | Lean declaration | Source |
| --- | --- | --- |
| **Theorem 1.1** for every d ≥ 2: A_{n,d} finite and subadditive, A_{n,d}/(n log 2) → κ_d, κ_d > 0, λ_d(ζ) exists for small ζ, and λ_d(ζ)/ζ^{4/3} → κ_d | [`theorem11`](../../HigherDimLFPP/Frozen/MainTheorem.lean#L31-L41) | Theorem 1.1, (1.3), (1.7) |
| (d − 1)^{2/3} κ₂ ≤ κ_d ≤ (d − 1) κ₂ for every d ≥ 2 | [`dimension_comparison`](../../HigherDimLFPP/Frozen/DimensionComparison.lean#L24-L25) | (1.8), Lemma 2.3 |
| κ₂ = a*/log 16, where a* = `LQGDimension.aStar` is the constant of the small-parameter LQG dimension paper | [`kappa_two_eq`](../../HigherDimLFPP/Frozen/KappaTwo.lean#L25) | new; replaces the paper's positivity input |
| For 0 < a < b and every d ≥ 1: k_{a,b,z}(t,y) = 1_{(a,b)}(t) K_t(z − y) is square integrable with squared norm log(b/a), so Var H_{a,b}(z) = log(b/a) | [`bandVec_norm_sq`](../../HigherDimLFPP/Frozen/BandVecNormSq.lean#L27-L29) | §1.1 |
| Non-vacuity: admissible kernels exist in every dimension d ≥ 1, and for each there is a probability space with a white noise and continuous versions of H_{ε,1} for all ε ∈ (0,1) | [`field_exists`](../../HigherDimLFPP/Frozen/FieldExists.lean#L25-L31) | §1.1 |
| d = 2, LQG dimension: (d_γ − 2)/γ^{4/3} → 2^{−1/3} κ₂ as γ ↓ 0, for the LQG dimension d_γ = `LQGMetric.dGamma γ` | [`lqg_dimension_asymptotics`](../../HigherDimLFPP/Frozen/LQGDimensionAsymptotics.lean#L27-L29) | the small-parameter LQG dimension paper, Theorem 1.1, (1.6), with its hypotheses discharged |
| d = 2, whole-plane GFF: for circle-average LFPP of the whole-plane GFF with h₁(0) = 0, the exponent exists for all small ξ > 0 and λ(ξ)/ξ^{4/3} → κ₂ | [`gff_circle_average_lfpp`](../../HigherDimLFPP/Frozen/GFFCircleAverage.lean#L27-L32) | Lemma A.1 and the planar convention of the paper's reference [5] |

The constants are characterized variationally; no numerical value is claimed.

## The twenty frozen definitions

Every project definition in these statements is frozen in its own file under
[`HigherDimLFPP/Frozen/`](../../HigherDimLFPP/Frozen/). The other names come from Mathlib, from the
[small-parameter LQG dimension release](../small-gamma-dimension/) (`LQGDimension.aStar`,
`LQGDimension.gaussianExpectedMax`, `LQGDimension.IsGFFCircleAverage`, `LQGDimension.IsLFPPExponent`) and
from the [LQG metric release](../lqg-metric/) (`LQGMetric.dGamma`).

| Paper | Lean | Definition |
| --- | --- | --- |
| ℝ^d | [`Rd d`](../../HigherDimLFPP/Frozen/Rd.lean#L20) | `EuclideanSpace ℝ (Fin d)`, with the Euclidean norm. |
| V_{n,d} | [`Vg E n`](../../HigherDimLFPP/Frozen/Vg.lean#L24), with E = ℝ^{d−1} | Functions ℝ → E that vanish at 0, at 1 and outside [0,1], and are affine on each closed dyadic interval [k2⁻ⁿ, (k+1)2⁻ⁿ]. |
| E(f), (1.4) | [`energy f`](../../HigherDimLFPP/Frozen/Energy.lean#L22) | ½∫₀¹ ‖f′(x)‖² dx, with Mathlib's derivative. |
| the covariance (1.5) | [`gCov f g`](../../HigherDimLFPP/Frozen/GCov.lean#L22) | π∫₀¹ (‖f(x)‖ + ‖g(x)‖ − ‖f(x) − g(x)‖) dx. |
| E sup (G(f) − E(f)) | [`Ag E n`](../../HigherDimLFPP/Frozen/Ag.lean#L26) | The supremum, over finite families F ⊆ V_n(E), of the expected maximum of G(f) − E(f), f ∈ F, for the centered Gaussian vector with covariance `gCov`; in `EReal`. |
| A_{n,d}, (1.6) | [`A n d`](../../HigherDimLFPP/Frozen/A.lean#L20) | `Ag (Rd (d - 1)) n`. |
| κ_d, (1.7) | [`kappa d`](../../HigherDimLFPP/Frozen/Kappa.lean#L22) | The real infimum over n ≥ 1 of `(A n d).toReal / (n log 2)`. |
| the kernel κ | [`IsLFPPKernel κ`](../../HigherDimLFPP/Frozen/IsLFPPKernel.lean#L26) | C^∞, nonnegative, compactly supported, radial, with ∫κ² = 1. |
| K_t | [`scaleKernel κ t`](../../HigherDimLFPP/Frozen/ScaleKernel.lean#L20) | z ↦ t^{−(d+1)/2} κ(z/t). |
| the noise space | [`WN d`](../../HigherDimLFPP/Frozen/WN.lean#L26) | L²(ℝ × ℝ^d), with the time coordinate first. |
| W | [`IsWhiteNoise P W`](../../HigherDimLFPP/Frozen/IsWhiteNoise.lean#L24) | An isonormal Gaussian process on `WN d`: each W(f) is measurable, and every finite combination ∑ cᵢ W(fᵢ) is centered Gaussian with variance ‖∑ cᵢ fᵢ‖². |
| k_{a,b,z} | [`bandKernel κ a b z`](../../HigherDimLFPP/Frozen/BandKernel.lean#L22) | (t, y) ↦ 1_{(a,b)}(t) K_t(z − y). |
| k_{a,b,z} in L² | [`bandVec κ a b z`](../../HigherDimLFPP/Frozen/BandVec.lean#L23) | Its class in `WN d`, or 0 if it is not square integrable; `bandVec_norm_sq` excludes the second case for 0 < a < b. |
| H_{a,b}, (1.1) | [`IsBandVersion P W κ a b H`](../../HigherDimLFPP/Frozen/IsBandVersion.lean#L23) | H(·, ω) is continuous for every ω, each H(z) is measurable, and H(z) = W(k_{a,b,z}) almost surely for every z. |
| U | [`cube d`](../../HigherDimLFPP/Frozen/Cube.lean#L19) | (−2,2)^d. |
| e₁ | [`e₁ d`](../../HigherDimLFPP/Frozen/E1.lean#L19) | (1, 0, …, 0). |
| paths in (1.2) | [`IsAdmissiblePath d γ`](../../HigherDimLFPP/Frozen/IsAdmissiblePath.lean#L27) | γ is continuous on [0,1], maps [0,1] into U, runs from 0 to e₁, and is C¹ on each piece of a finite partition of [0,1]. |
| the LFPP length | [`lfppLength ζ φ γ`](../../HigherDimLFPP/Frozen/LfppLength.lean#L25) | ∫₀¹ e^{ζ φ(γ(t))} ‖γ′(t)‖ dt, so arclength is counted with multiplicity. |
| D^ζ_{ε,d}, (1.2) | [`lfppDistance d ζ φ`](../../HigherDimLFPP/Frozen/LfppDistance.lean#L21) | The infimum of `lfppLength ζ φ γ` over admissible paths γ, applied to φ = H_{ε,1}. |
| λ_d(ζ), (1.3) | [`IsLFPPExponent H P ζ λ`](../../HigherDimLFPP/Frozen/IsLFPPExponent.lean#L23) | `TendstoInMeasure`: log D^ζ_{ε,d} / log ε → λ in probability as ε ↓ 0, with D^ζ_{ε,d} = `lfppDistance d ζ (H ε)`. |

## Correspondence with Theorem 1.1

| Paper | Lean conjunct | Comment |
| --- | --- | --- |
| (A_{n,d})_{n≥1} is finite | `∀ n, A n d ≠ ⊥ ∧ A n d ≠ ⊤` | Also for n = 0, where A_{0,d} = 0. |
| (A_{n,d}) is subadditive | `∀ n r, A (n + r) d ≤ A n d + A r d` | In `EReal`, for all n, r ≥ 0. |
| κ_d = inf_{n≥1} A_{n,d}/(n log 2) = lim, finite | the definition of `kappa`, and `Tendsto (fun n => (A n d).toReal / (n * log 2)) atTop (𝓝 (kappa d))` | A limit in ℝ is finite. Finiteness of A_{n,d} makes `toReal` exact. |
| κ_d > 0 | `0 < kappa d` | The paper states it as a consequence of the planar lower bound; here it is proved (see below). It also rules out the junk value of a real infimum. |
| λ_d(ζ) exists for all small ζ > 0 | `∃ ζ₀ > 0, ∀ ζ ∈ Ioo 0 ζ₀, ∃ lam, IsLFPPExponent H P ζ lam` | The paper imports this from [DGZ, Proposition 1.1]; here it is a conclusion. |
| λ_d(ζ)/ζ^{4/3} → κ_d | `∀ lam, (∃ ζ₀ > 0, ∀ ζ ∈ Ioo 0 ζ₀, IsLFPPExponent H P ζ (lam ζ)) → Tendsto (fun ζ => lam ζ / ζ ^ (4/3)) (𝓝[>] 0) (𝓝 (kappa d))` | Stated for every exponent function; exponents are unique, and the previous conjunct shows one exists. |

## Scope and statement conventions

- **The white-noise model.** The paper's W is white noise on ℝ^d × (0,∞) with Lebesgue control measure.
  Here W is an isonormal Gaussian process on L²(ℝ × ℝ^d), time first; only t > 0 enters, through the
  kernels. H_{ε,1} is any continuous version of z ↦ W(k_{ε,1,z}), which is how the path integrals in
  (1.2) are read. The theorem quantifies over every kernel, every probability space in Lean's `Type`
  universe, every white noise and every family of continuous versions. P is not assumed to be a
  probability measure: the white-noise axiom forces it. All laws, and the exponent itself, are the same
  for every realization: [`exponent_exists`](../../HigherDimLFPP/Exist/Exponent.lean#L100) chooses λ_d(ζ)
  before the probability space. The frozen files cite this choice as ruling H10.
- **Paths.** The paper takes the infimum in (1.2) over rectifiable paths. Admissible paths here are
  piecewise C¹ maps [0,1] → U from 0 to e₁, with arclength counted with multiplicity. This is the path
  class of DGZ and of the planar paper. The paper's Appendix A.1 notes that the two infima agree at every
  fixed cutoff, because the weight is continuous and positive and rectifiable paths can be approximated
  by polygons in the open cube. That equality is not formalized. The frozen files cite this choice as
  ruling H8.
- **Smoothness.** "Smooth" is C^∞ (`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`), not analytic: a compactly
  supported analytic kernel would vanish.
- **Expected suprema.** A_{n,d} is the supremum over finite subfamilies of expected maxima, the
  convention of the planar release. It equals E sup for every continuous (separable) version, and needs
  no measurability of a supremum over an uncountable family.
- **Junk values.** `EReal.toReal`, real infima and `bandVec` have default values outside their domains.
  The finiteness conjunct, `0 < kappa d` and `bandVec_norm_sq` exclude them. LFPP distances of continuous
  fields are positive and finite, and measurable (by rational polygonal approximation); both are proved.
- **Convergence in probability** is Mathlib's `TendstoInMeasure`, as ε ↓ 0. The limits in ζ are along ζ ↓
  0 (`𝓝[>] 0`).
- **Quantifier order.** In `theorem11`, ζ₀ may depend on the realization. This is harmless: by
  `exponent_exists` the exponent exists for every ζ > 0 and does not depend on the realization.

## Differences from the paper

### The existence of the exponent is proved

The paper's Theorem 1.1 uses the fixed-parameter exponent λ_d(ζ), supplied by [DGZ, Proposition 1.1] and
its Appendix A.1. Here it is a theorem for every ζ > 0
([`exponent_exists`](../../HigherDimLFPP/Exist/Exponent.lean#L100)). The formalized route is DGZ §§2–3:
concentration of log D (DGZ Lemma 2.7), the quantile Lemmas 3.2 and 3.5, the crude bounds e^{−An} ≤ λ_n ≤
e^{An}, the near-subadditivity of Lemma 3.3 ([`lemma33`](../../HigherDimLFPP/Exist/Lemma33.lean#L514))
and Proposition 3.1 by Hammersley's lemma ([`prop31`](../../HigherDimLFPP/Exist/Prop31.lean#L56)).
Appendix A.1 then passes from dyadic to arbitrary cutoffs.

**The duality gap and its repair.** In the proof of Lemma 2.10 and in Step 3 of Lemma 3.3, DGZ invoke
"duality" for site percolation on ℤ^d without proof or reference. In d = 2 this is planar duality. In d ≥
3 the facts needed (the outer boundary of a finite ∗-connected set is connected; neighbouring enclosing
clusters meet) are boundary-connectivity theorems of Deuschel–Pisztora and Timár type. The statements are
true, but they are not proved in DGZ. Both uses are replaced by proved statements in
[`HigherDimLFPP/Perc/`](../../HigherDimLFPP/Perc/), which depends only on Mathlib:

1. a mod-2 discrete Poincaré lemma on ℤ^d: a ℤ/2-valued 1-cochain with vanishing plaquette sums is a
   coboundary ([`poincareMod2`](../../HigherDimLFPP/Perc/Poincare.lean#L234));
2. exterior-boundary connectivity: the exterior sites ∗-adjacent to a finite ∗-connected set form a
   nearest-neighbour-connected set ([`extBoundaryConn`](../../HigherDimLFPP/Perc/ExtBoundary.lean#L150));
3. a surgery lemma: a lattice path between open sites whose closed clusters are small and do not enclose
   the endpoints can be rerouted through open sites near the path
   ([`surgeryLemma`](../../HigherDimLFPP/Perc/Surgery.lean#L100));
4. Peierls, diameter and enclosure bounds for finite-range site percolation
   ([`peierlsD`](../../HigherDimLFPP/Perc/Peierls.lean#L289),
   [`diameterBound`](../../HigherDimLFPP/Perc/Clusters.lean#L94),
   [`enclosureBound`](../../HigherDimLFPP/Perc/Clusters.lean#L243)). The enclosure bound replaces DGZ's
   Lemma 2.10. It needs d ≥ 2 and is false for d = 1.

In Lemma 3.3, the event that 0 and e₁ lie in infinite open clusters is replaced by small closed clusters
near the box and open, unenclosed endpoints. The path is then built with the surgery lemma. Infinite
clusters and the uniqueness of enclosing clusters are never used.

Other changes to DGZ's arguments change constants or routes, not statements. Oscillation bounds over
boxes replace gradient bounds, so no smooth version of the field is needed. Lower quantiles replace the
continuity of laws. DGZ's Lemma 3.4 is replaced by a form uniform in n > m ≥ 1. The crude bounds are
proved before Hammersley's lemma is applied: DGZ's proof of Proposition 3.1 needs finiteness, which comes
from their Lemma 3.7, proved later.

### Positivity without an LFPP input

The paper derives κ_d > 0 from the planar lower bound λ₂(ζ) ≥ cζ^{4/3} of its reference [5], through
Lemma A.1 and (1.8). That route needs the identification of the planar LFPP exponent, Lemma A.1 and the
existence of the planar exponent. The formalization proves instead the exact identity κ₂ = a*/log 16
([`kappa_two_eq`](../../HigherDimLFPP/Frozen/KappaTwo.lean#L25)): the planar paper's index spaces at mesh
16⁻ᵏ = 2⁻⁴ᵏ are V_{4k,2}, with the same covariance, energy and expected-supremum convention. Here a* > 0
is a purely Gaussian theorem of the planar release (`LQGDimension.theorem11_aStar`). Then (1.8) gives κ_d
≥ (d − 1)^{2/3} κ₂ > 0.

### Comparisons without the existence of the exponent

The paper's comparisons (4.25) and (5.29) are inequalities for λ_d(ζ), so they use its existence. Here
both are proved first as probability bounds for log D^ζ_{ε,d} / log ε
([`upperComparison_limsup`](../../HigherDimLFPP/Upper/UpperAssembly.lean#L331),
[`lowerComparison_liminf`](../../HigherDimLFPP/Lower/LowerAssembly.lean#L346)), and combined with the
existence of the exponent by a squeeze
([`theorem11_of_inputs`](../../HigherDimLFPP/Assembly/Reductions.lean#L44)). The limit therefore holds
for every exponent function. The upper comparison rests on Lemma 4.3
([`goodRecordMeanBound_all`](../../HigherDimLFPP/Upper/LocalMean.lean#L532)), and the lower comparison on
Lemma 5.3 ([`lemma53Holds_holds`](../../HigherDimLFPP/Lower/Lemma53.lean#L649)).

### Corrections adopted from the audits

The proof follows a corrected rewrite of the paper, prepared from independent section-by-section audits.
The main items:

- **Lemma 4.4 (records).** As literally stated it is false for records whose cube data cannot come from
  an actual chain. A bad record whose two adverse cubes coincide admits near-point chords, whose variance
  grows like δ⁻¹ log(1/ε). The record families carry the chord-length constraints, as in the planar
  formalization; then every claim of the lemma holds, uniformly in the cutoff.
- **Lemmas 3.2 and 3.3.** The paper's Lemma 3.2 gives convergence of expected suprema, but (4.13) needs
  them with an energy drift; Lemma 3.2 is proved in that form, with uniform covariance convergence on
  vertex balls. The paper's Lemma 3.3 is not needed: Lemma 4.3 uses a covariance limit for explicit
  polygons and Lemma 5.2 a same-parameter coupling. The constants of Section 4 are explicit (threshold a₀
  = c₀/K with c₀ = 1/500, and an explicit good family).
- **Section 5.** The W∞ control is stated for distribution functions, without box suprema, and frames are
  composed recursively.
- **Sections 2–3.** Dudley's entropy integral is not used; finiteness of A_{n,d} follows from Lemma 2.3
  and the planar identity A_{4k,2} = a_k. The concentration bound (2.4) is used with the constant π²/8
  instead of 1/2, which changes only absolute constants. The white-noise representation of G_d over
  spheres is not used: positive semidefiniteness of (1.5) is proved by Gaussian projection. The facts the
  paper uses without statement (point variances, increments, band additivity, continuous versions,
  oscillation and supremum bounds, stochastic Fubini) are stated and proved. Derivative bounds are
  replaced by increment bounds.
- **Appendix A.1.** The Cameron–Martin and concentration-about-a-median step is replaced by DGZ's Lemma
  2.7 and a quantile lemma, and the cutoff comparison by an explicit tail bound uniform in ε.

### The two-dimensional corollaries

- [`gff_circle_average_lfpp`](../../HigherDimLFPP/Frozen/GFFCircleAverage.lean#L27-L32). For every
  circle-average process of the whole-plane GFF normalized by h₁(0) = 0
  (`LQGDimension.IsGFFCircleAverage`), the circle-average LFPP exponent (`LQGDimension.IsLFPPExponent`:
  paths in ℂ from 0 to 1 inside (−2,2)²) exists for all small ξ, and λ(ξ)/ξ^{4/3} → κ₂ = a*/log 16. This
  is the planar release's `LQGDimension.theorem11_lambda` **without its existence hypothesis**. The
  circle averages are built from the same κ-white noise as H_{ε,1}. The heat-kernel GFF of the LQG metric
  release would not do: its difference from H_{ε,1} has variance of order log(1/ε). The proof identifies
  the covariance with the circle-average covariance (Frullani, Newton's theorem), proves the
  circle-average part of the paper's Lemma A.1, and transfers exponents between paths in ℂ and in ℝ², and
  laws to every circle-average process.
- [`lqg_dimension_asymptotics`](../../HigherDimLFPP/Frozen/LQGDimensionAsymptotics.lean#L27-L29). (d_γ −
  2)/γ^{4/3} → 2^{−1/3} κ₂ = 2^{−1/3} a*/log 16, where d_γ = `LQGMetric.dGamma γ` = 2/χ_γ and χ_γ is the
  Liouville graph distance exponent of Ding–Zeitouni–Zhang (Ding–Gwynne's d_γ). This is
  `LQGDimension.theorem11_dimension` with its hypotheses discharged by theorems of the [LQG
  metric](../lqg-metric/) and [Gaussian LQG distance](../gaussian-lqg-distance/) releases
  (`GaussianLQG.dimensionInput_holds`, `GaussianLQG.dgThm1_5_holds`,
  `LQGMetric.DG.isLFPPExponent_of_dgThm1_5`). The limit implies d_γ → 2, so the default value d_γ = 4
  that `dGamma` would take if no exponent existed does not occur for small γ.

### Not formalized

- The equality of the rectifiable and piecewise C¹ infima in (1.2) (App. A.1; see above).
- The first part of Lemma A.1 (mollified fields in general d), and other regularizations. Only the
  circle-average part in d = 2 is formalized.
- The paper's Lemma 3.3, which no step needs after the changes above.
- Any statement uniform in d. As in the paper, d is fixed and constants may depend on it; no rate as d →
  ∞ is claimed.
- Numerical values of κ_d or a*.

## Verification

The export adds **160 `HigherDimLFPP` modules**, copied byte-for-byte from development commit
`ab73b5b7338fe49917894eac509a727ef7a39efc`, the commit that sealed `theorem11`. The local import closure
of the seven frozen theorems has **3,562 modules**: 160 HigherDimLFPP, 2,362 LQGMetric, 931
QuantumZipper, 107 LQGDimension and 2 GaussianLQG. The other 3,402 were already part of this release and
are byte-identical. Lean `v4.34.0-rc2` and Mathlib `a4c8ef0a69f52ec80525d5086bb3542f4660faaf` match the
rest of the release.

- **Kernel replay (development workspace).** `lake env leanchecker --fresh HigherDimLFPP` re-checked, in
  a fresh environment, every declaration in the import closure of the development root module, which
  imports the seven frozen theorem modules, Mathlib included. It **exited with code 0**, with no errors,
  on 19 October 2026 (08:55–09:08 CEST, 12 min 34 s), on the Lean sources of commit `ab73b5b73`.
- **Fresh build and focused certificate (this export).** The 160 new modules were **compiled afresh from
  the exported files**, with the public verifier's per-module settings. The 3,402 previously released
  dependencies were reused from a cache after all 3,562 source files were checked byte-for-byte.
  [`Check.lean`](Check.lean) was then compiled afresh and **passed**. It checks the verbatim statements
  of the seven theorems, prints the twenty definitions, derives an exponent for an actual field, and
  checks the existence of the exponent, the percolation statements and both comparisons. It rejects
  `sorry` and audits **54,822 project declarations and 138,850 reachable declarations**, allowing only
  `propext`, `Classical.choice` and `Quot.sound`. See [verification.json](verification.json).
- The [public workflow](https://github.com/leobon12/lean-formalizations/actions/workflows/verify.yml)
  rebuilds every module from source and runs the combined [certificate](../../Certificate.lean), which
  includes these seven theorems.

To reproduce from the public repository:

```sh
lake exe cache get
lake build HigherDimLFPP.Frozen.MainTheorem HigherDimLFPP.Frozen.DimensionComparison \
  HigherDimLFPP.Frozen.KappaTwo HigherDimLFPP.Frozen.BandVecNormSq HigherDimLFPP.Frozen.FieldExists \
  HigherDimLFPP.Frozen.LQGDimensionAsymptotics HigherDimLFPP.Frozen.GFFCircleAverage
lake env lean results/higher-dim-lfpp/Check.lean
for m in MainTheorem DimensionComparison KappaTwo BandVecNormSq FieldExists \
    LQGDimensionAsymptotics GFFCircleAverage; do
  lake env leanchecker --fresh HigherDimLFPP.Frozen.$m
done
```

`leanchecker --fresh` accepts a single module, hence the loop; each run replays Mathlib as well.

The sources are published byte-for-byte. Their docstrings cite development documents that are not part of
this snapshot: the corrected rewrite ("blueprint"), rulings (such as H8 and H10 above), audits, work
packets and the frozen-anchor manifest. Kernel checking establishes the Lean proofs; correspondence with
the paper is the subject of the conventions above.

## Credits

The paper builds on Ding–Gwynne–Zhuang [DGZ, arXiv:2310.03996] and on the small-parameter LQG dimension
paper (its reference [5]); the formalization also uses results of Ding–Zeitouni–Zhang, Ding–Gwynne and
Gwynne–Miller through the earlier releases. It reuses the [small-parameter LQG
dimension](../small-gamma-dimension/), [LQG metric](../lqg-metric/), [Quantum Zipper](../quantum-zipper/)
and [Gaussian LQG distance](../gaussian-lqg-distance/) releases. The original mathematical results are
due to their authors; source-file attribution is retained. The statements were frozen and audited
following Scott Armstrong's
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) workflow.

[All released formalizations](../../README.md)
