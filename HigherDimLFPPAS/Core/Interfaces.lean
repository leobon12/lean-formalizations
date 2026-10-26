import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.IsWeakExpMetric
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.TendstoInProbLU
import HigherDimLQGMetric.Frozen.AEps
import HigherDimLQGMetric.Frozen.LfppDist
import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLQGMetric.Frozen.ConvTrunc
import HigherDimLQGMetric.Frozen.KernelSymbol
import HigherDimLQGMetric.Core.Defs
import HigherDimLQGMetric.Metric.Internal
import HigherDimLQGMetric.Metric.ContMetric
import HigherDimLQGMetric.Weak.DetLFPPMetric
import HigherDimLQGMetric.Sec4.LocField
import HigherDimLQGMetric.Sec4.LocAnalysis
import HigherDimLQGMetric.Sec4.Basic
import HigherDimLQGMetric.Sec4.Lemma41Uniform
import HigherDimLQGMetric.Sec4.Lemma43
import HigherDimLQGMetric.Sec4.Lemma44
import HigherDimLQGMetric.Sec4.Radii
import HigherDimLQGMetric.Shell.Defs
import HigherDimLQGMetric.ConvField.RadialCont
import LQGMetric.Metric.Geodesic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
import Mathlib.Probability.Moments.Variance

/-!
# Interface statements shared between packets (orchestrator-owned; drafted by planner PL, 2026-10-26)

Path: `HigherDimLFPPAS/Core/Interfaces.lean` (namespace `HigherDimLFPPAS.Core`). Interface-first scheduling (the pattern
of `HigherDimLQGContinuity/Core/Interfaces.lean`, its rulings N6/N12): a statement that one packet proves and other
packets consume before it lands is defined here **once**, as a named `Prop`; consumers take it as a hypothesis,
producers prove it (as an implication from the standing hypotheses `Setting` and the interfaces they consume), and the
final assembly (packet ASM) discharges every hypothesis. Workers import this module and never edit or redefine it.
**None of these `Prop`s may appear in a frozen statement**: they are internal interfaces below the anchors.

Imports: `HigherDimLQGMetric`, `HigherDimLFPP` (through it), `LQGMetric`, Mathlib, and one frozen *definition* of this
library (`IsAdmissibleSeed`, sorry-free). No frozen theorem anchor, no packet module.

Sources of the shapes (corrected statements; "Details for later use" of the audits): `planning/audits/MA1-sections-1-3.md`
(Def. 3.1′ = `GoodAnnulus`; Lemmas 2.4, 2.5, 3.2, 3.3: A6, A7, A9–A12), `MA2-sections-4-6.md` (Props 4.1, 5.1, Lemmas
6.1–6.2, Theorem 1.2: D-A … D-E and its Details (c)), `MA3-inputs.md` (Lemma 2.3 = P2–P7, Lemma 2.7 = P9–P11),
`MA4-crosscheck-3-5.md`, `S1-statement-audit.md`; rulings L6–L8. Planner's checks: this module
elaborates with no diagnostics; `SeedFacts` is proved from the repository for
`IsLFPPKernel` seeds and from packet G1's copies for `IsAdmissibleSeed` seeds (standard axioms); `GoodAnnulus` implies
packet D4's `d4GoodAt` and `Comp` is D4's `d4Comparison` by `Iff.rfl`.

Contents:
* §1 Objects: `locFieldC`, `convFieldC`, `Meps` (`M_ε`), `Neps` (`N_ε`), `locFieldR`, `locFieldRC`, `MepsR` (the rescaled
  localized metric of (3.8)), `cRatio` (`c_ε(r)`, (1.8)), `window` (`𝒩_ε(u)`, (3.1)), `mesh` (Lemma 3.3), `GoodAnnulus`
  (`E′_ε(z,r)`, Definition 3.1′) with `goodAnnulus_symm`, `IsInternalGeodesic`, `Comp` (`𝒞^{G→G'}_{ε,R}(C,q)`, (4.1)),
  `ASConclusion` ((1.7)).
* §2 Standing hypotheses: `SeedFacts` (kernel and field facts of the seed), `Setting` (hypotheses of Theorem 1.2 with a
  general `Q > √(2d)`, MA1 MN-1).
* §3 Appendix A: `Lemma23i`, `Lemma23ii`, `Lemma23iii`, `RescaledLoc` ((3.9)), `FieldGauss`.
* §4 Lemmas 2.4, 2.5, 2.7 and the rescaling: `Lemma24Conv`, `Lemma24Confine`, `Lemma25Unif`, `Lemma25Window`,
  `Lemma25Exponent`, `LocFieldScaling`, `CoordScaling`, `AffineInternalScaling`, `UnitSpeedAdmissible`, `PairLaw`,
  `RescaledConv`, `Lemma43SStmt`, `Lemma44SStmt`, `Lemma45SStmt`, `Lemma27Stmt`.
* §5 Section 3: `Lemma32Marginal`, `Lemma32Meas`, `Lemma33Stmt`.
* §6 Sections 4–6: `Prop41Stmt`, `Prop51Stmt`, `Lemma61Stmt`, `Lemma62Stmt`.

Conventions (junk safety): internal metrics, set distances and lengths are `ℝ≥0∞`-valued (`⊤` if no rectifiable path);
probabilities of possibly non-measurable sets are outer measures (as in `TendstoInProbLU` and `theorem12`; Borel–Cantelli
is `MeasureTheory.ae_eventually_notMem`, which needs no measurability); real exponents are `Real.rpow`, `(256 : ℝ) ^ (-k)`
is `zpow`. Every junk branch below (`if … then … else`) is never taken where the interfaces are used (`0 < ε < 1`,
admissible seed), as recorded in each docstring. Each interface's docstring states its source and why it is true and
not vacuous; `PACKET-PLAN.md` §1 lists producer and consumers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal

namespace HigherDimLFPPAS.Core

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## §1 Objects -/

open Classical in
/-- `ĥ*_ε` of (2.5) bundled as a continuous function. Junk `0` only off continuity; `locField κ ε g` is continuous for
**every** distribution `g` once `K` is smooth and `0 < locRad ε` (`HigherDimLQGMetric.continuous_locField`), i.e. for
every `ε ∈ (0, 1)` and admissible seed. -/
def locFieldC (κ : Rd d → ℝ) (ε : ℝ) (g : DistRd d) : C(Rd d, ℝ) :=
  if hc : Continuous (locField κ ε g) then ⟨locField κ ε g, hc⟩ else 0

open Classical in
/-- `h*_ε = h ∗ K_ε` bundled as a continuous function (junk `0` off continuity; for a normalized LGF it is continuous
for all `ε > 0` simultaneously, a.s.: `SeedFacts.jointCont`). -/
def convFieldC (κ : Rd d → ℝ) (ε : ℝ) (g : DistRd d) : C(Rd d, ℝ) :=
  if hc : Continuous (convMollify κ ε g) then ⟨convMollify κ ε g, hc⟩ else 0

open Classical in
/-- `M_ε = 𝔞_ε⁻¹ D̂^ε_g` of (2.6) as a continuous length metric (`fieldLfppMetric_isLength`; its global distance is the
`C¹`-path LFPP distance of `ĥ*_ε`, `fieldLfpp_eq_lfppDistOn`). Junk: unnormalized when `aEps κ ξ ε ≤ 0`, which never
happens for admissible seeds (`SeedFacts.aEps_pos`). -/
def Meps (κ : Rd d → ℝ) (ξ ε : ℝ) (g : DistRd d) : ContMetric d :=
  if ha : 0 < aEps κ ξ ε then
    (fieldLfppMetric ξ (locFieldC κ ε g)).smul (aEps κ ξ ε)⁻¹ (inv_pos.2 ha)
  else fieldLfppMetric ξ (locFieldC κ ε g)

open Classical in
/-- `N_ε = 𝔞_ε⁻¹ D^ε_g` of (2.6) as a continuous length metric. Where `convMollify κ ε g` is continuous and
`aEps κ ξ ε > 0`, `(Neps κ ξ ε g).1 = (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g` (`fieldLfpp_eq_lfppDistOn`,
`ContMetric.smul_apply`): the metric of the frozen conclusion (1.7). -/
def Neps (κ : Rd d → ℝ) (ξ ε : ℝ) (g : DistRd d) : ContMetric d :=
  if ha : 0 < aEps κ ξ ε then
    (fieldLfppMetric ξ (convFieldC κ ε g)).smul (aEps κ ξ ε)⁻¹ (inv_pos.2 ha)
  else fieldLfppMetric ξ (convFieldC κ ε g)

/-- The localized field of (3.8): kernel scale `δ = ε / r`, truncation radius `locRad ε / r = δ L_ε` (the logarithmic
factor is `L_ε`, not `L_δ`): `ĝ_{δ,ε} = Z_ε⁻¹ g ∗ (K_δ ψ(·/(δ L_ε)))` (MA1 A10.1, MA3 P2.4′). For `r = 1` it is
`locField κ ε g`. The deterministic identity relating it to `locField` at `z + r·` is the interface `LocFieldScaling`. -/
def locFieldR (κ : Rd d → ℝ) (ε r : ℝ) (g : DistRd d) (x : Rd d) : ℝ :=
  (locMass κ (ε / r) (locRad ε / r))⁻¹ * g (locTest κ (ε / r) (locRad ε / r) x)

open Classical in
/-- `locFieldR` bundled as a continuous function (junk `0` off continuity; continuous for every `g` when `K` is
smooth and `0 < locRad ε / r`, as `continuous_locField`). -/
def locFieldRC (κ : Rd d → ℝ) (ε r : ℝ) (g : DistRd d) : C(Rd d, ℝ) :=
  if hc : Continuous (locFieldR κ ε r g) then ⟨locFieldR κ ε r g, hc⟩ else 0

open Classical in
/-- The rescaled localized metric `𝔐_{ε,δ}(g) = 𝔞_δ⁻¹ D^{(ĝ_{δ,ε})}`, `δ = ε / r` (MA1 A10.1, MA3 P9(b)). Lemma 3.2's
normalization (MA1 A10.1): a.s. `M_ε(z + r·, z + r·) = c_ε(r) r^{ξQ} e^{ξ h_r(z)} 𝔐_{ε,ε/r}(h^{z,r})`. Junk as `Meps`. -/
def MepsR (κ : Rd d → ℝ) (ξ ε r : ℝ) (g : DistRd d) : ContMetric d :=
  if ha : 0 < aEps κ ξ (ε / r) then
    (fieldLfppMetric ξ (locFieldRC κ ε r g)).smul (aEps κ ξ (ε / r))⁻¹ (inv_pos.2 ha)
  else fieldLfppMetric ξ (locFieldRC κ ε r g)

/-- `c_ε(r) = r 𝔞_{ε/r} / (r^{ξQ} 𝔞_ε)` of (1.8); by `rfl` the repository's `l9bRatio` with `c_r = r^{ξQ}` (checked). -/
abbrev cRatio (κ : Rd d → ℝ) (ξ Q ε r : ℝ) : ℝ :=
  l9bRatio κ ξ (fun s => s ^ (ξ * Q)) ε r

/-- The window `𝒩_ε(u) = {256^{-k} : k ∈ ℤ} ∩ [ε^u, ε^{u/2}]` of (3.1). Definitionally equal to
`HigherDimLFPPAS.Windows.winRadiusWindow ε u` (packet D6: counting `winRadiusWindow_count`, ordering, disjointness). -/
def window (ε u : ℝ) : Set ℝ :=
  (fun k : ℤ => (256 : ℝ) ^ (-k)) ''
    {k : ℤ | ε ^ u ≤ (256 : ℝ) ^ (-k) ∧ (256 : ℝ) ^ (-k) ≤ ε ^ (u / 2)}

/-- The mesh of Lemma 3.3: grid points of spacing `ε^u/(100 d)` in `B_{R+1}`. Every point of `B_R` is within `ε^u/100`
of a mesh point once `ε^u/100 < 1` (`HigherDimLQGMetric.exists_gridPt_near`, error `≤ d · s`; MA2 §4.1.4). -/
def mesh (d : ℕ) (ε u R : ℝ) : Set (Rd d) :=
  (gridPts (ε ^ u / (100 * (d : ℝ))) : Set (Rd d)) ∩ ball (0 : Rd d) (R + 1)

/-- The Borel good event `E′_ε(z, r)` of Definition 3.1′ (MA1 A9), for the ordered pair `(G, G')` = `(D, M_ε)`, ratio
`c = c_ε(r)`, constants `A, η` and connection radius `b = b_ε = 8 ε^{q₀}`; `U = A_{r/4, 2r}(z)`, `V = A_{r/2, 3r/2}(z)`,
`S_in = S_{3r/4}(z)`, `S_out = S_r(z)`, `δ_G = G(S_in, S_out; U)`:
(i′) `G'(x,y;U) ≤ (1+η) c G(x,y;V)`, `G(x,y;U) ≤ (1+η) c⁻¹ G'(x,y;V)` on `S_in × S_out`;
(ii′) `G(x,y;U) ≤ A δ_G`, `G'(x,y;U) ≤ A δ_{G'}` on `S_in × S_in`;
(iii′) `G'(x,w;U) ≤ η c δ_G`, `G(x,w;U) ≤ η c⁻¹ δ_{G'}` for `x ∈ F = Ā_{3r/4, r}(z)`, `w ∈ B_b(x)`.
`E′ ⊂ E` (paper's Definition 3.1) because `F ⊂ V ⊂ U` (proved in the planner's probe against D4's `d4GoodAt`);
Proposition 4.1 works verbatim with `E′`, and `E′` is a countable intersection of Borel conditions (MA1 A9, A11). -/
def GoodAnnulus (G G' : ContMetric d) (A η c b : ℝ) (z : Rd d) (r : ℝ) : Prop :=
  (∀ x ∈ sphere z (3 * r / 4), ∀ y ∈ sphere z r,
      G'.internal (ann z (r / 4) (2 * r)) x y ≤
          ENNReal.ofReal ((1 + η) * c) * G.internal (ann z (r / 2) (3 * r / 2)) x y ∧
        G.internal (ann z (r / 4) (2 * r)) x y ≤
          ENNReal.ofReal ((1 + η) / c) * G'.internal (ann z (r / 2) (3 * r / 2)) x y) ∧
  (∀ x ∈ sphere z (3 * r / 4), ∀ y ∈ sphere z (3 * r / 4),
      G.internal (ann z (r / 4) (2 * r)) x y ≤
          ENNReal.ofReal A * setDistIn G (ann z (r / 4) (2 * r)) (sphere z (3 * r / 4)) (sphere z r) ∧
        G'.internal (ann z (r / 4) (2 * r)) x y ≤
          ENNReal.ofReal A * setDistIn G' (ann z (r / 4) (2 * r)) (sphere z (3 * r / 4)) (sphere z r)) ∧
  (∀ x ∈ annCl z (3 * r / 4) r, ∀ w ∈ ball x b,
      G'.internal (ann z (r / 4) (2 * r)) x w ≤
          ENNReal.ofReal (η * c) * setDistIn G (ann z (r / 4) (2 * r)) (sphere z (3 * r / 4)) (sphere z r) ∧
        G.internal (ann z (r / 4) (2 * r)) x w ≤
          ENNReal.ofReal (η / c) * setDistIn G' (ann z (r / 4) (2 * r)) (sphere z (3 * r / 4)) (sphere z r))

/-- `E′` is symmetric under `(G, G', c) ↔ (G', G, c⁻¹)` (MA2 §2.6): the reverse half of Proposition 4.1 is the forward
half for the interchanged pair. -/
theorem goodAnnulus_symm (G G' : ContMetric d) (A η c b : ℝ) (z : Rd d) (r : ℝ) :
    GoodAnnulus G G' A η c b z r ↔ GoodAnnulus G' G A η c⁻¹ b z r := by
  unfold GoodAnnulus
  simp only [div_inv_eq_mul, ← div_eq_mul_inv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun x hx y hy => (h1 x hx y hy).symm, fun x hx y hy => (h2 x hx y hy).symm,
      fun x hx w hw => (h3 x hx w hw).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun x hx y hy => (h1 x hx y hy).symm, fun x hx y hy => (h2 x hx y hy).symm,
      fun x hx w hw => (h3 x hx w hw).symm⟩

/-- A unit-speed minimizing curve for the internal metric `G(·,·;V)` (verbatim the body of packet D4's
`HigherDimLFPPAS.Improve.d4InternalGeodesic`). Every unit-speed global geodesic with image in `B_R` is one for
`V = B_{R+1}` (MA2 Details (c), note 2), and the class is closed under restriction to subintervals. -/
def IsInternalGeodesic (G : ContMetric d) (V : Set (Rd d)) (P : ℝ → Rd d) (T : ℝ) : Prop :=
  0 ≤ T ∧ ContinuousOn P (Icc 0 T) ∧ MapsTo P (Icc 0 T) V ∧
    (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, G.internal V (P s) (P t) = ENNReal.ofReal |t - s|) ∧
    (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → G.len P s t = ENNReal.ofReal (t - s))

/-- `𝒞^{G→G'}_{ε,R}(C, q)` of (4.1) (verbatim the body of packet D4's `HigherDimLFPPAS.Improve.d4Comparison`, same
argument order; `Iff.rfl` checked): for every `G`-internal geodesic of `B_{R+1}` with image in `B_R`, the `G'`-distance
inside `B_{R+2}` between the `8ε^q`-balls around its endpoints is at most `C` times its `G`-length. Monotone in `C`, in
the endpoint radius (smaller `q`, for `ε < 1`) and in the output domain. -/
def Comp (G G' : ContMetric d) (R ε q C : ℝ) : Prop :=
  ∀ (P : ℝ → Rd d) (T : ℝ), IsInternalGeodesic G (ball 0 (R + 1)) P T →
    MapsTo P (Icc 0 T) (ball 0 R) →
    setDistIn G' (ball 0 (R + 2)) (ball (P 0) (8 * ε ^ q)) (ball (P T) (8 * ε ^ q)) ≤
      ENNReal.ofReal C * G.len P 0 T

/-- The conclusion (1.7) of Theorem 1.2: verbatim the conclusion of the frozen anchor `asConvergence` (one probability-one
event for every compact `F`, the supremum computed in `[0, ∞]`). -/
def ASConclusion (κ : Rd d → ℝ) (ξ : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
    Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
        edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
      (𝓝[>] 0) (𝓝 0)

/-! ## §2 Standing hypotheses -/

/-- The kernel and convolution-field facts of the seed `κ` used downstream (paper §1 kernel facts; Appendix A Step 1).
Each field is, verbatim for this `κ`, the conclusion of a repository theorem stated for `IsLFPPKernel κ` and of its
sign-free copy by packet G1 (`HigherDimLFPPAS.Signed.<name>_seed`, hypothesis `IsAdmissibleSeed κ`; MA3 §4.1: no proof
uses `nonneg`): `kernel*` ← `l1c_convKernel`; `radial` ← `l2b_radial`; `trunc` ← `l2b_ae_convMollify_tendsto` with
`l2b_convMollify_eq_of_tendsto`; `jointCont` ← `l2b_ae_convMollify_continuousOn`; `affine` ← `l9b_ae_convMollify_affine`;
`aEps_pos` ← `l10a_aEps_pos`; `locHyp` ← `l9b_eventually_locHyp`; `locError` ← `l9b_locField_error`; `shellMeas` ←
`ref1_lemma43_aeEventIn`. Producers (proofs checked by the planner, standard axioms): `seedFacts_of_isLFPPKernel` and
`seedFacts_of_admissible` (packet SF). Non-vacuous: inhabited by every nonnegative seed (`exists_isLFPPKernel`). -/
structure SeedFacts (d : ℕ) (κ : Rd d → ℝ) : Prop where
  kernelSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)
  kernelIntegrable : Integrable (convKernel κ)
  kernelIntegral : ∫ x, convKernel κ x = 1
  kernelRadial : ∀ x y : Rd d, ‖x‖ = ‖y‖ → convKernel κ x = convKernel κ y
  kernelDecay : ∃ C : ℝ, ∀ x : Rd d, |convKernel κ x| ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1))
  kernelFourier : FourierTransform.fourier (fun x : Rd d => (convKernel κ x : ℂ)) =
    fun ζ => (kernelSymbol κ ζ : ℂ)
  radial : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P → ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      convMollify κ ε (h ω) z = (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * sphereAvg (h ω) r z
  trunc : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P → ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z))
  jointCont : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P → ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Rd d => convMollify κ p.1 (h ω) p.2) (Ioi 0 ×ˢ univ)
  affine : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P → ∀ (u : Rd d) (r : ℝ), 0 < r → ∀ᵐ ω ∂P,
      (∀ ε : ℝ, 0 < ε → ∀ x : Rd d,
        convMollify κ ε (h ω) (u + r • x) =
          convMollify κ (ε / r) (recentAff r u (h ω)) x + sphereAvg (affineComp r u (h ω)) 1 0) ∧
      sphereAvg (affineComp r u (h ω)) 1 0 = sphereAvg (h ω) r u
  aEps_pos : ∀ ξ ε : ℝ, 0 < ε → 0 < aEps κ ξ ε
  locHyp : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 ∧ 0 < locRad ε ∧ 1 ≤ locRad ε / (2 * ε) ∧
    1 / 2 ≤ locMass κ ε (locRad ε)
  locError : ∀ {CK : ℝ}, 0 ≤ CK →
    (∀ u : ℝ, 0 ≤ u → |convKernel κ (u • e₁ d)| ≤ CK * (1 + u) ^ (-((d : ℝ) + 1))) →
    ∀ {ε s : ℝ}, 0 < ε → ε ≤ 1 → 0 < s → 1 ≤ s / (2 * ε) → 1 / 2 ≤ locMass κ ε s →
    ∀ {g : DistRd d} {z : Rd d} {C : ℝ}, 0 ≤ C →
    convMollify κ ε g z = sphArea d * ∫ r in Ioi (0 : ℝ),
      r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * sphereAvg g r z →
    g (locTest κ ε s z) = sphArea d * ∫ r in Ioi (0 : ℝ),
      r ^ (d - 1) * locTest κ ε s z (z + r • e₁ d) * sphereAvg g r z →
    ContinuousOn (fun r => sphereAvg g r z) (Ioi 0) →
    (∀ r : ℝ, 0 < r → |sphereAvg g r z| ≤ C * l2b_growthWeight r) →
    |convMollify κ ε g z - (locMass κ ε s)⁻¹ * g (locTest κ ε s z)| ≤
      C * sphArea d * (1 + Real.log ε⁻¹) * (6 * CK / Real.sqrt (s / (2 * ε))) *
        (1 + 2 * sphArea d * l9bKernelMoment κ)
  shellMeas : ∀ {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}, IsWeakExpMetric d ξ D c →
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d},
    IsNormalizedLGF h P → ∀ {ε : ℝ}, 0 < locRad ε → locMass κ ε (locRad ε) ≠ 0 →
    ∀ {r : ℝ}, 24 * locRad ε ≤ r → ∀ (u : Rd d) {C : ℝ}, 0 < C →
      AEEventIn P (fieldSigma0 h (ann u (r / 4) (4 * r))) {ω | shellGood κ ξ D c ε C u r (h ω)}

/-- The standing hypotheses of the internal proof of Theorem 1.2: `d ≥ 3`, `ξ > 0`, a strong assignment at an
**arbitrary** `Q > √(2d)` (MA1 MN-1; the frozen anchor uses `Q = distExp d ξ`), the paper's seed (`IsAdmissibleSeed`,
ruling L7) together with its kernel/field facts, the normalized LGF, and Assumption 1.1 (v) for the given field. For
the frozen anchor `asConvergence` it is built (packet ASM) from `IsAdmissibleSeed κ` (with `seedFacts_of_admissible`),
`IsNormalizedLGF h P` and the three fields of `Assumption11 d ξ κ D P h` at `Q = distExp d ξ`. Every hypothesis is a
hypothesis of the paper (no theorem-shaped field). -/
structure Setting (d : ℕ) (ξ Q : ℝ) (κ : Rd d → ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop where
  dim : 3 ≤ d
  xi_pos : 0 < ξ
  subcrit : Real.sqrt (2 * d) < Q
  admissible : IsAdmissibleSeed κ
  seed : SeedFacts d κ
  strong : IsStrongExpMetric d ξ Q D
  field : IsNormalizedLGF h P
  conv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
    (fun ω => (D (h ω)).1)

/-! ## §3 Appendix A (Lemma 2.3; MA3 P2–P7) -/

/-- **Lemma 2.3 (i)**, pathwise, for all `ε ↓ 0` on one event, every radius (MA2 m5 and flag; MA3 P2.4): a.s., for every
`R > 0`, `ĥ*_ε − h*_ε → 0` uniformly on `B̄_R`. True: MA3 P2.3–P2.4 (one random constant `C_R` for all `ε ≤ ε₀`). -/
def Lemma23i (κ : Rd d → ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R →
    TendstoUniformlyOn (fun ε x => locField κ ε (h ω) x - convMollify κ ε (h ω) x) (fun _ => 0)
      (𝓝[>] (0 : ℝ)) (closedBall (0 : Rd d) R)

/-- **Lemma 2.3 (ii)**, (2.7), with the sharp coefficient `√(2d)` for both fields (MA3 P5, P7; needed by (6.4), MA2
§2.18): a.s., for every `R, η > 0`, eventually in `ε ↓ 0`, `sup_{B̄_R} |h*_ε|, |ĥ*_ε| ≤ (√(2d) + η) log ε⁻¹`. Not vacuous:
`Var h*_ε(x) = log ε⁻¹ + O(1)`, so the bound fails for `η < 0`; the coefficient is the sharp one. -/
def Lemma23ii (κ : Rd d → ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ᵐ ω ∂P, ∀ R η : ℝ, 0 < R → 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ closedBall (0 : Rd d) R,
    |convMollify κ ε (h ω) x| ≤ (Real.sqrt (2 * d) + η) * Real.log ε⁻¹ ∧
      |locField κ ε (h ω) x| ≤ (Real.sqrt (2 * d) + η) * Real.log ε⁻¹

/-- **Lemma 2.3 (iii)**, (2.8), for both fields (MA3 P6 by window chaining, no differentiable version; P7): for every
`a > 0`, a.s., for every `R, η > 0`, eventually in `n`, the oscillation over `ε, δ ∈ [(n+1)^{-a}, n^{-a}]` on `B̄_R` is
at most `η`. -/
def Lemma23iii (κ : Rd d → ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ᵐ ω ∂P, ∀ R η : ℝ, 0 < R → 0 < η → ∀ᶠ n : ℕ in atTop,
    ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)), ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
    ∀ x ∈ closedBall (0 : Rd d) R,
      |convMollify κ ε (h ω) x - convMollify κ δ (h ω) x| ≤ η ∧
        |locField κ ε (h ω) x - locField κ δ (h ω) x| ≤ η

/-- **(3.9)**, the rescaled localization bound (MA3 P2.4′, MA1 A10.2), in the per-parameter almost-sure form its consumer
(`RescaledConv`) uses along countably many parameters: for every `R` there are a random constant `C(ω)`, a deterministic
rate `ρ(ε) → 0` and `ε₀` such that for each `ε < ε₀` and `r ∈ [ε, 1]`, a.s. on `B̄_R`,
`|ĝ_{ε/r, ε} − g ∗ K_{ε/r}| ≤ C ρ(ε)`. True with `ρ(ε) = (1 + log ε⁻¹)/(log ε⁻¹)^{10}` (MA3, repository decay) or
`(1 + log ε⁻¹)(L_ε/2)^{-1/2}` (MA1, via `SeedFacts.locError` at kernel scale `ε/r`, radius `locRad ε / r`). -/
def RescaledLoc (κ : Rd d → ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ (C : Ω → ℝ) (ρ : ℝ → ℝ) (ε₀ : ℝ), 0 < ε₀ ∧ Tendsto ρ (𝓝[>] 0) (𝓝 0) ∧
    ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ r ∈ Icc ε 1, ∀ᵐ ω ∂P, ∀ x ∈ closedBall (0 : Rd d) R,
      |locFieldR κ ε r (h ω) x - convMollify κ (ε / r) (h ω) x| ≤ C ω * ρ ε

/-- The Gaussian structure of `H_t(x) = h*_{e^{-t}}(x)` used by (2.7) and (2.8) (MA3 P3.1, P4.1′, P4.4): `H` is a
centered Gaussian process indexed by `(t, x)` (a zero-mass pairing of the LGF, MA3 P4.4), `|Var H_t(x) − t| ≤ C_R` for
`t ≥ 0`, `x ∈ B̄_R` ((A.4), MA3 P3.1 proof 2), and the Hölder canonical-metric bound (MA3 P4.1′)
`Var(H_t(x) − H_{t'}(x')) ≤ C (|t − t'| + e^{max(t,t')} ‖x − x'‖)` for `t, t' ≥ 0`, `|t − t'| ≤ 1`. Not vacuous: the
variance clause forces `Var H_t(x) → ∞` (junk `variance = 0` off `L²` would contradict it). -/
def FieldGauss (κ : Rd d → ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  IsGaussianProcess (fun (p : ℝ × Rd d) (ω : Ω) => convMollify κ (Real.exp (-p.1)) (h ω) p.2) P ∧
  (∀ p : ℝ × Rd d, ∫ ω, convMollify κ (Real.exp (-p.1)) (h ω) p.2 ∂P = 0) ∧
  (∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ x ∈ closedBall (0 : Rd d) R,
    |variance (fun ω => convMollify κ (Real.exp (-t)) (h ω) x) P - t| ≤ C) ∧
  (∃ C : ℝ, ∀ t t' : ℝ, 0 ≤ t → 0 ≤ t' → |t - t'| ≤ 1 → ∀ x x' : Rd d,
    variance (fun ω => convMollify κ (Real.exp (-t)) (h ω) x -
        convMollify κ (Real.exp (-t')) (h ω) x') P ≤
      C * (|t - t'| + Real.exp (max t t') * ‖x - x'‖))

/-! ## §4 Lemmas 2.4, 2.5, 2.7 and the rescaling -/

/-- **Lemma 2.4 (i)**: `M_ε → D` in probability, locally uniformly (MA1 A6.2: subsequences, Lemma 2.3(i), the density
observation A6.1 and properness of `D`). -/
def Lemma24Conv (κ : Rd d → ℝ) (ξ : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  TendstoInProbLU P (fun ε ω => (Meps κ ξ ε (h ω)).1) (𝓝[>] 0) (fun ω => (D (h ω)).1)

/-- **Lemma 2.4 (ii)** (MA1 A6.3; MA2's shape with unit-speed geodesics): for compact `F` and `p < 1` there is a
deterministic `R` such that, for all small `ε`, with outer probability `≥ p`, every pair in `F` has a unit-speed
`M_ε`-geodesic and every `M_ε`-geodesic between points of `F` stays in `B_R`. -/
def Lemma24Confine (κ : Rd d → ℝ) (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistRd d) : Prop :=
  ∀ F : Set (Rd d), IsCompact F → ∀ p : ℝ, p < 1 → ∃ R : ℝ, 0 < R ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ENNReal.ofReal p ≤ P {ω | ∀ x ∈ F, ∀ y ∈ F,
      (∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = x ∧ γ T = y ∧ ContinuousOn γ (Icc 0 T) ∧
          ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, (Meps κ ξ ε (h ω)).1 (γ s, γ t) = |t - s|) ∧
      ∀ (γ : ℝ → Rd d) (T : ℝ), γ 0 = x → γ T = y →
        LQGMetric.MetricGeometry.IsGeodesicCurve ((Meps κ ξ ε (h ω)).pt ∘ γ) 0 T →
          MapsTo γ (Icc 0 T) (ball 0 R)}

/-- **Lemma 2.5**, uniform form (MA1 A7.4, median-continuity route, no regular variation): `c_ε(r) → 1` uniformly for
`r` in compact subsets of `(0, ∞)`. Producer: packet N1 (running). -/
def Lemma25Unif (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc a b, |cRatio κ ξ Q ε r - 1| ≤ η

/-- **Lemma 2.5**, (2.10) (MA1 A7.4): for every `a > 0`, `sup_{ε ∈ [(n+1)^{-a}, n^{-a}]} |𝔞_ε/𝔞_{n^{-a}} − 1| → 0`. -/
def Lemma25Window (κ : Rd d → ℝ) (ξ : ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      |aEps κ ξ ε / aEps κ ξ ((n : ℝ) ^ (-a)) - 1| ≤ η

/-- **Lemma 2.5**, `𝔞_ε = ε^{1 − ξQ + o(1)}` (MA1 A7.5), as two-sided power bounds for small `ε` (`ε < 1`, so the
exponents order the powers). -/
def Lemma25Exponent (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ε ^ (1 - ξ * Q + η) ≤ aEps κ ξ ε ∧ aEps κ ξ ε ≤ ε ^ (1 - ξ * Q - η)

/-- The deterministic two-parameter scaling of the localized field (MA1 A10.1): for every distribution `g`, `0 < ε < 1`,
`r > 0`, `ĥ*_ε(z + r x) = ĝ_{ε/r, ε}[h(r · + z)](x)` and `Z_{ε/r} (radius locRad ε / r) = Z_ε`. True by the change of
variables `w = z + r v` (`K_δ(v/r) = r^d K_{rδ}(v)`, `radBump (s/2) s (v/r) = radBump (rs/2) (rs) v`,
`affineComp r z g φ = r^{-d} g(φ((· − z)/r))`); smoothness of `K` makes the test functions non-junk. -/
def LocFieldScaling (κ : Rd d → ℝ) : Prop :=
  ∀ ε r : ℝ, 0 < ε → ε < 1 → 0 < r →
    locMass κ (ε / r) (locRad ε / r) = locMass κ ε (locRad ε) ∧
    ∀ (z : Rd d) (g : DistRd d) (x : Rd d),
      locField κ ε g (z + r • x) = locFieldR κ ε r (affineComp r z g) x

/-- The coordinate change (1.5) in the paper's form, with `h^{z,r} = recentAff r z h` (MA1 A2, S1 §4.3(a)): for fixed
`r > 0` and `z`, a.s., for all `u, v`, `D_h(z + r u, z + r v) = r^{ξQ} e^{ξ h_r(z)} D_{h^{z,r}}(u, v)`. True from
`IsStrongExpMetric.coord` and `weyl` with the constant `sphereAvg (affineComp r z h) 1 0 + Q log r` (Weyl scaling of a
length metric by a constant is multiplication), and `sphereAvg (affineComp r z h) 1 0 = h_r(z)` a.s.
(`IsWholeSpaceLGF.ae_sphereAvg_affineComp`). -/
def CoordScaling (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ z : Rd d, ∀ᵐ ω ∂P, ∀ u v : Rd d,
    (D (h ω)).1 (z + r • u, z + r • v) =
      r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r z) * (D (recentAff r z (h ω))).1 (u, v)

/-- Internal metrics under a homothety (deterministic): if `G'(z + r u, z + r v) = c G(u, v)` for all `u, v` (`r, c > 0`),
then `G'(z + r u, z + r v; z + r V) = c G(u, v; V)` for every set `V`: the map `x ↦ z + r x` multiplies lengths by `c`
(as in `HigherDimLQGMetric.internal_smul` and `Sharp/ShellScaling.lean`). -/
def AffineInternalScaling (d : ℕ) : Prop :=
  ∀ (G G' : ContMetric d) (z : Rd d) (r c : ℝ), 0 < r → 0 < c →
    (∀ u v : Rd d, G'.1 (z + r • u, z + r • v) = c * G.1 (u, v)) →
    ∀ (V : Set (Rd d)) (u v : Rd d),
      G'.internal ((fun x => z + r • x) '' V) (z + r • u) (z + r • v) =
        ENNReal.ofReal c * G.internal V u v

/-- Admissibility of unit-speed global geodesics (MA2 Details (c), note 2; deterministic): a curve with
`G(γ s, γ t) = |t − s|` on `[0, T]` and image in `B_R` is an `IsInternalGeodesic` of `B_{R+1}` (internal `≥` global
`= |t − s|`, and `≤` the length of `γ|[s,t]`, which is `t − s`). Used for the `D`-geodesics (Lemma 2.2) and the
`M_ε`-geodesics (`Lemma24Confine`, `Lemma62Stmt`) fed to `Comp`. -/
def UnitSpeedAdmissible (d : ℕ) : Prop :=
  ∀ (G : ContMetric d) (R : ℝ) (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T → ContinuousOn γ (Icc 0 T) →
    MapsTo γ (Icc 0 T) (ball 0 R) → (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, G.1 (γ s, γ t) = |t - s|) →
    IsInternalGeodesic G (ball 0 (R + 1)) γ T

/-- Equality in law of the rescaled pair (MA1 A10.3 "realization"): for `0 < ε ≤ r ≤ 1` and every centre `z`, the pair
`(D_{h^{z,r}}, 𝔐_{ε,ε/r}(h^{z,r}))`, `h^{z,r} = recentAff r z h`, has the law of `(D_h, 𝔐_{ε,ε/r}(h))`, and the latter pair
is a.e.-measurable (so the push-forwards are not junk). True: `recentAff r z h` has the law `normLGFLaw d` of `h`
(`isNormalizedLGF_recentAff`, `l9b_map_eq_normLGFLaw`) and the pair is a measurable function of the field
(`IsStrongExpMetric.measurable`; `MepsR` is the LFPP metric of a field that is continuous and measurable in `g`,
`measurable_continuousMap_of_eq_lfppMetric`). -/
def PairLaw (κ : Rd d → ℝ) (ξ : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ ε r : ℝ, 0 < ε → ε ≤ r → r ≤ 1 → ∀ z : Rd d,
    AEMeasurable (fun ω => (D (h ω), MepsR κ ξ ε r (h ω))) P ∧
    Measure.map (fun ω => (D (recentAff r z (h ω)), MepsR κ ξ ε r (recentAff r z (h ω)))) P =
      Measure.map (fun ω => (D (h ω), MepsR κ ξ ε r (h ω))) P

/-- **Rescaled convergence on the pinned field** (MA1 A10.3, MA3 P9(b); the common core of Lemma 3.2 and Lemma 4.3′):
along every sequence `ε_j ↓ 0` with `ε_j ≤ r_j ≤ 1` and `ε_j / r_j → 0`, `𝔐_{ε_j, ε_j/r_j}(h) → D_h` in probability,
locally uniformly. True: `RescaledLoc` → 0 along the sequence, (1.6) along `δ_j = ε_j/r_j → 0`, and the density
observation (MA1 A6.1) with properness of `D_h` (Lemma 2.2) along a.s. convergent subsequences. -/
def RescaledConv (κ : Rd d → ℝ) (ξ : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ ε r : ℕ → ℝ, (∀ j, 0 < ε j ∧ ε j ≤ r j ∧ r j ≤ 1) → Tendsto ε atTop (𝓝 0) →
    Tendsto (fun j => ε j / r j) atTop (𝓝 0) →
    TendstoInProbLU P (fun j ω => (MepsR κ ξ (ε j) (r j) (h ω)).1) atTop (fun ω => (D (h ω)).1)

/-- **Lemma 4.3′** (MA3 P9; replaces the DGZ-tightness input of [3] Lemma 4.3 by (1.6) + (3.9); no sign condition): the
good shell events `E^ε_r(u; C)` of [3] (4.5) (repository `shellGood`, scale constants `c_r = r^{ξQ}`) have probability
`≥ p` uniformly in `ε < ε₀`, `r ∈ N^ε` (`dyad k`, `k ∈ nIdx ζ ε`) and `u`. -/
def Lemma43SStmt (κ : Rd d → ℝ) (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∀ p : ℝ, p < 1 → ∃ C : ℝ, 1 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ k ∈ nIdx ζ ε, ∀ u : Rd d,
      ENNReal.ofReal p ≤ P {ω | shellGood κ ξ D (fun r => r ^ (ξ * Q)) ε C u (dyad k) (h ω)}

/-- **Lemma 4.4′** ([3] Lemma 4.4 with the polynomial rate of its event (4.11), MA3 P11 Steps 2–3; the repository form of
`ref1_lemma44` with `≤ θ` replaced by `≤ K ε^β`): uniformly over deterministic radius sets `R ⊆ N^ε` with
`|N^ε| ≤ 10 |R|` and ratio bounds `m ≤ c_ε(r) ≤ M` on `R`, the coarse comparisons (4.9)–(4.10) hold on `U` except on an
event of outer probability `O_U(ε^β)`; `C, β` do not depend on `U`. -/
def Lemma44SStmt (κ : Rd d → ℝ) (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ C β : ℝ, 0 < C ∧ 0 < β ∧
    ∀ U : Set (Rd d), IsOpen U → Bornology.IsBounded U → IsConnected U →
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ R : Finset ℕ, R ⊆ nIdx ζ ε →
      (nIdx ζ ε).card ≤ 10 * R.card → ∀ m M : ℝ, 0 < m → 0 < M →
      (∀ k ∈ R, m ≤ cRatio κ ξ Q ε (dyad k) ∧ cRatio κ ξ Q ε (dyad k) ≤ M) →
      P {ω | ¬ ∀ z ∈ U, ∀ w ∈ U,
          ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
              fieldSetDistIn ξ (locField κ ε (h ω)) (thickening (ε ^ (1 - ζ)) U)
                (ball z (ε ^ (1 - ζ))) (ball w (ε ^ (1 - ζ))) ≤
            ENNReal.ofReal (C * M) * (D (h ω)).internal U z w ∧
          setDistIn (D (h ω)) (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ)))
              (ball w (ε ^ (1 - ζ))) ≤
            ENNReal.ofReal (C * m⁻¹) *
              (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * fieldDistIn ξ (locField κ ε (h ω)) U z w)} ≤
        ENNReal.ofReal (K * ε ^ β)

/-- **Lemma 4.5′** (MA3 P10; the repository form of `ref1_lemma45`): for small `ε`, at least half of the radii of `N^ε`
have `C⁻¹ ≤ c_ε(r) ≤ C`. Deterministic (the normalizers are); proved under `Setting` for some field. -/
def Lemma45SStmt (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ C : ℝ, 1 ≤ C ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁,
    (nIdx ζ ε).card ≤ 2 * ((nIdx ζ ε).filter fun k =>
      C⁻¹ ≤ cRatio κ ξ Q ε (dyad k) ∧ cRatio κ ξ Q ε (dyad k) ≤ C).card

/-- **Lemma 2.7** (localized coarse comparison with polynomial rate; MA3's corrected statement for `U = B_ρ`, which is
every use in §§5–6, MA2 §1.3): for each `q ∈ (0,1)` there are `C_q ≥ 2` and `β_q > 0`, independent of `ρ`, such that
(2.11) and (2.12) hold for all `x, y ∈ B_ρ` except on an event of outer probability `≤ K_ρ ε^{β_q}`. -/
def Lemma27Stmt (κ : Rd d → ℝ) (ξ : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ q ∈ Ioo (0 : ℝ) 1, ∃ C β : ℝ, 2 ≤ C ∧ 0 < β ∧ ∀ ρ : ℝ, 0 < ρ →
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | ¬ ∀ x ∈ ball (0 : Rd d) ρ, ∀ y ∈ ball (0 : Rd d) ρ,
          setDistIn (Meps κ ξ ε (h ω)) (thickening (ε ^ q) (ball 0 ρ)) (ball x (ε ^ q))
              (ball y (ε ^ q)) ≤ ENNReal.ofReal C * (D (h ω)).internal (ball 0 ρ) x y ∧
          setDistIn (D (h ω)) (thickening (ε ^ q) (ball 0 ρ)) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
            ENNReal.ofReal C * (Meps κ ξ ε (h ω)).internal (ball 0 ρ) x y} ≤
        ENNReal.ofReal (K * ε ^ β)

/-! ## §5 Section 3 -/

/-- **Lemma 3.2**, marginal part, for `E′` (MA1 A10; the "`∃ ε₀, ∀ ε < ε₀, ∀ z, ∀ r ∈ 𝒩_ε(u)`" form that Lemma 3.3
needs): for every `p < 1` there is `A ≥ 1`, independent of `η, u, q₀`, with `P[E′_ε(z,r)] ≥ p`. -/
def Lemma32Marginal (κ : Rd d → ℝ) (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ p : ℝ, p < 1 → ∃ A : ℝ, 1 ≤ A ∧ ∀ η u q₀ : ℝ, 0 < η → 0 < u → u < q₀ → q₀ < 1 →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ z : Rd d, ∀ r ∈ window ε u,
      ENNReal.ofReal p ≤ P {ω | GoodAnnulus (D (h ω)) (Meps κ ξ ε (h ω)) A η
        (cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r}

/-- **Lemma 3.2**, measurability (3.7) for `E′` (MA1 A11): for small `ε` (so that `ε L_ε + b_ε < r/16` on the window) the
event is a.s. equal to an event of `σ((h − h_r(z))|_{A_{r/8, 8r}(z)})` (repository `fieldSigma0`: mean-zero pairings, the
form `lemmaA1` consumes). -/
def Lemma32Meas (κ : Rd d → ℝ) (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ A η u q₀ : ℝ, 1 ≤ A → 0 < η → 0 < u → u < q₀ → q₀ < 1 →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ z : Rd d, ∀ r ∈ window ε u,
      AEEventIn P (fieldSigma0 h (ann z (r / 8) (8 * r)))
        {ω | GoodAnnulus (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r}

/-- **Lemma 3.3** (MA1 A12, MA4 B.1): one `A ≥ 1`, independent of `η, u, q₀, R`; uniformly over deterministic
`R_ε ⊆ 𝒩_ε(u)` with `|𝒩_ε(u)| ≤ 4 |R_ε|`, every mesh point has a good radius in `R_ε` except on an event of outer
probability `≤ K ε^u` (the proof gives `ε^{(d+4)u}`). Not vacuous: `𝒩_ε(u)` is nonempty for small `ε` (D6's count), so
admissible `R_ε` exist, and the mesh is nonempty. -/
def Lemma33Stmt (κ : Rd d → ℝ) (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ η u q₀ R : ℝ, 0 < η → 0 < u → u < q₀ → q₀ < 1 → 0 ≤ R →
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ Rε : Finset ℝ, (↑Rε : Set ℝ) ⊆ window ε u →
      (window ε u).ncard ≤ 4 * Rε.card →
      P {ω | ¬ ∀ z ∈ mesh d ε u R, ∃ r ∈ Rε,
          GoodAnnulus (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r} ≤
        ENNReal.ofReal (K * ε ^ u)

/-! ## §6 Sections 4–6 -/

/-- **Proposition 4.1**, deterministic (MA2 m1, D-A; MA4's closed-ball hits; `E′` in place of `E`, MA1 A9): for
`0 < u < q₀ < 1`, `η > 0`, `A ≥ 1` there is `ε₀` such that for `ε < ε₀`, every `R ≥ 2`, every pair of metrics, every
finite `R_ε ⊆ 𝒩_ε(u)` and every upper bound `m` of a positive ratio function on `R_ε`: covering of the mesh by `E′` and
`𝒞(C, q₀)` imply `𝒞(θ max{C, m} + (1 − θ + 3η) m, u/2)`, `θ = A/(A+1)`. The reverse direction is the instance
`(G', G, c⁻¹)` through `goodAnnulus_symm`. Producer: packet D4 (continuation D4c1) through the adapter P41W. -/
def Prop41Stmt (d : ℕ) : Prop :=
  1 ≤ d → ∀ u q₀ η A : ℝ, 0 < u → u < q₀ → q₀ < 1 → 0 < η → 1 ≤ A →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ R : ℝ, 2 ≤ R →
      ∀ (G G' : ContMetric d) (Rε : Finset ℝ) (c : ℝ → ℝ) (m C : ℝ),
        (∀ r ∈ Rε, r ∈ window ε u ∧ 0 < c r ∧ c r ≤ m) →
        (∀ z ∈ mesh d ε u R, ∃ r ∈ Rε, GoodAnnulus G G' A η (c r) (8 * ε ^ q₀) z r) →
        Comp G G' R ε q₀ C →
        Comp G G' R ε (u / 2) (A / (A + 1) * max C m + (1 - A / (A + 1) + 3 * η) * m)

/-- **Proposition 5.1** (MA2 m3: outer-measure form; m4: explicit constants): for every `δ ∈ (0,1)` there are
`q_δ ∈ (0,1)`, `β_δ > 0`, independent of `R`, such that both sharp comparison properties hold except on an event of
outer probability `≤ K_R ε^{β_δ}`. -/
def Prop51Stmt (κ : Rd d → ℝ) (ξ : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ q β : ℝ, 0 < q ∧ q < 1 ∧ 0 < β ∧ ∀ R : ℝ, 2 ≤ R →
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | ¬ (Comp (D (h ω)) (Meps κ ξ ε (h ω)) R ε q (1 + δ) ∧
          Comp (Meps κ ξ ε (h ω)) (D (h ω)) R ε q (1 + δ))} ≤ ENNReal.ofReal (K * ε ^ β)

/-- **Lemma 6.1** (MA2 D-C): there are `C_* > 0` and `β_* > 0` such that for every `a` with `a β_* > 1`, a.s., for every
integer `R ≥ 1`: (6.2) `M_{ε_n}(x,y;B_{R+2}) ≤ C_* D(x,y;B_{R+1}) + o(1)` uniformly on `B̄_R`, along `ε_n = n^{-a}`;
(6.3) for every `ρ_n → 0`, `sup_{|x−y| ≤ ρ_n} M_{ε_n}(x,y;B_{R+2}) → 0` on `B̄_R`. Uses the sharp (2.7) (MA2 §2.18). -/
def Lemma61Stmt (κ : Rd d → ℝ) (ξ : ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop :=
  ∃ C β : ℝ, 0 < C ∧ 0 < β ∧ ∀ a : ℝ, 1 < a * β → ∀ᵐ ω ∂P, ∀ R : ℕ, 1 ≤ R →
    (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
        (Meps κ ξ ((n : ℝ) ^ (-a)) (h ω)).internal (ball 0 (R + 2)) x y ≤
          ENNReal.ofReal C * (D (h ω)).internal (ball 0 (R + 1)) x y + ENNReal.ofReal η) ∧
    (∀ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R, ‖x - y‖ ≤ ρ n →
        (Meps κ ξ ((n : ℝ) ^ (-a)) (h ω)).internal (ball 0 (R + 2)) x y ≤ ENNReal.ofReal η)

/-- **Lemma 6.2** (MA2 §§2.19–2.20, D-D2, D-D3; m5, m6), in the form the proof of Theorem 1.2 consumes: a.s., for every
`k`, some integer `R > k + 4` such that for every small `ε`, for all `x, y ∈ B̄_k`, the global `M_ε`- and `N_ε`-distances
equal the internal ones on `B_R`, and a unit-speed `M_ε`-geodesic from `x` to `y` exists inside `B_R`. Enlarging `R`
preserves every clause. -/
def Lemma62Stmt (κ : Rd d → ℝ) (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistRd d) : Prop :=
  ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ R : ℕ, (k : ℝ) + 4 < R ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ∀ x ∈ closedBall (0 : Rd d) k, ∀ y ∈ closedBall (0 : Rd d) k,
      ENNReal.ofReal ((Meps κ ξ ε (h ω)).1 (x, y)) = (Meps κ ξ ε (h ω)).internal (ball 0 R) x y ∧
      ENNReal.ofReal ((Neps κ ξ ε (h ω)).1 (x, y)) = (Neps κ ξ ε (h ω)).internal (ball 0 R) x y ∧
      ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = x ∧ γ T = y ∧ ContinuousOn γ (Icc 0 T) ∧
        MapsTo γ (Icc 0 T) (ball 0 R) ∧
        ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, (Meps κ ξ ε (h ω)).1 (γ s, γ t) = |t - s|

end HigherDimLFPPAS.Core
