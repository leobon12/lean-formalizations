import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.NormLGFLaw
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Frozen.AEps
import HigherDimLQGMetric.Frozen.LfppDist
import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLQGMetric.Frozen.ContMetricInstMetricSpace
import HigherDimLQGMetric.Frozen.ContMetricIsLength
import HigherDimLQGMetric.Core.Defs
import HigherDimLQGMetric.Events.Defs
import HigherDimLQGMetric.Select.GeodRel
import HigherDimLQGMetric.Metric.ContMetric
import HigherDimLQGMetric.Metric.WeylBasic
import HigherDimLQGMetric.Weak.DetDefs
import HigherDimLQGMetric.LogEnergy.Basic
import HigherDimLQGMetric.DGZ.Sec41Defs
import HigherDimLQGMetric.DGZ.Functionals
import GaussianLQG.Probability.GaussianLp
import LQGMetric.Statement.LFPP
import HigherDimLQGContinuity.Frozen.EuclidDistC
import HigherDimLQGContinuity.Frozen.IsMedianOne
import HigherDimLQGContinuity.Frozen.SupDistLU
import HigherDimLQGContinuity.Frozen.XiRange
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Interface statements shared between packets (orchestrator-owned; drafted by planner PL1, frozen 2026-10-22, ruling N12;
  version 2: Part B's site certificate (ruling N13) and the metric-version interface of `theorem11_metric` (IA1))

Path: `HigherDimLQGContinuity/Core/Interfaces.lean` (namespace `HigherDimLQGContinuity`). Ruling N6 (interface-first
scheduling), N8 (one declaration per fact; Part A's `logMean`/`rho`), N9 (the §4 interfaces). The interface pattern of the
previous campaign (its ruling M30, `HigherDimLQGMetric/Core/Interfaces.lean`, `Core/MainInputs.lean`): a statement that one
packet proves and other packets consume before it lands is defined here **once**, as a named `Prop`; consumers take it as
a hypothesis, producers prove it, the assembly discharges it. Workers import this module and never edit or redefine it.
These `Prop`s must never appear in a frozen statement (hypothesis smuggling).

Imports: only `HigherDimLQGMetric`, `HigherDimLFPP` (through it), `GaussianLQG`, `LQGMetric`, Mathlib and the four frozen
*definition* anchors of this library (never a frozen theorem anchor, never a packet module).

Contents (source of each shape in brackets; producer → consumers in the packet plan `planning/PACKET-PLAN.md`):

* §1 Normalizations: `logMean`, `rho` (Part A `a:def-rho`, [C] (1.6)), `pin`, `pinLaw` (Part A `a:def-pin`, (2.5)).
* §2 Local events: `annA`, `annK`, `IsWitness`, `Hdown`, `Hup`, `LocalRefs`, `PairRefs`, `CompOn`, `polyB`,
  `HolderEnvelope` (Part A §2.6, `a:def-AK`–`a:def-refs`, `a:def-comp`, `a:def-envelope`).
* §3 `UniformEstimates` (Lemma 2.1, Part A `a:def-uniform`; NA4's `UniformCore` is a projection, not a second shape).
* §4 Parameter windows: `MarginWindow`, `SubcritLocal`, `PhiRate` (NA4 §6.1/§6.3; producer: packet PARX from PAR's
  landed `subcritSet_eq_Ioo`, `gap24`, `phiXi_lipschitz`).
* §5 Uniform DGZ exports (Part D, NA3 Details (d) with BWD's corrections ED, ruling N8): `UHyp`, `UExpRate`,
  `CrudeLowerShape`, `UCor52Shape`, `UQuantCompShape`, `UHolderTightShape`, `UNondegShape`, `UDistInfShape`,
  `WNUpperMomentShape` (W1), `WNInvCrossShape` (W2), `ConvUpperMomentShape` (C1), `ConvInvCrossShape` (C2).
* §6 Comparison: `Prop35Shape` (Part A `a:def-prop35`), `logProfile`, `Prop37Shape` (Part C `c:lem-p37`: NA4's consumer
  form with Part A's pins).
* §7 Lemma 5.1 chain (NA4 A1–A4, Part C): `MarginalEuclidStmt` (NA4's `Lemma51Stmt`), `StrongRotLaw`, `frameFunRd`,
  `PairingFrame`, `ConcentrationStmt`; §5 chain: `PosVersionStmt`, `EndpointStmt`, `MetricVersionStmt` (§§5.3–5.4).
* §8 §4 interfaces (NA2 §3.3, ruling N9): `siteC`, `siteA` (= `annA`), `siteB`, `firstVisit`, `lastVisit`,
  `PassesTrigger`, `IsGeodSeg`, `IsWeylInternal`, `ForcingCert`, `Lemma43Forcing`, `Lemma44Pinned`, `Prop45OfCounts`; and
  Part B's site certificate (version 2, ruling N13): `DUpper`, `SiteRefs`, `siteAout`, `siteBtrig`, `siteEps0`,
  `SeedRefs`, `SeedFav`, `SiteCatalogue`, `SiteCertOfLabel` (`b:def-dupper`, `b:def-refs4`, `b:def-sitedata`,
  `b:def-seedfav`, `b:thm-sitecert`).
* §9 The frozen theorem statements as propositions (verbatim): `Theorem11XiStmt`, `Theorem11Stmt`, `Prop18Stmt`,
  `MedianOneStrongExistsStmt`, `Theorem11MetricStmt`.

Conventions (junk safety, ruling N5): moments are `lintegral`s; inverse moments are `[0, ∞]`-valued (`x⁻¹ ^ q`, so a zero
distance gives `⊤`); probabilities of possibly non-measurable sets are outer measures (HDLM ruling M34); every
`cthickening` radius is positive; pinned objects are written `pinLaw d s` + `rho D g` (Part A's convention; NA4's
`rhoPin10 ξ D g` is `rho D (pin 10 g)` a.s., Part A `a:lem-pin`). `ϕ(ξ) = ξ Q(ξ)` is written out (`ξ * distExp d ξ`) for
`ξ > 0`; PAR's `phiXi` is not imported (it is a packet module), and agrees with it for `ξ > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## §1 Normalizations ([C] (1.6), (2.5)) -/

/-- `E log D_g(0, e₁)` under `normLGFLaw d` (Part A `a:def-rho`). A Bochner integral: junk value `0` off `L¹`; every
consumer carries the integrability clause `UniformEstimates.logIntegrable`. -/
def logMean (D : DistRd d → ContMetric d) : ℝ :=
  ∫ g, Real.log ((D g).1 (0, e₁ d)) ∂(normLGFLaw d)

/-- `ρ^D_g = e^{-E log D(0, e₁)} D_g`, the mean-log normalization (1.6) (Part A `a:def-rho`; ruling N8). -/
def rho (D : DistRd d → ContMetric d) (g : DistRd d) : ContMetric d :=
  (D g).smul (Real.exp (-logMean D)) (Real.exp_pos _)

/-- The radius-`s` pin `g - g_s(0)` (Part A `a:def-pin`). -/
def pin (s : ℝ) (g : DistRd d) : DistRd d :=
  addConst g (-sphereAvg g s 0)

/-- The law of the radius-`s`-pinned field (`s = 1`: `normLGFLaw d` a.s.; `s = 10`: [C] (2.5)). `pin s` is measurable
(`measurable_sphereAvg_left`, `Measurable.addConst`), so this push-forward is not the junk zero measure. -/
def pinLaw (d : ℕ) (s : ℝ) : Measure (DistRd d) :=
  (normLGFLaw d).map (pin s)

/-! ## §2 Local events and references at unit scale ([C] (2.11)–(2.12), p. 6) -/

/-- `A = {1/2 < |x| < 7/2}` ([C] (2.11)). -/
def annA (d : ℕ) : Set (Rd d) := ann (0 : Rd d) (1 / 2) (7 / 2)

/-- `K = {3/4 ≤ |x| ≤ 1}` ([C] (2.11)). -/
def annK (d : ℕ) : Set (Rd d) := annCl (0 : Rd d) (3 / 4) 1

/-- A witness for `G` (Part A `a:def-witness`, the `A`-form): a path in `K` from `∂B_{3/4}` to `∂B_1` along which the
`A`-internal metric of `G` grows linearly; by `a:lem-witness` this is [C]'s intrinsic `K`-geodesic minimizing in `A`. -/
def IsWitness (G : ContMetric d) (γ : C(unitInterval, Rd d)) : Prop :=
  ‖γ 0‖ = 3 / 4 ∧ ‖γ 1‖ = 1 ∧ (∀ t, γ t ∈ annK d) ∧
    ∀ s t : unitInterval, G.internal (annA d) (γ s) (γ t) =
      ENNReal.ofReal |(s : ℝ) - t| * G.internal (annA d) (γ 0) (γ 1)

/-- `H↓(D, E; b)` for the ordered pair (primary `D`, secondary `E`), a set of pinned fields (Part A `a:def-H`). -/
def Hdown (D E : DistRd d → ContMetric d) (b : ℝ) : Set (DistRd d) :=
  {g | ∃ γ : C(unitInterval, Rd d), IsWitness (rho E g) γ ∧
    (rho E g).internal (annA d) (γ 0) (γ 1) ≤ ENNReal.ofReal b * (rho D g).internal (annA d) (γ 0) (γ 1)}

/-- `H↑(D, E; b)` for the ordered pair (primary `D`, secondary `E`) (Part A `a:def-H`). -/
def Hup (D E : DistRd d → ContMetric d) (b : ℝ) : Set (DistRd d) :=
  {g | ∃ γ : C(unitInterval, Rd d), IsWitness (rho D g) γ ∧
    ENNReal.ofReal b * (rho D g).internal (annA d) (γ 0) (γ 1) < (rho E g).internal (annA d) (γ 0) (γ 1)}

/-- The local references of one metric at unit scale with constants `(H₀, σ₀, β₀, m, M)` (Part A `a:def-refs`, with
NA1's `diamK`; every clause is a condition on the `A`-internal profile on `annCl 0 (5/8) (3/2)`). -/
structure LocalRefs (G : ContMetric d) (H₀ σ₀ β₀ m M : ℝ) : Prop where
  lower : ∀ x ∈ annCl (0 : Rd d) (5 / 8) (3 / 2), ∀ y ∈ annCl (0 : Rd d) (5 / 8) (3 / 2),
    ENNReal.ofReal (H₀⁻¹ * ‖x - y‖ ^ β₀) ≤ G.internal (annA d) x y
  upper : ∀ x ∈ annCl (0 : Rd d) (5 / 8) (3 / 2), ∀ y ∈ annCl (0 : Rd d) (5 / 8) (3 / 2),
    ‖x - y‖ ≤ 1 / 64 → G.internal (annA d) x y ≤ ENNReal.ofReal (H₀ * ‖x - y‖ ^ σ₀)
  cross : ENNReal.ofReal m ≤ setDistIn G (annA d) (sphere (0 : Rd d) (3 / 4)) (sphere (0 : Rd d) 1)
  diam : diamIn G (annA d) (sphere (0 : Rd d) 1) ≤ ENNReal.ofReal M
  diamK : diamIn G (annA d) (annK d) ≤ ENNReal.ofReal M

/-- The pair references (symmetric in `(D, E)`; Part A `a:def-refs`). -/
def PairRefs (D E : DistRd d → ContMetric d) (H₀ σ₀ β₀ m M : ℝ) : Set (DistRd d) :=
  {g | LocalRefs (rho D g) H₀ σ₀ β₀ m M ∧ LocalRefs (rho E g) H₀ σ₀ β₀ m M}

/-- `E ≤ c D + e` on `B̄_R²` (Part A `a:def-comp`). -/
def CompOn (E D : ContMetric d) (c e R : ℝ) : Prop :=
  ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R, E.1 (x, y) ≤ c * D.1 (x, y) + e

/-- A fixed polynomial bound `A (1 + x + y)^k` ([C] l. 89–92; Part A `a:conv`(iv)). -/
def polyB (A k x y : ℝ) : ℝ := A * (1 + x + y) ^ k

/-- Hölder envelope (2.1)–(2.3) of one normalized metric under a law `ν` (Part A `a:def-envelope`). -/
def HolderEnvelope (ν : Measure (DistRd d)) (ρ : DistRd d → ContMetric d) (p σ β C A : ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∃ H : DistRd d → ℝ, Measurable H ∧ (∀ g, 1 ≤ H g) ∧
    ∫⁻ g, ENNReal.ofReal (H g ^ p) ∂ν ≤ ENNReal.ofReal (C * (1 + R) ^ A) ∧
    ∀ᵐ g ∂ν,
      (∀ z ∈ closedBall (0 : Rd d) R, ∀ s ∈ Ioc (0 : ℝ) 1,
        diamIn (ρ g) (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (H g * s ^ σ)) ∧
      (∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
        (H g)⁻¹ * ‖x - y‖ ^ β ≤ (ρ g).1 (x, y))

/-! ## §3 Lemma 2.1: uniform one-metric estimates (Part A `a:def-uniform`, interface of ruling N6)

`∀ξ,D` means: every `ξ ∈ (0, ξ̄]` and every `D` strong at `(ξ, Q(ξ))`. The fixed geometric data are quantified before
the constants, the constants before the parameter. Producer: the Appendix-A chain (packets L1–L4 of the plan, Part D
`d:thm-A3` canonical by ruling N8, with Part A's pin step `a:ssec-l21-proof` Step 5), proving
`∀ d ≥ 3, ∀ ξ̄ subcritical, ∀ s ∈ [1, 10], UniformEstimates d ξ̄ s`. NA4's `UniformCore d b` (Lemma 5.1's input) is the
projection of `UniformEstimates d b 1` written out in NA4 A0; it is derived inside packet N4, not frozen twice. -/

/-- **Lemma 2.1** for the parameter window `(0, ξ̄]` and the pin radius `s` (Part A `a:def-uniform`, clauses (E0)–(E6)). -/
structure UniformEstimates (d : ℕ) (ξbar s : ℝ) : Prop where
  /-- (E0) log-integrability of the unit distance (so `logMean D` is not junk) -/
  logIntegrable : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
    IsStrongExpMetric d ξ (distExp d ξ) D →
      Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d)
  /-- (E1) the two-sided Hölder envelope with polynomial growth in `R` -/
  envelope : ∃ p σ β C A : ℝ, 0 < p ∧ 0 < σ ∧ σ < 1 ∧ 1 < β ∧ 0 < C ∧ 0 ≤ A ∧
    ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → HolderEnvelope (pinLaw d s) (rho D) p σ β C A
  /-- (E2) inverse moments of every order of fixed annular crossings -/
  cross : ∀ (z : Rd d) (r₁ r₂ q : ℝ), 0 < r₁ → r₁ < r₂ → 0 < q → ∃ K : ℝ,
    ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, (setDistIn (rho D g) univ (sphere z r₁) (sphere z r₂))⁻¹ ^ q ∂(pinLaw d s) ≤
          ENNReal.ofReal K
  /-- (E3) a positive moment of fixed buffered internal diameters -/
  diam : ∃ pplus : ℝ, 0 < pplus ∧ ∀ U Kc : Set (Rd d), IsOpen U → Bornology.IsBounded U → IsConnected U →
    IsCompact Kc → Kc ⊆ U → ∃ K : ℝ,
    ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, (diamIn (rho D g) U Kc) ^ pplus ∂(pinLaw d s) ≤ ENNReal.ofReal K
  /-- (E4) all logarithmic moments of fixed point distances -/
  logMoments : ∀ x y : Rd d, x ≠ y → ∀ q : ℝ, 1 ≤ q → ∃ K : ℝ,
    ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, ENNReal.ofReal (|Real.log ((rho D g).1 (x, y))| ^ q) ∂(pinLaw d s) ≤ ENNReal.ofReal K
  /-- (E5) relative escape with a prescribed factor `K` (the exponent does not depend on `K`) -/
  escape : ∃ pesc : ℝ, 0 < pesc ∧ ∀ K : ℝ, 1 ≤ K → ∃ CK : ℝ,
    ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → ∀ R S : ℝ, 1 ≤ R → 4 ≤ S →
        pinLaw d s {g | ¬ (ENNReal.ofReal K * diamIn (rho D g) (ball 0 (2 * R)) (ball 0 R) <
          setDistIn (rho D g) univ (sphere 0 (2 * R)) (sphere 0 (S * R)))} ≤
          ENNReal.ofReal (CK * S ^ (-pesc))
  /-- (E6) proper and geodesic -/
  proper : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
    IsStrongExpMetric d ξ (distExp d ξ) D →
      ∀ᵐ g ∂(pinLaw d s), ProperSpace (rho D g).Space ∧
        ∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d), IsConstSpeedGeod (rho D g) x y γ

/-! ## §4 Parameter windows (NA4 §6.1, §6.3; producer: packet PARX, corollaries of PAR's landed `subcritSet_eq_Ioo`,
`gap24`, `phiXi_lipschitz`; proofs checked by PL1 in scratch. Part C uses PAR's lemmas directly (`c:lem-window`,
`c:cor-phirate`); these `Prop`s record the contract for packets written against NA4's shapes.) -/

/-- A compact parameter window `[lo, hi]` with a uniform subcritical margin `ξ(Q(ξ) - √(2d)) ≥ m` ((2.4)). -/
def MarginWindow (d : ℕ) (lo hi : ℝ) : Prop :=
  0 ≤ lo ∧ lo < hi ∧ ∃ m : ℝ, 0 < m ∧ ∀ ξ ∈ Icc lo hi, 0 < ξ →
    Real.sqrt (2 * d) < distExp d ξ ∧ m ≤ ξ * (distExp d ξ - Real.sqrt (2 * d))

/-- Every positive subcritical parameter lies in the interior of a margin window (continuity of `ξ ↦ ξQ(ξ)`, NA4 F5.1c;
ruling N7: the `ξ`-core needs this continuity, not monotonicity). -/
def SubcritLocal (d : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∃ lo hi : ℝ, 0 < lo ∧ lo < ξ ∧ ξ < hi ∧ MarginWindow d lo hi

/-- `|ϕ(ξ) - 1| ≤ √(2d) ξ` near `0` (NA4 A4; PAR's `phiXi_lipschitz` at `η = 0` gives it for every `ξ > 0`). -/
def PhiRate (d : ℕ) : Prop :=
  ∃ ξ₁ : ℝ, 0 < ξ₁ ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξ₁, |ξ * distExp d ξ - 1| ≤ Real.sqrt (2 * d) * ξ

/-! ## §5 Uniform DGZ exports (Part D `d:sec-udgz`, `d:sec-moments`; NA3 Details (d), BWD's corrections, ruling N8)

Stated over `UHyp d κ b μ ξ` (NA3 ROUTE-4: `ξ ∈ S(b, μ) = {ξ ∈ (0, b] : ξ(Q(ξ) - √(2d)) ≥ μ}`), uniformly over dyadic
realizations. They cross packet boundaries inside the Appendix-A block (U-chain → A1–A4 → L1); none is consumed outside
it (the block's only external export is `UniformEstimates`). -/

/-- The uniform standing hypothesis of the port of DGZ §§4–6 (NA3 Details (d), verbatim; Part D `d:def-param`). -/
structure UHyp (d : ℕ) (κ : Rd d → ℝ) (b μ ξ : ℝ) : Prop where
  base : DGZ.DGZHyp d κ ξ (distExp d ξ)
  le_b : ξ ≤ b
  gap : μ ≤ ξ * (distExp d ξ - Real.sqrt (2 * d))

/-- **U-EXP** (Part D `d:prop-uexp`, (D.1); NA3's `UExpRate` generalized to every quantile `p ∈ (0, 1)` with the
two-sided bound at every depth): `log a_n(p)/(n log 2) → ϕ(ξ) - 1` uniformly on `(0, b]`. -/
def UExpRate (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b ϑ : ℝ, 0 < b → 0 < ϑ → ∀ p : ℝ≥0∞, 0 < p → p < 1 → ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ ξ : ℝ, 0 < ξ → ξ ≤ b →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H →
      (∀ n : ℕ, N ≤ n →
        |Real.log (DGZ.aQ P H ξ n p) / (n * Real.log 2) - (ξ * distExp d ξ - 1)| ≤ ϑ) ∧
      ∀ n : ℕ, C⁻¹ * (2 : ℝ) ^ (-((1 - ξ * distExp d ξ + ϑ) * n)) ≤ DGZ.aQ P H ξ n p ∧
        DGZ.aQ P H ξ n p ≤ C * (2 : ℝ) ^ (-((1 - ξ * distExp d ξ - ϑ) * n))

/-- **CRUDE** (Part D `d:lem-crude`; NA3 R1 with `q' < 1`, ED: `lowerQuantile` at `1` is junk): replaces the lower half
of (A.2) in every use; every `ξ ≥ 0`, no subcriticality. -/
def CrudeLowerShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ ξ : ℝ, 0 ≤ ξ → ∀ q q' : ℝ≥0∞, 0 < q → q < q' → q' < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n m : ℕ, m ≤ n →
        DGZ.aQ P H ξ n q ≤ (q' - q).toReal⁻¹ * (2 : ℝ) ^ (ξ ^ 2 * m / 2) * DGZ.aQ P H ξ (n - m) q'

/-- **U-Cor 5.2** ((A.2) upper half; Part D `d:prop-u52`; NA3 verbatim). -/
def UCor52Shape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → ∀ ε : ℝ, 0 < ε → ∀ q q' : ℝ≥0∞, 0 < q → q < q' → q' < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n k : ℕ, k ≤ n →
        DGZ.aQ P H ξ (n - k) q ≤ C * (2 : ℝ) ^ ((1 - ξ * distExp d ξ + ε) * k) * DGZ.aQ P H ξ n q'

/-- **U-(A.4)**, comparability of fixed quantiles (Part D `d:prop-u64`(b); NA3 verbatim). -/
def UQuantCompShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → ∀ p q : ℝ≥0∞, 0 < p → p < 1 → 0 < q → q < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ,
        DGZ.aQ P H ξ n p ≤ C * DGZ.aQ P H ξ n q

/-- **U-Hölder tightness** (Part D `d:thm-A1`(c), `d:lem-u61`; NA3 verbatim). -/
def UHolderTightShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → ∀ β : ℝ, 0 < β → β < μ →
    ∀ U V : Set (Rd d), IsOpen U → IsOpen V → IsConnected V → Bornology.IsBounded V →
      closure V ⊆ U → ∀ θ : ℝ, 0 < θ → ∃ M : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ,
            P {ω | ∃ x ∈ V, ∃ y ∈ V, M * DGZ.aQ P H ξ n 2⁻¹ * ‖x - y‖ ^ β <
              HigherDimLFPP.lfppDistOn ξ (fun w => H n w ω) U x y} ≤ ENNReal.ofReal θ

/-- **U-nondegeneracy** ((A.3) at every depth; Part D `d:prop-u64`(a); NA3 verbatim). -/
def UNondegShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → ∀ (c : Rd d) (r₁ r₂ : ℝ), 0 < r₂ → r₂ < r₁ → ∀ θ : ℝ, 0 < θ →
    ∃ δ : ℝ, 0 < δ ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ,
        P {ω | DGZ.acrossDist ξ (fun w => H n w ω) c r₁ r₂ ≤ δ * DGZ.aQ P H ξ n 2⁻¹} ≤
          ENNReal.ofReal θ

/-- **U-distance to infinity** (Part D `d:thm-A1`(g), `d:lem-u65`(c); NA3 verbatim). -/
def UDistInfShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → ∀ r T θ : ℝ, 0 < r → 0 < θ → ∃ R : ℝ, r < R ∧ ∃ N : ℕ,
    ∀ ξ : ℝ, UHyp d κ b μ ξ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
        P {ω | DGZ.acrossDist ξ (fun w => H n w ω) 0 R r ≤ T * DGZ.aQ P H ξ n 2⁻¹} ≤
          ENNReal.ofReal θ

/-- **W1** confined upper chaining with moments, white noise (Part D `d:prop-W1`; NA3's shape with BWD's corrections:
the moment order `p` quantified under `8pb ≤ √(2d)`, the bound almost surely and pointwise in the endpoints). -/
def WNUpperMomentShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → μ ≤ 1 → ∀ σ : ℝ, 0 < σ → σ < μ → ∀ p : ℝ, 0 < p →
    8 * p * b ≤ Real.sqrt (2 * d) → ∃ C A : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∃ Hr : Ω → ℝ, Measurable Hr ∧ (∀ ω, 1 ≤ Hr ω) ∧
        ∫⁻ ω, ENNReal.ofReal (Hr ω ^ p) ∂P ≤ ENNReal.ofReal (C * (1 + R) ^ A) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ closedBall (0 : Rd d) R, ∀ s ∈ Ioc (0 : ℝ) 1, ∀ x ∈ ball z s, ∀ y ∈ ball z s,
          HigherDimLFPP.lfppDistOn ξ (fun w => H n w ω) (ball z (3 / 2 * s)) x y ≤
            Hr ω * s ^ σ * DGZ.aQ P H ξ n 2⁻¹

/-- **W2** inverse moments of fixed-shell crossings, white noise (Part D `d:prop-W2`(a); NA3 verbatim). -/
def WNInvCrossShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → ∀ (c : Rd d) (r₁ r₂ : ℝ), 0 < r₂ → r₂ < r₁ → ∀ q : ℝ, 0 < q →
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ,
        ∫⁻ ω, (ENNReal.ofReal (DGZ.acrossDist ξ (fun w => H n w ω) c r₁ r₂ /
          DGZ.aQ P H ξ n 2⁻¹))⁻¹ ^ q ∂P ≤ ENNReal.ofReal C

/-- **C1** upper modulus with moments for the convolution LFPP of the normalized LGF, normalized by the median `aEps`
(Part D `d:prop-C1`; NA3's shape with BWD's correction `32pb ≤ √(2d)`). -/
def ConvUpperMomentShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → μ ≤ 1 → ∀ σ : ℝ, 0 < σ → σ < μ → ∀ p : ℝ, 0 < p →
    32 * p * b ≤ Real.sqrt (2 * d) → ∃ C A : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ ε ∈ Ioo (0 : ℝ) 1,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
      IsNormalizedLGF h P → ∀ R : ℝ, 1 ≤ R →
      ∃ Hr : Ω → ℝ, Measurable Hr ∧ (∀ ω, 1 ≤ Hr ω) ∧
        ∫⁻ ω, ENNReal.ofReal (Hr ω ^ p) ∂P ≤ ENNReal.ofReal (C * (1 + R) ^ A) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ closedBall (0 : Rd d) R, ∀ s ∈ Ioc (0 : ℝ) 1, ∀ x ∈ ball z s, ∀ y ∈ ball z s,
          HigherDimLFPP.lfppDistOn ξ (convMollify κ ε (h ω)) (ball z (3 / 2 * s)) x y ≤
            aEps κ ξ ε * Hr ω * s ^ σ

/-- **C2** inverse moments of a fixed Euclidean annulus crossing, convolution LFPP (Part D `d:prop-C2`; NA3 verbatim). -/
def ConvInvCrossShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → ∀ (z : Rd d) (a c : ℝ), 0 < a → a < c → ∀ q : ℝ, 0 < q →
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ ε ∈ Ioo (0 : ℝ) 1,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
      IsNormalizedLGF h P →
        ∫⁻ ω, (ENNReal.ofReal (aEps κ ξ ε)⁻¹ * infPairs (lfppDist κ ξ ε (h ω)) (sphere z a)
          (sphere z c))⁻¹ ^ q ∂P ≤ ENNReal.ofReal C

/-! ## §6 The comparison interfaces ([C] Props 3.5, 3.7) -/

/-- **Proposition 3.5** as consumed by Proposition 3.6 (Part A `a:def-prop35`, interface of ruling N6; NA1's `prop35`;
NA2 confirms that `g, ε∗, t∗` depend only on `(a, v)`). Under the radius-ten pin: for every target `pt` there are a
guarded radius and a source confidence such that, for `0 < a ≤ ξ, η ≤ ξ̄`, a near-sharp source comparison at coefficient
`c` makes `H↑(c - gn)` rare. Producer: Part B (§4, packets Q1–Q11); consumer: packet P8b (`prop36`). -/
def Prop35Shape (d : ℕ) (ξbar : ℝ) : Prop :=
  ∀ Cb pt : ℝ, 1 < Cb → 0 < pt →
    ∃ Rs q₀ Ap kp v₀ : ℝ, 1 ≤ Rs ∧ 0 < q₀ ∧ 0 < v₀ ∧ v₀ ≤ 1 / 2 ∧
    ∀ a ∈ Ioc (0 : ℝ) ξbar, ∀ v ∈ Ioo (0 : ℝ) v₀, ∃ gn εs ts : ℝ,
      Real.exp (-polyB Ap kp a⁻¹ v⁻¹) ≤ gn ∧ gn ≤ v ∧ 0 < εs ∧ εs ≤ v ∧
      Real.log εs⁻¹ ≤ polyB Ap kp a⁻¹ v⁻¹ ∧ Real.exp (-polyB Ap kp a⁻¹ v⁻¹) ≤ ts ∧
      ∀ ξ ∈ Icc a ξbar, ∀ η ∈ Icc a ξbar, |η - ξ| ≤ ts → ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
        ∀ c : ℝ, 1 + 20 * v ≤ c → c ≤ Cb →
          pinLaw d 10 {g | ¬ CompOn (rho E g) (rho D g) c εs Rs} ≤ ENNReal.ofReal q₀ →
          pinLaw d 10 (Hup D E (c - gn)) ≤ ENNReal.ofReal pt

/-- The profile `log(1 + |F|)` of [C] §5.1 (`F ≥ 0` in every use; NA4 §6.1). -/
def logProfile (F : C(Rd d × Rd d, ℝ)) : C(Rd d × Rd d, ℝ) :=
  ⟨fun p => Real.log (1 + |F p|),
    (continuous_const.add F.continuous.abs).log fun p =>
      (show (0 : ℝ) < 1 + |F p| by positivity).ne'⟩

/-- **Proposition 3.7 in the form used by §5** (Part C `c:lem-p37`, `prop37_window`, verbatim shape; NA4's `Prop37Shape`
with Part A's pins: target under the unit pin `normLGFLaw d`, seed alternative (S) under the radius-ten pin at radius `1`,
windows `[a, ξ̄]` with `ξ̄` subcritical, `n` real). Producer: packet P8b (from Part A `a:prop37`, `a:prop37-seed` with the
hypothesis `Prop35Shape d ξ̄`); consumers: E1a, E1b, E3. -/
def Prop37Shape (d : ℕ) : Prop :=
  ∀ ξbar : ℝ, 0 < ξbar → Real.sqrt (2 * d) < distExp d ξbar →
    ∃ ps c' : ℝ, 0 < ps ∧ ps < 1 ∧ 0 < c' ∧ ∀ R : ℝ, 1 ≤ R →
    ∃ B M C c : ℝ, 0 < B ∧ 0 < M ∧ 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ a ∈ Ioc (0 : ℝ) ξbar, ∀ ξ ∈ Icc a ξbar, ∀ η ∈ Icc a ξbar, ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 8 → ∀ n : ℝ,
          C * δ ^ (-M) * Real.log (C / δ) ≤ n → |ξ - η| * n ≤ c * δ →
          (|ξ - η| ≤ Real.exp (-(C * a ^ (-B) * δ ^ (-B))) ∨
            pinLaw d 10 {g | ENNReal.ofReal (c' * δ) < supDistLU d 1 (rho D g).1 (rho E g).1} ≤
              ENNReal.ofReal ps) →
          normLGFLaw d {g | ENNReal.ofReal δ <
              supDistLU d R (logProfile (rho D g).1) (logProfile (rho E g).1)} ≤
            ENNReal.ofReal (C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n)))

/-! ## §7 Lemma 5.1 and the §5 chain (NA4 A1–A7, ruling N7; Part C; unit-pin convention for the global objects, Part C
`c:conv`(iv)). Only statements that cross a packet boundary of the plan are here (NA4's `PairEuclidStmt`,
`HolderMomentsStmt`, `MedianStmt` stay inside packets N5 and E4). -/

/-- **Lemma 5.1** ((5.3); Part C `c:thm-lem51`, `MarginalEuclidStmt` — NA4's `Lemma51Stmt`, renamed in Part C because
`HigherDimLQGMetric.Lemma51`/`lemma51` exist; both pins `s ∈ {1, 10}` in Part A's convention `pinLaw d s` + `rho`).
Producer: packet N5; consumer: E3 (base nodes at `s = 1`, the seed (S) of `Prop37Shape` at `s = 10`). -/
def MarginalEuclidStmt (d : ℕ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∀ p : ℝ, 1 ≤ p → ∀ r : ℝ, 0 < r → r < 1 →
    ∃ ξ₁ C : ℝ, 0 < ξ₁ ∧ 0 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξ₁, ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → ∀ s : ℝ, s = 1 ∨ s = 10 →
        ∫⁻ g, supDistLU d R (rho D g).1 (euclidDistC d) ^ p ∂(pinLaw d s) ≤
          ENNReal.ofReal (C * ξ ^ (r * p))

/-- Rotation (and reflection) invariance in law of every strong assignment at `Q(ξ)` (NA4 A3, verbatim; not an axiom
of [8]). Producer: packet N2; consumer: N5. -/
def StrongRotLaw (d : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
    ∀ O : Rd d ≃ₗᵢ[ℝ] Rd d,
      (normLGFLaw d).map (fun g => (D g).1.comp ⟨fun p => (O p.1, O p.2), by fun_prop⟩) =
        (normLGFLaw d).map (fun g => (D g).1)

/-- `f_v = ∑_j v_j e_j` (NA4 §6.1). -/
def frameFunRd (e : ℕ → C(Rd d, ℝ)) (v : ℕ →₀ ℝ) : C(Rd d, ℝ) :=
  v.sum fun j c => c • e j

/-- **The pairing frame** (NA4 A2; Part C `c:def-frame`, with its field `one_le_Cb` and `σ < 1`): a coordinate realization of the normalized LGF on `(ℝ^ℕ, stdP)` whose
finitely supported coordinate shifts are shifts by bounded continuous `e_j`, with the Bessel bound for compactly
supported Hölder-regular probability measures. Data; its existence `Nonempty (PairingFrame d)` is produced by packet
N3 and consumed by N4 and E5. -/
structure PairingFrame (d : ℕ) where
  e : ℕ → C(Rd d, ℝ)
  bdd : ∀ j, ∃ M : ℝ, ∀ x, |e j x| ≤ M
  T : GaussianLQG.Coord → DistRd d
  measurable_T : Measurable T
  normalized : IsNormalizedLGF T GaussianLQG.stdP
  good : Set GaussianLQG.Coord
  measurableSet_good : MeasurableSet good
  ae_good : GaussianLQG.stdP goodᶜ = 0
  shift_mem : ∀ ω ∈ good, ∀ v : ℕ →₀ ℝ, GaussianLQG.shiftBy ω v ∈ good
  shift : ∀ ω ∈ good, ∀ v : ℕ →₀ ℝ, T (GaussianLQG.shiftBy ω v) = addFun (T ω) (frameFunRd e v)
  Cb : ℝ
  one_le_Cb : 1 ≤ Cb
  bessel : ∀ (ν : Measure (Rd d)), IsProbabilityMeasure ν → ∀ S B σ : ℝ, 1 ≤ S → 1 ≤ B → 0 < σ →
    σ < 1 → ν (closedBall (0 : Rd d) S)ᶜ = 0 →
    (∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → (ν (closedBall z r)).toReal ≤ B * r ^ σ) →
    ∀ n : ℕ, ∑ j ∈ Finset.range n, (∫ x, e j x ∂ν) ^ 2 ≤
      Cb * (1 + (Real.log B + 1) / σ + Real.log (2 + S))

/-- (3.20) without the log-Sobolev bootstrap: `‖log ρ(0, e₁)‖_p ≤ C p ξ` for all `p ≥ 2` (NA4's `ConcentrationStmt`, `rho`
for `rhoMetric`; Part C `c:prop-conc` proves it on `(0, ξ̄]` for `p ≥ 1`). Producer: packet N4; consumer: N5. -/
def ConcentrationStmt (d : ℕ) : Prop :=
  ∃ ξ₂ C : ℝ, 0 < ξ₂ ∧ 0 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξ₂, ∀ D : DistRd d → ContMetric d,
    IsStrongExpMetric d ξ (distExp d ξ) D → ∀ p : ℝ, 2 ≤ p →
      eLpNorm (fun g => Real.log ((rho D g).1 (0, e₁ d))) (ENNReal.ofReal p) (normLGFLaw d) ≤
        ENNReal.ofReal (C * p * ξ)

/-- §5.1 (NA4 A5; Part C `c:def-posstmt`, unit pin): one jointly measurable family, a version of `ρ^ξ` at every
deterministic positive subcritical `ξ`, a.s. continuous on the positive subcritical set. Producer: packet E1b; consumers:
E3, E4. -/
def PosVersionStmt (d : ℕ) (X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)) : Prop :=
  Measurable (Function.uncurry X) ∧
  (∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ → ∀ D : DistRd d → ContMetric d,
    IsStrongExpMetric d ξ (distExp d ξ) D → ∀ᵐ g ∂(normLGFLaw d), X ξ g = (rho D g).1) ∧
  ∀ᵐ g ∂(normLGFLaw d),
    ContinuousOn (fun ξ => X ξ g) {ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ}

/-- §5.2 (NA4 A6; Part C `c:thm-endpoint`, unit pin): the Euclidean endpoint (5.8) for the same family. Producer: packet
E3; consumer: E4. -/
def EndpointStmt (d : ℕ) (X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)) : Prop :=
  ∀ᵐ g ∂(normLGFLaw d), Tendsto (fun ξ => X ξ g)
    (𝓝[{ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ}] 0) (𝓝 (euclidDistC d))

/-- §§5.3–5.4 (Part C `c:sec-optional`: `c:lem-opt-metric`, `c:lem-opt-proper`, `c:lem-opt-geod`; ruling N11): on one
almost-sure event, every member of the positive-parameter family is a continuous length metric (the metric clause of
`theorem11_metric` before the median normalization). Producer: packet E5 (`metricVersion_of`, from `PosVersionStmt` and
a `PairingFrame`); consumer: E4 (`theorem11_metric_of_parts`). -/
def MetricVersionStmt (d : ℕ) (X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)) : Prop :=
  ∀ᵐ g ∂(normLGFLaw d), ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∃ M : ContMetric d, M.1 = X ξ g ∧ M.IsLength

/-! ## §8 The §4 interfaces (NA2 §3.3, ruling N9)

Site coordinates: a site radius and its primary unit are normalized to one ([C] §4.2, l. 713–716). The deterministic
statements are about `ContMetric`s and sets, never about fields. -/

/-- The collector `C = {3/2 ≤ |x| ≤ 5/2}` of a site ([C] l. 716). -/
def siteC (d : ℕ) : Set (Rd d) := annCl (0 : Rd d) (3 / 2) (5 / 2)

/-- The site inspection `A = {1/2 < |x| < 7/2}` ([C] l. 716); the same set as `annA d` of (2.11), so it is defined as
`annA d` (ruling N8: one declaration per fact; NA2 used a second copy). -/
def siteA (d : ℕ) : Set (Rd d) := annA d

/-- The site ball `B = B₄` ([C] l. 716). -/
def siteB (d : ℕ) : Set (Rd d) := ball (0 : Rd d) 4

/-- First visit time of `P|[a, b]` to `F` (junk `sInf ∅ = 0` excluded: used only under `PassesTrigger`). -/
def firstVisit (P : ℝ → Rd d) (a b : ℝ) (F : Set (Rd d)) : ℝ := sInf {t | t ∈ Icc a b ∧ P t ∈ F}

/-- Last visit time of `P|[a, b]` to `F` (junk excluded as for `firstVisit`). -/
def lastVisit (P : ℝ → Rd d) (a b : ℝ) (F : Set (Rd d)) : ℝ := sSup {t | t ∈ Icc a b ∧ P t ∈ F}

/-- The source trigger ([C] l. 744–746), made total (NA2 R9, ruling N9): the path visits the collector and the source
internal distance in `B` between its first and last collector visits is `≥ btrig`. -/
def PassesTrigger (D : ContMetric d) (P : ℝ → Rd d) (a b btrig : ℝ) : Prop :=
  (∃ t ∈ Icc a b, P t ∈ siteC d) ∧
    ENNReal.ofReal btrig ≤
      D.internal (siteB d) (P (firstVisit P a b (siteC d))) (P (lastVisit P a b (siteC d)))

/-- `P|[a, b]` is a `D`-geodesic segment. -/
def IsGeodSeg (D : ContMetric d) (P : ℝ → Rd d) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn P (Icc a b) ∧ D.len P a b = ENNReal.ofReal (D.1 (P a, P b))

/-- `D'` is the Weyl modification of `D` by the weight `e^{ξ F}`, on every open set (internal form). -/
def IsWeylInternal (ξ : ℝ) (F : C(Rd d, ℝ)) (D D' : ContMetric d) : Prop :=
  ∀ U : Set (Rd d), IsOpen U → ∀ x y : Rd d, D'.internal U x y = weylScaleOn ξ F D U x y

/-- **The deterministic forcing certificate of one site** (NA2 §3.1, probe `NA2Section4.lean`, verbatim except the
added field `h_pos`, NA2 finding 5): the
hypotheses of Lemma 4.3, bundled. `U` is the closed plateau network with open core `Uo` (finitely many open balls), the
nodes are the closed remnants and gates of the subdivided incidence tree, `Ch` indexes the chambers with their two
opposite gates. Costs: access and star diameters `ε₀` (fixed before `v`), the discounted network `εnet = θ A_net` and
the attachments `εatt = C H h^s`, both `≪ H⁻¹ δsep^b` ((4.11)–(4.12)). Data (a `Type`). -/
structure ForcingCert (D E : ContMetric d) (f : C(Rd d, ℝ))
    (ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ) where
  U : Set (Rd d)
  Uo : Set (Rd d)
  hU : IsClosed U
  hUo : IsOpen Uo
  hUoU : Uo ⊆ U
  /-- the support collar is positive (NA2 finding 5: `cthickening` at a radius `≤ 0` is the closure, a junk value) -/
  h_pos : 0 < h
  hV : cthickening h U ⊆ interior (siteC d)
  f_eq : ∀ x ∈ U, f x = M
  f_bd : ∀ x, 0 ≤ f x ∧ f x ≤ M
  f_supp : tsupport f ⊆ cthickening (h / 2) U
  θ_eq : θ = Real.exp (-(ξ * M))
  access : ∀ x ∈ siteC d, ∃ y ∈ Uo, D.internal (siteA d) x y ≤ ENNReal.ofReal ε₀
  net : ∀ x ∈ Uo, ∀ y ∈ Uo, ENNReal.ofReal θ * D.internal Uo x y ≤ ENNReal.ofReal εnet
  attach : ∀ x ∈ cthickening h U, ∃ y ∈ Uo, D.internal (siteA d) x y ≤ ENNReal.ofReal εatt
  collar : ∀ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) →
    ((‖P 0‖ = 3 / 2 ∧ ‖P 1‖ = 1 / 2) ∨ (‖P 0‖ = 5 / 2 ∧ ‖P 1‖ = 7 / 2)) →
      ENNReal.ofReal aout ≤ D.len P 0 1
  lower : ∀ x ∈ siteC d, ∀ y ∈ siteC d, ENNReal.ofReal (H⁻¹ * ‖x - y‖ ^ b) ≤ D.internal (siteA d) x y
  Node : Type
  node_fin : Fintype Node
  N : Node → Set (Rd d)
  N_closed : ∀ n, IsClosed (N n)
  adj : SimpleGraph Node
  Ch : Type
  ch_fin : Fintype Ch
  gate0 : Ch → Node
  gate1 : Ch → Node
  cover : U ⊆ ⋃ n, N n
  sep : ∀ n n', n ≠ n' → ¬ adj.Adj n n' → ∀ x ∈ N n, ∀ y ∈ N n', δsep ≤ dist x y
  /-- a connected node set containing no pair of opposite gates lies in one augmented vertex star, of source diameter
  `≤ ε₀` -/
  star : ∀ S : Set Node, (adj.induce S).Connected → (∀ e : Ch, ¬ (gate0 e ∈ S ∧ gate1 e ∈ S)) →
    ∃ W : Set (Rd d), (⋃ n ∈ S, cthickening h (N n)) ⊆ W ∧ diamIn D (siteA d) W ≤ ENNReal.ofReal ε₀
  /-- the favorable arc of each chamber ((4.10)), its gate connectors ((4.6)) and the gate diameters -/
  arc : ∀ e : Ch, ∃ u w : Rd d, ∃ G₀ G₁ Cham : Set (Rd d),
    IsOpen G₀ ∧ IsOpen G₁ ∧ IsOpen Cham ∧ G₀ ⊆ Uo ∧ G₁ ⊆ Uo ∧ Cham ⊆ Uo ∧
    u ∈ N (gate0 e) ∧ w ∈ N (gate1 e) ∧ u ∈ G₀ ∧ w ∈ G₁ ∧ d₀ ≤ D.1 (u, w) ∧
    diamIn D (siteA d) (cthickening h (N (gate0 e))) ≤ ENNReal.ofReal (v * d₀ / 1000) ∧
    diamIn D (siteA d) (cthickening h (N (gate1 e))) ≤ ENNReal.ofReal (v * d₀ / 1000) ∧
    (∀ x ∈ cthickening h (N (gate0 e)), ∃ y ∈ G₀,
      E.internal (siteB d) x y ≤ ENNReal.ofReal (v * θ * d₀ / 1000)) ∧
    (∀ x ∈ cthickening h (N (gate1 e)), ∃ y ∈ G₁,
      E.internal (siteB d) x y ≤ ENNReal.ofReal (v * θ * d₀ / 1000)) ∧
    (∀ y ∈ G₀, E.internal G₀ y u ≤ ENNReal.ofReal (v * d₀ / 1000)) ∧
    (∀ y ∈ G₁, E.internal G₁ y w ≤ ENNReal.ofReal (v * d₀ / 1000)) ∧
    E.internal Cham u w ≤ ENNReal.ofReal ((1 + 4 * v) * D.1 (u, w))

/-- **Lemma 4.3** (deterministic forcing; [C] l. 738–852; NA2's `lemma43_forcing` as a proposition, all binders
universally quantified in the same order). For the modified metrics `D' = e^{-ξ f} D`, `E' = e^{-η f} E` with
`|η - ξ| M ≤ Ω`, every `D'`-geodesic segment with endpoints outside `B` that passes the source trigger contains a block
in `A` between two enlarged opposite gates, of `D'`-length `≥ θ d₀ / 2`, whose endpoints are joined inside `B` at
`E'`-cost `≤ (1 + 6v) e^{2Ω}` times the block length. Producer: packet Q6; consumers: Q8a, Q9. -/
def Lemma43Forcing (d : ℕ) : Prop :=
  ∀ {D E D' E' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ η M θ h δsep ε₀ εnet εatt btrig aout H b v d₀ Ω : ℝ},
    ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ →
    IsWeylInternal ξ (-f) D D' → IsWeylInternal η (-f) E E' →
    0 ≤ ξ → 0 ≤ η → 0 < d₀ → |η - ξ| * M ≤ Ω → 0 < v → v ≤ 1 / 100 → Ω ≤ v / 100 →
    3 * ε₀ < 2 * aout → εnet ≤ ε₀ → 7 * ε₀ < btrig → 4 * h ≤ δsep →
    2 * εatt + εnet < H⁻¹ * (δsep / 2) ^ b →
    ∀ (P : ℝ → Rd d) (a c : ℝ), IsGeodSeg D' P a c → P a ∉ siteB d → P c ∉ siteB d →
      PassesTrigger D P a c btrig →
      ∃ s t : ℝ, a ≤ s ∧ s ≤ t ∧ t ≤ c ∧ (∀ τ ∈ Icc s t, P τ ∈ siteA d) ∧
        ENNReal.ofReal (θ * d₀ / 2) ≤ D'.len P s t ∧
        E'.internal (siteB d) (P s) (P t) ≤
          ENNReal.ofReal ((1 + 6 * v) * Real.exp (2 * Ω)) * D'.len P s t

open Classical in
/-- **Lemma 4.4** under the radius-ten pin with shifts supported in `B₄` (NA2 R12; `lemma44_pinned` as a proposition):
from `s7b_cm_markov_count`/`cm_holder_count`, `pin 10 (shiftNorm h F) = addFun (pin 10 h) F` a.s., and
`p = 1 + √(2 log N)/M`. Producer: packet Q8b; consumer: Q8b's `prop45_of_counts`, Q9. -/
def Lemma44Pinned (d : ℕ) : Prop :=
  ∀ {ι : Type} (S : Finset ι) (A : ι → Set (DistRd d)), (∀ i, MeasurableSet (A i)) →
    ∀ (F : ι → C(Rd d, ℝ)) {M : ℝ}, 0 ≤ M → (∀ i, IsCMBounded (F i) M) →
    (∀ i, tsupport (F i) ⊆ ball (0 : Rd d) 4) → ∀ {L U : ℝ}, 0 < L → 0 ≤ U →
    ∀ B : Set (DistRd d),
      (∀ᵐ g ∂(pinLaw d 10), g ∈ B → L ≤ ((S.filter fun i => g ∈ A i).card : ℝ)) →
      (∀ᵐ g ∂(pinLaw d 10), ((S.filter fun i => addFun g (F i) ∈ A i).card : ℝ) ≤ U) →
      pinLaw d 10 B ≤
        ENNReal.ofReal (U / L * min (S.card : ℝ) (Real.exp (M * Real.sqrt (2 * Real.log S.card))))

open Classical in
/-- **Proposition 4.5 from its counts** ([C] (4.18), (4.20), (4.21); NA2's `prop45_of_counts` as a proposition): with the
lower multiplicity `#{Z : H ∈ A_Z} ≥ e^{m₀ℓ/2}/k^k` on `B`, the active bound `#{Z : h + f_Z ∈ A_Z} ≤ (CK₁J)^k (k+1)^k`,
the index count `≤ (CJ e^{D₀ℓ})^k` and energies `≤ k M₀`, Lemma 4.4 and the depth condition give
`P(B) ≤ Δ^{2μ+2}`, `Δ = e^{-ℓ}`. Producer: packet Q8b; consumer: Q9. -/
def Prop45OfCounts (d : ℕ) : Prop :=
  ∀ {α : Type} (Idx : Finset (Finset α)) (A : Finset α → Set (DistRd d)),
    (∀ Z, MeasurableSet (A Z)) → ∀ (F : Finset α → C(Rd d, ℝ))
    {k m₀ : ℕ} {κ μ D₀ M₀ CJ CKJ ℓ : ℝ}, 0 < κ → 0 < D₀ → 0 < M₀ → 1 ≤ CJ → 1 ≤ CKJ →
    (4 * μ + 4) / (κ / 2) ≤ k → κ * k ≤ m₀ →
    max (max (Real.log CJ / D₀) (4 * (2 * Real.log k + Real.log CKJ + 1) / (κ / 2)))
      (max (64 * k * D₀ * M₀ ^ 2 / ((κ / 2) ^ 2)) (2 * Real.log k)) ≤ ℓ →
    (∀ Z ∈ Idx, IsCMBounded (F Z) (k * M₀)) → (∀ Z, tsupport (F Z) ⊆ ball (0 : Rd d) 4) →
    (Idx.card : ℝ) ≤ (CJ * Real.exp (D₀ * ℓ)) ^ k → ∀ B : Set (DistRd d),
    (∀ᵐ g ∂(pinLaw d 10), g ∈ B →
      Real.exp (m₀ * ℓ / 2) / (k : ℝ) ^ k ≤ ((Idx.filter fun Z => g ∈ A Z).card : ℝ)) →
    (∀ᵐ g ∂(pinLaw d 10),
      ((Idx.filter fun Z => addFun g (F Z) ∈ A Z).card : ℝ) ≤ CKJ ^ k * (k + 1 : ℝ) ^ k) →
    pinLaw d 10 B ≤ ENNReal.ofReal (Real.exp (-(2 * μ + 2) * ℓ))

/-! ### The site certificate (interface version 2; ruling N13; blueprint Part B)

Part B's consumer contract of the site certificate: `b:def-dupper` (`DUpper`), `b:def-refs4` (`SiteRefs`, `SeedRefs`),
`b:def-sitedata` (F2) (`siteAout`, `siteBtrig`, `siteEps0`), `b:def-seedfav` (`SeedFav`) and Theorem `b:thm-sitecert`
(`SiteCertOfLabel`) with `b:lem-label-exists` (exhaustion), `b:lem-src-meas` (Borel validity, locality),
`b:lem-catalogue`, `b:lem-bump` and `b:lem-order`(d) (the polynomial bounds). Order of constants as in Part B: the site
references (F1), then the fixed site geometry (F3)–(F5) (tree edges `Edge`, reserved-box centres `centre e = m_e`, box
size `L`; seed radii `s_{e,j} = (L/4) 8^{-j}`, `j = 1, …, Ntr`), then the number of trials `Ntr` and the seed constants
(F6) (seed references `(H₀, σ₀, β₀, m, M)`, doubled-ball constants `(Hsd, σsd)`, unit bound `Λ`), then `d₀` and the
threshold `vsite`, then the tolerance `v`; the bump height `ξ⁻¹ log θ⁻¹` is the only dependence on `ξ`. The concrete
labels, network and source predicate of Part B (`EdgeLabel`, `SiteLabel`, `labelCatalogue`, `IsRealizable`,
`siteConsts`, `labelNet`, `SiteSource`) are owned by the producer packets Q3–Q7: they never cross the boundary to the
consumers Q9–Q11, and Part B leaves `C_net`, `C_J`, `C_bump`, `v_site` non-explicit, so they are not frozen here.
Correction to `b:thm-sitecert`(iv) (IA1 finding): the primary metric must be a length metric (the certificate's global
`D(u, w)` equals the seed-internal one only for length metrics; counterexample `min(D, c)`, which has the same internal
metrics). -/

/-- Doubled-ball upper reference `DUp(G, W, H, σ)` (Part B `b:def-dupper`): for every ball with `B̄_{2ρ}(z) ⊆ W`, the
internal diameter of `B_ρ(z)` in `B_{2ρ}(z)` is at most `H ρ^σ`. A condition on `G(·, ·; W)` only. -/
def DUpper (G : ContMetric d) (W : Set (Rd d)) (H σ : ℝ) : Prop :=
  ∀ (z : Rd d) (ρ : ℝ), 0 < ρ → closedBall z (2 * ρ) ⊆ W →
    diamIn G (ball z (2 * ρ)) (ball z ρ) ≤ ENNReal.ofReal (H * ρ ^ σ)

/-- The site references (R1)–(R4) of a metric in site coordinates (Part B `b:def-refs4`) with the constants (F1)
`(Hup, s, Hlo, b, mc, A0)`: (R1) doubled-ball upper reference in `A`; (R2) intrinsic lower bound on the collector;
(R3) both collar crossings inside `A`; (R4) the `A`-internal diameter of the collector. Every clause is a condition on
the internal metric of `G` in `A`. -/
def SiteRefs (Hup s Hlo b mc A0 : ℝ) (G : ContMetric d) : Prop :=
  DUpper G (siteA d) Hup s ∧
  (∀ x ∈ siteC d, ∀ y ∈ siteC d, ENNReal.ofReal (Hlo⁻¹ * ‖x - y‖ ^ b) ≤ G.internal (siteA d) x y) ∧
  ENNReal.ofReal mc ≤ setDistIn G (siteA d) (sphere (0 : Rd d) 1) (sphere (0 : Rd d) (3 / 2)) ∧
  ENNReal.ofReal mc ≤ setDistIn G (siteA d) (sphere (0 : Rd d) (5 / 2)) (sphere (0 : Rd d) 3) ∧
  diamIn G (siteA d) (siteC d) ≤ ENNReal.ofReal A0

/-- (F2) the collar constant `aout = ½ min(mc, Hlo⁻¹)` (Part B `b:def-sitedata`). -/
def siteAout (mc Hlo : ℝ) : ℝ := min mc Hlo⁻¹ / 2

/-- (F2) the trigger threshold `btrig = aout / 32`. -/
def siteBtrig (mc Hlo : ℝ) : ℝ := siteAout mc Hlo / 32

/-- (F2) the access and star scale `ε₀ = btrig / 8`. -/
def siteEps0 (mc Hlo : ℝ) : ℝ := siteBtrig mc Hlo / 8

/-- The seed references (Part B `b:def-refs4`): local references `(H₀, σ₀, β₀, m, M)` (Part A `a:def-refs`) of both
metrics and their doubled-ball upper references `(Hsd, σsd)` in `A`. -/
def SeedRefs (H₀ σ₀ β₀ m M Hsd σsd : ℝ) (D E : ContMetric d) : Prop :=
  LocalRefs D H₀ σ₀ β₀ m M ∧ LocalRefs E H₀ σ₀ β₀ m M ∧ DUpper D (annA d) Hsd σsd ∧
    DUpper E (annA d) Hsd σsd

/-- A favorable seed at centre `c` and radius `r` (Part B `b:def-seedfav`, site coordinates, both metrics in primary
site units): seed units `SD, SE ∈ [Λ⁻¹, Λ]` with the cap `|log(SE/SD)| ≤ v/10`, the seed references of the pulled-back
metrics `D'' = SD⁻¹ D(c + r·)`, `E'' = SE⁻¹ E(c + r·)`, and an `E''`-witness with own-unit ratio `≤ 1 + 2v`. -/
def SeedFav (H₀ σ₀ β₀ m M Hsd σsd Λ v : ℝ) (D E : ContMetric d) (c : Rd d) (r : ℝ) : Prop :=
  ∃ hr : r ≠ 0, ∃ SD SE : ℝ, ∃ hSD : 0 < SD, ∃ hSE : 0 < SE,
    Λ⁻¹ ≤ SD ∧ SD ≤ Λ ∧ Λ⁻¹ ≤ SE ∧ SE ≤ Λ ∧ |Real.log (SE / SD)| ≤ v / 10 ∧
    SeedRefs H₀ σ₀ β₀ m M Hsd σsd ((D.affine r hr c).smul SD⁻¹ (inv_pos.2 hSD))
      ((E.affine r hr c).smul SE⁻¹ (inv_pos.2 hSE)) ∧
    ∃ γ : C(unitInterval, Rd d), IsWitness ((E.affine r hr c).smul SE⁻¹ (inv_pos.2 hSE)) γ ∧
      ((E.affine r hr c).smul SE⁻¹ (inv_pos.2 hSE)).internal (annA d) (γ 0) (γ 1) ≤
        ENNReal.ofReal (1 + 2 * v) *
          ((D.affine r hr c).smul SD⁻¹ (inv_pos.2 hSD)).internal (annA d) (γ 0) (γ 1)

/-- A finite label catalogue: a profile (unit-height bump of the plateau network, Part B `b:def-bump`) and the source
validity predicate (Part B `b:def-source`) of each label. Data; the concrete catalogue of Part B instantiates it. -/
structure SiteCatalogue (d : ℕ) where
  Label : Type
  fintypeLabel : Fintype Label
  prof : Label → C(Rd d, ℝ)
  Source : Label → ContMetric d → ContMetric d → Prop

/-- **The site certificate** (Part B Theorem `b:thm-sitecert`, with `b:lem-label-exists`, `b:lem-src-meas`,
`b:lem-catalogue`, `b:lem-bump`, `b:lem-order`(d)). Given the site references (F1), there are a fixed site geometry
and, for every number of trials and seed constants (F6), a unit-pair bound `d₀ > 0` and a threshold `vsite ≤ 1/100`,
such that for every tolerance `v ∈ (0, vsite]` there are a label catalogue and the scales `θ, ς, δsep, εnet, εatt`
(polynomial in `v`) with: (i) catalogue bounds; (ii) Borel validity on pairs of length metrics, locality in `B`, and
validity ⇒ the primary site references; (iii) exhaustion of the favorable site event; (iv) the forcing certificate of
every valid label for a length primary metric, with the side conditions of `Lemma43Forcing` (those not displayed follow
from the (F2) formulas: `3 ε₀ < 2 aout`, `7 ε₀ < btrig`). Producer: packet Q7 (from Q3–Q6); consumers: Q9, Q10, Q11. -/
def SiteCertOfLabel (d : ℕ) : Prop :=
  ∀ Hup s Hlo b mc A0 : ℝ, 1 ≤ Hup → 0 < s → s ≤ 1 → 1 ≤ Hlo → 1 ≤ b → 0 < mc → Hlo⁻¹ ≤ A0 →
  ∃ (Edge : Type) (_ : Fintype Edge) (centre : Edge → Rd d) (L : ℝ), 0 < L ∧
    (∀ e, closedBall (centre e) L ⊆ interior (siteC d)) ∧
  ∀ (Ntr : ℕ) (H₀ σ₀ β₀ m M Hsd σsd Λ : ℝ), 1 ≤ H₀ → 0 < σ₀ → σ₀ < 1 → 1 < β₀ → 0 < m → m < M →
    1 ≤ Hsd → 0 < σsd → σsd ≤ 1 → 1 ≤ Λ →
  ∃ d₀ vsite Ap kp : ℝ, 0 < d₀ ∧ 0 < vsite ∧ vsite ≤ 1 / 100 ∧
  ∀ v ∈ Ioc (0 : ℝ) vsite, ∃ (cat : SiteCatalogue d) (θ ς δsep εnet εatt : ℝ),
    Real.exp (-polyB Ap kp 0 v⁻¹) ≤ θ ∧ θ < 1 ∧ 0 < ς ∧ 4 * ς ≤ δsep ∧ εnet ≤ siteEps0 mc Hlo ∧
    2 * εatt + εnet < Hlo⁻¹ * (δsep / 2) ^ b ∧
    -- (i) the catalogue
    Real.log (@Fintype.card cat.Label cat.fintypeLabel) ≤ polyB Ap kp 0 v⁻¹ ∧
    (∀ ℓ, (∀ x, 0 ≤ cat.prof ℓ x ∧ cat.prof ℓ x ≤ 1) ∧ tsupport (cat.prof ℓ) ⊆ interior (siteC d) ∧
      IsCMBounded (cat.prof ℓ) (polyB Ap kp 0 v⁻¹)) ∧
    -- (ii) validity: Borel on pairs of length metrics, local in `B`, and it contains the primary references
    (∀ ℓ, ∃ S : Set (ContMetric d × ContMetric d), MeasurableSet S ∧
      ∀ D E : ContMetric d, D.IsLength → E.IsLength → ((D, E) ∈ S ↔ cat.Source ℓ D E)) ∧
    (∀ ℓ (D E D₂ E₂ : ContMetric d), (∀ x y, D.internal (siteB d) x y = D₂.internal (siteB d) x y) →
      (∀ x y, E.internal (siteB d) x y = E₂.internal (siteB d) x y) →
      (cat.Source ℓ D E ↔ cat.Source ℓ D₂ E₂)) ∧
    (∀ ℓ (D E : ContMetric d), cat.Source ℓ D E → SiteRefs Hup s Hlo b mc A0 D) ∧
    -- (iii) exhaustion: the primary references and a favorable concentric seed on every edge give a valid label
    (∀ D E : ContMetric d, D.IsLength → E.IsLength → SiteRefs Hup s Hlo b mc A0 D →
      (∀ e : Edge, ∃ j : Fin Ntr, SeedFav H₀ σ₀ β₀ m M Hsd σsd Λ v D E (centre e)
        (L / 4 * (8 : ℝ)⁻¹ ^ ((j : ℕ) + 1))) →
      ∃ ℓ, cat.Source ℓ D E) ∧
    -- (iv) the forcing certificate of every valid label (primary metric a length metric)
    (∀ ξ : ℝ, 0 < ξ → ∀ ℓ (D E : ContMetric d), D.IsLength → cat.Source ℓ D E →
      Nonempty (ForcingCert D E ((ξ⁻¹ * Real.log θ⁻¹) • cat.prof ℓ) ξ (ξ⁻¹ * Real.log θ⁻¹) θ ς δsep
        (siteEps0 mc Hlo) εnet εatt (siteAout mc Hlo) Hlo b v d₀))

/-! ## §9 The frozen theorem statements as propositions (verbatim from `HigherDimLQGContinuity/Frozen/*.lean`)

For the assembly (pattern of the previous campaign's `Core/MainInputs.lean`): packets prove implications between these
without importing the anchors; the providers `<anchor>_impl` then state the frozen text verbatim and close by `exact`.
The orchestrator checks the verbatim copy mechanically (ABI of the anchor statement = the unfolded `Prop`). -/

/-- the statement of the frozen anchor `theorem11Xi`, verbatim -/
def Theorem11XiStmt : Prop :=
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D ξ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ ξ₀ ∈ xiRange d, ∀ R : ℝ, 0 < R →
          Tendsto (fun ξ => supDistLU d R (D ξ (h ω)) (D ξ₀ (h ω))) (𝓝[xiRange d] ξ₀) (𝓝 0)

/-- the statement of the frozen anchor `theorem11`, verbatim -/
def Theorem11Stmt : Prop :=
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ γ : ℝ, 0 < γ → γ < Real.sqrt (2 * d) →
        ∀ ξ : ℝ, 0 < ξ → distExp d ξ = (d : ℝ) / γ + γ / 2 →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D γ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ γ₀ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∀ R : ℝ, 0 < R →
          Tendsto (fun γ => supDistLU d R (D γ (h ω)) (D γ₀ (h ω)))
            (𝓝[Ico (0 : ℝ) (Real.sqrt (2 * d))] γ₀) (𝓝 0)

/-- the statement of the frozen anchor `prop18`, verbatim -/
def Prop18Stmt : Prop :=
    ∀ d : ℕ, 3 ≤ d →
      ContinuousOn (distExp d) (Ioi 0) ∧
      StrictAntiOn (distExp d) {ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ} ∧
      Tendsto (fun ξ => ξ * distExp d ξ) (𝓝[>] 0) (𝓝 1) ∧
      ∃ Ξ : ℝ → ℝ, Ξ 0 = 0 ∧
        StrictMonoOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        ContinuousOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        Ξ '' Ico 0 (Real.sqrt (2 * d)) = xiRange d ∧
        (∀ γ ∈ Ioo (0 : ℝ) (Real.sqrt (2 * d)), ∀ ξ : ℝ, 0 < ξ →
          (distExp d ξ = (d : ℝ) / γ + γ / 2 ↔ ξ = Ξ γ)) ∧
        Tendsto (fun γ => γ / Ξ γ) (𝓝[>] 0) (𝓝 (d : ℝ))

/-- the statement of the frozen anchor `medianOneStrong_exists`, verbatim -/
def MedianOneStrongExistsStmt : Prop :=
    ∀ d : ℕ, 3 ≤ d → ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E ∧ IsMedianOne d E

/-- the statement of the frozen anchor `theorem11_metric` (approval version 2, ruling N11), verbatim -/
def Theorem11MetricStmt : Prop :=
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ γ : ℝ, 0 < γ → γ < Real.sqrt (2 * d) →
        ∀ ξ : ℝ, 0 < ξ → distExp d ξ = (d : ℝ) / γ + γ / 2 →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D γ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, (∀ γ₀ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∀ R : ℝ, 0 < R →
            Tendsto (fun γ => supDistLU d R (D γ (h ω)) (D γ₀ (h ω)))
              (𝓝[Ico (0 : ℝ) (Real.sqrt (2 * d))] γ₀) (𝓝 0)) ∧
          ∀ γ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∃ M : ContMetric d, M.1 = D γ (h ω) ∧ M.IsLength

end HigherDimLQGContinuity
