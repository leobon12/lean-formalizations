import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import SupercriticalLQGUniqueness.Frozen.IsLFPPNormalizer
import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing
import SupercriticalLQGUniqueness.Frozen.RescaledLFPP
import SupercriticalLQGUniqueness.Frozen.LSCMetricToLSCFun
import SupercriticalLQGUniqueness.Frozen.LSCTendsto
import SupercriticalLQGUniqueness.Frozen.LSCTendstoInProbability
import SupercriticalLQGUniqueness.Frozen.AcrossDist
import SupercriticalLQGUniqueness.Frozen.AroundDist
import SupercriticalLQGUniqueness.Frozen.ScaleTranslateDist
import SupercriticalConformalCovariance.Frozen.XiCrit
import SupercriticalLQGUniqueness.B2.Polylog.P7Trunc
import SupercriticalLQGUniqueness.B2.Polylog.P4Costs
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3
import LQGMetric.Metric.Geodesic
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Meas.UM
import SupercriticalLFPPAS.Field.LocalizedApproximation
import SupercriticalLFPPAS.Compare.ScaleRatio
import SupercriticalLFPPAS.Iteration.Radii
import SupercriticalLFPPAS.Iteration.Recursion
import SupercriticalLFPPAS.Inputs.RationalCircleDistanceFinite
import Mathlib.Analysis.ConstantSpeed

/-!
# Interface statements shared between packets (orchestrator-owned; drafted by planner PL, 2026-10-26)

Path: `SupercriticalLFPPAS/Core/Interfaces.lean` (namespace `SupercriticalLFPPAS.Core`). Interface-first scheduling (packet
plan `planning/PACKET-PLAN.md`, precedent: ruling N6/N12 of `higher_dim_lqg_continuity`). A statement that one packet proves
and other packets consume before it lands is defined here **once**, as a named `Prop`. Consumers take it as a hypothesis,
producers prove it (as an implication from the interfaces they consume), the assembly (packet ASM) composes the
`…_holds` theorems into the provider of the frozen anchor `lfpp_ae_lscTendsto`. Workers import this module and never edit
or redefine it. **These `Prop`s must never appear in a frozen statement** (hypothesis smuggling): they are consumed only
inside proofs below the anchors.

Imports: the repository libraries (`SupercriticalLQGUniqueness`, `SupercriticalConformalCovariance`, `LQGMetric`), Mathlib
and four landed modules of this library: `Field.LocalizedApproximation` (`uniformLocalizationExponent`), `Compare.ScaleRatio`
(`Compare.kappa`, D6), `Iteration.Radii`/`Iteration.Recursion` (`radiusExponents`, `annulusBase`, `contractionFactor`, D7),
`Inputs.RationalCircleDistanceFinite` (`rationalCircle`, D2). Never a frozen theorem anchor, never a running packet's module.

Sources of the shapes (binding mathematics): `planning/audits/SB1-sections-1-3.md` (§§1–3.1, Details A1–A13, (c)),
`planning/audits/SB2-sections-3-7.md` (§§3.2–7, Details D1–D11, (c)), `planning/audits/SB3-crosscheck-3-7.md` (§5),
`planning/audits/S1-statement-audit.md` (the frozen surface v2, rulings P6/P7).

Contents:
* §0 The setting: `IsLFPPLimitAll`, `Setup` (ξ, Q, 𝔞, D with their sealed properties), `IsJointHeatVersion`.
* §1 Objects: `locMetric` (X̂_ε), `locFieldC`/`locMetricY` (H_{δ,L}, Y_{δ,L}), `lfppM` (X_ε), `kappaS` (κ_ε(r), D6's
  `Compare.kappa`), `recentred` (h^{z,r}), `srcV`, `tgtU`, `bandRad` (radius `4096^j`); reused landed objects:
  `Iteration.radiusExponents` (R_ε(s,t)), `Iteration.contractionFactor` (F(C,K)), `SupercriticalLFPPAS.rationalCircle`.
* §2 Field estimates (Lemma 2.1): `LocApproxStmt` (2.1), `MeshOscStmt` (2.2), `UnifLocStmt` (2.3).
* §3 Scaling and comparison adapters: `ScalingDStmt` (1.3), `DilationStmt` (2.4), `KappaBoundsStmt` (2.6),
  `LocCompareStmt` (2.7)–(2.8).
* §4 Confinement: `ConfinementStmt` (Lemma 2.2), `LocCircleStmt` (2.9), `LFPPGeodesicStmt` (LFPP geodesics).
* §5 §3: `OneWayCompare`, `Lemma32Event`, `Lemma32EventU`, `Lemma32LocStmt` (Lemma 3.2, localized, uniform in L),
  `Lemma32MeasStmt`, `Lemma32LocalityStmt` (Remark 3.3), `SurroundProp`, `Lemma35Stmt` (Lemma 3.5), `AnnTightStmt`
  (annular tightness of D and Y_{δ,L}).
* §6 Good scales: `GoodScale` (deterministic content of a good root scale, geodesic-independent), `UnitGoodStmt` (§3.3 at
  the unit scale), `RootEventStmt` (§3.3 at centre z and radius r).
* §7 Contraction: `IsGeodIn`, `GoodDiskIn`, `Lemma41Stmt` (Lemma 4.1′ of SB2 D6), `CompIn`, `ContractionStmt` (§4.2).
* §8 Identification: `NoContractStmt` ((5.6) and its q′ analogue, in the form consumed by Proposition 5.1),
  `Prop51Stmt` (Proposition 5.1).
* §9 Interpolation and the theorem: `NormalizerWindowStmt` (Lemma 6.1, corrected absolute form), `Lemma62Stmt`
  (Lemma 6.2), `MainAeStmt` (§7), `Lfpp_ae_lscTendstoStmt` (the frozen anchor's type, verbatim), `Lfpp_ae_lscTendstoAllXiStmt`
  (the unfrozen all-ξ corollary, S1 N1).

Conventions (junk safety): probabilities of possibly non-measurable events are outer measures (`P S` for any `S`), used
only in upper bounds (Borel–Cantelli `MeasureTheory.measure_limsup_atTop_eq_zero` holds for arbitrary sets) or in lower
bounds whose producer must show them (`NoContractStmt`); lower bounds on probabilities of events consumed by the annulus
iteration (1.6) are stated for `MeasurableSet`/`AEEventIn` events only. Distances are `ℝ≥0∞`-valued, so no `toReal` junk
occurs. Every `Set.Ioi 0`-valued argument carries its positivity proof. "Uniform over the probability space" (constants
quantified before `Ω`) is used exactly where a unit-scale statement is applied to many recentred fields `h^{z,r}` on one
space (the producer obtains it from the law-transfer lemma
`SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.prob_preimage_eq_of_normalized`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Core

open LQGMetric (DistC addConst circleAvg IsGFFPlusBddCont)
open SupercriticalLQGUniqueness (IsStrongLQGMetric IsLFPPExponent IsLFPPNormalizer IsNormalizedWholePlaneGFF
  IsHeatSmoothing rescaledLFPP LSCMetric LSCTendsto LSCTendstoInProbability EuclideanAnnulus acrossDist aroundDist
  scaleTranslateDist Disconnects)
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn annAt closedAnn compareHolds)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)
open LQGMetric.Blueprint (AEEventIn fieldSigma0On fieldSigmaClosed0 annulus)
open SupercriticalConformalCovariance (xiCrit)

/-! ## §0 The setting -/

/-- The LFPP-limit property of a strong LQG metric, verbatim the second conjunct of the sealed
`SupercriticalLQGUniqueness.exists_strongLQGMetric_lfppLimit` ([1, Thms 1.3, 1.8]; paper (i)). -/
def IsLFPPLimitAll (ξ : Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric) : Prop :=
  ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusBddCont h P →
    ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
      LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
        (fun ω => (D (h ω)).toLSCFun.1)

/-- The data fixed in §1 of the paper: ξ > 0, the exponent `Q` ((1.5) of [1]), the median normalizer `𝔞 = m`, and the
strong LQG metric `D` that is the LFPP limit. Inhabited for every `ξ > 0` by the sealed `existsUnique_isLFPPExponent`,
`existsUnique_isLFPPNormalizer` and `exists_strongLQGMetric_lfppLimit` (packet ASM proves `exists_setup`). Every shape below
is stated for an arbitrary `S : Setup`, i.e. for every `ξ > 0` (S1 N1, SB1 item 6, SB2 §1.2: no step uses `ξ > ξ_crit`). -/
structure Setup where
  ξ : Set.Ioi (0 : ℝ)
  Q : ℝ
  hQ : IsLFPPExponent ξ Q
  m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)
  hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)
  D : DistC → LSCMetric
  hD : IsStrongLQGMetric ξ Q D
  hlim : IsLFPPLimitAll ξ D

/-- The version hypotheses of the frozen surface v2 (ruling P6): continuous heat versions `X ε` of `h*_ε`, a.s. jointly
continuous in `(ε, z)`. Satisfiable (`exists_jointHeatVersion`); unique a.s. for all ε at once
(`ae_eq_of_jointHeatVersions`, T0). -/
def IsJointHeatVersion {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)) : Prop :=
  (∀ ε, IsHeatSmoothing P h ε (X ε)) ∧ ∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2

/-! ## §1 Objects -/

/-- `X̂_ε = 𝔞_ε⁻¹ D̂^ε_h`: LFPP of the localized field `ĥ_ε` (cutoff radius `ε log ε⁻¹`, [2, §2.3] with `q = 1`; paper
§2.1, SB1 §2.3). -/
def locMetric (S : Setup) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (g : DistC) : LSCMetric :=
  SupercriticalLQGUniqueness.B2.Polylog.plLocMetric (S.ξ : ℝ) 1 S.m ε hε g

/-- `H_{δ,L}`: the normalized localized heat field with cutoff radius `δL` (paper (2.3)); the PL field with exponent
`log L / log log δ⁻¹`, whose radius is exactly `δL` when `1 < log δ⁻¹ ≤ L` (`Field.plRad_uniform_eq`). Every shape uses it
only in that range. -/
def locFieldC (δ L : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (g : DistC) : C(ℂ, ℝ) :=
  SupercriticalLQGUniqueness.B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ g

/-- `Y_{δ,L}`: LFPP of `H_{δ,L}` divided by `𝔞_δ` (paper §3.2, before Lemma 3.5). The same term as P32's
`Local.locMetric (S.ξ : ℝ) S.m δ L hδ g`; unfolds to `B2.Median.lfppMetric (S.ξ : ℝ) (S.m ⟨δ, _⟩) (locFieldC δ L hδ g)`. -/
def locMetricY (S : Setup) (δ L : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (g : DistC) : LSCMetric :=
  SupercriticalLQGUniqueness.B2.Polylog.plLocMetric (S.ξ : ℝ) (Field.uniformLocalizationExponent δ L) S.m δ hδ g

/-- `X_ε = 𝔞_ε⁻¹ D^ε` for the continuous field `φ` (in use `φ = X ε ω`); pointwise equal to `rescaledLFPP`
(`B2.Median.lfppMetric_toLSCFun`). -/
def lfppM (S : Setup) (ε : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) : LSCMetric :=
  SupercriticalLQGUniqueness.B2.Median.lfppMetric (S.ξ : ℝ) (S.m ε) φ

/-- `κ_ε(r) = r 𝔞_{ε/r} / (r^{ξQ} 𝔞_ε)` (paper (2.5)): D6's `Compare.kappa` for the setup. -/
abbrev kappaS (S : Setup) (ε r : Set.Ioi (0 : ℝ)) : ℝ :=
  SupercriticalLFPPAS.Compare.kappa (S.ξ : ℝ) S.Q S.m ε r

/-- `h^{z,r} = h(z + r·) − h_r(z)` (paper (1.3)). -/
def recentred (r : Set.Ioi (0 : ℝ)) (z : ℂ) (g : DistC) : DistC :=
  addConst (scaleTranslateDist r z g) (-circleAvg g r z)

/-- `V = {1/2 ≤ |z| ≤ 3}` of Lemma 3.2 (the same body as P32's `Local.srcV`). -/
def srcV : Set ℂ := {z | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3}
/-- `U = {1/8 ≤ |z| ≤ 16}` of Lemma 3.2 (the same body as P32's `Local.tgtU`). -/
def tgtU : Set ℂ := {z | 1 / 8 ≤ ‖z‖ ∧ ‖z‖ ≤ 16}

/-- The radius `B^j`, `B = Iteration.annulusBase = 4096`, as a positive real (the radii of
`Iteration.radiusSet`; exponents `Iteration.radiusExponents ε s t`, i.e. `ε^t < B^j < ε^s`). -/
def bandRad (j : ℤ) : Set.Ioi (0 : ℝ) :=
  ⟨SupercriticalLFPPAS.Iteration.annulusBase ^ j,
    zpow_pos (show (0 : ℝ) < SupercriticalLFPPAS.Iteration.annulusBase by
      norm_num [SupercriticalLFPPAS.Iteration.annulusBase]) j⟩

/-! ## §2 Field estimates (Lemma 2.1; producer: the field adapters packet FA on top of D5/D5c1) -/

/-- (2.1) for a jointly continuous version: a.s., for every compact `K`, `sup_K |h*_ε − ĥ_ε| → 0` (SB1 item 14). -/
def LocApproxStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), IsJointHeatVersion P h X →
      ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1, ∀ z ∈ K,
          |X ⟨ε, hε.1⟩ ω z - SupercriticalLQGUniqueness.B2.Polylog.plMollify 1 ε hε (h ω) z| ≤ η

/-- (2.2), two-point form: for every `a > 0`, a.s., for every compact `K`,
`sup_{ε,δ ∈ [(n+1)^{-a}, n^{-a}]} sup_K |h*_ε − h*_δ| → 0` (SB1 A6: explicit rate `2aC_K(2 + a log(n+1))/n`). -/
def MeshOscStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), IsJointHeatVersion P h X →
      ∀ a : ℝ, 0 < a → ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
        ∀ ε δ : Set.Ioi (0 : ℝ), ((n : ℝ) + 1) ^ (-a) ≤ (ε : ℝ) → (ε : ℝ) ≤ (n : ℝ) ^ (-a) →
          ((n : ℝ) + 1) ^ (-a) ≤ (δ : ℝ) → (δ : ℝ) ≤ (n : ℝ) ^ (-a) → ∀ z ∈ K, |X ε ω z - X δ ω z| ≤ η

/-- (2.3), in the form consumed (convergence in outer probability, uniformly in `L ≥ log δ⁻¹`): for every compact `K`
and `σ > 0`, the outer probability that some `δ < δ₁` and some `L ≥ log δ⁻¹` give `sup_K |H_{δ,L} − h*_δ| > σ` tends to
`0` as `δ₁ ↓ 0`. Implied by the a.s. bound `sup_K |H_{δ,L} − h*_δ| ≤ C_K (8 + 4 log δ⁻¹) e^{−(log δ⁻¹)²/4}` (SB1 A6)
together with a measurable (or a.s. finite and dominated by a measurable) `C_K`. -/
def UnifLocStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), IsJointHeatVersion P h X →
      ∀ K : Set ℂ, IsCompact K → ∀ σ : ℝ, 0 < σ →
        Tendsto (fun δ₁ : ℝ => P {ω | ∃ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), δ < δ₁ ∧ ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧
            ∃ z ∈ K, σ < |locFieldC δ L hδ (h ω) z - X ⟨δ, hδ.1⟩ ω z|}) (𝓝[>] 0) (𝓝 0)

/-! ## §3 Scaling and comparison adapters -/

/-- (1.3): `h^{z,r}` is again a normalized whole-plane GFF, and a.s. `D_h(z + r·, z + r·) = r^{ξQ} e^{ξ h_r(z)} D_{h^{z,r}}`
for fixed deterministic `r, z` (SB1 A3: Axiom IV plus Weyl scaling by a random constant). -/
def ScalingDStmt (S : Setup) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ (r : Set.Ioi (0 : ℝ)) (z : ℂ),
      IsNormalizedWholePlaneGFF (fun ω => recentred r z (h ω)) P ∧
      ∀ᵐ ω ∂P, ∀ u v : ℂ, S.D (h ω) (z + (r : ℝ) • u, z + (r : ℝ) • v) =
        ENNReal.ofReal ((r : ℝ) ^ ((S.ξ : ℝ) * S.Q) * Real.exp ((S.ξ : ℝ) * circleAvg (h ω) r z)) *
          S.D (recentred r z (h ω)) (u, v)

/-- (2.4), deterministic, for every distribution `g` and every real `c` (SB1 A7, SB2 D3 "Scaling"): (i) `X̂_ε = Y_{ε,log ε⁻¹}`;
(ii) `H_{δ,L}[g](z + s·) = H_{δ/s,L}[g(z + s·) − c] + c`; (iii) `Y_{δ,L}[g](z + s·, z + s·) =
(s 𝔞_{δ/s}/𝔞_δ) e^{ξc} Y_{δ/s,L}[g(z + s·) − c]`. With `δ = ε`, `s = r`, `L = log ε⁻¹`, `c = h_r(z)`: (2.4) and the factor
`κ_ε(r) r^{ξQ} e^{ξh_r(z)}`. -/
def DilationStmt (S : Setup) : Prop :=
  (∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), 1 < Real.log ε⁻¹ → ∀ g : DistC,
      locMetric S ε hε g = locMetricY S ε (Real.log ε⁻¹) hε g) ∧
  ∀ (δ L : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (s : Set.Ioi (0 : ℝ)) (hδs : δ / s ∈ Ioo (0 : ℝ) 1),
    1 < Real.log δ⁻¹ → Real.log δ⁻¹ ≤ L → 1 < Real.log (δ / s)⁻¹ → Real.log (δ / s)⁻¹ ≤ L →
    ∀ (z : ℂ) (c : ℝ) (g : DistC),
      (∀ u : ℂ, locFieldC δ L hδ g (z + (s : ℝ) • u) =
        locFieldC (δ / s) L hδs (addConst (scaleTranslateDist s z g) (-c)) u + c) ∧
      ∀ u v : ℂ, locMetricY S δ L hδ g (z + (s : ℝ) • u, z + (s : ℝ) • v) =
        ENNReal.ofReal ((s : ℝ) * (S.m ⟨δ / s, hδs.1⟩ : ℝ) / (S.m ⟨δ, hδ.1⟩ : ℝ) * Real.exp ((S.ξ : ℝ) * c)) *
          locMetricY S (δ / s) L hδs (addConst (scaleTranslateDist s z g) (-c)) (u, v)

/-- (2.6) ([2, Lemma 3.7] with `𝔠_r = r^{ξQ}`, SB1 A8; producer D6): `C_ζ⁻¹ ≤ κ_ε(r) ≤ C_ζ` for `100ε^{1−ζ} ≤ r ≤ 1`,
`ε ≤ ε₀`. -/
def KappaBoundsStmt (S : Setup) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ C : ℝ, 1 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε r : Set.Ioi (0 : ℝ), (ε : ℝ) ≤ ε₀ →
    100 * (ε : ℝ) ^ (1 - ζ) ≤ r → (r : ℝ) ≤ 1 → C⁻¹ ≤ kappaS S ε r ∧ kappaS S ε r ≤ C

/-- (2.7)–(2.8) ([2, Prop 3.6] at `q = 1`, SB1 A9; producer D6): for each `ζ` a constant `C₀` independent of `U`; for
every bounded connected open `U` a polynomial failure bound for the two-sided comparison `compareHolds` (internal set
distances in `B_ρ(U)` between `ρ`-balls, `ρ = ε^{1−ζ}`). -/
def LocCompareStmt (S : Setup) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
    ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P → ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
        P {ω | ¬ compareHolds (locMetric S ε hε (h ω)) (S.D (h ω)) (ε ^ (1 - ζ)) U C₀} ≤
          ENNReal.ofReal (c₀ * ε ^ p₀)

/-! ## §4 Confinement (Lemma 2.2, (2.9)) and LFPP geodesics -/

/-- Lemma 2.2 in its measurable form (SB1 item 20, A10): for compact `K` and `M`, the probability that the localized or
ordinary normalized escape distance from `K` to `∂B_R(0)` is at most `M` tends to `0` as first `ε → 0`, then `R → ∞`. -/
def ConfinementStmt (S : Setup) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
      ∀ K : Set ℂ, IsCompact K → ∀ M η : ℝ, 0 < η → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1,
          P {ω | setDist (locMetric S ε hε (h ω)) K (sphere 0 R) ≤ ENNReal.ofReal M} ≤ ENNReal.ofReal η ∧
          P {ω | setDist (lfppM S ⟨ε, hε.1⟩ (X ⟨ε, hε.1⟩ ω)) K (sphere 0 R) ≤ ENNReal.ofReal M} ≤
            ENNReal.ofReal η

/-- (2.9), multiplicative form (equivalent to convergence in probability since `0 < D(O,O′) < ∞` a.s.; SB1 A10): for
disjoint positive-radius rational circles, `X̂_ε(O,O′)/D(O,O′) → 1` in outer probability. -/
def LocCircleStmt (S : Setup) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ (q₁ q₂ : ℚ × ℚ) (r₁ r₂ : ℚ), 0 < r₁ → 0 < r₂ →
      Disjoint (SupercriticalLFPPAS.rationalCircle q₁ r₁) (SupercriticalLFPPAS.rationalCircle q₂ r₂) →
      ∀ θ : ℝ, 0 < θ →
        Tendsto (fun ε : ℝ => P {ω | ∃ hε : ε ∈ Ioo (0 : ℝ) 1,
            ¬ (setDist (locMetric S ε hε (h ω)) (SupercriticalLFPPAS.rationalCircle q₁ r₁)
                  (SupercriticalLFPPAS.rationalCircle q₂ r₂) ≤
                ENNReal.ofReal (Real.exp θ) * setDist (S.D (h ω)) (SupercriticalLFPPAS.rationalCircle q₁ r₁)
                  (SupercriticalLFPPAS.rationalCircle q₂ r₂) ∧
              setDist (S.D (h ω)) (SupercriticalLFPPAS.rationalCircle q₁ r₁)
                  (SupercriticalLFPPAS.rationalCircle q₂ r₂) ≤
                ENNReal.ofReal (Real.exp θ) * setDist (locMetric S ε hε (h ω))
                  (SupercriticalLFPPAS.rationalCircle q₁ r₁) (SupercriticalLFPPAS.rationalCircle q₂ r₂))})
          (𝓝[>] 0) (𝓝 0)

/-- A unit-speed `d`-geodesic `P : [0, T] → ℂ`, Euclidean-continuous, with image in `B_R(0)` (SB2 D6 "Data"). -/
def IsGeodIn (d : LSCMetric) (P : ℝ → ℂ) (T R : ℝ) : Prop :=
  LQGMetric.MetricGeometry.IsGeodesicCurve (d.pt ∘ P) 0 T ∧ HasUnitSpeedOn (d.pt ∘ P) (Icc 0 T) ∧
    ContinuousOn P (Icc 0 T) ∧ ∀ t ∈ Icc 0 T, P t ∈ ball (0 : ℂ) R

/-- Deterministic geodesic existence for LFPP of a continuous field (SB1 item 22, SB2 D9 step 3): if `X(z,w)` is below the
distance from `z` to `∂B_R(0)` and `|z| < R`, a unit-speed `X`-geodesic from `z` to `w` exists inside `B_R(0)`
(Arzelà–Ascoli on `B̄_R`; continuity of the field suffices). -/
def LFPPGeodesicStmt : Prop :=
  ∀ (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (z w : ℂ) (R : ℝ), ‖z‖ < R →
    SupercriticalLQGUniqueness.B2.Median.lfppMetric ξ a φ (z, w) <
      setDist (SupercriticalLQGUniqueness.B2.Median.lfppMetric ξ a φ) {z} (sphere 0 R) →
    ∃ (P : ℝ → ℂ) (T : ℝ), P 0 = z ∧ P T = w ∧ IsGeodIn (SupercriticalLQGUniqueness.B2.Median.lfppMetric ξ a φ) P T R

/-! ## §5 Lemma 3.2, Remark 3.3, Lemma 3.5, annular tightness -/

/-- One direction of (3.1)–(3.2): for `|u| = 1`, `|v| = 2` with `S(u,v;V) ≤ M`, `T(B_η(u), B_η(v); U) ≤ S(u,v;V) + ν`. -/
def OneWayCompare (S T : LSCMetric) (η ν M : ℝ) : Prop :=
  ∀ u v : srcV, ‖(u : ℂ)‖ = 1 → ‖(v : ℂ)‖ = 2 → S.internal srcV (u, v) ≤ ENNReal.ofReal M →
    T.internalSetDist tgtU {x | (x : ℂ) ∈ ball (u : ℂ) η} {x | (x : ℂ) ∈ ball (v : ℂ) η} ≤
      S.internal srcV (u, v) + ENNReal.ofReal ν

/-- The event of Lemma 3.2 (both directions). -/
def Lemma32Event (S T : LSCMetric) (η ν M : ℝ) : Prop :=
  OneWayCompare S T η ν M ∧ OneWayCompare T S η ν M

/-- The event of Lemma 3.2 with the additive error and the cutoff in units `t = e^{ξ h_1(0)}` (SB1 A12.9); for a
normalized field `t = 1` a.s. -/
def Lemma32EventU (S T : LSCMetric) (η ν M t : ℝ) : Prop := Lemma32Event S T η (ν * t) (M * t)

/-- Lemma 3.2, localized version, uniform in `L ≥ log δ⁻¹` on one event (SB1 items 25–26, A12.8), with the threshold
uniform over normalized fields (law invariance). -/
def Lemma32LocStmt (S : Setup) : Prop :=
  ∀ M η ν : ℝ, 0 < η → 0 < ν → ∀ ϑ : ℝ, 0 < ϑ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), δ < δ₀ →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
        P {ω | ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧ ¬ Lemma32Event (S.D (h ω)) (locMetricY S δ L hδ (h ω)) η ν M} ≤
          ENNReal.ofReal ϑ

/-- Remark 3.3 (SB1 A13), measurability part: the ordinary and localized Lemma 3.2 events are null-measurable, and the
field-level localized failure set is universally measurable (for the law transfer). -/
def Lemma32MeasStmt (S : Setup) : Prop :=
  ∀ M η ν : ℝ,
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P → ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
        ∀ δ : Set.Ioi (0 : ℝ),
          NullMeasurableSet {ω | Lemma32Event (S.D (h ω)) (lfppM S δ (X δ ω)) η ν M} P) ∧
    ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), LQGMetric.UMeasurableSet
      {g : DistC | ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧ ¬ Lemma32Event (S.D g) (locMetricY S δ L hδ g) η ν M}

/-- Remark 3.3 (SB1 A12.9, A13), locality part: for `δL < 1/16`, the unit-adjusted localized Lemma 3.2 event is a.s.
an event of `h|_{A_{1/16,32}(0)}` modulo additive constants. -/
def Lemma32LocalityStmt (S : Setup) : Prop :=
  ∀ M η ν : ℝ, 0 < η → η < 1 / 10 →
    ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (L : ℝ), 1 < Real.log δ⁻¹ → Real.log δ⁻¹ ≤ L → δ * L < 1 / 16 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
        AEEventIn P (fieldSigma0On h (annulus 0 (1 / 16) 32 : Set ℂ))
          {ω | Lemma32EventU (S.D (h ω)) (locMetricY S δ L hδ (h ω)) η ν M
            (Real.exp ((S.ξ : ℝ) * circleAvg (h ω) 1 0))}

/-- The separating-path conclusion of Lemma 3.5 at scale `r` (SB2 D3, D6(c)): for every Euclidean-continuous
`d`-geodesic segment `P|[α,β]` through `p ∈ Kp` whose endpoints lie outside `B_{2√η r}(p)`, a `d'`-curve `σ` inside
`B_{2√η r}(p)`, avoiding `p`, whose complement component containing `p` is bounded and contains `B_{ηr}(p)`, with
`len_{d'}(σ) ≤ b · len_d(P|[α,β])`. -/
def SurroundProp (d d' : LSCMetric) (Kp : Set ℂ) (r η b : ℝ) : Prop :=
  ∀ (P : ℝ → ℂ) (α β : ℝ), LQGMetric.MetricGeometry.IsGeodesicCurve (d.pt ∘ P) α β →
    ContinuousOn P (Icc α β) → ∀ p ∈ Kp, p ∈ P '' Icc α β →
      2 * Real.sqrt η * r ≤ dist (P α) p → 2 * Real.sqrt η * r ≤ dist (P β) p →
      ∃ (σ : ℝ → ℂ) (a' b' : ℝ), d'.IsCurve σ a' b' ∧ ContinuousOn σ (Icc a' b') ∧
        σ '' Icc a' b' ⊆ ball p (2 * Real.sqrt η * r) ∧ p ∉ σ '' Icc a' b' ∧
        ball p (η * r) ⊆ connectedComponentIn (σ '' Icc a' b')ᶜ p ∧
        Bornology.IsBounded (connectedComponentIn (σ '' Icc a' b')ᶜ p) ∧
        d'.len σ a' b' ≤ ENNReal.ofReal b * d.len P α β

/-- Lemma 3.5 (canonical form, SB2 item 5, D3), with constants uniform over normalized fields: for compact
`K ⊂ A_{3/4,5/2}(0)` and `q > 0`, an event `F` local in `A_{1/2,3}(0)` modulo constants, of probability `≥ 1 − Cη^q`, on
which (a.s.) the separating-path conclusion holds in both directions `(D, Y_{δ,L})`, `(Y_{δ,L}, D)` with bound `Cη^θ`. -/
def Lemma35Stmt (S : Setup) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ (annulus 0 (3 / 4) (5 / 2) : Set ℂ) → ∀ q : ℝ, 0 < q →
    ∃ θ C η₀ : ℝ, 0 < θ ∧ 0 < C ∧ 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ δ₀ ℓ₀ : ℝ, 0 < δ₀ ∧ 0 < ℓ₀ ∧ ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (L : ℝ), δ < δ₀ →
        Real.log δ⁻¹ ≤ L → δ * L < ℓ₀ →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
          IsNormalizedWholePlaneGFF h P →
            ∃ F : Set Ω, AEEventIn P (fieldSigma0On h (annulus 0 (1 / 2) 3 : Set ℂ)) F ∧
              ENNReal.ofReal (1 - C * η ^ q) ≤ P F ∧
              ∀ᵐ ω ∂P, ω ∈ F →
                SurroundProp (S.D (h ω)) (locMetricY S δ L hδ (h ω)) K 1 η (C * η ^ θ) ∧
                SurroundProp (locMetricY S δ L hδ (h ω)) (S.D (h ω)) K 1 η (C * η ^ θ)

/-- Annular tightness (paper (iv); [2, Lemma 3.1], [6, Prop 4.1], `B2.Polylog.PLHeatAnnulusTight`, V′; SB2 M3/M4) for `D`
and for `Y_{δ,L}` uniformly in small `δ`, `L ≥ log δ⁻¹`, and uniformly over normalized fields: lower tail of the across
distance and upper tail of the around distance, for every Euclidean annulus. -/
def AnnTightStmt (S : Setup) : Prop :=
  ∀ A : EuclideanAnnulus, ∀ ϑ : ℝ, 0 < ϑ → ∃ Mt δ₀ : ℝ, 0 < Mt ∧ 0 < δ₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
        (P {ω | acrossDist (S.D (h ω)) A < ENNReal.ofReal Mt⁻¹} ≤ ENNReal.ofReal ϑ ∧
          P {ω | ENNReal.ofReal Mt < aroundDist (S.D (h ω)) A} ≤ ENNReal.ofReal ϑ) ∧
        ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), δ < δ₀ → ∀ L : ℝ, Real.log δ⁻¹ ≤ L →
          P {ω | acrossDist (locMetricY S δ L hδ (h ω)) A < ENNReal.ofReal Mt⁻¹} ≤ ENNReal.ofReal ϑ ∧
          P {ω | ENNReal.ofReal Mt < aroundDist (locMetricY S δ L hδ (h ω)) A} ≤ ENNReal.ofReal ϑ

/-! ## §6 Good root scales (§3.3) -/

/-- The deterministic content of a good root scale at centre `c`, radius `r` (§3.3 consequences; SB2 D4 (G1)–(G3), M4),
for source `d`, target `d'`, target scaling bound `K`. Geodesic-independent and covariant under `u ↦ c + r u` (with `K`
multiplied by the ratio of the two metric factors). (a) `d(around A_{7r,8r}(c)) ≤ A · d(across Ā_{r,2r}(c))`; (b) for
`|u − c| = r`, `|v − c| = 2r` with `d(u,v; V_r(c)) ≤ d(around A_{7r,8r}(c))`, `d'(B_{ηr/2}(u), B_{ηr/2}(v); U_r(c)) ≤
(1 + d₀/10) K d(u,v; V_r(c))` (`V_r(c) = Ā_{r/2,3r}(c)`, `U_r(c) = Ā_{r/8,16r}(c)`); (c) Lemma 3.5's separating paths at
the points of `∂B_r(c) ∪ ∂B_{2r}(c)` with bound `(d₀/10) K`. -/
structure GoodScale (d d' : LSCMetric) (c : ℂ) (r : ℝ) (hr : 0 < r) (η d₀ A K : ℝ) : Prop where
  ratio : aroundDist d (annAt c (7 * r) (8 * r) (by positivity) (by linarith)) ≤
    ENNReal.ofReal A * acrossIn d c r (2 * r)
  cross : ∀ u v : closedAnn c (r / 2) (3 * r), dist (u : ℂ) c = r → dist (v : ℂ) c = 2 * r →
    d.internal (closedAnn c (r / 2) (3 * r)) (u, v) ≤
      aroundDist d (annAt c (7 * r) (8 * r) (by positivity) (by linarith)) →
    d'.internalSetDist (closedAnn c (r / 8) (16 * r)) {x | (x : ℂ) ∈ ball (u : ℂ) (η * r / 2)}
        {x | (x : ℂ) ∈ ball (v : ℂ) (η * r / 2)} ≤
      ENNReal.ofReal ((1 + d₀ / 10) * K) * d.internal (closedAnn c (r / 2) (3 * r)) (u, v)
  surround : SurroundProp d d' (sphere c r ∪ sphere c (2 * r)) r η (d₀ / 10 * K)

/-- §3.3 at the unit scale (canonical units; SB2 D4 items 1–2): `p₀` first, then `A` (hence `λ = 1/(5A)`) independent of
`d₀`, then `η` with `2√η < 1/10`, then thresholds for `(δ, L)`, all uniform over normalized fields; an event `G`, local in
`A_{1/16,32}(0)` modulo constants, with `P(G) ≥ p₀`, on which (a.s.) both directions are good scales at `(0, 1)` with
`K = 1`. -/
def UnitGoodStmt (S : Setup) : Prop :=
  ∀ p₀ : ℝ, p₀ < 1 → ∃ A : ℝ, 1 ≤ A ∧ ∀ d₀ : ℝ, 0 < d₀ → ∃ η : ℝ, 0 < η ∧ 2 * Real.sqrt η < 1 / 10 ∧
    ∃ δ₀ ℓ₀ : ℝ, 0 < δ₀ ∧ 0 < ℓ₀ ∧ ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (L : ℝ), δ < δ₀ →
      Real.log δ⁻¹ ≤ L → δ * L < ℓ₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
          ∃ G : Set Ω, AEEventIn P (fieldSigma0On h (annulus 0 (1 / 16) 32 : Set ℂ)) G ∧
            ENNReal.ofReal p₀ ≤ P G ∧
            ∀ᵐ ω ∂P, ω ∈ G →
              GoodScale (S.D (h ω)) (locMetricY S δ L hδ (h ω)) 0 1 one_pos η d₀ A 1 ∧
              GoodScale (locMetricY S δ L hδ (h ω)) (S.D (h ω)) 0 1 one_pos η d₀ A 1

/-- §3.3 at centre `z` and radius `r` (SB2 D4 item 3, M5): the events `E_{ε,r}(z)`, in every band `ε^t ≤ r ≤ ε^s` and for
small `ε`, are measurable for the closed-annulus σ-algebra of `h − h_r(z)` on `Ā_{r/16,32r}(z)` modulo constants (the
form of `Concentration.paper_annulus_concentration`) with probability `≥ p₀`; on `E_{ε,r}(z)` (a.s.) `(D, X̂_ε)` is a good
scale with `K = κ_ε(r)` and `(X̂_ε, D)` with `K = κ_ε(r)⁻¹`. -/
def RootEventStmt (S : Setup) : Prop :=
  ∀ p₀ : ℝ, p₀ < 1 → ∃ A : ℝ, 1 ≤ A ∧ ∀ d₀ : ℝ, 0 < d₀ → ∃ η : ℝ, 0 < η ∧ 2 * Real.sqrt η < 1 / 10 ∧
    ∀ s t : ℝ, 0 < s → s < t → t < 1 → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P → ∃ E : ℝ → ℝ → ℂ → Set Ω,
        (∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∀ r : ℝ, ε ^ t ≤ r → r ≤ ε ^ s → ∀ z : ℂ,
            MeasurableSet[fieldSigmaClosed0 (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
              {x | r / 16 ≤ dist x z ∧ dist x z ≤ 32 * r}] (E ε r z) ∧
            ENNReal.ofReal p₀ ≤ P (E ε r z)) ∧
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (r : ℝ) (hr : 0 < r) (z : ℂ), ∀ᵐ ω ∂P, ω ∈ E ε r z →
          GoodScale (S.D (h ω)) (locMetric S ε hε (h ω)) z r hr η d₀ A (kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩) ∧
          GoodScale (locMetric S ε hε (h ω)) (S.D (h ω)) z r hr η d₀ A (kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩)⁻¹

/-! ## §7 Contraction (Lemma 4.1, §4.2) -/

/-- The deterministic content of a good disk relative to one source geodesic `P` on `[0, L]`, target costs internal to
`W` (SB2 D6 (a)–(c), verbatim SB2 (c) `GoodDiskIn`). -/
structure GoodDiskIn (d d' : LSCMetric) (W : Set ℂ) (P : ℝ → ℂ) (L η d₀ A Kf : ℝ) (c : ℂ) (r : ℝ) : Prop where
  pos : 0 < r
  ratio : aroundDist d (annAt c (7 * r) (8 * r) (by positivity) (by linarith)) ≤
    ENNReal.ofReal A * acrossIn d c r (2 * r)
  cross : ∀ s t, 0 ≤ s → s ≤ t → t ≤ L → dist (P s) c = r → dist (P t) c = 2 * r →
    (∀ u ∈ Icc s t, P u ∈ closedAnn c r (2 * r)) →
    ENNReal.ofReal (t - s) ≤ aroundDist d (annAt c (7 * r) (8 * r) (by positivity) (by linarith)) →
    d'.internalSetDist W {y | (y : ℂ) ∈ ball (P s) (η * r / 2)}
      {y | (y : ℂ) ∈ ball (P t) (η * r / 2)} ≤ ENNReal.ofReal ((1 + d₀ / 10) * Kf * (t - s))
  surround : ∀ α β p, 0 ≤ α → α ≤ β → β ≤ L → p ∈ P '' Icc α β →
    (dist p c = r ∨ dist p c = 2 * r) →
    2 * Real.sqrt η * r ≤ dist (P α) p → 2 * Real.sqrt η * r ≤ dist (P β) p →
    ∃ (σ : ℝ → ℂ) (a' b' : ℝ), d'.IsCurve σ a' b' ∧ ContinuousOn σ (Icc a' b') ∧
      σ '' Icc a' b' ⊆ ball p (r / 10) ∧ σ '' Icc a' b' ⊆ W ∧ p ∉ σ '' Icc a' b' ∧
      ball p (η * r) ⊆ connectedComponentIn (σ '' Icc a' b')ᶜ p ∧
      Bornology.IsBounded (connectedComponentIn (σ '' Icc a' b')ᶜ p) ∧
      d'.len σ a' b' ≤ ENNReal.ofReal (d₀ / 10 * Kf * (β - α))

/-- Lemma 4.1′ (SB2 D6 and (c) `covering_joining_in`, internal form, with the convexity/containment hypotheses SB2 lists
for the immediate case): every unit-speed source geodesic in `B_R(0)` all of whose points have a good disk within
`r_min/10`, with a prior comparison `(C₀, ρ_old < η r_min/4)` on all subsegments, satisfies
`d'(B_{513 r_max}(z), B_{513 r_max}(w); W) ≤ F(C₀, K) L`, `λ = 1/(5A)`. -/
def Lemma41Stmt : Prop :=
  ∀ (d d' : LSCMetric) (W : Set ℂ) (R : ℝ), Bornology.IsBounded W → Convex ℝ W → ball (0 : ℂ) (R + 1) ⊆ W →
    ∀ (P : ℝ → ℂ) (L : ℝ), IsGeodIn d P L R →
    ∀ (η d₀ A Kf C₀ rmin rmax ρold : ℝ), 0 < η → 2 * Real.sqrt η < 1 / 10 → 0 ≤ d₀ → 1 ≤ A → 0 ≤ Kf → 0 ≤ C₀ →
      0 < rmin → rmin ≤ rmax → 513 * rmax ≤ 1 → 0 < ρold → ρold < η * rmin / 4 →
      (∀ t ∈ Icc 0 L, ∃ c r, dist c (P t) < rmin / 10 ∧ r ∈ Icc rmin rmax ∧
        GoodDiskIn d d' W P L η d₀ A Kf c r) →
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ L →
        d'.internalSetDist W {y | (y : ℂ) ∈ ball (P s) ρold} {y | (y : ℂ) ∈ ball (P t) ρold} ≤
          ENNReal.ofReal (C₀ * (t - s))) →
      d'.internalSetDist W {y | (y : ℂ) ∈ ball (P 0) (513 * rmax)} {y | (y : ℂ) ∈ ball (P L) (513 * rmax)} ≤
        ENNReal.ofReal (SupercriticalLFPPAS.Iteration.contractionFactor C₀ Kf (1 / (5 * A)) d₀ * L)

/-- A comparison with constant `C` and endpoint radius `ρ` for every subsegment of every unit-speed source geodesic in
`B_R(0)`, target costs internal to `W` (the "prior comparison" of Lemma 4.1 and §4.2; (5.1)–(5.2) in internal form). -/
def CompIn (d d' : LSCMetric) (W : Set ℂ) (R C ρ : ℝ) : Prop :=
  ∀ (P : ℝ → ℂ) (T : ℝ), IsGeodIn d P T R → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
    d'.internalSetDist W {y | (y : ℂ) ∈ ball (P s) ρ} {y | (y : ℂ) ∈ ball (P t) ρ} ≤
      ENNReal.ofReal (C * (t - s))

/-- §4.2, one contraction step (SB2 D7): `λ ∈ (0,1]` fixed before `d₀` and the bands; for `0 < 4s ≤ t < t_old < 1`, `R`,
`C`, there are `β, c₁, ε₁` such that for `ε < ε₁`, every `S_ε ⊆ R_ε(s,t)` with `3#S_ε ≥ #R_ε(s,t)` and every `K` bounding
`κ_ε` (resp. `κ_ε⁻¹`) on `S_ε`, the outer probability that the comparison `(C, 513ε^{t_old})` holds but `(F(C,K), 513ε^s)`
fails is at most `c₁ε^β`, for `(D, X̂_ε)` (resp. `(X̂_ε, D)`), with `W = B_{R+2}(0)`. -/
def ContractionStmt (S : Setup) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ ∀ d₀ : ℝ, 0 < d₀ → ∀ R : ℝ, 1 ≤ R → ∀ s t told C : ℝ,
    0 < s → 4 * s ≤ t → t < told → told < 1 → 0 ≤ C →
    ∃ β c₁ ε₁ : ℝ, 0 < β ∧ 0 < c₁ ∧ 0 < ε₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₁ →
        ∀ Sε : Finset ℤ, Sε ⊆ SupercriticalLFPPAS.Iteration.radiusExponents ε s t →
          (SupercriticalLFPPAS.Iteration.radiusExponents ε s t).card ≤ 3 * Sε.card → ∀ K : ℝ, 0 ≤ K →
          ((∀ j ∈ Sε, kappaS S ⟨ε, hε.1⟩ (bandRad j) ≤ K) →
            P {ω | CompIn (S.D (h ω)) (locMetric S ε hε (h ω)) (ball 0 (R + 2)) R C (513 * ε ^ told) ∧
              ¬ CompIn (S.D (h ω)) (locMetric S ε hε (h ω)) (ball 0 (R + 2)) R
                (SupercriticalLFPPAS.Iteration.contractionFactor C K lam d₀) (513 * ε ^ s)} ≤ ENNReal.ofReal (c₁ * ε ^ β)) ∧
          ((∀ j ∈ Sε, (kappaS S ⟨ε, hε.1⟩ (bandRad j))⁻¹ ≤ K) →
            P {ω | CompIn (locMetric S ε hε (h ω)) (S.D (h ω)) (ball 0 (R + 2)) R C (513 * ε ^ told) ∧
              ¬ CompIn (locMetric S ε hε (h ω)) (S.D (h ω)) (ball 0 (R + 2)) R
                (SupercriticalLFPPAS.Iteration.contractionFactor C K lam d₀) (513 * ε ^ s)} ≤ ENNReal.ofReal (c₁ * ε ^ β))

/-! ## §8 Identification of the constant (Proposition 5.1) -/

/-- (5.6) and its q′ analogue in the form consumed by Proposition 5.1 (SB2 D9 steps 3–4): a comparison with a constant
`c < 1` and radii `ρ(ε) → 0` fails with outer probability bounded below, in both directions, for some `R`. -/
def NoContractStmt (S : Setup) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ c : ℝ, c < 1 → ∀ ρ : ℝ → ℝ, (∀ ε, 0 < ρ ε) →
      Tendsto ρ (𝓝[>] 0) (𝓝 0) → ∃ R θ : ℝ, 1 ≤ R ∧ 0 < θ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1,
        ENNReal.ofReal θ ≤ P {ω | ¬ CompIn (S.D (h ω)) (locMetric S ε hε (h ω)) (ball 0 (R + 2)) R c (ρ ε)} ∧
        ENNReal.ofReal θ ≤ P {ω | ¬ CompIn (locMetric S ε hε (h ω)) (S.D (h ω)) (ball 0 (R + 2)) R c (ρ ε)}

/-- Proposition 5.1 (internal form; SB2 D9): for `u > 0`, `R ≥ 1` there are `s, β > 0` with
`P(¬((5.1) ∧ (5.2))) = O(ε^β)`, radius `513 ε^s`, target costs internal to `B_{R+2}(0)` (internal ≥ whole-plane). -/
def Prop51Stmt (S : Setup) : Prop :=
  ∀ u R : ℝ, 0 < u → 1 ≤ R → ∃ s β c₁ ε₁ : ℝ, 0 < s ∧ 0 < β ∧ 0 < c₁ ∧ 0 < ε₁ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P → ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₁ →
        P {ω | ¬ (CompIn (S.D (h ω)) (locMetric S ε hε (h ω)) (ball 0 (R + 2)) R (1 + u) (513 * ε ^ s) ∧
          CompIn (locMetric S ε hε (h ω)) (S.D (h ω)) (ball 0 (R + 2)) R (1 + u) (513 * ε ^ s))} ≤
          ENNReal.ofReal (c₁ * ε ^ β)

/-! ## §9 Interpolation (Lemmas 6.1–6.2) and the theorem (§7) -/

/-- Lemma 6.1, corrected symmetric form (SB3 §5(a), SB2 M10): for `a > 0`, eventually in `n`, any two cutoffs in
`[(n+1)^{-a}, n^{-a}]` have `|log(𝔞_ε/𝔞_δ)| ≤ η`. -/
def NormalizerWindowStmt (S : Setup) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ ε δ : Set.Ioi (0 : ℝ),
    ((n : ℝ) + 1) ^ (-a) ≤ (ε : ℝ) → (ε : ℝ) ≤ (n : ℝ) ^ (-a) →
    ((n : ℝ) + 1) ^ (-a) ≤ (δ : ℝ) → (δ : ℝ) ≤ (n : ℝ) ^ (-a) →
      |Real.log ((S.m ε : ℝ) / (S.m δ : ℝ))| ≤ η

/-- Lemma 6.2 (SB2 D10), escape form: a.s., for every compact `K` and `M`, there are `R` with `K ⊆ B_R(0)` and `ε₀ > 0`
such that for every cutoff `ε < ε₀` the localized and ordinary normalized distances from `K` to `∂B_R(0)` exceed `M` (so
every such path of length `≤ M` starting in `K` stays in `B_R(0)`). -/
def Lemma62Stmt (S : Setup) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), IsJointHeatVersion P h X →
      ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → ∀ M : ℝ, ∃ R : ℝ, K ⊆ ball 0 R ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
          ENNReal.ofReal M < setDist (locMetric S ε hε (h ω)) K (sphere 0 R) ∧
          ENNReal.ofReal M < setDist (lfppM S ⟨ε, hε.1⟩ (X ⟨ε, hε.1⟩ ω)) K (sphere 0 R)

/-- §7, Theorem 1.1 for the strong metric `D` of the setup (every `ξ > 0`, every jointly continuous version). -/
def MainAeStmt (S : Setup) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), IsJointHeatVersion P h X →
      ∀ᵐ ω ∂P, ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        LSCTendsto (fun n => rescaledLFPP (S.ξ : ℝ) (S.m (ε n)) (X (ε n) ω)) (S.D (h ω)).toLSCFun.1

/-- The exact type of the frozen anchor `SupercriticalLFPPAS.lfpp_ae_lscTendsto` (v2, ruling P7), verbatim; the probe
checks `example : Lfpp_ae_lscTendstoStmt = type_of% @lfpp_ae_lscTendsto := rfl`. -/
def Lfpp_ae_lscTendstoStmt : Prop :=
    ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) →
      ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
          (∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2) →
        ∀ L : Ω → LSCMetric,
          LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
            (fun ω => (L ω).toLSCFun.1) →
          ∀ᵐ ω ∂P, ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
            LSCTendsto (fun n => rescaledLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω)) (L ω).toLSCFun.1

/-- The unfrozen all-ξ corollary (S1 N1; SCC precedent A23): the frozen statement without `xiCrit < ξ`. -/
def Lfpp_ae_lscTendstoAllXiStmt : Prop :=
    ∀ ξ : Set.Ioi (0 : ℝ),
      ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
          (∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2) →
        ∀ L : Ω → LSCMetric,
          LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
            (fun ω => (L ω).toLSCFun.1) →
          ∀ᵐ ω ∂P, ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
            LSCTendsto (fun n => rescaledLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω)) (L ω).toLSCFun.1

end SupercriticalLFPPAS.Core
