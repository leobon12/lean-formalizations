import HigherDimLFPPAS.Coarse.Lemma45
import HigherDimLFPPAS.Bridge.Internal
import HigherDimLFPPAS.Normalizer.Seed
import HigherDimLFPPAS.Frozen.Assumption11
import HigherDimLQGMetric.Sec10.Lemma101
import HigherDimLQGMetric.Events.ScaledEvent

/-!
# Lemma 2.7: localized coarse comparison with a polynomial rate, for signed seeds (packet C27; MA3 P11)

Paper §2.3, Lemma 2.7, in MA3's corrected form (S2; Details P11): for every `q ∈ (0,1)` and `β > 0` there are
`C ≥ 2` and `ε₀ > 0`, depending only on `(d, ξ, κ, D, q, β)` (not on `U`), such that for every `R' ≥ 0`, every
`U ⊆ B̄_{R'}(0)`, every normalized LGF `h` and every `ε ∈ (0, ε₀)`, outside an event of outer probability
`≤ (2R' + 7)^d ε^β`, for all `x, y ∈ U`:

* (2.11) `M_ε(B_{ε^q}(x), B_{ε^q}(y); B_{ε^q}(U)) ≤ C D(x, y; U)`;
* (2.12) `D(B_{ε^q}(x), B_{ε^q}(y); B_{ε^q}(U)) ≤ C M_ε(x, y; U)`,

with `M_ε = 𝔞_ε⁻¹ D̂^ε_h` the normalized LFPP metric of the localized field `ĥ*_ε = locField κ ε h`. The paper's
statement (`C_q`, `β_q` independent of `U`, probability `1 − O_U(ε^{β_q})`) is the case `β = 1`; `B_{ε^q}(U)` is
`Metric.thickening (ε ^ q) U`.

Forms:
* `c27_lemma27_fieldDist`: `M_ε` through the piecewise-`C¹` infima `fieldSetDistIn`/`fieldDistIn` (as the host's
  `ref1_lemma44`), any bounded `U`;
* `c27_lemma27`: `M_ε = 𝔞_ε⁻¹ · fieldLfppMetric ξ φ` (`ContMetric.smul`) for every continuous bundling `φ` of
  `locField κ ε h`, with the internal metrics `ContMetric.internal`/`setDistIn` (MA2 §4.1 items 1–2), `U` open and
  bounded; via the bridge of packet D5 (`Bridge.fieldSetDistIn_eq_setDistIn_open`, `fieldDistIn_eq_internal_open`);
* `c27_lemma27_assumption11`: the same from the frozen `Assumption11` (ruling L6), and `c27_lemma27_nonneg` for
  `κ ≥ 0` (`IsLFPPKernel`, MA3 §4.2: the signed route covers it).

The hypotheses of the internal lemmas are: `d ≥ 3`, `ξ > 0`, a signed seed, a strong assignment at an arbitrary `Q`
(sharp weak by `lemma101`), and (1.6) for one normalized field (transferred to the canonical space by N1's
`lfppConv_transfer`). Proof (MA3 P11): Lemma 4.5′ selects the deterministic radii `R^ε` with `C₅⁻¹ ≤ c_ε(r) ≤ C₅`
(at least half of `N^ε`), and Lemma 4.4′ with `ζ = 1 − q`, `m = C₅⁻¹`, `M = C₅` gives the comparisons with
`C = max(2, C₄ C₅)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Coarse

open HigherDimLQGMetric HigherDimLFPPAS.Signed
open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

/-- **Lemma 2.7**, piecewise-`C¹` form (MA3 P11; (1.6) on the canonical space, sharp weak `D`). -/
theorem c27_lemma27_fieldDist_of_weak (hd : 3 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 2 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ R' : ℝ, 0 ≤ R' → ∀ U : Set (Rd d),
      U ⊆ closedBall 0 R' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | ¬ ∀ x ∈ U, ∀ y ∈ U,
          ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * fieldSetDistIn ξ (locField κ ε (h ω))
              (thickening (ε ^ q) U) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
            ENNReal.ofReal C * (D (h ω)).internal U x y ∧
          setDistIn (D (h ω)) (thickening (ε ^ q) U) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
            ENNReal.ofReal C * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
              fieldDistIn ξ (locField κ ε (h ω)) U x y)} ≤
          ENNReal.ofReal ((2 * R' + 7) ^ d * ε ^ β) := by
  have hζ0 : 0 < 1 - q := by linarith
  have hζ1 : 1 - q < 1 := by linarith
  obtain ⟨C₅, hC₅, ε₅, hε₅, H45⟩ := c27_lemma45 hd hD hκ hconv hζ0 hζ1
  obtain ⟨C₄, hC₄, ε₄, hε₄, H44⟩ := c27_lemma44 hd hD hκ hconv hζ0 hζ1 hβ
  refine ⟨max 2 (C₄ * C₅), le_max_left _ _, min ε₄ ε₅, lt_min hε₄ hε₅, ?_⟩
  intro R' hR' U hU Ω _ P _ h hh ε hε
  have hq : 1 - (1 - q) = q := by ring
  have hcard := H45 ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  set R := (nIdx (1 - q) ε).filter fun k =>
    C₅⁻¹ ≤ l9bRatio κ ξ (fun r => r ^ (ξ * Q)) ε (dyad k) ∧
      l9bRatio κ ξ (fun r => r ^ (ξ * Q)) ε (dyad k) ≤ C₅ with hRdef
  have hC₅0 : 0 < C₅ := by linarith
  have hbound := H44 R' hR' U hU P h hh ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ R
    (Finset.filter_subset _ _) (by omega) C₅⁻¹ C₅ (inv_pos.2 hC₅0) hC₅0
    (fun k hk => (Finset.mem_filter.1 hk).2)
  simp only [hq, inv_inv] at hbound
  refine le_trans (measure_mono fun ω hω => ?_) hbound
  intro hgood
  apply hω
  intro x hx y hy
  obtain ⟨h1, h2⟩ := hgood x hx y hy
  have hC : ENNReal.ofReal (C₄ * C₅) ≤ ENNReal.ofReal (max 2 (C₄ * C₅)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  exact ⟨h1.trans (mul_le_mul_left hC _), h2.trans (mul_le_mul_left hC _)⟩

/-- (1.6) for one normalized field gives (1.6) on the canonical space `(DistRd d, normLGFLaw d)` (N1's transfer). -/
theorem c27_conv_canonical (hd : 2 ≤ d) {ξ Q : ℝ} {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {h₀ : Ω₀ → DistRd d}
    (hh₀ : IsNormalizedLGF h₀ P₀)
    (hconv : TendstoInProbLU P₀ (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h₀ ω)) (𝓝[>] 0)
      (fun ω => (D (h₀ ω)).1)) :
    TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1) := by
  have := l9b_normLGFLaw_prob hd
  exact Normalizer.lfppConv_transfer hd hκ hD.measurable hh₀ hconv (l9b_normLGFLaw_normalized hd)

/-- **Lemma 2.7**, piecewise-`C¹` form, from a strong assignment at any `Q` and (1.6) for one normalized field. -/
theorem c27_lemma27_fieldDist (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) {κ : Rd d → ℝ}
    (hκ : IsAdmissibleSeed κ) {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {h₀ : Ω₀ → DistRd d}
    (hh₀ : IsNormalizedLGF h₀ P₀)
    (hconv : TendstoInProbLU P₀ (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h₀ ω)) (𝓝[>] 0)
      (fun ω => (D (h₀ ω)).1))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 2 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ R' : ℝ, 0 ≤ R' → ∀ U : Set (Rd d),
      U ⊆ closedBall 0 R' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | ¬ ∀ x ∈ U, ∀ y ∈ U,
          ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * fieldSetDistIn ξ (locField κ ε (h ω))
              (thickening (ε ^ q) U) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
            ENNReal.ofReal C * (D (h ω)).internal U x y ∧
          setDistIn (D (h ω)) (thickening (ε ^ q) U) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
            ENNReal.ofReal C * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
              fieldDistIn ξ (locField κ ε (h ω)) U x y)} ≤
          ENNReal.ofReal ((2 * R' + 7) ^ d * ε ^ β) :=
  c27_lemma27_fieldDist_of_weak hd (lemma101 (by omega) hξ hD) hκ
    (c27_conv_canonical (by omega) hκ hD hh₀ hconv) hq0 hq1 hβ

/-- **Lemma 2.7** (MA3 P11; MA2 §4.1 conventions): `M_ε = 𝔞_ε⁻¹ · fieldLfppMetric ξ φ` for every continuous bundling
`φ` of `ĥ*_ε`, internal metrics and set distances of `ContMetric`s, `U` open and bounded. -/
theorem c27_lemma27 (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) {κ : Rd d → ℝ}
    (hκ : IsAdmissibleSeed κ) {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {h₀ : Ω₀ → DistRd d}
    (hh₀ : IsNormalizedLGF h₀ P₀)
    (hconv : TendstoInProbLU P₀ (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h₀ ω)) (𝓝[>] 0)
      (fun ω => (D (h₀ ω)).1))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 2 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ R' : ℝ, 0 ≤ R' → ∀ U : Set (Rd d), IsOpen U →
      U ⊆ closedBall 0 R' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | ¬ ∀ φ : C(Rd d, ℝ), ⇑φ = locField κ ε (h ω) → ∀ ha : 0 < (aEps κ ξ ε)⁻¹,
          ∀ x ∈ U, ∀ y ∈ U,
            setDistIn ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha) (thickening (ε ^ q) U)
                (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
              ENNReal.ofReal C * (D (h ω)).internal U x y ∧
            setDistIn (D (h ω)) (thickening (ε ^ q) U) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
              ENNReal.ofReal C * ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha).internal U x y} ≤
          ENNReal.ofReal ((2 * R' + 7) ^ d * ε ^ β) := by
  obtain ⟨C, hC, ε₀, hε₀, H⟩ := c27_lemma27_fieldDist hd hξ hκ hD hh₀ hconv hq0 hq1 hβ
  refine ⟨C, hC, ε₀, hε₀, fun R' hR' U hUo hU Ω _ P _ h hh ε hε => ?_⟩
  refine le_trans (measure_mono fun ω hω => ?_) (H R' hR' U hU P h hh ε hε)
  intro hgood
  apply hω
  intro φ hφ ha x hx y hy
  obtain ⟨h1, h2⟩ := hgood x hx y hy
  have hT : IsOpen (thickening (ε ^ q) U) := isOpen_thickening
  rw [← hφ, Bridge.fieldSetDistIn_eq_setDistIn_open ξ φ hT] at h1
  rw [← hφ, Bridge.fieldDistIn_eq_internal_open ξ φ hUo] at h2
  rw [setDistIn_smul, ContMetric.internal_smul]
  exact ⟨h1, h2⟩

/-- **Lemma 2.7** from the frozen `Assumption11` (ruling L6; `Q = Q(ξ) = distExp d ξ`). -/
theorem c27_lemma27_assumption11 (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {κ : Rd d → ℝ}
    (hκ : IsAdmissibleSeed κ) {D : DistRd d → ContMetric d}
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {h₀ : Ω₀ → DistRd d}
    (hh₀ : IsNormalizedLGF h₀ P₀) (hA : Assumption11 d ξ κ D P₀ h₀)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 2 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ R' : ℝ, 0 ≤ R' → ∀ U : Set (Rd d), IsOpen U →
      U ⊆ closedBall 0 R' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | ¬ ∀ φ : C(Rd d, ℝ), ⇑φ = locField κ ε (h ω) → ∀ ha : 0 < (aEps κ ξ ε)⁻¹,
          ∀ x ∈ U, ∀ y ∈ U,
            setDistIn ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha) (thickening (ε ^ q) U)
                (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
              ENNReal.ofReal C * (D (h ω)).internal U x y ∧
            setDistIn (D (h ω)) (thickening (ε ^ q) U) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
              ENNReal.ofReal C * ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha).internal U x y} ≤
          ENNReal.ofReal ((2 * R' + 7) ^ d * ε ^ β) :=
  c27_lemma27 hd hξ hκ hA.strong hh₀ hA.conv hq0 hq1 hβ

/-- **Lemma 2.7 for `κ ≥ 0`** (MA3 §4.2): the signed route applies to every nonnegative seed. -/
theorem c27_lemma27_nonneg (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {D : DistRd d → ContMetric d}
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {h₀ : Ω₀ → DistRd d}
    (hh₀ : IsNormalizedLGF h₀ P₀) (hA : Assumption11 d ξ κ D P₀ h₀)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 2 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ R' : ℝ, 0 ≤ R' → ∀ U : Set (Rd d), IsOpen U →
      U ⊆ closedBall 0 R' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | ¬ ∀ φ : C(Rd d, ℝ), ⇑φ = locField κ ε (h ω) → ∀ ha : 0 < (aEps κ ξ ε)⁻¹,
          ∀ x ∈ U, ∀ y ∈ U,
            setDistIn ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha) (thickening (ε ^ q) U)
                (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
              ENNReal.ofReal C * (D (h ω)).internal U x y ∧
            setDistIn (D (h ω)) (thickening (ε ^ q) U) (ball x (ε ^ q)) (ball y (ε ^ q)) ≤
              ENNReal.ofReal C * ((fieldLfppMetric ξ φ).smul (aEps κ ξ ε)⁻¹ ha).internal U x y} ≤
          ENNReal.ofReal ((2 * R' + 7) ^ d * ε ^ β) :=
  c27_lemma27_assumption11 hd hξ hκ.toAdmissibleSeed hh₀ hA hq0 hq1 hβ

end HigherDimLFPPAS.Coarse
