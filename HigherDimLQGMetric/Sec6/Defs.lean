import HigherDimLQGMetric.Events.Defs
import HigherDimLQGMetric.Frozen.WeylScale

/-!
# [S] §6: trap properties, the trap family, locality, Corollary 6.3 (definitions)

Packet S6a. The definitions of MA3 Details (c) §6 (`planning/audits/statements/MA3Statements.lean.txt`,
the durable copy of MA3's checked scratch section), **verbatim**, re-based on the library's surface:
`ContMetric`, `weylScale` (frozen), `ContMetric.internal` (frozen), `ContMetric.len` (M1),
`ann`, `sNorm`, `AEEventIn`, `fieldSigma0` (`Core/Defs`), `Config`, `config`, `IsGeodIn`, `IsGeod`,
`WitEvent`, `scaleWin` (S4a, `Events/Defs`).

* `IsWeylOf ξ f D D'`: the continuous metric `D'` represents the Weyl scaling `e^{ξ f}·D`.
* `bumpAt f r z = f((· − z)/r)` and `occLen D P V` (the `D`-length that `P|[0,1]` spends in `V`).
* `TrapProps`: (T1)–(T4) of [S] Proposition 6.2 (l. 1015–1037), deterministic, (T3) with the internal
  `B_{4r}(z)` threshold (MA3 E11).
* `TrapFamily`: [S] Proposition 6.2 in the corrected deterministic form (MA3 E10, D-6.2).
* `ConfigLocal`: locality of configuration events; `Cor63`: [S] Corollary 6.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- `D'` represents the Weyl-scaled metric `e^{ξ f}·D` -/
def IsWeylOf (ξ : ℝ) (f : C(Rd d, ℝ)) (D D' : ContMetric d) : Prop :=
  ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y

/-- `f_{z,r}(x) = f((x − z)/r)` -/
def bumpAt (f : C(Rd d, ℝ)) (r : ℝ) (z : Rd d) : C(Rd d, ℝ) :=
  f.comp ⟨fun x => r⁻¹ • (x - z), by fun_prop⟩

/-- total `D`-length of `P|[0,1]` spent in `V` (finite families of disjoint subintervals) -/
def occLen (D : ContMetric d) (P : ℝ → Rd d) (V : Set (Rd d)) : ℝ≥0∞ :=
  ⨆ (I : Finset (ℝ × ℝ)) (_ : (I : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioo p.1 p.2))
    (_ : ∀ p ∈ I, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1 ∧ ∀ τ ∈ Icc p.1 p.2, P τ ∈ V),
    ∑ p ∈ I, D.len P p.1 p.2

/-- **(T1)–(T4)** at `(z, r, j)` with scale `s` (l. 1015–1037), deterministic, for an original
metric `D`, a comparison metric `D̃`, and their discounted versions given by Weyl scaling. (T3) is
stated with the internal `B_{4r}(z)` threshold (the form used in §8, (C4); l. 1036–1037). -/
def TrapProps (ξ : ℝ) (V : Set (Rd d)) (f : ℕ → C(Rd d, ℝ)) (J : ℕ) (a b c g H c' : ℝ)
    (D Dt : ContMetric d) (s r : ℝ) (z : Rd d) (j : ℕ) : Prop :=
  -- (T1)
  (∀ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) → P 0 ∈ closure ((fun x => r • x + z) '' V) →
      P 1 ∈ Metric.sphere z r ∪ Metric.sphere z (3 * r) →
      ENNReal.ofReal (a * s) ≤ D.len P 0 1) ∧
  -- (T2)
  (∀ D' : ContMetric d, IsWeylOf ξ (-bumpAt (f j) r z) D D' →
      ∀ u ∈ closure ((fun x => r • x + z) '' V), ∀ v ∈ closure ((fun x => r • x + z) '' V),
        D'.internal (ann z r (3 * r)) u v ≤ ENNReal.ofReal ((2 * a - g) * s)) ∧
  -- (T3)
  (∀ D' Dt' : ContMetric d, IsWeylOf ξ (-bumpAt (f j) r z) D D' →
      IsWeylOf ξ (-bumpAt (f j) r z) Dt Dt' →
      ∀ P : ℝ → Rd d, IsGeodIn D' (Metric.ball z (4 * r)) P →
      ∀ σ₁ σ₂ : ℝ, 0 ≤ σ₁ → σ₁ ≤ σ₂ → σ₂ ≤ 1 →
      P σ₁ ∈ closure ((fun x => r • x + z) '' V) → P σ₂ ∈ closure ((fun x => r • x + z) '' V) →
      (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ closure ((fun x => r • x + z) '' V) → σ₁ ≤ τ ∧ τ ≤ σ₂) →
      ENNReal.ofReal (b * s) ≤ D.internal (Metric.ball z (4 * r)) (P σ₁) (P σ₂) →
      ∃ τ₁ τ₂ : ℝ, σ₁ ≤ τ₁ ∧ τ₁ ≤ τ₂ ∧ τ₂ ≤ σ₂ ∧
        ENNReal.ofReal (c * s) ≤ D'.len P τ₁ τ₂ ∧
        Dt'.internal (Metric.ball z (4 * r)) (P τ₁) (P τ₂) ≤ ENNReal.ofReal c' * D'.len P τ₁ τ₂) ∧
  -- (T4)
  (∀ Z : Finset (Rd d × ℕ), (z, j) ∈ Z → (∀ q ∈ Z, q.2 < J) →
      (Z : Set (Rd d × ℕ)).Pairwise
        (fun q q' => Disjoint (Metric.ball q.1 (4 * r)) (Metric.ball q'.1 (4 * r))) →
      ∀ D'' : ContMetric d, IsWeylOf ξ (-(∑ q ∈ Z, bumpAt (f q.2) r q.1)) D D'' →
      ∀ P : ℝ → Rd d, IsGeod D'' P →
        (∀ τ₁ τ₂ τ : ℝ, 0 ≤ τ₁ → τ₁ ≤ τ → τ ≤ τ₂ → τ₂ ≤ 1 →
          P τ₁ ∈ closure ((fun x => r • x + z) '' V) →
          P τ₂ ∈ closure ((fun x => r • x + z) '' V) → P τ ∈ Metric.ball z (4 * r)) ∧
        occLen D P ((fun x => r • x + z) '' V) ≤ ENNReal.ofReal (H * s))

/-- **Proposition 6.2** (finite deterministic trap family, l. 996–1119), split into the trap data,
(P) the probability bound at the scales of (16), and (T) the deterministic properties on the
configuration sets `N j`. `aL, A₀L, ℓL, β₀L` are the regularity constants of the lower pair. -/
def TrapFamily (d : ℕ) (ξ Q : ℝ) (D Dt : DistRd d → ContMetric d)
    (cs Cs c1 aL A₀L ℓL β₀L pstar : ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 →
  ∃ (m : ℕ) (V : Set (Rd d)) (J : ℕ) (f : ℕ → C(Rd d, ℝ)) (N : ℕ → Set (Config d))
    (a b c g H Mf c' : ℝ),
    IsOpen V ∧ closure V ⊆ ann 0 1 3 ∧ Metric.sphere (0 : Rd d) 2 ⊆ V ∧
    (∀ j < J, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) ∧ HasCompactSupport (f j) ∧
      tsupport (f j) ⊆ ann 0 1 3 ∧ (∀ x, 0 ≤ f j x) ∧ (∀ x, 0 < f j x ↔ x ∈ V) ∧
      (∀ x, f j x ≤ Mf)) ∧
    0 < a ∧ 0 < b ∧ 0 < c ∧ g = a ∧ H = a * Real.exp (ξ * Mf) ∧ c' < Cs ∧ 2 * b < g / 2 ∧
    (∀ j < J, MeasurableSet (N j)) ∧
    -- (P)
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal pstar ≤
        P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c1⁻¹ ((64 : ℝ)⁻¹ ^ m * r) 0) →
      ∀ z : Rd d, ENNReal.ofReal p ≤
        P {ω | ∃ j < J, config (D (h ω)) (Dt (h ω)) (sNorm ξ Q (h ω) r z) r z ∈ N j}) ∧
    -- (T)
    (∀ D₀ Dt₀ : ContMetric d, D₀.IsLength → Dt₀.IsLength →
      (∀ x y, cs * D₀.1 (x, y) ≤ Dt₀.1 (x, y) ∧ Dt₀.1 (x, y) ≤ Cs * D₀.1 (x, y)) →
      ∀ (s r : ℝ) (z : Rd d) (j : ℕ), 0 < s → 0 < r → j < J →
        config D₀ Dt₀ s r z ∈ N j → TrapProps ξ V f J a b c g H c' D₀ Dt₀ s r z j)

/-- locality of configuration events: a.s. events of the field modulo constants on
`A_{r/2,5r}(z)` (from Axioms II–III; l. 1008–1009, 1099–1101) -/
def ConfigLocal (d : ℕ) (ξ Q : ℝ) (D Dt : DistRd d → ContMetric d) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ (r : ℝ) (z : Rd d), 0 < r →
    ∀ S : Set (Config d), MeasurableSet S →
      AEEventIn P (fieldSigma0 h (ann z (r / 2) (5 * r)))
        {ω | config (D (h ω)) (Dt (h ω)) (sNorm ξ Q (h ω) r z) r z ∈ S}

/-- **Corollary 6.3** (l. 1120–1129), for the shift `m` of Proposition 6.2 -/
def Cor63 (d : ℕ) (ξ Q : ℝ) (D Dt : DistRd d → ContMetric d)
    (cs c0 c1 aL A₀L ℓL β₀L pstar : ℝ) (m : ℕ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ R : ℝ, 0 < R →
    ENNReal.ofReal pstar ≤ P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c0⁻¹ R 0) →
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (2 / 3 : ℝ) * (scaleWin ε R).ncard ≤
        ({j ∈ scaleWin ε R | ENNReal.ofReal pstar ≤
          P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c1⁻¹
            ((64 : ℝ)⁻¹ ^ m * (64 : ℝ) ^ j) 0)} : Set ℤ).ncard

/-! ### Elementary API -/

theorem bumpAt_apply (f : C(Rd d, ℝ)) (r : ℝ) (z x : Rd d) :
    bumpAt f r z x = f (r⁻¹ • (x - z)) := rfl

theorem bumpAt_affine (f : C(Rd d, ℝ)) {r : ℝ} (hr : r ≠ 0) (z x : Rd d) :
    bumpAt f r z (r • x + z) = f x := by
  rw [bumpAt_apply, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr, one_smul]

end HigherDimLQGMetric
