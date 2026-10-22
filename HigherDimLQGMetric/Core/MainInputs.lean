import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.IsWeakExpMetric
import HigherDimLQGMetric.Frozen.AddFun
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Frozen.AEps
import HigherDimLQGMetric.Frozen.LfppDist
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont
import HigherDimLQGMetric.Frozen.IsLGFPlusCont
import HigherDimLQGMetric.Frozen.TendstoInProbLU
import HigherDimLQGMetric.Frozen.IsNormalizedLGF

/-!
# The statements of the main theorems and of their last inputs, as propositions (orchestrator-owned)

For the final assembly (packet L10a, interface pattern): `Theorem12Stmt`, `Theorem14Stmt`, `Theorem14SharpStmt`,
`StrongUniquenessStmt`, `SharpWeakNonemptyStmt` are the statements of the frozen theorem anchors `theorem12`, `theorem14`,
`theorem14Sharp`, `strongUniqueness`, `sharpWeak_nonempty`, copied **verbatim** from `HigherDimLQGMetric/Frozen/*.lean`
(checked mechanically by the orchestrator); workers prove implications between them without importing the anchors.
`Theorem16Shape` ([1] Theorem 1.6 = (E2); MA6's `theorem16`), `Cor102SharpShape` (MA4's `cor102_sharp`) and
`Lemma103Shape` (MA4's `lemma103`) are the audited statements of the corresponding packets (L9c, S8, S8b), as propositions.
Workers import this module and never edit or redefine it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- the statement of the main theorem, [S] Theorem 1.2 (existence, uniqueness, LFPP convergence), verbatim -/
def Theorem12Stmt : Prop :=
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    (∃ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D ∧
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P →
        TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
          (fun ω => (D (h ω)).1)) ∧
    ∀ D D' : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d ξ (distExp d ξ) D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v)

/-- the statement of the main theorem, [S] Theorem 1.4 (uniqueness in the weak class), verbatim -/
def Theorem14Stmt : Prop :=
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ (D D' : DistRd d → ContMetric d) (c c' : ℝ → ℝ),
      IsWeakExpMetric d ξ D c → IsWeakExpMetric d ξ D' c' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v)

/-- the statement of the Phase A anchor `theorem14Sharp` (uniqueness in the sharp weak class), verbatim -/
def Theorem14SharpStmt : Prop :=
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsSharpWeakExpMetric d ξ Q D → IsSharpWeakExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v)

/-- the statement of the Phase A anchor `strongUniqueness`, verbatim -/
def StrongUniquenessStmt : Prop :=
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ Q D → IsStrongExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v)

/-- the statement of the sanity anchor `sharpWeak_nonempty`, verbatim -/
def SharpWeakNonemptyStmt : Prop :=
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ D : DistRd d → ContMetric d, IsSharpWeakExpMetric d ξ (distExp d ξ) D

/-- **[1] Theorem 1.6** (= (E2); MA6's `theorem16`): every weak assignment has normalizers comparable to
`r^{ξ Q(ξ)}`, hence is sharp weak at `Q(ξ) = distExp d ξ` -/
def Theorem16Shape : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ {ξ : ℝ}, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ {D : DistRd d → ContMetric d} {c : ℝ → ℝ}, IsWeakExpMetric d ξ D c →
    (∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r →
        C⁻¹ * r ^ (ξ * distExp d ξ) ≤ c r ∧ c r ≤ C * r ^ (ξ * distExp d ξ)) ∧
      IsSharpWeakExpMetric d ξ (distExp d ξ) D

/-- **[S] Corollary 10.2, sharp form** (MA4's `cor102_sharp`): a sharp weak assignment is strong -/
def Cor102SharpShape : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ {ξ Q : ℝ}, 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ {D : DistRd d → ContMetric d}, IsSharpWeakExpMetric d ξ Q D → IsStrongExpMetric d ξ Q D

/-- **[S] Lemma 10.3** (MA4's `lemma103`): full support of the normalized point distance -/
def Lemma103Shape : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ {ξ Q : ℝ}, 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ {D : DistRd d → ContMetric d}, IsSharpWeakExpMetric d ξ Q D →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ {u v : ℝ}, 0 < u → u < v →
        0 < P {ω | (D (h ω)).1 (0, e₁ d) ∈ Ioo u v}

end HigherDimLQGMetric
