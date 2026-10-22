import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLFPP.Paths.DistOn

/-!
# Deterministic metric statements for [1] §3

This module records the statement shapes from MA5 Details (c). The distance and
properness definitions are the audit's literal formulas; the path predicate
is the existing, structurally identical `HigherDimLFPP.IsPcwC1Path`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- MA5's piecewise C¹ path predicate, reused from HigherDimLFPP. -/
abbrev IsPiecewiseC1Path (P : ℝ → Rd d) (z w : Rd d) : Prop :=
  HigherDimLFPP.IsPcwC1Path P z w

/-- The extended LFPP length, as in MA5 Details (c). -/
def lfppLen (ξ : ℝ) (φ : Rd d → ℝ) (P : ℝ → Rd d) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (ξ * φ (P t)) * ‖deriv P t‖)

/-- LFPP distance of a continuous field, in the extended nonnegative reals. -/
def fieldLfppE (ξ : ℝ) (φ : Rd d → ℝ) (z w : Rd d) : ℝ≥0∞ :=
  ⨅ P : {P : ℝ → Rd d // IsPiecewiseC1Path P z w}, lfppLen ξ φ P.1

/-- LFPP distance as a real function on pairs. -/
def fieldLfpp (ξ : ℝ) (φ : Rd d → ℝ) : Rd d × Rd d → ℝ :=
  fun p => (fieldLfppE ξ φ p.1 p.2).toReal

open Classical in
/-- A function on pairs bundled as continuous when possible; zero otherwise. -/
def toCMapRd (f : Rd d × Rd d → ℝ) : C(Rd d × Rd d, ℝ) :=
  if hf : Continuous f then ⟨f, hf⟩ else 0

/-- The supremal distance between two points of a set. -/
def supPairs (D : Rd d × Rd d → ℝ) (A : Set (Rd d)) : ℝ≥0∞ :=
  ⨆ u ∈ A, ⨆ v ∈ A, ENNReal.ofReal (D (u, v))

/-- The infimal distance between two sets. -/
def infPairs (D : Rd d × Rd d → ℝ) (A B : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ u ∈ A, ⨅ v ∈ B, ENNReal.ofReal (D (u, v))

/-- MA5's properness at infinity: crossing distances diverge. -/
def IsProperFn (D : Rd d × Rd d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ M : ℝ, ∃ R : ℝ, r < R ∧
    ENNReal.ofReal M ≤ infPairs D (Metric.closedBall 0 r) (Metric.sphere 0 R)

/-- A continuous metric that is also a length metric. -/
def IsContLengthFn (D : C(Rd d × Rd d, ℝ)) : Prop :=
  ∃ hD : IsContinuousMetric D, ContMetric.IsLength (⟨D, hD⟩ : ContMetric d)

/-- MA5 DL1: locally uniform limits of length metrics with a proper limit. -/
def L6c_lengthLimit : Prop :=
  ∀ (d : ℕ) (Dn : ℕ → C(Rd d × Rd d, ℝ)) (D : C(Rd d × Rd d, ℝ)),
    (∀ n, IsContLengthFn (Dn n)) → IsContinuousMetric D → IsProperFn D →
    (∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n)) ⇑D atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R)) →
    IsContLengthFn D

/-- MA5's deterministic Weyl continuity statement. -/
def L6d_weylCont : Prop :=
  ∀ (d : ℕ) (ξ : ℝ) (Dn : ℕ → ContMetric d) (D : ContMetric d) (Gn : ℕ → C(Rd d, ℝ))
    (G : C(Rd d, ℝ)), (∀ n, (Dn n).IsLength) → D.IsLength → IsProperFn D.1 →
    (∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R)) →
    (∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Gn n)) ⇑G atTop
      (Metric.closedBall (0 : Rd d) R)) → (∃ M : ℝ, ∀ z, |G z| ≤ M) →
    ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n (p : Rd d × Rd d) => (weylScale ξ (Gn n) (Dn n) p.1 p.2).toReal)
      (fun p => (weylScale ξ G D p.1 p.2).toReal) atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R)

/-- MA5's LFPP Weyl identity. -/
def L6e_weylLfpp : Prop :=
  ∀ (d : ℕ) (ξ : ℝ) (φ g : C(Rd d, ℝ)) (hD : IsContinuousMetric (toCMapRd (fieldLfpp ξ ⇑φ))),
    ∀ z w : Rd d, weylScale ξ g (⟨toCMapRd (fieldLfpp ξ ⇑φ), hD⟩ : ContMetric d) z w =
      fieldLfppE ξ (⇑φ + ⇑g) z w

end HigherDimLQGMetric
