import HigherDimLQGMetric.Frozen.ContMetric
import HigherDimLQGMetric.Frozen.ContMetricInternal
import HigherDimLQGMetric.Frozen.ContMetricIsLength
import HigherDimLQGMetric.Frozen.WeylScale
import HigherDimLQGMetric.Frozen.IsLGFPlusCont
import HigherDimLQGMetric.Frozen.RestrictTo
import HigherDimLQGMetric.Frozen.AddFun
import HigherDimLQGMetric.Frozen.AddConst
import HigherDimLQGMetric.Frozen.AffineComp
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont
import HigherDimLQGMetric.Frozen.NormalizedAtScale
import HigherDimLQGMetric.Frozen.TightOver

/-!
# Frozen definition: `IsWeakExpMetric`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] Definition 1.3, l. 99–109 (= [1] §1.2, Axioms I–V, TeX l. 237–262): Axioms (I)–(III) as in
Definition 1.1, translation covariance (for fixed `z`, a.s. `D_{h(·+z)} = D_h(·+z, ·+z)`), and
deterministic normalizers `c_r > 0` such that `c_r⁻¹ e^{-ξ h_r(0)} D_h(r·, r·)` is tight locally uniformly
over `0 < r < R` for every finite `R` (LGF plus continuous function), and over all `r > 0` for an LGF plus
a bounded continuous function, with all limits continuous metrics. No a priori bound on `c_r` (MA0
fidelity note 7). `c_pos` is implied by the tightness fields (a law carried by `c_r⁻¹·(metric)` with
`c_r ≤ 0` is not carried by metrics) and is stated for convenience.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- **Definition 1.3** (the auxiliary weak class = [1, §1.2] Axioms I–V) with normalizers `c`. -/
structure IsWeakExpMetric (d : ℕ) (ξ : ℝ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ) : Prop where
  /-- a metric assignment is a measurable map -/
  measurable : Measurable D
  /-- (I) length metric -/
  length : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength
  /-- (II) locality -/
  locality : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ U : TopologicalSpace.Opens (Rd d),
      ∃ F : DistOn U → (Rd d → Rd d → ℝ≥0∞), Measurable F ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, (D (h ω)).internal U z w = F (restrictTo U (h ω)) z w
  /-- (III) Weyl scaling, simultaneously for all continuous `f` -/
  weyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ z w : Rd d,
      weylScale ξ f (D (h ω)) z w = ENNReal.ofReal ((D (addFun (h ω) f)).1 (z, w))
  /-- translation covariance: for fixed `z`, a.s. `D_{h(·+z)} = D_h(· + z, · + z)` -/
  translation : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ z : Rd d, ∀ᵐ ω ∂P, ∀ u v : Rd d,
      (D (affineComp 1 z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z)
  /-- the deterministic normalizers are positive -/
  c_pos : ∀ r : ℝ, 0 < r → 0 < c r
  /-- tightness across scales over `0 < r < R`, every `R`, for an LGF plus a continuous function -/
  tight : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ R : ℝ, 0 < R →
      TightOver P (fun r ω => normalizedAtScale ξ D c (h ω) r) (Ioo 0 R)
  /-- ... and over all `r > 0` for an LGF plus a bounded continuous function -/
  tight_bdd : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusBddCont h P →
      TightOver P (fun r ω => normalizedAtScale ξ D c (h ω) r) (Ioi 0)

end HigherDimLQGMetric
