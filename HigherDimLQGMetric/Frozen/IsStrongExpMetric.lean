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

/-!
# Frozen definition: `IsStrongExpMetric`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M12, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] Definition 1.1, l. 63–81 (the four strong axioms), with the setting of l. 50–62: a measurable
assignment `h ↦ D_h` from `𝒟'(ℝ^d)` to continuous metrics such that, whenever the input `h` is a
whole-space LGF plus a possibly random continuous function (on any probability space `Ω : Type`):
(I) a.s. `D_h` is a length metric; (II) for deterministic open `U`, `D_h(·,·;U)` is a.s. a measurable
function of `h|_U` (simultaneously for all `z, w ∈ U`); (III) a.s., simultaneously for all continuous
`f`, `D_{h+f} = e^{ξf}·D_h`; (IV) for each fixed `r > 0`, `z`, a.s. simultaneously for all `u, v`,
`D_h(ru + z, rv + z) = D_{h(r·+z) + Q log r}(u, v)`. No other assumption (l. 80–81).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- **Definition 1.1** (the four strong axioms) at the parameters `(ξ, Q)`. -/
structure IsStrongExpMetric (d : ℕ) (ξ Q : ℝ) (D : DistRd d → ContMetric d) : Prop where
  /-- a metric assignment is a measurable map -/
  measurable : Measurable D
  /-- (I) length metric -/
  length : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength
  /-- (II) locality: for deterministic open `U`, `D_h(·,·;U)` is a.s. a measurable function of
  `h|_U` -/
  locality : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ U : TopologicalSpace.Opens (Rd d),
      ∃ F : DistOn U → (Rd d → Rd d → ℝ≥0∞), Measurable F ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, (D (h ω)).internal U z w = F (restrictTo U (h ω)) z w
  /-- (III) Weyl scaling, simultaneously for all continuous `f` -/
  weyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ z w : Rd d,
      weylScale ξ f (D (h ω)) z w = ENNReal.ofReal ((D (addFun (h ω) f)).1 (z, w))
  /-- (IV) coordinate change: for fixed `r > 0` and `z`, a.s. for all `u, v`,
  `D_h(ru + z, rv + z) = D_{h(r·+z) + Q log r}(u, v)` -/
  coord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : Rd d, ∀ᵐ ω ∂P, ∀ u v : Rd d,
      (D (h ω)).1 (r • u + z, r • v + z) =
        (D (addConst (affineComp r z (h ω)) (Q * Real.log r))).1 (u, v)

end HigherDimLQGMetric
