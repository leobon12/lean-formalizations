import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Frozen.TendstoInProbLU
import HigherDimLQGMetric.Frozen.AEps
import HigherDimLQGMetric.Frozen.LfppDist
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Frozen definition: `Assumption11`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L6, L8; statement audit
`planning/audits/S1-statement-audit.md`).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): **Assumption 1.1**, l. 90–116, for the metric
assignment `D` and the pinned field `h` on its probability space `(Ω, P)` (l. 49–50, 83).
* `subcritical`: l. 103 ("`Q = Q(ξ) > √(2d)` is the LFPP distance exponent"), `Q(ξ) = HigherDimLQGMetric.distExp d ξ`.
* `strong`: the preamble (l. 90–92, "a measurable metric assignment `g ↦ D_g`, defined for a whole-space
  log-correlated Gaussian field plus a continuous function") and (i)–(iv), l. 93–106, read as the four strong
  axioms of [5] Definition 1.1 at `(ξ, Q(ξ))` (l. 19–22, 115–116: "the four metric axioms and (1.6) are exactly
  the conclusions needed from the earlier characterization"), i.e. the sealed `HigherDimLQGMetric.IsStrongExpMetric`
  (ruling L6: codomain `ContMetric d`, the field class of [5] Definition 1.1, (iv) in the `Q log r` form).
  (iv) is written there as `D_h(ru + z, rv + z) = D_{h(r·+z) + Q log r}(u, v)` for every field of the class, which is
  (1.5) together with "the corresponding covariance identities [...] after continuous perturbations" (l. 103–106)
  through (iii).
* `conv`: (v), l. 108–111, (1.6): on the original field probability space, `𝔞_ε⁻¹ D^ε_h → D_h` in probability,
  locally uniformly on `ℝ^d × ℝ^d`, as `ε ↓ 0`, with `D^ε` of (1.3) (`lfppDist`) and `𝔞_ε` of (1.4) (`aEps`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLFPPAS

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **Assumption 1.1** for the assignment `D`, the seed `κ` and the field `h` on `(Ω, P)`: subcriticality
`Q(ξ) > √(2d)`, the strong axioms (i)–(iv) at `Q = Q(ξ)`, and (1.6) on the original field probability space. -/
structure Assumption11 (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop where
  /-- `Q = Q(ξ) > √(2d)` (l. 103) -/
  subcritical : Real.sqrt (2 * d) < distExp d ξ
  /-- the measurable assignment and (i)–(iv) (l. 90–106) -/
  strong : IsStrongExpMetric d ξ (distExp d ξ) D
  /-- (v), (1.6): `𝔞_ε⁻¹ D^ε_h → D_h` in probability, locally uniformly (l. 108–111) -/
  conv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
    (fun ω => (D (h ω)).1)

end HigherDimLFPPAS
