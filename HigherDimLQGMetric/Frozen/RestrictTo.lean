import HigherDimLQGMetric.Frozen.DistRd

/-!
# Frozen definition: `restrictTo`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 67 (Axiom (II), `h|_U`): the restriction of `h ∈ 𝒟'(ℝ^d)` to the open set `U`, i.e. `h`
composed with the inclusion `𝓓(U) ⊆ 𝓓(ℝ^d)` (mathlib's `TestFunction.monoCLM`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h|_U ∈ 𝒟'(U)`: `h` composed with the inclusion `𝓓(U) ⊆ 𝓓(ℝ^d)`. -/
def restrictTo {d : ℕ} (U : TopologicalSpace.Opens (Rd d)) (h : DistRd d) : DistOn U :=
  h.comp (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤))

end HigherDimLQGMetric
