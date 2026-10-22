import Mathlib.Analysis.Distribution.TestFunction
import HigherDimLFPP.Frozen.Rd

/-!
# Frozen definition: `TestOn`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 61, 67 and [1] §1.2 footnote (TeX l. 242): `𝓓(U)`, the real smooth (`C^∞`) test functions with
compact support in the open set `U ⊆ ℝ^d` (mathlib's `TestFunction` at smoothness `⊤ : ℕ∞`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `𝓓(U)`: real smooth test functions with compact support in the open set `U ⊆ ℝ^d` (mathlib
`TestFunction U ℝ ⊤`, smoothness `⊤ : ℕ∞ = C^∞`). -/
abbrev TestOn {d : ℕ} (U : TopologicalSpace.Opens (Rd d)) : Type := 𝓓(U, ℝ)

end HigherDimLQGMetric
