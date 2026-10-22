import HigherDimLQGMetric.Frozen.ContMetric
import HigherDimLQGMetric.Frozen.SphereAvg
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Frozen definition: `normalizedAtScale`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 99–106 (Definition 1.3: `c_r⁻¹ e^{-ξ h_r(0)} D_h(r·, r·)`): the normalized scale-`r` metric, as an
element of `C(ℝ^d × ℝ^d, ℝ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The normalized scale-`r` metric `c_r⁻¹ e^{-ξ h_r(0)} D_h(r ·, r ·)`. -/
def normalizedAtScale {d : ℕ} (ξ : ℝ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ)
    (h : DistRd d) (r : ℝ) : C(Rd d × Rd d, ℝ) :=
  ((c r)⁻¹ * Real.exp (-ξ * sphereAvg h r 0)) •
    (D h).1.comp ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩

end HigherDimLQGMetric
