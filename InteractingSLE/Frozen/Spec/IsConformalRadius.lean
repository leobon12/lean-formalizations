-- Frozen anchor (definition, spec_IsConformalRadius_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.CStarAlgebra.Classes

set_option autoImplicit false

noncomputable section

namespace InteractingSLE

/-- **`r` is the conformal radius of the domain `D` at `z`** (Specification p. 157, `source/spec/p145-192.md` L234, and
Theorem 2.6, p. 40): `r = |φ'(0)|` for a conformal map `φ` of the unit disc onto `D` with `φ(0) = z` (holomorphic on the
disc and a bijection onto `D`). The module `InteractingSLE.Spec.Sec2.T2426Cert` proves that this relation is functional
(every such map has the same `|φ'(0)|`), that `2 Im z` is the conformal radius of `ℍ` at `z`, and that `ℍ ∖ K_t`
has a conformal radius at every `z ∉ K_t` for a continuous driver from `0`. -/
def IsConformalRadius (D : Set ℂ) (z : ℂ) (r : ℝ) : Prop :=
  ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) ∧
    Set.BijOn φ (Metric.ball (0 : ℂ) 1) D ∧ φ 0 = z ∧ ‖deriv φ 0‖ = r

end InteractingSLE
