/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiExistsMart
import InteractingSLE.Spec.Sec2.JacobiExistsNatural
import InteractingSLE.Spec.Sec2.TwoSeedExists

/-!
# Existence of the two-sided Jacobi diffusion, and the two-seed evolution for every weight

Packet PROVE-YW-JACOBI. Specification p. 22, L498–L512 ("Let `U` be the diffusion on `[0, 1]` …
Take a two-sided stationary version `(U_u)_{u ∈ ℝ}`"), cited there as standard one-dimensional
diffusion theory.

* `Jacobi.exists_isJacobiDiffusion`: for all `κ, a, b > 0` there is a Jacobi diffusion on all of `ℝ`
  in the martingale-problem form `Jacobi.IsJacobiDiffusion` of `JacobiSDE.lean`. It is the continuous
  version `jacU` of the coordinate process of the path measure `pathMeasure` (Riesz–Markov on
  `ℝ → [0, 1]` from the moments of the Jacobi semigroup, `JacobiExistsRiesz.lean`; continuity by
  Kolmogorov–Chentsov, `JacobiExistsPath.lean`), which solves the polynomial martingale problem
  (`JacobiExistsMart.lean`), in its natural filtration (`JacobiExistsNatural.lean`).
* `exists_isIntegratedSLEEvolution_twoSeed`: the frozen conclusion of Theorem 2.2's existence for two
  seeds at `0⁻, 0⁺` holds for **every** pair of weights, unconditionally (the hypothesis of the landed
  `exists_isIntegratedSLEEvolution_twoSeed_of_jacobiExists` is discharged).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-- **Existence of the two-sided Jacobi diffusion** for all `κ, a, b > 0`. -/
theorem Jacobi.exists_isJacobiDiffusion {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓗 : Filtration ℝ mΩ) (U : ℝ → Ω → ℝ), Jacobi.IsJacobiDiffusion κ a b P 𝓗 U :=
  ⟨JacobiExists.PathSpace, inferInstance, JacobiExists.pathMeasure κ a b hκ ha hb, inferInstance,
    Jacobi.natFilt (JacobiExists.isJacobiMP_jacU hκ ha hb).measurable,
    JacobiExists.jacU κ a b hκ ha hb, (JacobiExists.isJacobiMP_jacU hκ ha hb).isJacobiDiffusion⟩

/-- **Two seeds at `0⁻, 0⁺`, every weight**: the frozen conclusion of
`exists_isIntegratedSLEEvolution` for `nL = nR = 1`, `xL = xR = 0`, unconditionally. -/
theorem exists_isIntegratedSLEEvolution_twoSeed {κ : ℝ} (hκ : 0 < κ) {xL xR : Fin 1 → ℝ}
    (hxL : ∀ i, xL i = 0) (hxR : ∀ i, xR i = 0) (ρL ρR : Fin 1 → ℝ) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ :=
  exists_isIntegratedSLEEvolution_twoSeed_of_jacobiExists hκ
    (fun _ _ ha hb => Jacobi.exists_isJacobiDiffusion hκ ha hb) hxL hxR ρL ρR

end Sec2

end InteractingSLE
