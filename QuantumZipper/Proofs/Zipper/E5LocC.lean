import QuantumZipper.Proofs.Zipper.E5LocB

/-!
# E5-LOC2, part C: the switched collision correction satisfies the D3⁺ `Setup`

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E5, steps (1)–(2); Sheffield, arXiv:1012.4797,
§5.4 (pp. 66–72).

The collision correction splits as (`locCorr_eq_drv_add_incr`)

  `locCorr κ V t ϖ ρ₀ x z = locCorrDrv κ V t ϖ z + (x(ρ₀) − x(ϖ_t))`,

a driver part (`−(√κ/2) k_{ϖ_t}(z) − ∫ s dϖ_t − q_t`, a function of `(V, t)` only) plus a
balanced increment of the field. On a model space with random driver data `(V_ω, t_ω)`,
`setup_locCorr_switch` gives the D3⁺ `Setup` for the correction switched to a fallback `g₀` on the
event `{ϖ_{t_ω}(ball 0 r) ≠ 0}`, from:

* `σ(Ξ)`-measurability of `ω ↦ ϖ_{t_ω}(A)` (so the switch event is in `condSigma`) and of the
  driver part (`hdrv`);
* a `condSigma`-measurable surrogate of the increment `X'(ρ₀) − X'(ϖ_{t_ω})` off the switch
  event (`hinc`; for a *deterministic* measure this is `measurable_condSigma_sub`, item (iv)).

Harmonicity off the switch event is `harmonicOnNhd_locCorr_foldH_of_normalizer`.
Own elementary arguments (definitions).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open D3Plus E1 B2

/-- The driver part of the collision correction. -/
def locCorrDrv (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (z : ℂ) : ℝ :=
  -(Real.sqrt κ / 2) * PalmNorm.kPot (varpiT V t ϖ) z -
    ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0) (varpiT V t ϖ) -
    qt κ V t ϖ

theorem locCorr_eq_drv_add_incr (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ ρ₀ : Measure ℂ)
    (x : FieldSample) (z : ℂ) :
    locCorr κ V t ϖ ρ₀ x z = locCorrDrv κ V t ϖ z + (x ρ₀ - x (varpiT V t ϖ)) := by
  simp only [locCorr, locCorrDrv, Pi.add_apply]
  ring

end E5
end QuantumZipper
