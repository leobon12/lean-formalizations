import QuantumZipper.Proofs.Thm18.G1ZB2CMain
import QuantumZipper.Proofs.Thm18.G1RegRepScale
import QuantumZipper.Proofs.Thm18.G1ZMeasReg
import QuantumZipper.Proofs.Zipper.F2AddConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-B2C (3): the pathwise re-embedding identity from geometry and shifted regularity

Theorem 1.8, G1 zoom, node B2-C. Sheffield, arXiv:1012.4797, proof of Proposition 1.7 (pp. 25–26).

`G1SideShiftPathStmt` (G1ZB2CMain.lean) is derived from two smaller nodes:

* `G1SideShiftGeomStmt` (**deterministic geometry**): rescaling a good driver by `s` (Brownian
  scaling, `canonConfig`) rescales the side domain by `1/s`, so the (epsilon-chosen) side maps
  differ by a dilation: `ψ_{W_s}(w) = s⁻¹ ψ_W(b w)` on `ℍ` (uniqueness of the normalized
  uniformizer up to a positive factor, Pommerenke, *Boundary behaviour of conformal maps*, Thm 2.1
  / the Riemann mapping theorem; `trace_scale`, RS/TraceShift.lean).
* `G1SideShiftRegStmt` (**a.s. regularity of the shifted field**): the `G1.ChoiceRegular`
  package for `Y + C` pulled back by `ψ_W`, `evalReg`-commutation with constants along the pushed
  folded circles (`E1.RegShift`) and scale consistency of `Y + C` at the pushed circles.

The derivation (`g1zB2c_data_eq`, deterministic; `g1SideShiftPathStmt_of`) is own bookkeeping
from `G1.data_canonical_coordChange_eq` (choice independence), `G1Meas.coordChange_rescale_apply`
(pulling back a rescaled field) and `F2.coordChange_addConst_fc` (constants commute with
`coordChange` at folded circles).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization CoordsFull

/-- **Geometry of Brownian rescaling** (deterministic, node). -/
def G1SideShiftGeomStmt : Prop :=
  ∀ W : ℝ → ℝ, G1zDrvGood W → ∀ s : ℝ, 0 < s → ∀ left : Bool, ∃ b : ℝ, 0 < b ∧
    EqOn (g1zSideMap left (fun r => W (s ^ 2 * max r 0) / s))
      (fun w => (s : ℂ)⁻¹ * g1zSideMap left W ((b : ℂ) * w)) H

/-- Raw regularity of the dilated, scaled chart `w ↦ s⁻¹ ψ(b w)` at a folded circle. -/
theorem g1zB2c_scaled_chart {ψ : ℂ → ℂ}
    (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0)
    (hint : ∀ d ∈ Hbar, ∀ r > 0, Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    {s b : ℝ} (hs : 0 < s) (hb : 0 < b) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    (∀ᵐ u ∂foldedCircle d r, deriv (fun w => (s : ℂ)⁻¹ * ψ ((b : ℂ) * w)) u ≠ 0) ∧
    Integrable (fun u => Real.log ‖deriv (fun w => (s : ℂ)⁻¹ * ψ ((b : ℂ) * w)) u‖)
      (foldedCircle d r) := by
  have hae := TwoPoint.foldedCircle_ae_mem_H d hr
  have hder : ∀ u : ℂ, deriv (fun w => (s : ℂ)⁻¹ * ψ ((b : ℂ) * w)) u =
      (s : ℂ)⁻¹ * ((b : ℂ) * deriv ψ ((b : ℂ) * u)) := by
    intro u
    rw [deriv_const_mul_field']
    beta_reduce
    rw [deriv_comp_mul_left, smul_eq_mul]
  have hbr : 0 < b * r := mul_pos hb hr
  have hH := CircleFubini.foldH_mem_Hbar' ((b : ℂ) * d)
  have hint' := hint _ hH _ hbr
  rw [WedgeTK.fc_foldH_eq, ← WedgeTK.fc_map_mul d r hb] at hint'
  have hint'' : Integrable (fun z => Real.log ‖deriv ψ ((b : ℂ) * z)‖) (foldedCircle d r) :=
    hint'.comp_measurable (measurable_const_mul _)
  refine ⟨hae.mono fun u hu => ?_, ?_⟩
  · rw [hder]
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hs.ne'))
      (mul_ne_zero (by exact_mod_cast hb.ne') (hψ0 _ (G1.mul_mem_H hb hu)))
  · refine (hint''.add (integrable_const (Real.log b - Real.log s))).congr ?_
    filter_upwards [hae] with u hu
    rw [hder, norm_mul, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hs.le, Real.norm_of_nonneg hb.le,
      Real.log_mul (inv_ne_zero hs.ne') (mul_ne_zero hb.ne'
        (norm_ne_zero_iff.2 (hψ0 _ (G1.mul_mem_H hb hu)))),
      Real.log_mul hb.ne' (norm_ne_zero_iff.2 (hψ0 _ (G1.mul_mem_H hb hu))), Real.log_inv]
    simp only [Pi.add_apply]
    ring

end Thm18Asm
end QuantumZipper
