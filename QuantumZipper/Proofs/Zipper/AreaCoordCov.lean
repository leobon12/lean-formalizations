import QuantumZipper.Proofs.Zipper.AreaCoord
import QuantumZipper.Proofs.Analysis.Pushforward

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AREA-COORD (3): the merging differences in the unzipped coordinates (deterministic)

First step of the fixed-time input `E6.WedgeAreaMergeFixStmt` (`AreaCoord.lean`): the change of
variables `w = f̂_t(z)` (`f̂_t = fwdMapInv W t : ℍ → ℍ \ K_t`, real Jacobian `‖f̂_t'‖²`) turns the
merging difference into one integral over `ℍ` against the test function:

  `mergeDiff γ x W f t k = ∫_ℍ ρ^{x_t}_k(z) f(z) dz − ∫_ℍ ‖f̂_t'(z)‖² ρ^x_k(f̂_t z) f(z) dz`

(`mergeDiff_eq_setIntegral`), where `ρ^y_k(z) = 2^{-kγ²/2} e^{γ avgReg y k z}` is the density of
`areaApprox γ y k` on `ℍ` (`areaDensK`). This is the computation of Sheffield–Wang,
arXiv:1605.06171, proof of Thm 1.4, p. 12 (the display after (3.5), turning (3.5) into the
integrals over `S` compared in (3.6)/(3.7)), for `φ = f̂_t`. The change of variables is mathlib's
`integral_image_eq_integral_abs_det_fderiv_smul` with the Jacobian `‖φ'‖²`
(`QuantumZipper.abs_det_fderiv_eq_normSq`). Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

/-- The density of `areaApprox γ y k` with respect to Lebesgue measure on `ℍ`. -/
def areaDensK (γ : ℝ) (y : FieldSample) (k : ℕ) (z : ℂ) : ℝ :=
  radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z)

theorem areaDensK_nonneg (γ : ℝ) (y : FieldSample) (k : ℕ) (z : ℂ) : 0 ≤ areaDensK γ y k z :=
  mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le

theorem measurable_areaDensK (γ : ℝ) (y : FieldSample) (k : ℕ) :
    Measurable (areaDensK γ y k) := by
  have h : Measurable fun z : ℂ => avgReg y k z :=
    (measurable_avgReg k).comp measurable_prodMk_left
  exact (Real.measurable_exp.comp (h.const_mul γ)).const_mul _

/-- Integrals against `areaApprox` are integrals over `ℍ` against its density. -/
theorem integral_areaApprox_eq (γ : ℝ) (y : FieldSample) (k : ℕ) (g : ℂ → ℝ) :
    ∫ z, g z ∂(areaApprox γ y k) = ∫ z in H, areaDensK γ y k z * g z := by
  show ∫ z, g z ∂((volume.restrict H).withDensity fun z => ENNReal.ofReal (areaDensK γ y k z)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_areaDensK γ y k).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (areaDensK_nonneg γ y k z)]

variable {W : ℝ → ℝ} {t : ℝ}

end QuantumZipper.E6
