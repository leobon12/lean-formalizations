import SmallGammaGeodesics.NIC.Gram
import SmallGammaGeodesics.NIC.Binomial

/-!
# NIC, part 1 (T4): the square root of `G` and the polar part `U_τ`

Packet P-G1, target T4; GA2 D5 Step 5. With `D_G := G − 1` (`‖D_G‖ ≤ 6δ ≤ 3/8 < 1/2`):

* `sqrtG := ∑ binom(1/2, n) D_Gⁿ` and `invSqrtG := ∑ binom(−1/2, n) D_Gⁿ` (`NIC.binomOp`);
* `sqrtG² = G` (`sqrtG_mul_sqrtG`), `sqrtG · invSqrtG = invSqrtG · sqrtG = 1`;
* `sqrtG` and `invSqrtG` are self-adjoint;
* `‖sqrtG − 1‖ ≤ ‖G − 1‖` and `‖invSqrtG − 1‖ ≤ 2‖G − 1‖`;
* `G v = v → sqrtG v = v` (`sqrtG_apply_of_gram`); in particular `sqrtG (J ρ_χ) = J ρ_χ` for
  `χ` supported where `Ψ` is holomorphic (`sqrtG_jH_cmTest`);
* `polar := τ̃ · invSqrtG` is a linear isometry **onto** `H_*` (`polar : Hstar ≃ₗᵢ[ℝ] Hstar`;
  `‖τ̃ S⁻ v‖² = ⟪G S⁻ v, S⁻ v⟫ = ⟪S v, S⁻ v⟫ = ⟪v, S S⁻ v⟫ = ‖v‖²`), and `τ̃ = polar · sqrtG`
  (`tauH_eq_polar_sqrtG`);
* consequences used by part 2: `polar (J ρ_χ) = τ̃ (J ρ_χ) = J (τ ρ_χ)` (`polar_jH_cmTest`) and
  `‖τ̃ v − polar v‖ ≤ ‖G − 1‖ ‖v‖` (`norm_tauH_sub_polar_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric

namespace NearIdPair

variable (D : NearIdPair)

/-- `D_G := G − 1` -/
def gramDev : Hstar →L[ℝ] Hstar := D.gram - 1

lemma norm_gramDev_le : ‖D.gramDev‖ ≤ 6 * D.δ := D.norm_gram_sub_one_le'

lemma norm_gramDev_le_half : ‖D.gramDev‖ ≤ 1 / 2 :=
  D.norm_gramDev_le.trans (by linarith [D.δ_le])

lemma norm_gramDev_lt_one : ‖D.gramDev‖ < 1 := D.norm_gramDev_le_half.trans_lt (by norm_num)

lemma isSelfAdjoint_gramDev : IsSelfAdjoint D.gramDev := D.isSelfAdjoint_gram_sub_one

/-- the series of `S` is norm-convergent -/
lemma summable_norm_sqrtG_series :
    Summable fun n : ℕ => ‖Ring.choose (1 / 2 : ℝ) n • D.gramDev ^ n‖ :=
  summable_norm_binom abs_half_le_one D.norm_gramDev_lt_one

/-- the series of `S⁻` is norm-convergent -/
lemma summable_norm_invSqrtG_series :
    Summable fun n : ℕ => ‖Ring.choose (-1 / 2 : ℝ) n • D.gramDev ^ n‖ :=
  summable_norm_binom abs_neg_half_le_one D.norm_gramDev_lt_one

/-- **`S := G^{1/2} = ∑ binom(1/2, n) (G − 1)ⁿ`** -/
def sqrtG : Hstar →L[ℝ] Hstar := binomOp (1 / 2) D.gramDev

/-- **`S⁻ := G^{−1/2} = ∑ binom(−1/2, n) (G − 1)ⁿ`** -/
def invSqrtG : Hstar →L[ℝ] Hstar := binomOp (-1 / 2) D.gramDev

/-- **T4**: `S² = G` -/
theorem sqrtG_mul_sqrtG : D.sqrtG * D.sqrtG = D.gram := by
  rw [sqrtG, binomOp_half_mul_self D.norm_gramDev_lt_one, gramDev, add_sub_cancel]

/-- **T4**: `S S⁻ = 1` -/
theorem sqrtG_mul_invSqrtG : D.sqrtG * D.invSqrtG = 1 :=
  binomOp_half_mul_neg_half D.norm_gramDev_lt_one

/-- **T4**: `S⁻ S = 1` -/
theorem invSqrtG_mul_sqrtG : D.invSqrtG * D.sqrtG = 1 :=
  binomOp_neg_half_mul_half D.norm_gramDev_lt_one

/-- **T4**: `S` is self-adjoint -/
theorem isSelfAdjoint_sqrtG : IsSelfAdjoint D.sqrtG :=
  isSelfAdjoint_binomOp _ D.isSelfAdjoint_gramDev

theorem isSelfAdjoint_invSqrtG : IsSelfAdjoint D.invSqrtG :=
  isSelfAdjoint_binomOp _ D.isSelfAdjoint_gramDev

/-- **T4**: `‖S − 1‖ ≤ ‖G − 1‖` -/
theorem norm_sqrtG_sub_one_le : ‖D.sqrtG - 1‖ ≤ ‖D.gram - 1‖ :=
  norm_binomOp_half_sub_one_le D.norm_gramDev_le_half

theorem norm_invSqrtG_sub_one_le : ‖D.invSqrtG - 1‖ ≤ 2 * ‖D.gram - 1‖ :=
  norm_binomOp_neg_half_sub_one_le D.norm_gramDev_le_half

lemma gramDev_apply_of_gram {v : Hstar} (hv : D.gram v = v) : D.gramDev v = 0 := by
  rw [gramDev, sub_apply, hv, one_apply_eq_self, sub_self]

/-- **T4**: `D v = 0 → S v = v` for `D = G − 1` -/
theorem sqrtG_apply_of_gramDev {v : Hstar} (hv : D.gramDev v = 0) : D.sqrtG v = v :=
  binomOp_apply_of_eq_zero abs_half_le_one D.norm_gramDev_lt_one hv

/-- **T4**: `G v = v → S v = v` (i.e. `(G − 1) v = 0 → S v = v`) -/
theorem sqrtG_apply_of_gram {v : Hstar} (hv : D.gram v = v) : D.sqrtG v = v :=
  binomOp_apply_of_eq_zero abs_half_le_one D.norm_gramDev_lt_one (D.gramDev_apply_of_gram hv)

theorem invSqrtG_apply_of_gram {v : Hstar} (hv : D.gram v = v) : D.invSqrtG v = v :=
  binomOp_apply_of_eq_zero abs_neg_half_le_one D.norm_gramDev_lt_one (D.gramDev_apply_of_gram hv)

/-- `S (J ρ_χ) = J ρ_χ` on Green densities supported where `Ψ` is holomorphic -/
theorem sqrtG_jH_cmTest {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ D.Ψ U) (χ : TestC)
    (hχ : tsupport (χ : ℂ → ℝ) ⊆ U) : D.sqrtG (jH (cmTest0' χ)) = jH (cmTest0' χ) :=
  D.sqrtG_apply_of_gram (D.gram_jH_cmTest hU hΨ χ hχ)

/-! ## The polar part -/

/-- `U_τ := τ̃ S⁻` as a continuous linear map -/
def polarCLM : Hstar →L[ℝ] Hstar := (D.tauH : Hstar →L[ℝ] Hstar) * D.invSqrtG

lemma polarCLM_apply (v : Hstar) : D.polarCLM v = D.tauH (D.invSqrtG v) := rfl

lemma sqrtG_invSqrtG_apply (v : Hstar) : D.sqrtG (D.invSqrtG v) = v := by
  rw [← mul_apply_eq_comp, D.sqrtG_mul_invSqrtG, one_apply_eq_self]

lemma invSqrtG_sqrtG_apply (v : Hstar) : D.invSqrtG (D.sqrtG v) = v := by
  rw [← mul_apply_eq_comp, D.invSqrtG_mul_sqrtG, one_apply_eq_self]

/-- `‖U_τ v‖ = ‖v‖` -/
theorem norm_polarCLM (v : Hstar) : ‖D.polarCLM v‖ = ‖v‖ := by
  have h : ‖D.polarCLM v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [polarCLM_apply, ← inner_gram_self, ← D.sqrtG_mul_sqrtG, mul_apply_eq_comp,
      D.sqrtG_invSqrtG_apply, ← real_inner_self_eq_norm_sq]
    have hs := D.isSelfAdjoint_sqrtG.isSymmetric v (D.invSqrtG v)
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [hs, D.sqrtG_invSqrtG_apply]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem polarCLM_surjective : Function.Surjective D.polarCLM := fun w =>
  ⟨D.sqrtG (D.tauH.symm w), by
    rw [polarCLM_apply, D.invSqrtG_sqrtG_apply, ContinuousLinearEquiv.apply_symm_apply]⟩

/-- **T4**: the polar part `U_τ := τ̃ S⁻`, a linear isometry of `H_*` onto itself. -/
def polar : Hstar ≃ₗᵢ[ℝ] Hstar :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (D.polarCLM : Hstar →ₗ[ℝ] Hstar)
      norm_map' := D.norm_polarCLM }
    D.polarCLM_surjective

lemma polar_apply (v : Hstar) : D.polar v = D.tauH (D.invSqrtG v) := rfl

/-- **T4**: `τ̃ = U_τ S` -/
theorem tauH_eq_polar_sqrtG (v : Hstar) : D.tauH v = D.polar (D.sqrtG v) := by
  rw [polar_apply, D.invSqrtG_sqrtG_apply]

/-- `U_τ (J ρ_χ) = τ̃ (J ρ_χ) = J (τ ρ_χ)` on Green densities supported where `Ψ` is holomorphic -/
theorem polar_jH_cmTest {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ D.Ψ U) (χ : TestC)
    (hχ : tsupport (χ : ℂ → ℝ) ⊆ U) :
    D.polar (jH (cmTest0' χ)) = jH (D.transport0 (cmTest0' χ)) := by
  rw [← D.sqrtG_jH_cmTest hU hΨ χ hχ, ← tauH_eq_polar_sqrtG, tauH_jH]

/-- `τ̃ v − U_τ v = U_τ ((S − 1) v)`, so `‖τ̃ v − U_τ v‖ ≤ ‖G − 1‖ ‖v‖` -/
theorem norm_tauH_sub_polar_le (v : Hstar) :
    ‖D.tauH v - D.polar v‖ ≤ ‖D.gram - 1‖ * ‖v‖ := by
  rw [tauH_eq_polar_sqrtG, ← map_sub, LinearIsometryEquiv.norm_map]
  calc ‖D.sqrtG v - v‖ = ‖(D.sqrtG - 1) v‖ := by rw [sub_apply, one_apply_eq_self]
    _ ≤ ‖D.sqrtG - 1‖ * ‖v‖ := (D.sqrtG - 1).le_opNorm v
    _ ≤ ‖D.gram - 1‖ * ‖v‖ := mul_le_mul_of_nonneg_right D.norm_sqrtG_sub_one_le (norm_nonneg _)

end NearIdPair

/-- **T4 in the packet's form**: for `CC.IsNearIdDiffeo Φ Ψ U ε`, `0 ≤ ε ≤ 1/32`,
`‖G − 1‖ ≤ 12ε ≤ 1/2` and `‖S − 1‖ ≤ 12ε`. -/
theorem norm_sqrtG_sub_one_le_ofDiffeo {Φ Ψ : ℂ → ℂ} {U : Set ℂ} {ε : ℝ}
    (hΦ : CC.IsNearIdDiffeo Φ Ψ U ε) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 32) :
    ‖(NearIdPair.ofDiffeo hΦ hε0 hε).sqrtG - 1‖ ≤ 12 * ε :=
  (NearIdPair.ofDiffeo hΦ hε0 hε).norm_sqrtG_sub_one_le.trans
    (norm_gram_sub_one_le_ofDiffeo hΦ hε0 hε)

end NIC
end SmallGammaGeodesics
