import HigherDimLQGMetric.Kernel.ConvKernelDirectional
import HigherDimLQGMetric.Kernel.ConvKernelSmooth
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Spatial decay of the convolution kernel

Integration by parts along lines avoids the singularity of high-order symbol derivatives at
the origin. Since those derivatives are integrable for orders below `2d`, the Fourier transform
decays with every such order. In particular the inverse transform defining `convKernel` decays
at order `d+1` and is integrable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Complex MeasureTheory Set
open scoped FourierTransform Real
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- The negative-sign Fourier character at frequency `x`. -/
def fourierPhase (x ζ : Rd d) : ℂ := (𝐞 (-(innerSL ℝ ζ x)) : ℂ)

private theorem fourierPhase_norm (x ζ : Rd d) : ‖fourierPhase x ζ‖ = 1 := by
  simp [fourierPhase]

private theorem fourierPhase_hasLineDerivAt (x v ζ : Rd d) :
    HasLineDerivAt ℝ (fourierPhase x)
      ((-2 * π * Complex.I * innerSL ℝ v x) * fourierPhase x ζ) ζ v := by
  have hd := Real.differentiable_fourierChar_neg_bilinear_left (innerSL ℝ) x ζ
  have h := hd.hasFDerivAt.hasLineDerivAt v
  have heq : fderiv ℝ (fourierPhase x) ζ v =
      (-2 * π * Complex.I * innerSL ℝ v x) * fourierPhase x ζ := by
    change (fderiv ℝ (fun z : Rd d => (𝐞 (-(innerSL ℝ z x)) : ℂ)) ζ) v =
      (-2 * π * Complex.I * innerSL ℝ v x) *
        (𝐞 (-(innerSL ℝ ζ x)) : ℂ)
    simpa only using
      Real.fderiv_fourierChar_neg_bilinear_left_apply (innerSL ℝ) ζ v x
  rw [← heq]
  exact h

private theorem integrable_fourierPhase_mul_directional (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (v x : Rd d) (n : ℕ)
    (hnd : n < 2 * d) :
    Integrable (fun ζ : Rd d => fourierPhase x ζ * directionalSymbol κ v n ζ) := by
  have hphase : AEStronglyMeasurable (fourierPhase x) volume := by
    apply Measurable.aestronglyMeasurable
    unfold fourierPhase
    fun_prop
  have hbound : ∀ᵐ ζ : Rd d ∂volume, ‖fourierPhase x ζ‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun ζ => le_of_eq (fourierPhase_norm x ζ))
  have h := (integrable_directionalSymbol hd hκ v n hnd).mul_bdd hphase hbound
  convert h using 1
  ext ζ
  exact mul_comm _ _

theorem directional_fourier_step (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (v x : Rd d) (hv : v ≠ 0)
    (n : ℕ) (hn : n + 1 < 2 * d) :
    (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v (n+1) ζ) =
      (2 * π * Complex.I * innerSL ℝ v x) *
        (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v n ζ) := by
  let c : ℂ := -2 * π * Complex.I * innerSL ℝ v x
  have h0 : Integrable (fun ζ : Rd d =>
      fourierPhase x ζ * directionalSymbol κ v n ζ) :=
    integrable_fourierPhase_mul_directional (by omega) hκ v x n (by omega)
  have h1 : Integrable (fun ζ : Rd d =>
      fourierPhase x ζ * directionalSymbol κ v (n+1) ζ) :=
    integrable_fourierPhase_mul_directional (by omega) hκ v x (n+1) hn
  have hp : Integrable (fun ζ : Rd d =>
      (c * fourierPhase x ζ) * directionalSymbol κ v n ζ) := by
    convert h0.const_mul c using 1
    ext ζ
    ring
  have hdim : 2 ≤ Module.finrank ℝ (Rd d) := by
    simpa only [finrank_euclideanSpace_fin] using hd
  have h := integral_bilinear_line_except_zero
    (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := fourierPhase x)
    (f' := fun ζ => c * fourierPhase x ζ)
    (g := directionalSymbol κ v n)
    (g' := directionalSymbol κ v (n+1))
    (v := v) (μ := volume)
    hdim hp h1 h0 hv
    (fun ζ => by simpa only [c] using fourierPhase_hasLineDerivAt x v ζ)
    (fun ζ hζ => directionalSymbol_hasLineDerivAt (by omega) hκ v n hζ)
  dsimp at h
  simp_rw [mul_assoc] at h
  rw [integral_const_mul] at h
  convert h using 1
  ring

private theorem directional_fourier_pow (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (v x : Rd d) (hv : v ≠ 0)
    (n : ℕ) (hn : n < 2 * d) :
    (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v n ζ) =
      (2 * π * Complex.I * innerSL ℝ v x) ^ n *
        (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v 0 ζ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [directional_fourier_step hd hκ v x hv n hn,
      ih (by omega), pow_succ]
    ring

private theorem directional_fourier_zero_eq (v x : Rd d) :
    (∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v 0 ζ) =
      𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x := by
  rw [Real.fourier_eq]
  congr 1

private theorem norm_directional_fourier_integral_le (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (v x : Rd d)
    (hv : ‖v‖ = 1) (n : ℕ) (hn : n < 2 * d) :
    ‖∫ ζ : Rd d, fourierPhase x ζ * directionalSymbol κ v n ζ‖ ≤
      ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ := by
  have hint : Integrable (fun ζ : Rd d =>
      ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖) := by
    simpa only [pow_zero, one_mul] using
      integrable_kernelSymbol_iteratedFDeriv_moment (by omega) hκ n 0 hn
  have hfn : Integrable (fun ζ : Rd d =>
      fourierPhase x ζ * directionalSymbol κ v n ζ) :=
    integrable_fourierPhase_mul_directional (by omega) hκ v x n hn
  calc
    _ ≤ ∫ ζ : Rd d, ‖fourierPhase x ζ * directionalSymbol κ v n ζ‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ζ : Rd d, ‖directionalSymbol κ v n ζ‖ := by
      congr 1
      funext ζ
      rw [norm_mul, fourierPhase_norm, one_mul]
    _ ≤ ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ := by
      apply integral_mono (integrable_directionalSymbol (by omega) hκ v n hn).norm hint
      intro ζ
      have hb := ContinuousMultilinearMap.le_opNorm
        (iteratedFDeriv ℝ n (kernelSymbol κ) ζ) (fun _ : Fin n => v)
      simpa only [directionalSymbol, Complex.norm_real, ← Real.norm_eq_abs,
        Finset.prod_const, Fintype.card_fin, hv, one_pow, mul_one] using hb

private theorem unitDirection_norm (x : Rd d) (hx : x ≠ 0) :
    ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp [norm_smul, hr]

private theorem inner_unitDirection (x : Rd d) (hx : x ≠ 0) :
    innerSL ℝ ((‖x‖⁻¹ : ℝ) • x) x = ‖x‖ := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [innerSL_apply_apply, real_inner_smul_left,
    real_inner_self_eq_norm_sq, sq]
  field_simp

private theorem fourier_symbol_pow_bound (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (v x : Rd d)
    (hv : ‖v‖ = 1) (n : ℕ) (hn : n < 2 * d) :
    ‖(2 * π * Complex.I * innerSL ℝ v x) ^ n‖ *
      ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
      ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ := by
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv
  have hpow := directional_fourier_pow hd hκ v x hv0 n hn
  rw [directional_fourier_zero_eq] at hpow
  have hnorm := norm_directional_fourier_integral_le hd hκ v x hv n hn
  rw [hpow, norm_mul] at hnorm
  exact hnorm

theorem fourier_symbol_spatial_pow_bound (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) (hn : n < 2 * d) :
    ∀ x : Rd d, x ≠ 0 →
      ‖x‖ ^ n * ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
        ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ := by
  intro x hx
  let v : Rd d := (‖x‖⁻¹ : ℝ) • x
  have hv : ‖v‖ = 1 := unitDirection_norm x hx
  have hi : innerSL ℝ v x = ‖x‖ := inner_unitDirection x hx
  have h := fourier_symbol_pow_bound hd hκ v x hv n hn
  rw [hi, norm_pow] at h
  have hcoef : ‖(2 * π * Complex.I * (‖x‖ : ℂ))‖ = 2 * π * ‖x‖ := by
    simp [Real.pi_pos.le, hx]
  rw [hcoef] at h
  have hle : ‖x‖ ^ n ≤ (2 * π * ‖x‖) ^ n := by
    apply pow_le_pow_left₀ (norm_nonneg x)
    have hp : 1 ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    nlinarith [norm_nonneg x]
  exact (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans h

private theorem fourier_symbol_basic_bound (x : Rd d) :
    ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
      ∫ ζ : Rd d, |kernelSymbol κ ζ| := by
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ (Rd d))
    (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x
  change ‖VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Rd d))
      (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
      ∫ ζ : Rd d, |kernelSymbol κ ζ|
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

theorem fourier_symbol_spatial_decay (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) (hn : n < 2 * d) :
    ∃ C : ℝ, ∀ x : Rd d,
      ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
        C * (1 + ‖x‖) ^ (-(n : ℝ)) := by
  let A : ℝ := ∫ ζ : Rd d, |kernelSymbol κ ζ|
  let B : ℝ := ∫ ζ : Rd d, ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖
  have hA : 0 ≤ A := integral_nonneg (fun _ => abs_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (fun _ => norm_nonneg _)
  let C : ℝ := 2 ^ n * (A + B)
  refine ⟨C, fun x => ?_⟩
  have hr : 0 < 1 + ‖x‖ := by positivity
  have hpow : (1 + ‖x‖) ^ n *
      ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤ C := by
    by_cases hx : ‖x‖ ≤ 1
    · have hle : (1 + ‖x‖) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
      calc
        _ ≤ (2 : ℝ) ^ n *
            ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ ≤ 2 ^ n * A :=
          mul_le_mul_of_nonneg_left (fourier_symbol_basic_bound x) (by positivity)
        _ ≤ C := by dsimp [C]; gcongr; linarith
    · have hx1 : 1 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
      have hx0 : x ≠ 0 := by
        intro he
        have : (1 : ℝ) ≤ 0 := by simpa [he] using hx1
        linarith
      have hle : (1 + ‖x‖) ^ n ≤ (2 * ‖x‖) ^ n := by gcongr; linarith
      calc
        _ ≤ (2 * ‖x‖) ^ n *
            ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)
        _ ≤ 2 ^ n * B := by
          rw [mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (fourier_symbol_spatial_pow_bound hd hκ n hn x hx0) (by positivity)
        _ ≤ C := by dsimp [C]; gcongr; linarith
  have h : ‖𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x‖ ≤
      C / (1 + ‖x‖) ^ n := by
    exact (le_div_iff₀ (pow_pos hr n)).mpr (by
      simpa only [mul_comm] using hpow)
  simpa only [Real.rpow_neg hr.le, Real.rpow_natCast, div_eq_mul_inv] using h

theorem convKernel_decay (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ C : ℝ, ∀ x : Rd d,
      |convKernel κ x| ≤ C * (1 + ‖x‖) ^ (-((d : ℝ) + 1)) := by
  obtain ⟨C, hC⟩ := fourier_symbol_spatial_decay hd hκ (d + 1) (by omega)
  refine ⟨C, fun x => ?_⟩
  have h := hC (-x)
  rw [norm_neg] at h
  have heq : (convKernel κ x : ℂ) =
      𝓕 (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) (-x) := by
    rw [convKernel_complex_eq_fourierInv]
    exact Real.fourierInv_eq_fourier_neg _ x
  rw [← heq] at h
  simpa only [Complex.norm_real, Nat.cast_add, Nat.cast_one, Real.norm_eq_abs] using h

theorem integrable_convKernel (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) : Integrable (convKernel κ) := by
  obtain ⟨C, hC⟩ := convKernel_decay hd hκ
  have hsource : Integrable (fun x : Rd d =>
      C * (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
    have hbase : Integrable (fun x : Rd d =>
        (1 + ‖x‖) ^ (-((d : ℝ) + 1))) := by
      apply integrable_one_add_norm (μ := volume)
      simp only [finrank_euclideanSpace_fin]
      norm_num
    exact hbase.const_mul C
  apply hsource.mono' (convKernel_contDiff (by omega) hκ).continuous.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using hC x

end HigherDimLQGMetric
