import HigherDimLQGMetric.Kernel.ConvKernelDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Near-zero derivatives of the square-root symbol

This is the derivative estimate in MA5 A2.4. The proof rescales to the unit
sphere and applies the general iterated composition bound with a fractional
scale factor common to all derivative orders up to `n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- A2.4 derivative bound at a scaled unit vector. -/
theorem kernelSymbol_iteratedFDeriv_scaled_near_zero (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, ∀ (r : ℝ) (u : Rd d), 0 < r → r ≤ 1 → ‖u‖ = 1 →
      |‖r • u‖ ^ d * symbolAux κ (r • u)| ≤ 1 / 2 →
      r ^ n * ‖iteratedFDeriv ℝ n (kernelSymbol κ) (r • u)‖ ≤ C * r ^ d := by
  obtain ⟨A, hA, hAi⟩ := symbolPerturb_scaled_deriv_bounded hκ n
  obtain ⟨B, hB, hBi⟩ := sqrt_one_sub_deriv_bounded n
  let C : ℝ := (n.factorial : ℝ) * B * A ^ n
  refine ⟨C, fun r u hr hr1 hu hp0 => ?_⟩
  let p : Rd d → ℝ := fun z => ‖z‖ ^ d * symbolAux κ z
  let q : Rd d → ℝ := fun y => p (r • y)
  let φ : ℝ → ℝ := fun t => Real.sqrt (1 - t)
  let s : Set (Rd d) := ({0}ᶜ : Set (Rd d)) ∩ q ⁻¹' Iio 1
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hru0 : r • u ≠ 0 := smul_ne_zero hr.ne' hu0
  have hpcont : Continuous p := (continuous_norm.pow d).mul (symbolAux_contDiff hκ).continuous
  have hscaleCont : Continuous (fun y : Rd d => r • y) :=
    (continuous_const : Continuous (fun _ : Rd d => r)).smul continuous_id
  have hqcont : Continuous q := hpcont.comp hscaleCont
  have hsopen : IsOpen s := isClosed_singleton.isOpen_compl.inter (isOpen_Iio.preimage hqcont)
  have huS : u ∈ s := by
    refine ⟨hu0, ?_⟩
    have : |q u| ≤ 1 / 2 := hp0
    have hle : q u ≤ 1 / 2 := le_trans (le_abs_self _) this
    exact lt_of_le_of_lt hle (by norm_num)
  have hpSmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p ({0}ᶜ : Set (Rd d)) := by
    intro z hz
    exact (((contDiffAt_norm ℝ (show z ≠ 0 from hz)).pow d).mul
      (symbolAux_contDiff hκ).contDiffAt).contDiffWithinAt
  have hqSmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q s := by
    intro y hy
    have hy0 : r • y ≠ 0 := smul_ne_zero hr.ne' hy.1
    have hpa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p (r • y) :=
      hpSmooth.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hy0)
    exact (hpa.comp y (contDiff_id.const_smul r).contDiffAt).contDiffWithinAt
  have hmap : MapsTo q s (Iio 1) := fun y hy => hy.2
  let D : ℝ := A * r ^ ((d : ℝ) / (n : ℝ))
  have houter : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i φ (Iio 1) (q u)‖ ≤ B := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Iio huS.2]
    exact hBi i hi (q u) hp0
  have hinner : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i q s u‖ ≤ D ^ i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hsopen huS]
    exact (hAi i hin r u hr hr1 hu).trans
      (scale_factor_bound hn hi hin hA hr hr1)
  have hc := norm_iteratedFDerivWithin_comp_le sqrt_one_sub_contDiffOn hqSmooth
    (by simp : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)) isOpen_Iio.uniqueDiffOn
    hsopen.uniqueDiffOn hmap huS houter hinner
  rw [iteratedFDerivWithin_of_isOpen n hsopen huS] at hc
  have hpow : D ^ n = A ^ n * r ^ d := by
    simp only [D, mul_pow]
    rw [← Real.rpow_mul_natCast (le_of_lt hr)]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have he : (d : ℝ) / (n : ℝ) * (n : ℝ) = d := by field_simp
    rw [he, Real.rpow_natCast]
  rw [hpow] at hc
  have heq : (φ ∘ q) = fun y : Rd d => kernelSymbol κ (r • y) := by
    funext y
    change Real.sqrt (1 - (‖r • y‖ ^ d * symbolAux κ (r • y))) =
      kernelSymbol κ (r • y)
    rw [kernelSymbol_eq_sqrt_symbolSq,
      kernelSymbol_sq_eq_one_sub_pow_aux hd hκ]
  rw [heq] at hc
  have hscale := congrFun (iteratedFDeriv_comp_const_smul_any r (kernelSymbol κ) n) u
  rw [hscale] at hc
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _), C,
    mul_assoc, mul_comm, mul_left_comm] using hc

/-- A2.4 weighted derivative bound on a punctured neighborhood of zero. -/
theorem kernelSymbol_iteratedFDeriv_near_zero (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) (hn : 0 < n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ C : ℝ, ∀ ζ : Rd d,
      ζ ≠ 0 → ‖ζ‖ < ρ →
      ‖ζ‖ ^ n * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤ C * ‖ζ‖ ^ d := by
  obtain ⟨ρ, hρ, hρ1, hsmall⟩ := symbolAux_small_near_zero hd hκ
  obtain ⟨C, hC⟩ := kernelSymbol_iteratedFDeriv_scaled_near_zero hd hκ n hn
  refine ⟨ρ, hρ, hρ1, C, fun ζ hζ hζρ => ?_⟩
  let r : ℝ := ‖ζ‖
  have hr : 0 < r := norm_pos_iff.mpr hζ
  let u : Rd d := r⁻¹ • ζ
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, r, inv_mul_cancel₀ hr.ne']
  have hru : r • u = ζ := by simp [u, smul_smul, mul_inv_cancel₀ hr.ne']
  have hp0 : |‖r • u‖ ^ d * symbolAux κ (r • u)| ≤ 1 / 2 := by
    rw [hru]
    exact hsmall ζ hζρ
  have h := hC r u hr (le_trans (le_of_lt hζρ) hρ1) hu hp0
  rw [hru] at h
  exact h

end HigherDimLQGMetric
