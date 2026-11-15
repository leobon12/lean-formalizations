import Mathlib.Analysis.InnerProductSpace.Laplacian
import QuantumZipper.Proofs.ItoLite.Dynkin
import QuantumZipper.Proofs.ItoLite.OptionalStopping
import InteractingSLE.Foundations.Brownian.Planar

/-!
# Dynkin's formula for planar Brownian motion

Packet GEO-BM of the geometry foundation (`planning/INFRA-GEO.md` §3, §4). Infrastructure
([RY] Revuz–Yor, Ch. VII §1; [Law05] Lawler, Ch. 2), not a frozen source-facing file.

For a planar Brownian motion `Z` (`IsPlanarBrownian 𝓕 Z P`) and `F : ℂ → ℝ` of class `C³` with
bounded first, second and third derivatives,

  `M_t = F(Z_t) − ∫₀ᵗ ½ ΔF(Z_r) dr`

is an `𝓕`-martingale (`IsPlanarBrownian.martingale_dynkin`). The proof uses no stochastic
integral; it is the two-dimensional version of QuantumZipper's `Dynkin.dynkin_additive` (whose
telescoping lemma `eq_of_step_bound` and Taylor bound `taylor2_bound` are reused): a second-order
Taylor expansion over `[a, a + h]`, the independence of `Z (a + h) − Z a` from `𝓕 a` with its
Gaussian moments (`E Δ = 0`, `E Δ_x² = E Δ_y² = h`, `E Δ_x Δ_y = 0`, `E |Δ|³ = O(h^{3/2})`), and
`E|Z_r − Z_a| = O(√h)` for the time integral give `|E[ξ (M_{a+h} − M_a)]| ≤ K h^{3/2}` for bounded
`𝓕 a`-measurable `ξ`; telescoping gives the martingale property.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal ENNReal Laplacian

namespace InteractingSLE

/-- The generator `½ Δ F` of planar Brownian motion. -/
def planarGen (F : ℂ → ℝ) (y : ℂ) : ℝ := (1 / 2) * Δ F y

namespace PlanarBM

open QuantumZipper.Dynkin (iteratedFDeriv_two_vec norm_fderiv_fderiv_apply_le taylor2_bound
  eq_of_step_bound abs_integral_le_of_split integrable_intervalIntegral_and_le
  measurable_integral_adapted)

/-! ### Algebra of the first and second derivatives on `ℂ ≅ ℝ²` -/

lemma eq_re_smul_add_im_smul (w : ℂ) : w = w.re • (1 : ℂ) + w.im • Complex.I := by
  apply Complex.ext <;> simp

lemma clm_apply_eq (L : ℂ →L[ℝ] ℝ) (w : ℂ) : L w = w.re * L 1 + w.im * L Complex.I := by
  conv_lhs => rw [eq_re_smul_add_im_smul w]
  simp only [map_add, map_smul, smul_eq_mul]

lemma bilin_apply_eq (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (w : ℂ) :
    B w w = w.re ^ 2 * B 1 1 + w.re * w.im * (B 1 Complex.I + B Complex.I 1)
      + w.im ^ 2 * B Complex.I Complex.I := by
  conv_lhs => rw [eq_re_smul_add_im_smul w]
  simp only [map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma planarGen_eq (F : ℂ → ℝ) (y : ℂ) :
    planarGen F y = (1 / 2) * (fderiv ℝ (fderiv ℝ F) y 1 1
      + fderiv ℝ (fderiv ℝ F) y Complex.I Complex.I) := by
  rw [planarGen, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_vec]

lemma abs_planarGen_le (F : ℂ → ℝ) (y : ℂ) : |planarGen F y| ≤ ‖iteratedFDeriv ℝ 2 F y‖ := by
  rw [planarGen, laplacian_eq_iteratedFDeriv_complexPlane]
  have h1 := QuantumZipper.Dynkin.abs_iteratedFDeriv_two_vec_le F y 1
  have h2 := QuantumZipper.Dynkin.abs_iteratedFDeriv_two_vec_le F y Complex.I
  simp only [norm_one, one_pow, mul_one, Complex.norm_I] at h1 h2
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := abs_add_le (iteratedFDeriv ℝ 2 F y ![1, 1])
    (iteratedFDeriv ℝ 2 F y ![Complex.I, Complex.I])
  linarith

lemma abs_planarGen_sub_le (F : ℂ → ℝ) (y z : ℂ) :
    |planarGen F y - planarGen F z| ≤ ‖iteratedFDeriv ℝ 2 F y - iteratedFDeriv ℝ 2 F z‖ := by
  rw [planarGen, planarGen, laplacian_eq_iteratedFDeriv_complexPlane]
  have h1 := QuantumZipper.Dynkin.abs_sub_apply_two_le (iteratedFDeriv ℝ 2 F y)
    (iteratedFDeriv ℝ 2 F z) 1
  have h2 := QuantumZipper.Dynkin.abs_sub_apply_two_le (iteratedFDeriv ℝ 2 F y)
    (iteratedFDeriv ℝ 2 F z) Complex.I
  simp only [norm_one, one_pow, mul_one, Complex.norm_I] at h1 h2
  have : (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 F y ![1, 1]
      + iteratedFDeriv ℝ 2 F y ![Complex.I, Complex.I]) - (1 / 2) * (iteratedFDeriv ℝ 2 F z ![1, 1]
      + iteratedFDeriv ℝ 2 F z ![Complex.I, Complex.I])
      = (1 / 2) * ((iteratedFDeriv ℝ 2 F y ![1, 1] - iteratedFDeriv ℝ 2 F z ![1, 1])
        + (iteratedFDeriv ℝ 2 F y ![Complex.I, Complex.I]
          - iteratedFDeriv ℝ 2 F z ![Complex.I, Complex.I])) := by ring
  rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := abs_add_le (iteratedFDeriv ℝ 2 F y ![1, 1] - iteratedFDeriv ℝ 2 F z ![1, 1])
    (iteratedFDeriv ℝ 2 F y ![Complex.I, Complex.I] - iteratedFDeriv ℝ 2 F z ![Complex.I, Complex.I])
  linarith

lemma continuous_planarGen {F : ℂ → ℝ} (hF : ContDiff ℝ 3 F) : Continuous (planarGen F) := by
  have h1 := QuantumZipper.Dynkin.continuous_iteratedFDeriv_two_vec hF 1
  have h2 := QuantumZipper.Dynkin.continuous_iteratedFDeriv_two_vec hF Complex.I
  have : planarGen F = fun y => (1 / 2) * (iteratedFDeriv ℝ 2 F y ![1, 1]
      + iteratedFDeriv ℝ 2 F y ![Complex.I, Complex.I]) := by
    funext y; rw [planarGen, laplacian_eq_iteratedFDeriv_complexPlane]
  rw [this]
  fun_prop

lemma abs_fderiv_apply_le {F : ℂ → ℝ} {C : ℝ} {y : ℂ} (hD1 : ‖fderiv ℝ F y‖ ≤ C) {v : ℂ} (hv : ‖v‖ = 1) :
    |fderiv ℝ F y v| ≤ C := by
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ F y v‖ ≤ ‖fderiv ℝ F y‖ * ‖v‖ := (fderiv ℝ F y).le_opNorm v
    _ ≤ C := by rw [hv, mul_one]; exact hD1

lemma abs_fderiv_fderiv_apply_le {F : ℂ → ℝ} {C : ℝ} {y : ℂ}
    (hD2 : ‖iteratedFDeriv ℝ 2 F y‖ ≤ C) {v w : ℂ} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    |fderiv ℝ (fderiv ℝ F) y v w| ≤ C := by
  rw [← Real.norm_eq_abs]
  have := norm_fderiv_fderiv_apply_le F y v w
  rw [hv, hw, mul_one, mul_one] at this
  exact this.trans hD2

/-- The deterministic one-step identity behind Dynkin's formula: along a continuous path `γ`, the
increment of `F(γ_t) − ∫₀ᵗ ½ΔF(γ_r) dr` over `[a, a + h]`, minus its first-order part and its
centred second-order part, is bounded by the Taylor remainder and the oscillation of the
generator. -/
lemma pathwise_step {F : ℂ → ℝ} (hF : ContDiff ℝ 3 F) {C : ℝ} (hC0 : 0 ≤ C)
    (hLip2 : ∀ y z, ‖iteratedFDeriv ℝ 2 F y - iteratedFDeriv ℝ 2 F z‖ ≤ C * ‖y - z‖)
    {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (a h : ℝ≥0) {x : ℝ} (hx : |x| ≤ 1) :
    |x * ((F (γ (a + h)) - ∫ r in (0 : ℝ)..((a + h : ℝ≥0) : ℝ), planarGen F (γ r.toNNReal))
        - (F (γ a) - ∫ r in (0 : ℝ)..(a : ℝ), planarGen F (γ r.toNNReal)))
      - x * ((γ (a + h) - γ a).re * fderiv ℝ F (γ a) 1
          + (γ (a + h) - γ a).im * fderiv ℝ F (γ a) Complex.I)
      - x * ((1 / 2) * fderiv ℝ (fderiv ℝ F) (γ a) 1 1 * ((γ (a + h) - γ a).re ^ 2 - h)
          + (1 / 2) * (fderiv ℝ (fderiv ℝ F) (γ a) 1 Complex.I
              + fderiv ℝ (fderiv ℝ F) (γ a) Complex.I 1)
            * ((γ (a + h) - γ a).re * (γ (a + h) - γ a).im)
          + (1 / 2) * fderiv ℝ (fderiv ℝ F) (γ a) Complex.I Complex.I
            * ((γ (a + h) - γ a).im ^ 2 - h))|
      ≤ C * ‖γ (a + h) - γ a‖ ^ 3
        + ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), C * ‖γ r.toNNReal - γ a‖ := by
  set Y := γ a with hY
  set w := γ (a + h) - γ a with hw
  set g : ℝ → ℝ := fun r => planarGen F (γ r.toNNReal) with hg
  have hgc : Continuous g := (continuous_planarGen hF).comp (hγ.comp continuous_real_toNNReal)
  have hah : (a : ℝ) ≤ ((a + h : ℝ≥0) : ℝ) := by push_cast; linarith [h.coe_nonneg]
  have hlen : ((a + h : ℝ≥0) : ℝ) - a = h := by push_cast; ring
  -- the time integral over `[a, a + h]`
  have hsub : (∫ r in (0 : ℝ)..((a + h : ℝ≥0) : ℝ), g r) - ∫ r in (0 : ℝ)..(a : ℝ), g r
      = ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), g r :=
    intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)
  have hsplit : ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), g r
      = h * planarGen F Y + ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), (g r - planarGen F Y) := by
    rw [intervalIntegral.integral_sub (hgc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, hlen, smul_eq_mul]
    ring
  have hosc : |∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), (g r - planarGen F Y)|
      ≤ ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), C * ‖γ r.toNNReal - Y‖ := by
    refine (intervalIntegral.abs_integral_le_integral_abs hah).trans ?_
    refine intervalIntegral.integral_mono_on hah ((hgc.sub continuous_const).abs.intervalIntegrable _ _)
      ((continuous_const.mul ((hγ.comp continuous_real_toNNReal).sub continuous_const).norm
        ).intervalIntegrable _ _) fun r _ => ?_
    exact (abs_planarGen_sub_le F _ _).trans (hLip2 _ _)
  -- Taylor expansion of `F` at `Y`
  have htay := taylor2_bound hF hC0 hLip2 Y w
  have hYw : Y + w = γ (a + h) := by rw [hY, hw]; ring
  rw [hYw, iteratedFDeriv_two_vec, bilin_apply_eq] at htay
  rw [clm_apply_eq (fderiv ℝ F Y) w] at htay
  have hgenY := planarGen_eq F Y
  -- assemble
  have hkey : x * ((F (γ (a + h)) - ∫ r in (0 : ℝ)..((a + h : ℝ≥0) : ℝ), g r)
        - (F Y - ∫ r in (0 : ℝ)..(a : ℝ), g r))
      - x * (w.re * fderiv ℝ F Y 1 + w.im * fderiv ℝ F Y Complex.I)
      - x * ((1 / 2) * fderiv ℝ (fderiv ℝ F) Y 1 1 * (w.re ^ 2 - h)
          + (1 / 2) * (fderiv ℝ (fderiv ℝ F) Y 1 Complex.I
              + fderiv ℝ (fderiv ℝ F) Y Complex.I 1) * (w.re * w.im)
          + (1 / 2) * fderiv ℝ (fderiv ℝ F) Y Complex.I Complex.I * (w.im ^ 2 - h))
      = x * ((F (γ (a + h)) - F Y - (w.re * fderiv ℝ F Y 1 + w.im * fderiv ℝ F Y Complex.I)
          - 1 / 2 * (w.re ^ 2 * fderiv ℝ (fderiv ℝ F) Y 1 1
            + w.re * w.im * (fderiv ℝ (fderiv ℝ F) Y 1 Complex.I
              + fderiv ℝ (fderiv ℝ F) Y Complex.I 1)
            + w.im ^ 2 * fderiv ℝ (fderiv ℝ F) Y Complex.I Complex.I))
          - ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), (g r - planarGen F Y)) := by
    have e1 : (F (γ (a + h)) - ∫ r in (0 : ℝ)..((a + h : ℝ≥0) : ℝ), g r)
        - (F Y - ∫ r in (0 : ℝ)..(a : ℝ), g r)
        = F (γ (a + h)) - F Y - ((∫ r in (0 : ℝ)..((a + h : ℝ≥0) : ℝ), g r)
          - ∫ r in (0 : ℝ)..(a : ℝ), g r) := by ring
    rw [e1, hsub, hsplit, hgenY]
    ring
  rw [hkey, abs_mul]
  have hR := htay
  calc |x| * |F (γ (a + h)) - F Y - (w.re * fderiv ℝ F Y 1 + w.im * fderiv ℝ F Y Complex.I)
          - 1 / 2 * (w.re ^ 2 * fderiv ℝ (fderiv ℝ F) Y 1 1
            + w.re * w.im * (fderiv ℝ (fderiv ℝ F) Y 1 Complex.I
              + fderiv ℝ (fderiv ℝ F) Y Complex.I 1)
            + w.im ^ 2 * fderiv ℝ (fderiv ℝ F) Y Complex.I Complex.I)
          - ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), (g r - planarGen F Y)|
      ≤ 1 * (C * ‖w‖ ^ 3 + ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), C * ‖γ r.toNNReal - Y‖) := by
        refine mul_le_mul hx ((abs_sub _ _).trans (add_le_add hR hosc)) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

end PlanarBM

namespace IsPlanarBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ}
  {P : Measure Ω}

open PlanarBM
open QuantumZipper.Dynkin (eq_of_step_bound abs_integral_le_of_split
  integrable_intervalIntegral_and_le measurable_integral_adapted)

lemma integrable_mul_comp_sub (hZ : IsPlanarBrownian 𝓕 Z P) {a h : ℝ≥0} {G : Ω → ℝ}
    (hG : Measurable[𝓕 a] G) {K : ℝ} (hGb : ∀ ω, |G ω| ≤ K) {φ : ℂ → ℝ}
    (hφ : Integrable φ (planarGaussian h)) :
    Integrable (fun ω => G ω * φ (Z (a + h) ω - Z a ω)) P := by
  have hi := hZ.integrable_comp_sub (le_self_add : a ≤ a + h) (φ := φ)
    (by rwa [add_tsub_cancel_left])
  exact hi.bdd_mul (hG.mono (𝓕.le a) le_rfl).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb ω)

lemma integral_mul_comp_sub_eq_zero (hZ : IsPlanarBrownian 𝓕 Z P) {a h : ℝ≥0} {G : Ω → ℝ}
    (hG : Measurable[𝓕 a] G) {φ : ℂ → ℝ} (hφ : Measurable φ)
    (hφ0 : ∫ w, φ w ∂(planarGaussian h) = 0) :
    ∫ ω, G ω * φ (Z (a + h) ω - Z a ω) ∂P = 0 := by
  rw [hZ.integral_mul_comp_sub hG hφ, hφ0, mul_zero]

lemma integral_re_sq_sub_planarGaussian (h : ℝ≥0) :
    ∫ w, (w.re ^ 2 - h) ∂(planarGaussian h) = 0 := by
  rw [integral_sub (integrable_re_sq_planarGaussian h) (integrable_const _),
    integral_re_sq_planarGaussian, integral_const, probReal_univ, one_smul, sub_self]

lemma integral_im_sq_sub_planarGaussian (h : ℝ≥0) :
    ∫ w, (w.im ^ 2 - h) ∂(planarGaussian h) = 0 := by
  rw [integral_sub (integrable_im_sq_planarGaussian h) (integrable_const _),
    integral_im_sq_planarGaussian, integral_const, probReal_univ, one_smul, sub_self]

/-- The one-step estimate: `|E[ξ (M_{a+h} − M_a)]| ≤ K h^{3/2}` for `𝓕 a`-measurable `|ξ| ≤ 1`. -/
theorem step_bound (hZ : IsPlanarBrownian 𝓕 Z P) {F : ℂ → ℝ} (hF : ContDiff ℝ 3 F) {C : ℝ}
    (hC0 : 0 ≤ C) (hD1 : ∀ y, ‖fderiv ℝ F y‖ ≤ C) (hD2 : ∀ y, ‖iteratedFDeriv ℝ 2 F y‖ ≤ C)
    (hLip2 : ∀ y z, ‖iteratedFDeriv ℝ 2 F y - iteratedFDeriv ℝ 2 F z‖ ≤ C * ‖y - z‖)
    {M : ℝ≥0 → Ω → ℝ}
    (hM : ∀ t ω, M t ω = F (Z t ω) - ∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω))
    (hMint : ∀ t, Integrable (M t) P) (a h : ℝ≥0) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 a] ξ)
    (hξb : ∀ ω, |ξ ω| ≤ 1) :
    |∫ ω, ξ ω * (M (a + h) ω - M a ω) ∂P|
      ≤ (8 * C * QuantumZipper.gaussianAbsMoment 3 + 2 * C * QuantumZipper.gaussianAbsMoment 1)
        * ((h : ℝ) * Real.sqrt h) := by
  have hP := hZ.isProbabilityMeasure
  set m1 := QuantumZipper.gaussianAbsMoment 1 with hm1def
  set m3 := QuantumZipper.gaussianAbsMoment 3 with hm3def
  have hm1 : 0 ≤ m1 := QuantumZipper.gaussianAbsMoment_nonneg 1
  have hh0 : (0 : ℝ) ≤ h := h.coe_nonneg
  have hF2 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hD1c : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ F)) := hF2.continuous_fderiv (by norm_num)
  have hZa : Measurable[𝓕 a] (Z a) := hZ.measurable a
  have hcoef1 : ∀ v : ℂ, Measurable[𝓕 a] (fun ω => fderiv ℝ F (Z a ω) v) := fun v =>
    (hD1c.clm_apply continuous_const).measurable.comp hZa
  have hcoef2 : ∀ v w : ℂ, Measurable[𝓕 a] (fun ω => fderiv ℝ (fderiv ℝ F) (Z a ω) v w) :=
    fun v w => ((hD2c.clm_apply continuous_const).clm_apply continuous_const).measurable.comp hZa
  have hn1 : ‖(1 : ℂ)‖ = 1 := norm_one
  have hnI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hb1 : ∀ ω (v : ℂ), ‖v‖ = 1 → |fderiv ℝ F (Z a ω) v| ≤ C := fun ω v hv =>
    abs_fderiv_apply_le (hD1 _) hv
  have hb2 : ∀ ω (v w : ℂ), ‖v‖ = 1 → ‖w‖ = 1 → |fderiv ℝ (fderiv ℝ F) (Z a ω) v w| ≤ C :=
    fun ω v w hv hw => abs_fderiv_fderiv_apply_le (hD2 _) hv hw
  -- coefficients and centred terms
  set c1 : Ω → ℝ := fun ω => ξ ω * fderiv ℝ F (Z a ω) 1 with hc1
  set c2 : Ω → ℝ := fun ω => ξ ω * fderiv ℝ F (Z a ω) Complex.I with hc2
  set c3 : Ω → ℝ := fun ω => ξ ω * ((1 / 2) * fderiv ℝ (fderiv ℝ F) (Z a ω) 1 1) with hc3
  set c4 : Ω → ℝ := fun ω => ξ ω * ((1 / 2) * (fderiv ℝ (fderiv ℝ F) (Z a ω) 1 Complex.I
    + fderiv ℝ (fderiv ℝ F) (Z a ω) Complex.I 1)) with hc4
  set c5 : Ω → ℝ := fun ω => ξ ω * ((1 / 2) * fderiv ℝ (fderiv ℝ F) (Z a ω) Complex.I Complex.I)
    with hc5
  have hξabs : ∀ ω, |ξ ω| ≤ 1 := hξb
  have hc1m : Measurable[𝓕 a] c1 := hξ.mul (hcoef1 1)
  have hc2m : Measurable[𝓕 a] c2 := hξ.mul (hcoef1 _)
  have hc3m : Measurable[𝓕 a] c3 := hξ.mul (measurable_const.mul (hcoef2 1 1))
  have hc4m : Measurable[𝓕 a] c4 :=
    hξ.mul (measurable_const.mul ((hcoef2 1 Complex.I).add (hcoef2 Complex.I 1)))
  have hc5m : Measurable[𝓕 a] c5 := hξ.mul (measurable_const.mul (hcoef2 _ _))
  have hmulb : ∀ {u v B : ℝ}, |u| ≤ 1 → |v| ≤ B → |u * v| ≤ B := fun {u v B} hu hv => by
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg v) hu).trans hv
  have hc1b : ∀ ω, |c1 ω| ≤ C := fun ω => hmulb (hξabs ω) (hb1 ω 1 hn1)
  have hc2b : ∀ ω, |c2 ω| ≤ C := fun ω => hmulb (hξabs ω) (hb1 ω _ hnI)
  have hc3b : ∀ ω, |c3 ω| ≤ C := fun ω => hmulb (hξabs ω) (by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith [hb2 ω 1 1 hn1 hn1])
  have hc4b : ∀ ω, |c4 ω| ≤ C := fun ω => hmulb (hξabs ω) (by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [abs_add_le (fderiv ℝ (fderiv ℝ F) (Z a ω) 1 Complex.I)
      (fderiv ℝ (fderiv ℝ F) (Z a ω) Complex.I 1), hb2 ω 1 _ hn1 hnI, hb2 ω _ 1 hnI hn1])
  have hc5b : ∀ ω, |c5 ω| ≤ C := fun ω => hmulb (hξabs ω) (by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith [hb2 ω _ _ hnI hnI])
  set Dz : Ω → ℂ := fun ω => Z (a + h) ω - Z a ω with hDz
  set W2 : Ω → ℝ := fun ω => c1 ω * (Dz ω).re + c2 ω * (Dz ω).im with hW2
  set W3 : Ω → ℝ := fun ω => c3 ω * ((Dz ω).re ^ 2 - h) + c4 ω * ((Dz ω).re * (Dz ω).im)
    + c5 ω * ((Dz ω).im ^ 2 - h) with hW3
  have hre : Measurable (fun w : ℂ => w.re) := Complex.measurable_re
  have him : Measurable (fun w : ℂ => w.im) := Complex.measurable_im
  have i1 : Integrable (fun ω => c1 ω * (Dz ω).re) P :=
    hZ.integrable_mul_comp_sub hc1m hc1b (φ := fun w => w.re) (integrable_re_planarGaussian h)
  have i2 : Integrable (fun ω => c2 ω * (Dz ω).im) P :=
    hZ.integrable_mul_comp_sub hc2m hc2b (φ := fun w => w.im) (integrable_im_planarGaussian h)
  have i3 : Integrable (fun ω => c3 ω * ((Dz ω).re ^ 2 - h)) P :=
    hZ.integrable_mul_comp_sub hc3m hc3b (φ := fun w => w.re ^ 2 - h)
      ((integrable_re_sq_planarGaussian h).sub (integrable_const (h : ℝ)))
  have i4 : Integrable (fun ω => c4 ω * ((Dz ω).re * (Dz ω).im)) P :=
    hZ.integrable_mul_comp_sub hc4m hc4b (φ := fun w => w.re * w.im)
      (integrable_re_mul_im_planarGaussian h)
  have i5 : Integrable (fun ω => c5 ω * ((Dz ω).im ^ 2 - h)) P :=
    hZ.integrable_mul_comp_sub hc5m hc5b (φ := fun w => w.im ^ 2 - h)
      ((integrable_im_sq_planarGaussian h).sub (integrable_const (h : ℝ)))
  have z1 : ∫ ω, c1 ω * (Dz ω).re ∂P = 0 :=
    hZ.integral_mul_comp_sub_eq_zero hc1m (φ := fun w => w.re) hre (integral_re_planarGaussian h)
  have z2 : ∫ ω, c2 ω * (Dz ω).im ∂P = 0 :=
    hZ.integral_mul_comp_sub_eq_zero hc2m (φ := fun w => w.im) him (integral_im_planarGaussian h)
  have z3 : ∫ ω, c3 ω * ((Dz ω).re ^ 2 - h) ∂P = 0 :=
    hZ.integral_mul_comp_sub_eq_zero hc3m (φ := fun w => w.re ^ 2 - h)
      ((hre.pow_const 2).sub measurable_const) (integral_re_sq_sub_planarGaussian h)
  have z4 : ∫ ω, c4 ω * ((Dz ω).re * (Dz ω).im) ∂P = 0 :=
    hZ.integral_mul_comp_sub_eq_zero hc4m (φ := fun w => w.re * w.im) (hre.mul him)
      (integral_re_mul_im_planarGaussian h)
  have z5 : ∫ ω, c5 ω * ((Dz ω).im ^ 2 - h) ∂P = 0 :=
    hZ.integral_mul_comp_sub_eq_zero hc5m (φ := fun w => w.im ^ 2 - h)
      ((him.pow_const 2).sub measurable_const) (integral_im_sq_sub_planarGaussian h)
  have hW2i : Integrable W2 P := i1.add i2
  have hW3i : Integrable W3 P := (i3.add i4).add i5
  have hW2z : ∫ ω, W2 ω ∂P = 0 := by
    show ∫ ω, (c1 ω * (Dz ω).re + c2 ω * (Dz ω).im) ∂P = 0
    rw [integral_add i1 i2, z1, z2, add_zero]
  have hW3z : ∫ ω, W3 ω ∂P = 0 := by
    show ∫ ω, (c3 ω * ((Dz ω).re ^ 2 - h) + c4 ω * ((Dz ω).re * (Dz ω).im)
      + c5 ω * ((Dz ω).im ^ 2 - h)) ∂P = 0
    have i34 : Integrable (fun ω => c3 ω * ((Dz ω).re ^ 2 - h) + c4 ω * ((Dz ω).re * (Dz ω).im)) P :=
      i3.add i4
    rw [integral_add i34 i5, integral_add i3 i4, z3, z4, z5]; norm_num
  -- the dominating function
  set g : ℝ → Ω → ℝ := fun r ω => C * ‖Z r.toNNReal ω - Z a ω‖ with hg
  have hah : (a : ℝ) ≤ ((a + h : ℝ≥0) : ℝ) := by push_cast; linarith
  have hgm : ∀ r, Measurable (g r) := fun r =>
    measurable_const.mul ((hZ.measurable_sub a r.toNNReal).norm)
  have hgc : ∀ ω, Continuous (g · ω) := fun ω =>
    continuous_const.mul (((hZ.continuous ω).comp continuous_real_toNNReal).sub
      continuous_const).norm
  have hgnn : ∀ r ω, 0 ≤ g r ω := fun r ω => mul_nonneg hC0 (norm_nonneg _)
  have hra : ∀ r ∈ Icc (a : ℝ) ((a + h : ℝ≥0) : ℝ), a ≤ r.toNNReal := fun r hr =>
    (Real.le_toNNReal_iff_coe_le (a.coe_nonneg.trans hr.1)).2 hr.1
  have hgint : ∀ r ∈ Icc (a : ℝ) ((a + h : ℝ≥0) : ℝ), Integrable (g r) P := fun r hr =>
    (hZ.integrable_norm_sub (hra r hr)).const_mul C
  have hgbd : ∀ r ∈ Icc (a : ℝ) ((a + h : ℝ≥0) : ℝ), ∫ ω, g r ω ∂P ≤ C * (2 * m1 * Real.sqrt h) := by
    intro r hr
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ((hZ.integral_norm_sub_le (hra r hr)).trans ?_) hC0
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
    rw [Real.coe_toNNReal _ (a.coe_nonneg.trans hr.1)]
    have := hr.2; push_cast at this; linarith
  obtain ⟨hIi, hIb⟩ := integrable_intervalIntegral_and_le hgm hgc hgnn hah hgint hgbd
  have hT3 : Integrable (fun ω => C * ‖Dz ω‖ ^ 3) P :=
    (hZ.integrable_comp_sub (le_self_add : a ≤ a + h) (φ := fun w => ‖w‖ ^ 3)
      (by rw [add_tsub_cancel_left]; exact integrable_norm_pow_three_planarGaussian h)).const_mul C
  have hYi : Integrable (fun ω => C * ‖Dz ω‖ ^ 3
      + ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), g r ω) P := hT3.add hIi
  have hT3b : ∫ ω, C * ‖Dz ω‖ ^ 3 ∂P ≤ C * (8 * m3 * ((h : ℝ) * Real.sqrt h)) := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    have := hZ.integral_comp_sub (le_self_add : a ≤ a + h)
      (φ := fun w => ‖w‖ ^ 3) (continuous_norm.pow 3).measurable
    rw [add_tsub_cancel_left] at this
    rw [this]
    have := integral_norm_pow_three_planarGaussian_le h
    linarith
  -- the pointwise bound
  have hpt : ∀ ω, |ξ ω * (M (a + h) ω - M a ω) - W2 ω - W3 ω|
      ≤ C * ‖Dz ω‖ ^ 3 + ∫ r in (a : ℝ)..((a + h : ℝ≥0) : ℝ), g r ω := by
    intro ω
    have hps := pathwise_step hF hC0 hLip2 (hZ.continuous ω) a h (hξabs ω)
    rw [hM, hM]
    calc _ = _ := by
          congr 1
          simp only [hW2, hW3, hc1, hc2, hc3, hc4, hc5, hDz]
          ring
      _ ≤ _ := hps
  have hsplit := abs_integral_le_of_split (P := P) (ξ := ξ)
    (Z := fun ω => M (a + h) ω - M a ω) (W2 := W2) (W3 := W3)
    (((hMint _).sub (hMint _)).bdd_mul (hξ.mono (𝓕.le a) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξabs ω))
    hW2i hW3i hW2z hW3z hYi hpt
  refine hsplit.trans ?_
  rw [integral_add hT3 hIi]
  have hlen : ((a + h : ℝ≥0) : ℝ) - a = h := by push_cast; ring
  rw [hlen] at hIb
  have : C * (2 * m1 * Real.sqrt h) * h = 2 * C * m1 * ((h : ℝ) * Real.sqrt h) := by ring
  nlinarith [hT3b, hIb]

/-- **Dynkin's formula for planar Brownian motion.** For `F : ℂ → ℝ` of class `C³` with bounded
first, second and third derivatives (and `F(Z_0)` integrable),
`F(Z_t) − ∫₀ᵗ ½ ΔF(Z_r) dr` is an `𝓕`-martingale. -/
theorem martingale_dynkin (hZ : IsPlanarBrownian 𝓕 Z P) {F : ℂ → ℝ} {C : ℝ}
    (hF : ContDiff ℝ 3 F)
    (hD : ∀ x, ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 3 F x‖ ≤ C)
    (hF0 : Integrable (fun ω => F (Z 0 ω)) P) :
    Martingale (fun t ω => F (Z t ω) - ∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω))
      𝓕 P := by
  have hP := hZ.isProbabilityMeasure
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hD 0).1
  have hLip2 : ∀ y z, ‖iteratedFDeriv ℝ 2 F y - iteratedFDeriv ℝ 2 F z‖ ≤ C * ‖y - z‖ :=
    fun y z => Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
      (fun p _ => (hF.differentiable_iteratedFDeriv (m := 2) (by norm_num)) p)
      (fun p _ => by rw [norm_fderiv_iteratedFDeriv]; exact (hD p).2.2) convex_univ
      (Set.mem_univ _) (Set.mem_univ _)
  have hFlip : ∀ y z, |F y - F z| ≤ C * ‖y - z‖ := fun y z => by
    rw [← Real.norm_eq_abs]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
      (fun p _ => (hF.differentiable (by norm_num)) p) (fun p _ => (hD p).1) convex_univ
      (Set.mem_univ _) (Set.mem_univ _)
  set M : ℝ≥0 → Ω → ℝ := fun t ω =>
    F (Z t ω) - ∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω) with hMdef
  have hM : ∀ t ω, M t ω = F (Z t ω) - ∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω) :=
    fun _ _ => rfl
  have hMm : ∀ t, Measurable[𝓕 t] (M t) := fun t =>
    (hF.continuous.measurable.comp (hZ.measurable t)).sub
      (measurable_integral_adapted 𝓕 hZ.measurable hZ.continuous (continuous_planarGen hF) t)
  have hMint : ∀ t, Integrable (M t) P := by
    intro t
    have hg : Integrable (fun ω => |F (Z 0 ω)| + C * ‖Z t ω - Z 0 ω‖ + C * t) P :=
      (hF0.abs.add ((hZ.integrable_norm_sub (bot_le : (0 : ℝ≥0) ≤ t)).const_mul C)).add (integrable_const _)
    refine Integrable.mono' hg ((hMm t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, hM]
    have h1 : |F (Z t ω)| ≤ |F (Z 0 ω)| + C * ‖Z t ω - Z 0 ω‖ := by
      have e1 := hFlip (Z t ω) (Z 0 ω)
      have e2 := abs_sub_abs_le_abs_sub (F (Z t ω)) (F (Z 0 ω))
      linarith
    have h2 : |∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω)| ≤ C * t := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ)) (C := C)
        (f := fun r => planarGen F (Z r.toNNReal ω))
        (fun r _ => by rw [Real.norm_eq_abs]; exact (abs_planarGen_le F _).trans (hD _).2.1)
      rw [sub_zero, abs_of_nonneg t.coe_nonneg, Real.norm_eq_abs] at this
      linarith
    calc |F (Z t ω) - ∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω)|
        ≤ |F (Z t ω)| + |∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω)| := abs_sub _ _
      _ ≤ |F (Z 0 ω)| + C * ‖Z t ω - Z 0 ω‖ + C * t := by linarith
  refine ⟨fun t => (hMm t).stronglyMeasurable, fun s t hst => ?_⟩
  have hK := fun a h ξ (hξ : Measurable[𝓕 a] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) =>
    hZ.step_bound hF hC0 (fun y => (hD y).1) (fun y => (hD y).2.1) hLip2 hM hMint a h hξ hξb
  set K := 8 * C * QuantumZipper.gaussianAbsMoment 3 + 2 * C * QuantumZipper.gaussianAbsMoment 1
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hMint t)
    (fun A _ _ => (hMint s).integrableOn) (fun A hA _ => ?_)
    ((hMm s).stronglyMeasurable.aestronglyMeasurable)).symm
  have hAm : MeasurableSet A := 𝓕.le s A hA
  set ξ : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hξdef
  have hξA : ∀ f : Ω → ℝ, ∫ ω, ξ ω * f ω ∂P = ∫ ω in A, f ω ∂P := by
    intro f
    rw [← integral_indicator hAm]
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [hξdef, hω]
  have hξb : ∀ ω, |ξ ω| ≤ 1 := fun ω => by by_cases hω : ω ∈ A <;> simp [hξdef, hω]
  have hξmeas : Measurable ξ := measurable_const.indicator hAm
  have hξM : ∀ r, Integrable (fun ω => ξ ω * M r ω) P := fun r =>
    (hMint r).bdd_mul hξmeas.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
  have hstepψ : ∀ a' h' : ℝ, (s : ℝ) ≤ a' → 0 ≤ h' → a' + h' ≤ t →
      |(∫ ω, ξ ω * M (a' + h').toNNReal ω ∂P) - ∫ ω, ξ ω * M a'.toNNReal ω ∂P|
        ≤ K * (h' * Real.sqrt h') := by
    intro a' h' ha' hh' _
    have ha0 : 0 ≤ a' := s.coe_nonneg.trans ha'
    have hsum : (a' + h').toNNReal = a'.toNNReal + h'.toNNReal := Real.toNNReal_add ha0 hh'
    have hξm : Measurable[𝓕 a'.toNNReal] ξ :=
      measurable_const.indicator (𝓕.mono ((Real.le_toNNReal_iff_coe_le ha0).2 ha') A hA)
    rw [hsum, ← integral_sub (hξM _) (hξM _)]
    have hb := hK a'.toNNReal h'.toNNReal ξ hξm hξb
    rw [Real.coe_toNNReal _ hh'] at hb
    refine le_of_eq_of_le ?_ hb
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    ring
  have heq := eq_of_step_bound (ψ := fun x => ∫ ω, ξ ω * M x.toNNReal ω ∂P)
    (NNReal.coe_le_coe.2 hst) hstepψ
  simp only [Real.toNNReal_coe] at heq
  rw [← hξA, ← hξA]
  exact heq.symm

end IsPlanarBrownian

end InteractingSLE
