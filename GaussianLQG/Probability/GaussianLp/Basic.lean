import GaussianLQG.Core.Defs
import LQGDimension.Gaussian.Concentration
import LQGDimension.Gaussian.MaxInequality
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Gaussian `L^p` inequality: basic tools

Auxiliary results for the Gaussian `L^p` inequality (blueprint Proposition `prop:gaussian-Lp`,
source (3.2)).

* `lintegral_rpow_le`, `enorm_integral_rpow_le`: Jensen's inequality for `p`-th powers,
  `(∫⁻ g)^p ≤ ν(univ)^(p-1) ∫⁻ g^p` for a finite measure and `p ≥ 1` (through Hölder,
  `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`).
* `pi_absolutelyContinuous`: finite products of absolutely continuous measures.
* `ae_differentiableAt_gaussPi`, `ae_differentiableAt_stdGaussian`: Rademacher's theorem under the
  standard Gaussian measure (which is absolutely continuous with respect to a Haar measure).
* `lintegral_enorm_rpow_stdGaussian`: for a continuous linear functional `L`,
  `E|L(Y)|^p = ‖L‖^p E|N|^p`, since `L(Y) ∼ 𝒩(0, ‖L‖²)`.
* `gaussLpConst p = (π/2) (E|N|^p)^{1/p}`, the constant `c_p` of the blueprint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

namespace GaussLp

/-! ### Jensen's inequality for `p`-th powers -/

section Jensen

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- **Jensen's inequality** for lower integrals and `p ≥ 1`:
`(∫⁻ g dν)^p ≤ ν(univ)^(p-1) ∫⁻ g^p dν` for a finite measure `ν`. -/
theorem lintegral_rpow_le [IsFiniteMeasure ν] {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) {p : ℝ}
    (hp : 1 ≤ p) : (∫⁻ x, g x ∂ν) ^ p ≤ ν univ ^ (p - 1) * ∫⁻ x, g x ^ p ∂ν := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have key := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) h1 hg.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top] at key
  simp only [enorm_eq_self, ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le] at key
  calc (∫⁻ x, g x ∂ν) ^ p
      ≤ ((∫⁻ x, g x ^ p ∂ν) ^ (1 / p) * ν univ ^ (1 / 1 - 1 / p)) ^ p :=
        ENNReal.rpow_le_rpow key hp0.le
    _ = ν univ ^ (p - 1) * ∫⁻ x, g x ^ p ∂ν := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        have e1 : 1 / p * p = 1 := by field_simp
        have e2 : (1 / 1 - 1 / p) * p = p - 1 := by field_simp
        rw [e1, e2, ENNReal.rpow_one, mul_comm]

/-- **Jensen's inequality** for Bochner integrals and `p ≥ 1`:
`‖∫ f dν‖ₑ^p ≤ ν(univ)^(p-1) ∫⁻ ‖f‖ₑ^p dν` for a finite measure `ν`. -/
theorem enorm_integral_rpow_le [IsFiniteMeasure ν] {f : α → ℝ} (hf : AEStronglyMeasurable f ν)
    {p : ℝ} (hp : 1 ≤ p) : ‖∫ x, f x ∂ν‖ₑ ^ p ≤ ν univ ^ (p - 1) * ∫⁻ x, ‖f x‖ₑ ^ p ∂ν :=
  (ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm f) (by linarith)).trans
    (lintegral_rpow_le hf.enorm hp)

/-- Jensen's inequality for a probability measure: `(∫⁻ g)^p ≤ ∫⁻ g^p`. -/
theorem lintegral_rpow_le_of_prob [IsProbabilityMeasure ν] {g : α → ℝ≥0∞}
    (hg : AEMeasurable g ν) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, g x ∂ν) ^ p ≤ ∫⁻ x, g x ^ p ∂ν := by
  simpa [measure_univ] using lintegral_rpow_le hg hp

/-- Jensen's inequality for a probability measure: `‖∫ f‖ₑ^p ≤ ∫⁻ ‖f‖ₑ^p`. -/
theorem enorm_integral_rpow_le_of_prob [IsProbabilityMeasure ν] {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) {p : ℝ} (hp : 1 ≤ p) :
    ‖∫ x, f x ∂ν‖ₑ ^ p ≤ ∫⁻ x, ‖f x‖ₑ ^ p ∂ν := by
  simpa [measure_univ] using enorm_integral_rpow_le hf hp

end Jensen

/-! ### Absolute continuity of finite products -/

/-- A finite product of absolutely continuous measures is absolutely continuous. -/
theorem pi_absolutelyContinuous {X : Type*} [MeasurableSpace X] :
    ∀ {n : ℕ} {μ ν : Fin n → Measure X} [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
      (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν
  | 0, μ, ν, _, _, _ => by
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | n + 1, μ, ν, _, _, h => by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
    have hμ := measurePreserving_piFinSuccAbove μ 0
    have hν := measurePreserving_piFinSuccAbove ν 0
    have key : (Measure.pi μ).map e ≪ (Measure.pi ν).map e := by
      rw [hμ.map_eq, hν.map_eq]
      exact (h 0).prod (pi_absolutelyContinuous fun j => h _)
    have := key.map e.symm.measurable
    rwa [e.map_symm_map, e.map_symm_map] at this

/-! ### Rademacher's theorem under Gaussian measures -/

/-- The standard Gaussian measure on `ℝⁿ`, in product form. -/
abbrev gaussPi (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => gaussianReal 0 1

theorem gaussPi_absolutelyContinuous (n : ℕ) : gaussPi n ≪ (volume : Measure (Fin n → ℝ)) := by
  rw [volume_pi]
  exact pi_absolutelyContinuous fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero

/-- **Rademacher's theorem** under the product Gaussian measure on `ℝⁿ`. -/
theorem ae_differentiableAt_gaussPi {n : ℕ} {φ : (Fin n → ℝ) → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) : ∀ᵐ x ∂gaussPi n, DifferentiableAt ℝ φ x :=
  (gaussPi_absolutelyContinuous n).ae_le hφ.ae_differentiableAt

section StdGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Rademacher's theorem** under the standard Gaussian measure of a finite-dimensional inner
product space. -/
theorem ae_differentiableAt_stdGaussian {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∀ᵐ x ∂stdGaussian E, DifferentiableAt ℝ φ x := by
  set b := stdOrthonormalBasis ℝ E
  set T : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    b.toBasis.equivFun.symm.toContinuousLinearEquiv
  have hT : (fun x : Fin (Module.finrank ℝ E) → ℝ => ∑ i, x i • b i) = ⇑T := by
    funext x
    show ∑ i, x i • b i = b.toBasis.equivFun.symm x
    rw [Module.Basis.equivFun_symm_apply, OrthonormalBasis.coe_toBasis]
  have hstd : stdGaussian E = (gaussPi (Module.finrank ℝ E)).map ⇑T := by
    rw [stdGaussian, hT]
  have : ((volume : Measure (Fin (Module.finrank ℝ E) → ℝ)).map ⇑T).IsAddHaarMeasure :=
    T.isAddHaarMeasure_map _
  have hac : stdGaussian E ≪ (volume : Measure (Fin (Module.finrank ℝ E) → ℝ)).map ⇑T := by
    rw [hstd]
    exact (gaussPi_absolutelyContinuous _).map T.continuous.measurable
  exact hac.ae_le hφ.ae_differentiableAt

/-! ### Gaussian moments -/

/-- For a continuous linear functional `L`, `L(Y)` has the law of `‖L‖ N` under the standard
Gaussian measure. -/
theorem stdGaussian_map_strongDual (L : StrongDual ℝ E) :
    (stdGaussian E).map L = (gaussianReal 0 1).map (fun z => ‖L‖ * z) := by
  rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, gaussianReal_map_const_mul]
  congr 1
  · ring
  · ext
    simp

/-- `E|L(Y)|^p = ‖L‖^p E|N|^p` for a continuous linear functional `L` and a standard Gaussian
vector `Y`. -/
theorem lintegral_enorm_rpow_stdGaussian (L : StrongDual ℝ E) {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ y, ‖L y‖ₑ ^ p ∂stdGaussian E = ‖L‖ₑ ^ p * ∫⁻ z, ‖z‖ₑ ^ p ∂gaussianReal 0 1 := by
  have hm : Measurable fun z : ℝ => ‖z‖ₑ ^ p := measurable_id.enorm.pow_const p
  calc ∫⁻ y, ‖L y‖ₑ ^ p ∂stdGaussian E
      = ∫⁻ z, ‖z‖ₑ ^ p ∂((stdGaussian E).map L) :=
        (lintegral_map hm L.continuous.measurable).symm
    _ = ∫⁻ z, ‖z‖ₑ ^ p ∂((gaussianReal 0 1).map (fun z => ‖L‖ * z)) := by
        rw [stdGaussian_map_strongDual]
    _ = ∫⁻ z, ‖‖L‖ * z‖ₑ ^ p ∂gaussianReal 0 1 := lintegral_map hm (measurable_const_mul _)
    _ = ∫⁻ z, ‖L‖ₑ ^ p * ‖z‖ₑ ^ p ∂gaussianReal 0 1 := by
        congr 1
        funext z
        rw [enorm_mul, enorm_norm, ENNReal.mul_rpow_of_nonneg _ _ hp]
    _ = ‖L‖ₑ ^ p * ∫⁻ z, ‖z‖ₑ ^ p ∂gaussianReal 0 1 := lintegral_const_mul _ hm

end StdGaussian

/-- `E|N|^p` as a lower integral equals the real moment `∫ |z|^p dγ`. -/
theorem lintegral_enorm_rpow_gaussianReal {p : ℝ} (hp : 0 < p) :
    ∫⁻ z, ‖z‖ₑ ^ p ∂gaussianReal 0 1 = ENNReal.ofReal (∫ z, |z| ^ p ∂gaussianReal 0 1) := by
  have hmem : MemLp id (ENNReal.ofReal p) (gaussianReal 0 1) := by
    simpa [ENNReal.ofReal] using memLp_id_gaussianReal (μ := 0) (v := 1) p.toNNReal
  have hint : Integrable (fun z : ℝ => |z| ^ p) (gaussianReal 0 1) := by
    have := hmem.integrable_norm_rpow (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using this
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => by positivity)]
  congr 1
  funext z
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg z) hp.le]

/-- The constant `c_p = (π/2) (E|N|^p)^{1/p}` of the Gaussian `L^p` inequality. -/
def gaussLpConst (p : ℝ) : ℝ :=
  Real.pi / 2 * (∫ z, |z| ^ p ∂gaussianReal 0 1) ^ (1 / p)

/-- `ofReal c_p = ofReal (π/2) · (E|N|^p)^{1/p}`, with the moment as a lower integral. -/
theorem ofReal_gaussLpConst {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (gaussLpConst p) =
      ENNReal.ofReal (Real.pi / 2) * (∫⁻ z, ‖z‖ₑ ^ p ∂gaussianReal 0 1) ^ (1 / p) := by
  have hM : 0 ≤ ∫ z, |z| ^ p ∂gaussianReal 0 1 :=
    integral_nonneg fun z => by positivity
  rw [gaussLpConst, ENNReal.ofReal_mul (by positivity), lintegral_enorm_rpow_gaussianReal hp,
    ENNReal.ofReal_rpow_of_nonneg hM (by positivity)]

end GaussLp

end GaussianLQG
