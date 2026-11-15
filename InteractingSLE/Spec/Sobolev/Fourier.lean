import InteractingSLE.Spec.Sobolev.Kernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Fourier definition of the local negative Sobolev norm

Source: `source/spec/p049-096.md`, Aux. lemma 11 (`#aux-11`, p. 83) and its proof ("By the Fourier
definition of the inhomogeneous Sobolev norm and Tonelli's theorem", `#id-SR2`, p. 84).

For a distribution `T ∈ 𝒟'(U)` and a cutoff `ζ ∈ 𝓓(U)`, the product `ζT` is a compactly supported
distribution on `ℝ² = ℂ`, whose Fourier transform is the smooth function
`ξ ↦ T(ζ e^{-2πi⟪·,ξ⟫}) = T(ζ cos(2π⟪·,ξ⟫)) - i T(ζ sin(2π⟪·,ξ⟫))` (Mathlib's normalization
`𝓕 f ξ = ∫ e^{-2πi⟪x,ξ⟫} f x dx`). Its inhomogeneous Sobolev norm of order `-ε` is

  `‖ζT‖²_{H^{-ε}} = ∫ |(ζT)^(ξ)|² (1 + |ξ|²)^{-ε} dξ ∈ [0, ∞]`,

and `T ∈ H^{-ε}_loc(U)` when this is finite for every cutoff.

## Main definitions

* `cosTest ζ ξ`, `sinTest ζ ξ` : the test functions `ζ(x) cos(2π⟪x, ξ⟫)`, `ζ(x) sin(2π⟪x, ξ⟫)`;
* `fourierSq T ζ ξ = T(cosTest ζ ξ)² + T(sinTest ζ ξ)² = |(ζT)^(ξ)|²`;
* `negSobolevSq ε T ζ = ‖ζT‖²_{H^{-ε}(ℝ²)}` (an extended real);
* `IsLocNegSobolev ε T` : `T ∈ H^{-ε}_loc(U)`.

## Main results

* `cosKer_bound`, `sinKer_bound` : `‖D^i_x (ζ(x) cos(2π⟪x, ξ⟫))‖ ≤ C_i (1 + |ξ|)^i`;
* `continuous_cosTest`, `continuous_sinTest`, `continuous_fourierSq`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function Real
open scoped Distributions ContDiff ENNReal

namespace InteractingSLE.Sobolev

open LQGMetric TopologicalSpace

/-! ### Derivatives of `cos` and `sin` along a linear phase -/

theorem abs_iteratedDeriv_cos_sin_le (n : ℕ) (t : ℝ) :
    |iteratedDeriv n Real.cos t| ≤ 1 ∧ |iteratedDeriv n Real.sin t| ≤ 1 := by
  induction n generalizing t with
  | zero => simp [Real.abs_cos_le_one, Real.abs_sin_le_one]
  | succ n ih =>
    rw [Real.iteratedDeriv_add_one_cos, Real.iteratedDeriv_add_one_sin]
    simp only [Pi.neg_apply, abs_neg]
    exact ⟨(ih t).2, (ih t).1⟩

/-- The linear phase `x ↦ 2π⟪x, ξ⟫`. -/
def phaseL (ξ : ℂ) : ℂ →L[ℝ] ℝ := (2 * π) • innerSL ℝ ξ

theorem phaseL_apply (ξ x : ℂ) : phaseL ξ x = 2 * π * inner ℝ x ξ := by
  simp [phaseL, real_inner_comm]

theorem norm_phaseL_le (ξ : ℂ) : ‖phaseL ξ‖ ≤ 2 * π * ‖ξ‖ := by
  rw [phaseL, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem norm_iteratedFDeriv_trig_comp_le {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hbd : ∀ n t, |iteratedDeriv n f t| ≤ 1) (ξ x : ℂ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ phaseL ξ) x‖ ≤ (2 * π * ‖ξ‖) ^ n := by
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hf _ (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  calc |iteratedDeriv n f (phaseL ξ x)| * ‖phaseL ξ‖ ^ n ≤ 1 * (2 * π * ‖ξ‖) ^ n :=
        mul_le_mul (hbd n _) (pow_le_pow_left₀ (norm_nonneg _) (norm_phaseL_le ξ) n)
          (by positivity) zero_le_one
    _ = (2 * π * ‖ξ‖) ^ n := one_mul _

/-! ### The cos/sin kernels -/

/-- The kernel `(ξ, x) ↦ ζ(x) cos(2π⟪x, ξ⟫)`. -/
def cosKer (ζ : ℂ → ℝ) (ξ x : ℂ) : ℝ := ζ x * Real.cos (2 * π * inner ℝ x ξ)

/-- The kernel `(ξ, x) ↦ ζ(x) sin(2π⟪x, ξ⟫)`. -/
def sinKer (ζ : ℂ → ℝ) (ξ x : ℂ) : ℝ := ζ x * Real.sin (2 * π * inner ℝ x ξ)

theorem contDiff_phase : ContDiff ℝ ∞ (fun p : ℂ × ℂ => 2 * π * inner ℝ p.2 p.1) :=
  contDiff_const.mul (contDiff_inner.comp (contDiff_snd.prodMk contDiff_fst))

theorem contDiff_cosKer {ζ : ℂ → ℝ} (hζ : ContDiff ℝ ∞ ζ) : ContDiff ℝ ∞ (uncurry (cosKer ζ)) :=
  (hζ.comp contDiff_snd).mul (Real.contDiff_cos.comp contDiff_phase)

theorem contDiff_sinKer {ζ : ℂ → ℝ} (hζ : ContDiff ℝ ∞ ζ) : ContDiff ℝ ∞ (uncurry (sinKer ζ)) :=
  (hζ.comp contDiff_snd).mul (Real.contDiff_sin.comp contDiff_phase)

/-- Polynomial bounds for the `x`-derivatives of `ζ(x) f(2π⟪x, ξ⟫)`, `f = cos, sin`. -/
theorem trigKer_bound {ζ : ℂ → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hbd : ∀ n t, |iteratedDeriv n f t| ≤ 1) (i : ℕ) :
    ∃ C, ∀ ξ x, ‖iteratedFDeriv ℝ i (fun x => ζ x * f (2 * π * inner ℝ x ξ)) x‖ ≤
      C * (1 + ‖ξ‖) ^ i := by
  have hM : ∀ j : ℕ, ∃ M, ∀ x, ‖iteratedFDeriv ℝ j ζ x‖ ≤ M := fun j =>
    (hζ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hζc.iteratedFDeriv j)
  choose M hM using hM
  refine ⟨∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * |M j| * (2 * π) ^ i, fun ξ x => ?_⟩
  have hξ : (1 : ℝ) ≤ 1 + ‖ξ‖ := le_add_of_nonneg_right (norm_nonneg _)
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  have hfun : (fun x => ζ x * f (2 * π * inner ℝ x ξ)) = fun x => ζ x * (f ∘ phaseL ξ) x := by
    funext y; simp [phaseL_apply]
  rw [hfun]
  refine (norm_iteratedFDeriv_mul_le hζ (hf.comp (phaseL ξ).contDiff) x
    (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have h1 : ‖iteratedFDeriv ℝ (i - j) (f ∘ phaseL ξ) x‖ ≤ (2 * π) ^ i * (1 + ‖ξ‖) ^ i := by
    refine (norm_iteratedFDeriv_trig_comp_le hf hbd ξ x (i - j)).trans ?_
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_right₀ h2π (Nat.sub_le i j))
      ((pow_le_pow_left₀ (norm_nonneg _) (by linarith) _).trans
        (pow_le_pow_right₀ hξ (Nat.sub_le i j))) (by positivity) (by positivity)
  calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j ζ x‖ * ‖iteratedFDeriv ℝ (i - j) (f ∘ phaseL ξ) x‖
      ≤ (i.choose j : ℝ) * |M j| * ((2 * π) ^ i * (1 + ‖ξ‖) ^ i) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ((hM j x).trans (le_abs_self _)) (by positivity))
          h1 (norm_nonneg _) (by positivity)
    _ = (i.choose j : ℝ) * |M j| * (2 * π) ^ i * (1 + ‖ξ‖) ^ i := by ring

theorem cosKer_bound {ζ : ℂ → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) (i : ℕ) :
    ∃ C, ∀ ξ x, ‖iteratedFDeriv ℝ i (cosKer ζ ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ i :=
  trigKer_bound hζ hζc Real.contDiff_cos (fun n t => (abs_iteratedDeriv_cos_sin_le n t).1) i

theorem sinKer_bound {ζ : ℂ → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) (i : ℕ) :
    ∃ C, ∀ ξ x, ‖iteratedFDeriv ℝ i (sinKer ζ ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ i :=
  trigKer_bound hζ hζc Real.contDiff_sin (fun n t => (abs_iteratedDeriv_cos_sin_le n t).2) i

/-! ### The test functions `ζ cos(2π⟪·, ξ⟫)`, `ζ sin(2π⟪·, ξ⟫)` -/

variable {U : Opens ℂ}

/-- The compact `tsupport ζ`. -/
def tsupportCompact (ζ : TestOn U) : Compacts ℂ := ⟨tsupport ζ, ζ.hasCompactSupport⟩

theorem tsupportCompact_subset (ζ : TestOn U) : (tsupportCompact ζ : Set ℂ) ⊆ U :=
  ζ.tsupport_subset

theorem cosKer_eq_zero (ζ : TestOn U) (ξ x : ℂ) (hx : x ∉ tsupportCompact ζ) :
    cosKer ζ ξ x = 0 := by
  simp [cosKer, image_eq_zero_of_notMem_tsupport hx]

theorem sinKer_eq_zero (ζ : TestOn U) (ξ x : ℂ) (hx : x ∉ tsupportCompact ζ) :
    sinKer ζ ξ x = 0 := by
  simp [sinKer, image_eq_zero_of_notMem_tsupport hx]

/-- `ζ(x) cos(2π⟪x, ξ⟫)` as a test function on `U`. -/
def cosTest (ζ : TestOn U) (ξ : ℂ) : TestOn U :=
  TestFunction.ofSupportedIn (tsupportCompact_subset ζ)
    (kernelIn (contDiff_cosKer ζ.contDiff) (cosKer_eq_zero ζ) ξ)

/-- `ζ(x) sin(2π⟪x, ξ⟫)` as a test function on `U`. -/
def sinTest (ζ : TestOn U) (ξ : ℂ) : TestOn U :=
  TestFunction.ofSupportedIn (tsupportCompact_subset ζ)
    (kernelIn (contDiff_sinKer ζ.contDiff) (sinKer_eq_zero ζ) ξ)

@[simp] theorem cosTest_apply (ζ : TestOn U) (ξ x : ℂ) :
    cosTest ζ ξ x = ζ x * Real.cos (2 * π * inner ℝ x ξ) := rfl

@[simp] theorem sinTest_apply (ζ : TestOn U) (ξ x : ℂ) :
    sinTest ζ ξ x = ζ x * Real.sin (2 * π * inner ℝ x ξ) := rfl

theorem continuous_cosTest (ζ : TestOn U) : Continuous (cosTest ζ) :=
  (TestFunction.continuous_ofSupportedIn _).comp (continuous_kernelIn _ _)

theorem continuous_sinTest (ζ : TestOn U) : Continuous (sinTest ζ) :=
  (TestFunction.continuous_ofSupportedIn _).comp (continuous_kernelIn _ _)

/-! ### The local negative Sobolev norm -/

/-- `|(ζT)^(ξ)|² = T(ζ cos(2π⟪·, ξ⟫))² + T(ζ sin(2π⟪·, ξ⟫))²`. -/
def fourierSq (T : DistOn U) (ζ : TestOn U) (ξ : ℂ) : ℝ :=
  T (cosTest ζ ξ) ^ 2 + T (sinTest ζ ξ) ^ 2

theorem fourierSq_nonneg (T : DistOn U) (ζ : TestOn U) (ξ : ℂ) : 0 ≤ fourierSq T ζ ξ := by
  unfold fourierSq; positivity

theorem continuous_fourierSq (T : DistOn U) (ζ : TestOn U) : Continuous (fourierSq T ζ) :=
  ((T.continuous.comp (continuous_cosTest ζ)).pow 2).add
    ((T.continuous.comp (continuous_sinTest ζ)).pow 2)

/-- The Sobolev weight `(1 + |ξ|²)^s`. -/
def sobWeight (s : ℝ) (ξ : ℂ) : ℝ := (1 + ‖ξ‖ ^ 2) ^ s

theorem sobWeight_pos (s : ℝ) (ξ : ℂ) : 0 < sobWeight s ξ :=
  Real.rpow_pos_of_pos (by positivity) s

theorem continuous_sobWeight (s : ℝ) : Continuous (sobWeight s) :=
  (continuous_const.add (continuous_norm.pow 2)).rpow_const fun ξ =>
    Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'

/-- `‖ζT‖²_{H^{-ε}(ℝ²)} = ∫ |(ζT)^(ξ)|² (1 + |ξ|²)^{-ε} dξ` (the Fourier definition). -/
def negSobolevSq (ε : ℝ) (T : DistOn U) (ζ : TestOn U) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (fourierSq T ζ ξ * sobWeight (-ε) ξ)

/-- `T ∈ H^{-ε}_loc(U)`: `ζT ∈ H^{-ε}(ℝ²)` for every cutoff `ζ ∈ 𝓓(U)`. -/
def IsLocNegSobolev (ε : ℝ) (T : DistOn U) : Prop :=
  ∀ ζ : TestOn U, negSobolevSq ε T ζ < ⊤

theorem measurable_fourierSq_mul (T : DistOn U) (ζ : TestOn U) (s : ℝ) :
    Measurable fun ξ => ENNReal.ofReal (fourierSq T ζ ξ * sobWeight s ξ) :=
  ENNReal.measurable_ofReal.comp
    ((continuous_fourierSq T ζ).mul (continuous_sobWeight s)).measurable

end InteractingSLE.Sobolev
