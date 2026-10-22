import HigherDimLQGMetric.Gauss.GaussianHolderCore
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The Gaussian Hölder inequality (D-GH), part 4: approximation and the geometric form (packet G2)

Source: planning audit `planning/audits/MA4-sections-7-10-appA.md`, Details (a) A7, Step 0 and
the statement `gaussianHolder_geom` ([7] = Chen–Dafnis–Paouris, arXiv:1306.2410, Theorem 3(i)
with `d_i = 1/K`, equivalently Theorem 1(i) with all `p_i = K`).

* `exists_smooth_approx` (A7, Step 0): a measurable `f : F → [0, 1]` is approximated in
  `L¹(μ)` (`μ` a probability measure) by smooth `g` with `δ ≤ g ≤ 1` (`δ > 0`) and bounded
  continuous gradient. Construction: a continuous compactly supported `L¹` approximant (Mathlib),
  clamped to `[0, 1]`; a uniform smooth approximant (Mathlib, convolution with a bump); a smooth
  cutoff (to make the gradient compactly supported, hence bounded); an affine rescaling into
  `(0, 1]`.
* `norm_sum_adjoint_sq_le`: `∑_i ‖U_i x‖² ≤ K ‖x‖²` implies `‖∑_i U_i† η_i‖² ≤ K ∑_i ‖η_i‖²`.
* `gaussianHolder_geom_smooth`: the geometric form for smooth `g_i : F_i → [δ, 1]`, from the
  smooth case `integral_prod_rpow_le_of_smooth` with `H_i = g_i^K ∘ U_i`, `c = 1/K` and
  `S_i = range U_i†`.
* `gaussianHolder_geom_general`: the geometric form for measurable `f_i : F_i → [0, 1]`, for
  arbitrary finite-dimensional inner product spaces `E`, `F_i`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric.Gauss

section Elementary

/-- `|∏ aᵢ - ∏ bᵢ| ≤ ∑ |aᵢ - bᵢ|` for families with values in `[0, 1]`. -/
lemma abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hA0 : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg fun i _ => ha0 i
    have hA1 : ∏ i ∈ s, a i ≤ 1 := Finset.prod_le_one₀ (fun i _ => ha0 i) fun i _ => ha1 i
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        (a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hA0]
      exact mul_le_of_le_one_right (abs_nonneg _) hA1
    · rw [abs_mul, abs_of_nonneg (hb0 j)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hb1 j)).trans ih

/-- `|a^K - b^K| ≤ K |a - b|` for `a, b ∈ [0, 1]` and `K ≥ 1`. -/
lemma abs_rpow_sub_rpow_le {a b K : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hK : 1 ≤ K) : |a ^ K - b ^ K| ≤ K * |a - b| := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t => t ^ K) (K * t ^ (K - 1)) (Icc 0 1) t :=
    fun t _ => (Real.hasDerivAt_rpow_const (Or.inr hK)).hasDerivWithinAt
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖K * t ^ (K - 1)‖ ≤ K := by
    intro t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith),
      abs_of_nonneg (Real.rpow_nonneg ht.1 _)]
    exact mul_le_of_le_one_right (by linarith) (Real.rpow_le_one ht.1 ht.2 (by linarith))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbd (convex_Icc 0 1)
    ⟨hb0, hb1⟩ ⟨ha0, ha1⟩
  simpa only [Real.norm_eq_abs] using h

/-- A product of numbers in `[0, 1]` is at most each factor. -/
lemma prod_le_of_mem_unit {ι : Type*} [Fintype ι] {a : ι → ℝ} (ha0 : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i ≤ 1) (i : ι) : ∏ j, a j ≤ a i := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
  exact mul_le_of_le_one_right (ha0 i)
    (Finset.prod_le_one₀ (fun j _ => ha0 j) fun j _ => ha1 j)

end Elementary

section Approx

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Smooth approximation** (MA4 A7, Step 0): a measurable `f : F → [0, 1]` is `ε`-close in
`L¹(μ)` to a smooth `g` with `δ ≤ g ≤ 1` for some `δ > 0`, whose gradient is continuous and
bounded. -/
theorem exists_smooth_approx (μ : Measure F) [IsProbabilityMeasure μ] {f : F → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : F → ℝ) (Dg : F → F) (δ C : ℝ), 0 < δ ∧ (∀ x, δ ≤ g x) ∧ (∀ x, g x ≤ 1) ∧
      HasBddGrad g Dg C ∧ ∫ x, |g x - f x| ∂μ ≤ ε := by
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]; exact hf1 x)
  -- a continuous compactly supported approximant
  obtain ⟨φ₀, hφ₀c, hφ₀int, hφ₀cont, hφ₀i⟩ :=
    hfi.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  -- clamped to `[0, 1]`
  set φ₁ : F → ℝ := fun x => max 0 (min 1 (φ₀ x)) with hφ₁
  have hφ₁cont : Continuous φ₁ := continuous_const.max (continuous_const.min hφ₀cont)
  have hφ₁c : HasCompactSupport φ₁ :=
    hφ₀c.comp_left (g := fun t : ℝ => max 0 (min 1 t)) (by simp)
  have hφ₁0 : ∀ x, 0 ≤ φ₁ x := fun x => le_max_left _ _
  have hφ₁1 : ∀ x, φ₁ x ≤ 1 := fun x => max_le zero_le_one (min_le_left _ _)
  have hφ₁f : ∀ x, |φ₁ x - f x| ≤ |φ₀ x - f x| := by
    intro x
    have h0 := hf0 x
    have h1 := hf1 x
    simp only [hφ₁]
    rcases le_total (φ₀ x) 0 with h | h
    · rw [min_eq_right (h.trans zero_le_one), max_eq_left h,
        abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rcases le_total (φ₀ x) 1 with h' | h'
      · rw [min_eq_right h', max_eq_right h]
      · rw [min_eq_left h', max_eq_right zero_le_one,
          abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
  -- a uniform smooth approximant
  set η : ℝ := ε / 8 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨g₀, hg₀s, hg₀⟩ :=
    (hφ₁c.uniformContinuous_of_continuous hφ₁cont).exists_contDiff_dist_le hη0
  -- a smooth cutoff equal to one on the support of `φ₁`
  obtain ⟨r, hr⟩ := hφ₁c.isCompact.isBounded.subset_closedBall (0 : F)
  set R : ℝ := max r 0 with hR
  have hR0 : 0 ≤ R := le_max_right _ _
  let χ : ContDiffBump (0 : F) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  set g₁ : F → ℝ := fun x => χ x * g₀ x with hg₁
  have hg₁s : ContDiff ℝ (⊤ : ℕ∞) g₁ := (χ.contDiff (n := ⊤)).mul hg₀s
  have hg₁c : HasCompactSupport g₁ := χ.hasCompactSupport.mul_right
  have hg₁φ : ∀ x, |g₁ x - φ₁ x| ≤ η := by
    intro x
    by_cases hx : x ∈ tsupport φ₁
    · have hx' : x ∈ Metric.closedBall (0 : F) χ.rIn := by
        have h1 := hr hx
        rw [Metric.mem_closedBall] at h1 ⊢
        show dist x 0 ≤ R + 1
        linarith [le_max_left r 0]
      have hχ := χ.one_of_mem_closedBall hx'
      simp only [hg₁, hχ, one_mul]
      have := hg₀ x
      rw [Real.dist_eq] at this
      exact this.le
    · have hz := image_eq_zero_of_notMem_tsupport hx
      simp only [hg₁, hz, sub_zero]
      have := hg₀ x
      rw [Real.dist_eq, hz, sub_zero] at this
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _)
        (abs_le.2 ⟨by linarith [χ.nonneg (x := x)], χ.le_one⟩)).trans this.le
  -- affine rescaling into `[η / (1 + 3η), 1]`
  set a : ℝ := (1 + 3 * η)⁻¹ with ha
  have ha0 : 0 < a := inv_pos.2 (by linarith)
  have ha1 : a * (1 + 3 * η) = 1 := inv_mul_cancel₀ (by linarith)
  have ha1' : a ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  set g : F → ℝ := fun x => (g₁ x + 2 * η) * a with hg
  set Dg : F → F := fun x => (InnerProductSpace.toDual ℝ F).symm (a • fderiv ℝ g₁ x) with hDg
  obtain ⟨C₁, hC₁⟩ := (hg₁s.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hg₁c.fderiv ℝ)
  refine ⟨g, Dg, η * a, |a| * C₁, mul_pos hη0 ha0, fun x => ?_, fun x => ?_, ?_, ?_⟩
  · have h1 := hg₁φ x
    have h2 := hφ₁0 x
    simp only [hg]
    refine mul_le_mul_of_nonneg_right ?_ ha0.le
    linarith [(abs_le.1 h1).1]
  · have h1 := hg₁φ x
    have h2 := hφ₁1 x
    simp only [hg]
    calc (g₁ x + 2 * η) * a ≤ (1 + 3 * η) * a :=
          mul_le_mul_of_nonneg_right (by linarith [(abs_le.1 h1).2]) ha0.le
      _ = 1 := by rw [mul_comm, ha1]
  · refine ⟨fun x => ?_, ?_, fun x => ?_⟩
    · have h1 : HasFDerivAt g₁ (fderiv ℝ g₁ x) x :=
        ((hg₁s.differentiable (by simp)) x).hasFDerivAt
      have h2 := (h1.add_const (2 * η)).mul_const a
      refine h2.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
      simp only [hDg, innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]
    · exact (InnerProductSpace.toDual ℝ F).symm.continuous.comp
        ((hg₁s.continuous_fderiv (by simp)).const_smul a)
    · simp only [hDg, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC₁ x) (abs_nonneg a)
  · -- the `L¹` error
    have hgcont : Continuous g := ((hg₁s.continuous).add continuous_const).mul continuous_const
    have hgf : ∀ x, |g x - f x| ≤ 3 * η + |φ₀ x - f x| := by
      intro x
      have h1 := hg₁φ x
      have h2 := hφ₁0 x
      have h3 := hφ₁1 x
      have e : g x - φ₁ x = a * ((g₁ x - φ₁ x) + η * (2 - 3 * φ₁ x)) := by
        simp only [hg]
        linear_combination (φ₁ x) * ha1
      have h4 : |g x - φ₁ x| ≤ 3 * η := by
        rw [e, abs_mul, abs_of_pos ha0]
        have h5 : |(g₁ x - φ₁ x) + η * (2 - 3 * φ₁ x)| ≤ 3 * η := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_pos hη0]
          have : |2 - 3 * φ₁ x| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
          nlinarith
        calc a * |(g₁ x - φ₁ x) + η * (2 - 3 * φ₁ x)| ≤ 1 * (3 * η) :=
              mul_le_mul ha1' h5 (abs_nonneg _) zero_le_one
          _ = 3 * η := one_mul _
      calc |g x - f x| = |(g x - φ₁ x) + (φ₁ x - f x)| := by ring_nf
        _ ≤ |g x - φ₁ x| + |φ₁ x - f x| := abs_add_le _ _
        _ ≤ 3 * η + |φ₀ x - f x| := add_le_add h4 (hφ₁f x)
    have hint1 : Integrable (fun x => |g x - f x|) μ :=
      Integrable.of_bound
        (continuous_abs.measurable.comp (hgcont.measurable.sub hfm)).aestronglyMeasurable 1
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_abs]
          have h1 := hg₁φ x
          have h2 := hφ₁0 x
          have h3 := hφ₁1 x
          have hgx0 : 0 ≤ g x := mul_nonneg (by linarith [(abs_le.1 h1).1]) ha0.le
          have hgx1 : g x ≤ 1 := by
            calc g x = (g₁ x + 2 * η) * a := rfl
              _ ≤ (1 + 3 * η) * a :=
                mul_le_mul_of_nonneg_right (by linarith [(abs_le.1 h1).2]) ha0.le
              _ = 1 := by rw [mul_comm, ha1]
          exact abs_le.2 ⟨by linarith [hf1 x], by linarith [hf0 x]⟩)
    have hint3 : Integrable (fun x => |φ₀ x - f x|) μ := (hφ₀i.sub hfi).abs
    have hint2 : Integrable (fun x => 3 * η + |φ₀ x - f x|) μ :=
      (integrable_const _).add hint3
    calc ∫ x, |g x - f x| ∂μ ≤ ∫ x, (3 * η + |φ₀ x - f x|) ∂μ :=
          integral_mono hint1 hint2 hgf
      _ = 3 * η + ∫ x, |φ₀ x - f x| ∂μ := by
          rw [integral_add (integrable_const _) hint3]
          simp
      _ ≤ 3 * η + ε / 2 := by
          gcongr
          calc ∫ x, |φ₀ x - f x| ∂μ = ∫ x, ‖f x - φ₀ x‖ ∂μ := by
                congr 1; funext x; rw [Real.norm_eq_abs, abs_sub_comm]
            _ ≤ ε / 2 := hφ₀int
      _ ≤ ε := by rw [hη]; linarith

end Approx


section Geom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
  [∀ i, InnerProductSpace ℝ (F i)] [∀ i, FiniteDimensional ℝ (F i)] [∀ i, MeasurableSpace (F i)]
  [∀ i, BorelSpace (F i)]

omit [MeasurableSpace E] [BorelSpace E] [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)] in
/-- The frame bound `∑_i ‖U_i x‖² ≤ K ‖x‖²` gives `‖∑_i U_i† η_i‖² ≤ K ∑_i ‖η_i‖²`
(`‖U†‖ = ‖U‖` for `U = (U_i)_i`). -/
lemma norm_sum_adjoint_sq_le (U : (i : ι) → E →L[ℝ] F i) {K : ℝ} (hK : 0 ≤ K)
    (hUK : ∀ x, ∑ i, ‖U i x‖ ^ 2 ≤ K * ‖x‖ ^ 2) (η : (i : ι) → F i) :
    ‖∑ i, ContinuousLinearMap.adjoint (U i) (η i)‖ ^ 2 ≤ K * ∑ i, ‖η i‖ ^ 2 := by
  set z := ∑ i, ContinuousLinearMap.adjoint (U i) (η i) with hz
  have h1 : ‖z‖ ^ 2 = ∑ i, ⟪η i, U i z⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    have : ⟪z, z⟫ = ⟪∑ i, ContinuousLinearMap.adjoint (U i) (η i), z⟫ := rfl
    rw [this, sum_inner]
    exact Finset.sum_congr rfl fun i _ => ContinuousLinearMap.adjoint_inner_left (U i) z (η i)
  have h2 : (∑ i, ⟪η i, U i z⟫) ^ 2 ≤ (∑ i, ‖η i‖ ^ 2) * ∑ i, ‖U i z‖ ^ 2 := by
    have h3 : |∑ i, ⟪η i, U i z⟫| ≤ ∑ i, ‖η i‖ * ‖U i z‖ :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => abs_real_inner_le_norm _ _)
    calc (∑ i, ⟪η i, U i z⟫) ^ 2 = |∑ i, ⟪η i, U i z⟫| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ i, ‖η i‖ * ‖U i z‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ ≤ (∑ i, ‖η i‖ ^ 2) * ∑ i, ‖U i z‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hA : 0 ≤ ∑ i, ‖η i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h4 : ‖z‖ ^ 2 * ‖z‖ ^ 2 ≤ (K * ∑ i, ‖η i‖ ^ 2) * ‖z‖ ^ 2 := by
    calc ‖z‖ ^ 2 * ‖z‖ ^ 2 = (∑ i, ⟪η i, U i z⟫) ^ 2 := by rw [← h1]; ring
      _ ≤ (∑ i, ‖η i‖ ^ 2) * ∑ i, ‖U i z‖ ^ 2 := h2
      _ ≤ (∑ i, ‖η i‖ ^ 2) * (K * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left (hUK z) hA
      _ = (K * ∑ i, ‖η i‖ ^ 2) * ‖z‖ ^ 2 := by ring
  rcases (sq_nonneg ‖z‖).eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg hK hA
  · exact le_of_mul_le_mul_right h4 h

/-- **D-GH, geometric form, smooth case**: for co-isometries `U_i` with `∑_i ‖U_i x‖² ≤ K ‖x‖²`
and smooth `g_i : F_i → [δ, 1]` with bounded continuous gradients,
`∫ ∏_i g_i(U_i x) dγ_E ≤ ∏_i (∫ g_i^K dγ_{F_i})^{1/K}`. -/
theorem gaussianHolder_geom_smooth (U : (i : ι) → E →L[ℝ] F i)
    (hU : ∀ i, (U i).comp (ContinuousLinearMap.adjoint (U i)) = ContinuousLinearMap.id ℝ (F i))
    {K : ℝ} (hK : 1 ≤ K) (hUK : ∀ x, ∑ i, ‖U i x‖ ^ 2 ≤ K * ‖x‖ ^ 2)
    (g : (i : ι) → F i → ℝ) (Dg : (i : ι) → F i → F i) {δ C : ℝ} (hδ : 0 < δ)
    (hg : ∀ i, HasBddGrad (g i) (Dg i) C) (hgδ : ∀ i y, δ ≤ g i y) (hg1 : ∀ i y, g i y ≤ 1) :
    ∫ x, ∏ i, g i (U i x) ∂(stdGaussian E) ≤
      ∏ i, (∫ y, g i y ^ K ∂(stdGaussian (F i))) ^ K⁻¹ := by
  have hK0 : 0 < K := by linarith
  have hg0 : ∀ i y, 0 < g i y := fun i y => hδ.trans_le (hgδ i y)
  set H : ι → E → ℝ := fun i x => g i (U i x) ^ K with hH
  set DH : ι → E → E := fun i x =>
    (K * g i (U i x) ^ (K - 1)) • ContinuousLinearMap.adjoint (U i) (Dg i (U i x)) with hDH
  set S : ι → Submodule ℝ E := fun i =>
    LinearMap.range ((ContinuousLinearMap.adjoint (U i) : F i →L[ℝ] E) : F i →ₗ[ℝ] E) with hS
  have hpow_le : ∀ i y, g i y ^ (K - 1) ≤ 1 := fun i y =>
    Real.rpow_le_one (hg0 i y).le (hg1 i y) (by linarith)
  have D : SmoothHolderData H DH S (δ ^ K) (K * C) := by
    refine ⟨Real.rpow_pos_of_pos hδ K, fun i => ⟨fun x => ?_, ?_, fun x => ?_⟩,
      fun i x => Real.rpow_le_rpow hδ.le (hgδ i _) hK0.le,
      fun i x => Real.rpow_le_one (hg0 i _).le (hg1 i _) hK0.le, fun i x => ?_⟩
    · have h1 := ((hg i).hasFDerivAt (U i x)).comp x (U i).hasFDerivAt
      have h2 := h1.rpow_const (p := K) (Or.inl (hg0 i (U i x)).ne')
      refine h2.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
      simp only [hDH, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        innerSL_apply_apply, smul_eq_mul, real_inner_smul_left,
        ContinuousLinearMap.adjoint_inner_left]
    · exact (continuous_const.mul (((hg i).continuous.comp (U i).continuous).rpow_const
        fun x => Or.inl (hg0 i _).ne')).smul ((ContinuousLinearMap.adjoint (U i)).continuous.comp
          ((hg i).continuous_grad.comp (U i).continuous))
    · simp only [hDH]
      rw [norm_smul, norm_adjoint_apply_of_comp_adjoint (U i) (hU i), Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hK0.le (Real.rpow_nonneg (hg0 i _).le _))]
      calc K * g i (U i x) ^ (K - 1) * ‖Dg i (U i x)‖ ≤ K * 1 * C :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hpow_le i _) hK0.le) ((hg i).norm_grad_le _)
              (norm_nonneg _) (by linarith)
        _ = K * C := by ring
    · simp only [hDH, hS]
      exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  have hSb : ∀ ξ : ι → E, (∀ i, ξ i ∈ S i) → K⁻¹ * ‖∑ i, ξ i‖ ^ 2 ≤ ∑ i, ‖ξ i‖ ^ 2 := by
    intro ξ hξ
    choose η hη using fun i => LinearMap.mem_range.1 (hξ i)
    have hη' : ∀ i, ContinuousLinearMap.adjoint (U i) (η i) = ξ i := hη
    have hnorm : ∀ i, ‖ξ i‖ = ‖η i‖ := fun i => by
      rw [← hη' i]
      exact norm_adjoint_apply_of_comp_adjoint (U i) (hU i) (η i)
    have h := norm_sum_adjoint_sq_le U hK0.le hUK η
    simp only [hη'] at h
    rw [inv_mul_le_iff₀ hK0]
    simpa only [hnorm] using h
  have hmain := integral_prod_rpow_le_of_smooth D (inv_nonneg.2 hK0.le) hSb
  have hl : ∀ x, ∏ i, H i x ^ K⁻¹ = ∏ i, g i (U i x) := fun x =>
    Finset.prod_congr rfl fun i _ => Real.rpow_rpow_inv (hg0 i _).le hK0.ne'
  have hr : ∀ i, ∫ x, H i x ∂(stdGaussian E) = ∫ y, g i y ^ K ∂(stdGaussian (F i)) := fun i =>
    integral_comp_of_comp_adjoint (U i) (hU i) (g := fun y => g i y ^ K)
      (((hg i).continuous.rpow_const fun y => Or.inl (hg0 i y).ne').aestronglyMeasurable)
  simp only [hl, hr] at hmain
  exact hmain

/-- **D-GH, geometric form** (MA4 A7; [7] Theorem 3(i) with `d_i = 1/K`), for arbitrary
finite-dimensional inner product spaces: if every `U_i : E → F_i` is a co-isometry
(`U_i U_i† = id`) and `∑_i ‖U_i x‖² ≤ K ‖x‖²` (`K ≥ 1`), then for measurable
`f_i : F_i → [0, 1]`, `∫ ∏_i f_i(U_i x) dγ_E ≤ ∏_i (∫ f_i^K dγ_{F_i})^{1/K}`. -/
theorem gaussianHolder_geom_general (U : (i : ι) → E →L[ℝ] F i)
    (hU : ∀ i, (U i).comp (ContinuousLinearMap.adjoint (U i)) = ContinuousLinearMap.id ℝ (F i))
    {K : ℝ} (hK : 1 ≤ K) (hUK : ∀ x, ∑ i, ‖U i x‖ ^ 2 ≤ K * ‖x‖ ^ 2)
    (f : (i : ι) → F i → ℝ) (hfm : ∀ i, Measurable (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hf1 : ∀ i y, f i y ≤ 1) :
    ∫ x, ∏ i, f i (U i x) ∂(stdGaussian E) ≤
      ∏ i, (∫ y, f i y ^ K ∂(stdGaussian (F i))) ^ K⁻¹ := by
  have hK0 : 0 < K := by linarith
  set m : ι → ℝ := fun i => ∫ y, f i y ^ K ∂(stdGaussian (F i)) with hm
  have hm0 : ∀ i, 0 ≤ m i := fun i => integral_nonneg fun y => Real.rpow_nonneg (hf0 i y) _
  set A := ∫ x, ∏ i, f i (U i x) ∂(stdGaussian E) with hA
  have hfK : ∀ i, Integrable (fun y => f i y ^ K) (stdGaussian (F i)) := fun i =>
    Integrable.of_bound ((hfm i).pow_const K).aestronglyMeasurable 1 (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hf0 i y) _)]
      exact Real.rpow_le_one (hf0 i y) (hf1 i y) hK0.le)
  have key : ∀ ε > 0, A ≤ ∏ i, (m i + K * ε) ^ K⁻¹ + Fintype.card ι * ε := by
    intro ε hε
    choose g Dg δ C hδ hgδ hg1 hg hgf using fun i =>
      exists_smooth_approx (stdGaussian (F i)) (hfm i) (hf0 i) (hf1 i) hε
    have hg0 : ∀ i y, 0 < g i y := fun i y => (hδ i).trans_le (hgδ i y)
    have hδ1 : ∀ i, δ i ≤ 1 := fun i => (hgδ i 0).trans (hg1 i 0)
    -- uniform constants
    set δ₀ := ∏ i, δ i with hδ₀
    have hδ₀ : 0 < δ₀ := Finset.prod_pos fun i _ => hδ i
    have hδ₀i : ∀ i, δ₀ ≤ δ i := prod_le_of_mem_unit (fun i => (hδ i).le) hδ1
    set C₀ := ∑ i, C i with hC₀
    have hCi : ∀ i, C i ≤ C₀ := fun i =>
      Finset.single_le_sum (f := C) (fun j _ => (hg j).nonneg) (Finset.mem_univ i)
    have hsm := gaussianHolder_geom_smooth U hU hK hUK g Dg hδ₀
      (fun i => (hg i).mono (hCi i)) (fun i y => (hδ₀i i).trans (hgδ i y)) hg1
    -- error in the left side
    have hgU : ∀ i, Integrable (fun x => |f i (U i x) - g i (U i x)|) (stdGaussian E) := fun i =>
      Integrable.of_bound (continuous_abs.measurable.comp
        (((hfm i).comp (U i).continuous.measurable).sub
          ((hg i).continuous.comp (U i).continuous).measurable)).aestronglyMeasurable 1
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_abs]
          exact abs_le.2 ⟨by linarith [hf0 i (U i x), hg1 i (U i x)],
            by linarith [hf1 i (U i x), hg0 i (U i x)]⟩)
    have hfU : Integrable (fun x => ∏ i, f i (U i x)) (stdGaussian E) :=
      Integrable.of_bound (Finset.measurable_prod _ fun i _ =>
        (hfm i).comp (U i).continuous.measurable).aestronglyMeasurable 1
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => hf0 i _)]
          exact Finset.prod_le_one₀ (fun i _ => hf0 i _) fun i _ => hf1 i _)
    have hgU' : Integrable (fun x => ∏ i, g i (U i x)) (stdGaussian E) :=
      integrable_of_continuous_of_bound (continuous_finsetProd _ fun i _ =>
        (hg i).continuous.comp (U i).continuous) (M := 1) fun x => by
          rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => (hg0 i _).le)]
          exact Finset.prod_le_one₀ (fun i _ => (hg0 i _).le) fun i _ => hg1 i _
    have hleft : A ≤ ∫ x, ∏ i, g i (U i x) ∂(stdGaussian E) + Fintype.card ι * ε := by
      have hpt : ∀ x, ∏ i, f i (U i x) ≤
          ∏ i, g i (U i x) + ∑ i, |f i (U i x) - g i (U i x)| := by
        intro x
        have h := abs_prod_sub_prod_le Finset.univ (a := fun i => f i (U i x))
          (b := fun i => g i (U i x)) (fun i => hf0 i _) (fun i => hf1 i _)
          (fun i => (hg0 i _).le) (fun i => hg1 i _)
        linarith [le_abs_self (∏ i, f i (U i x) - ∏ i, g i (U i x))]
      calc A ≤ ∫ x, (∏ i, g i (U i x) + ∑ i, |f i (U i x) - g i (U i x)|) ∂(stdGaussian E) :=
            integral_mono hfU (hgU'.add (integrable_finsetSum _ fun i _ => hgU i)) hpt
        _ = ∫ x, ∏ i, g i (U i x) ∂(stdGaussian E) +
              ∑ i, ∫ x, |f i (U i x) - g i (U i x)| ∂(stdGaussian E) := by
            rw [integral_add hgU' (integrable_finsetSum _ fun i _ => hgU i),
              integral_finsetSum _ fun i _ => hgU i]
        _ ≤ ∫ x, ∏ i, g i (U i x) ∂(stdGaussian E) + Fintype.card ι * ε := by
            gcongr
            calc ∑ i, ∫ x, |f i (U i x) - g i (U i x)| ∂(stdGaussian E)
                = ∑ i, ∫ y, |g i y - f i y| ∂(stdGaussian (F i)) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [integral_comp_of_comp_adjoint (U i) (hU i)
                    (g := fun y => |f i y - g i y|)
                    (continuous_abs.measurable.comp ((hfm i).sub
                      (hg i).continuous.measurable)).aestronglyMeasurable]
                  congr 1; funext y; rw [abs_sub_comm]
              _ ≤ ∑ _i : ι, ε := Finset.sum_le_sum fun i _ => hgf i
              _ = Fintype.card ι * ε := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    -- error in the right side
    have hright : ∀ i, ∫ y, g i y ^ K ∂(stdGaussian (F i)) ≤ m i + K * ε := by
      intro i
      have hgK : Integrable (fun y => g i y ^ K) (stdGaussian (F i)) :=
        integrable_of_continuous_of_bound ((hg i).continuous.rpow_const
          fun y => Or.inl (hg0 i y).ne') (M := 1) fun y => by
            rw [abs_of_nonneg (Real.rpow_nonneg (hg0 i y).le _)]
            exact Real.rpow_le_one (hg0 i y).le (hg1 i y) hK0.le
      have hgf' : Integrable (fun y => |g i y - f i y|) (stdGaussian (F i)) :=
        Integrable.of_bound (continuous_abs.measurable.comp
          ((hg i).continuous.measurable.sub (hfm i))).aestronglyMeasurable 1
          (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_abs]
            exact abs_le.2 ⟨by linarith [hf1 i y, hg0 i y], by linarith [hf0 i y, hg1 i y]⟩)
      have hpt : ∀ y, g i y ^ K ≤ f i y ^ K + K * |g i y - f i y| := fun y => by
        have h := abs_rpow_sub_rpow_le (hg0 i y).le (hg1 i y) (hf0 i y) (hf1 i y) hK
        linarith [le_abs_self (g i y ^ K - f i y ^ K)]
      calc ∫ y, g i y ^ K ∂(stdGaussian (F i))
          ≤ ∫ y, (f i y ^ K + K * |g i y - f i y|) ∂(stdGaussian (F i)) :=
            integral_mono hgK ((hfK i).add (hgf'.const_mul K)) hpt
        _ = m i + K * ∫ y, |g i y - f i y| ∂(stdGaussian (F i)) := by
            rw [integral_add (hfK i) (hgf'.const_mul K), integral_const_mul]
        _ ≤ m i + K * ε := by gcongr; exact hgf i
    have hgK0 : ∀ i, 0 ≤ ∫ y, g i y ^ K ∂(stdGaussian (F i)) := fun i =>
      integral_nonneg fun y => Real.rpow_nonneg (hg0 i y).le _
    calc A ≤ ∫ x, ∏ i, g i (U i x) ∂(stdGaussian E) + Fintype.card ι * ε := hleft
      _ ≤ ∏ i, (∫ y, g i y ^ K ∂(stdGaussian (F i))) ^ K⁻¹ + Fintype.card ι * ε := by
          gcongr
      _ ≤ ∏ i, (m i + K * ε) ^ K⁻¹ + Fintype.card ι * ε :=
          add_le_add_left (Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (hgK0 i) _)
            fun i _ => Real.rpow_le_rpow (hgK0 i) (hright i) (inv_nonneg.2 hK0.le)) _
  -- let `ε → 0`
  have hcont : Continuous fun ε : ℝ => ∏ i, (m i + K * ε) ^ K⁻¹ + Fintype.card ι * ε :=
    (continuous_finsetProd _ fun i _ => (Real.continuous_rpow_const (inv_nonneg.2 hK0.le)).comp
      (continuous_const.add (continuous_const.mul continuous_id))).add
      (continuous_const.mul continuous_id)
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [mul_zero, add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

end Geom

end HigherDimLQGMetric.Gauss
