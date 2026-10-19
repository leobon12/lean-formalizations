import GaussianLQG.Field.Realization.Field
import GaussianLQG.Field.Realization.Potential

/-!
# Mollified pairings of the coordinate field as limits of coordinate series

For `ω` in the convergence set `goodSet b` and a finite measure `ρ` with bounded support,
`∫ ⟨h̃(ω), ψ_{m,x}⟩ ρ(dx)` is the limit, along the subsequence `N_j`, of the partial sums of the
coordinate series with coefficients `∫∫ ψ_{m,x} ẽ_k dy ρ(dx)` (`tendsto_psum_pairCoef`).

Proof: `⟨h̃(ω), ψ_{m,x}⟩ = ∫ Y(ω) ∂_re ∂_im ψ_{m,x}` with `∂_re ∂_im ψ_{m,x} = (∂_re ∂_im ψ_{m,0})(· - x)`
(`d12_bumpTest`), the partial sums `S_{N_j}(ω)` converge to `Y(ω)` uniformly on compacts, and the
frame identity turns `∫ S_N ∂_re ∂_im ψ_{m,x}` into `∑_{k<N} ω_k ∫ ψ_{m,x} ẽ_k`; dominated
convergence in `x`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace GaussianLQG
namespace Realization

open LQGMetric LQGMetric.GFFExist

/-! ### Derivatives of translated mollifiers -/

lemma lineDerivCLM_apply' (v : ℂ) (φ : TestC) (z : ℂ) :
    (TestFunction.lineDerivCLM ℝ v : TestC →L[ℝ] TestC) φ z = fderiv ℝ (φ : ℂ → ℝ) z v := by
  rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply, ite_eq_left le_top]

lemma d12_apply (φ : TestC) (y : ℂ) :
    d12 φ y = fderiv ℝ (fun z => fderiv ℝ (φ : ℂ → ℝ) z Complex.I) y 1 := by
  have h : ((TestFunction.lineDerivCLM ℝ Complex.I : TestC →L[ℝ] TestC) φ : ℂ → ℝ) =
      fun z => fderiv ℝ (φ : ℂ → ℝ) z Complex.I := funext fun z => lineDerivCLM_apply' _ φ z
  show (TestFunction.lineDerivCLM ℝ (1 : ℂ) : TestC →L[ℝ] TestC)
      ((TestFunction.lineDerivCLM ℝ Complex.I : TestC →L[ℝ] TestC) φ) y = _
  rw [lineDerivCLM_apply', h]

/-- `∂_re ∂_im ψ_{m,x} = (∂_re ∂_im ψ_{m,0})(· - x)`. -/
lemma d12_bumpTest (m : ℕ) (x y : ℂ) : d12 (bumpTest m x) y = d12 (bumpTest m 0) (y - x) := by
  have hψ : (bumpTest m x : ℂ → ℝ) = fun z => bumpTest m 0 (z - x) :=
    funext (CircleAvg.bumpTest_eq_sub m x)
  rw [d12_apply, d12_apply, hψ]
  have h1 : (fun z => fderiv ℝ (fun z => bumpTest m 0 (z - x)) z Complex.I) =
      fun z => (fun w => fderiv ℝ (bumpTest m 0 : ℂ → ℝ) w Complex.I) (z - x) := by
    funext z
    rw [fderiv_comp_sub (f := (bumpTest m 0 : ℂ → ℝ))]
  rw [h1, fderiv_comp_sub (f := fun w => fderiv ℝ (bumpTest m 0 : ℂ → ℝ) w Complex.I)]

lemma integral_abs_d12_bumpTest (m : ℕ) (x : ℂ) :
    ∫ y, |d12 (bumpTest m x) y| = ∫ y, |d12 (bumpTest m 0) y| := by
  have e : (fun y => |d12 (bumpTest m x) y|) = fun y => |d12 (bumpTest m 0) (y - x)| :=
    funext fun y => by rw [d12_bumpTest m x y]
  rw [e]
  exact integral_sub_right_eq_self (fun y => |d12 (bumpTest m 0) y|) x

/-- Measurability of `x ↦ ∫ (∂_re ∂_im ψ_{m,x}) Z`. -/
lemma measurable_integral_d12_bump (m : ℕ) {Z : ℂ → ℝ} (hZ : Continuous Z) :
    Measurable fun x => ∫ y, d12 (bumpTest m x) y * Z y := by
  have e : (fun x => ∫ y, d12 (bumpTest m x) y * Z y) =
      fun x => ∫ y, d12 (bumpTest m 0) (y - x) * Z y :=
    funext fun x => integral_congr_ae (Eventually.of_forall fun y => by
      simp only [d12_bumpTest m x y])
  rw [e]
  have hc : Continuous fun p : ℂ × ℂ => d12 (bumpTest m 0) (p.2 - p.1) * Z p.2 :=
    ((d12 (bumpTest m 0)).continuous.comp (continuous_snd.sub continuous_fst)).mul
      (hZ.comp continuous_snd)
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- Measurability of `x ↦ ∫ ψ_{m,x} f`. -/
lemma measurable_integral_bump_mul (m : ℕ) {f : ℂ → ℝ} (hf : Continuous f) :
    Measurable fun x => ∫ y, bumpTest m x y * f y := by
  have e : (fun x => ∫ y, bumpTest m x y * f y) = fun x => ∫ y, bumpTest m 0 (y - x) * f y :=
    funext fun x => integral_congr_ae (Eventually.of_forall fun y => by
      simp only [CircleAvg.bumpTest_eq_sub m x y])
  rw [e]
  have hc : Continuous fun p : ℂ × ℂ => bumpTest m 0 (p.2 - p.1) * f p.2 :=
    ((bumpTest m 0).continuous.comp (continuous_snd.sub continuous_fst)).mul
      (hf.comp continuous_snd)
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma integrable_bump_mul (m : ℕ) (x : ℂ) {f : ℂ → ℝ} (hf : Continuous f) :
    Integrable fun y => bumpTest m x y * f y :=
  ((bumpTest m x).continuous.mul hf).integrable_of_hasCompactSupport
    (bumpTest m x).hasCompactSupport.mul_right

lemma abs_integral_bump_mul_le (m : ℕ) (x : ℂ) {f : ℂ → ℝ} (hf : Continuous f) {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) : |∫ y, bumpTest m x y * f y| ≤ B := by
  have hψ : Integrable fun y => bumpTest m x y :=
    (bumpTest m x).continuous.integrable_of_hasCompactSupport (bumpTest m x).hasCompactSupport
  calc |∫ y, bumpTest m x y * f y| ≤ ∫ y, |bumpTest m x y * f y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, bumpTest m x y * B := by
        refine integral_mono (integrable_bump_mul m x hf).abs (hψ.mul_const B) fun y => ?_
        rw [abs_mul, abs_of_nonneg (CircleAvg.bumpTest_nonneg m x y)]
        exact mul_le_mul_of_nonneg_left (hB y) (CircleAvg.bumpTest_nonneg m x y)
    _ = B := by rw [integral_mul_const, CircleAvg.integral_bumpTest', one_mul]

lemma integral_bump_mul_add_const (m : ℕ) (x : ℂ) {f : ℂ → ℝ} (hf : Continuous f) (c : ℝ) :
    ∫ y, bumpTest m x y * (f y + c) = (∫ y, bumpTest m x y * f y) + c := by
  have hψ : Integrable fun y => bumpTest m x y :=
    (bumpTest m x).continuous.integrable_of_hasCompactSupport (bumpTest m x).hasCompactSupport
  simp_rw [mul_add]
  rw [integral_add (integrable_bump_mul m x hf) (hψ.mul_const c), integral_mul_const,
    CircleAvg.integral_bumpTest', one_mul]

/-- An integrable function against a finite measure: bounded measurable functions. -/
lemma integrable_of_bounded {ρ : Measure ℂ} [IsFiniteMeasure ρ] {f : ℂ → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f ρ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

/-! ### The pairing coefficients -/

variable (b : HilbertBasis ℕ ℝ WNSpace)

/-- `P_{m,k}(ρ) = ∫∫ ψ_{m,x}(y) ẽ_k(y) dy ρ(dx)`. -/
def pairCoef (m : ℕ) (ρ : Measure ℂ) (k : ℕ) : ℝ :=
  ∫ x, (∫ y, bumpTest m x y * frameFun0 (b k) y) ∂ρ

lemma measurable_tildeField_bump {ω : Coord} (hω : ω ∈ goodSet b) (m : ℕ) :
    Measurable fun x => tildeField b ω (bumpTest m x) := by
  have e : (fun x => tildeField b ω (bumpTest m x)) =
      fun x => ∫ y, d12 (bumpTest m x) y * Ylim b ω y :=
    funext fun x => by simp only [tildeField_apply, Yfield_of_mem b hω]
  rw [e]
  exact measurable_integral_d12_bump m (continuous_Ylim b hω)

variable (hb : ∀ j, IsNiceWN (b j))
include hb

/-- `∫ S_N ∂_re ∂_im φ = ∑_{k<N} ω_k ∫ φ ẽ_k`. -/
lemma integral_d12_mul_fieldSum (φ : TestC) (N : ℕ) (ω : Coord) :
    ∫ y, d12 φ y * fieldSum b N ω y =
      ∑ k ∈ Finset.range N, ω k * ∫ y, φ y * frameFun0 (b k) y := by
  have e : ∀ y, d12 φ y * fieldSum b N ω y =
      ∑ k ∈ Finset.range N, ω k * (d12 φ y * rectCoef b y k) := fun y => by
    simp only [fieldSum, psum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun k _ =>
    (integrable_d12_mul_slice φ _ (continuous_rectCoef b k)).const_mul (ω k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_d12_mul_rectCoef b φ (hb k)]

/-- **Representation of mollified pairings.** For `ω` in the convergence set and a finite
measure `ρ` with bounded support, `∫ ⟨h̃(ω), ψ_{m,x}⟩ ρ(dx)` is the limit of the partial sums of
the coordinate series with coefficients `pairCoef b m ρ`, along the subsequence `N_j`. -/
theorem tendsto_psum_pairCoef {ω : Coord} (hω : ω ∈ goodSet b) (m : ℕ) {ρ : Measure ℂ}
    [IsFiniteMeasure ρ] {R : ℝ} (hR : ρ (closedBall (0 : ℂ) R)ᶜ = 0) :
    Integrable (fun x => tildeField b ω (bumpTest m x)) ρ ∧
      Tendsto (fun j => psum (pairCoef b m ρ) (subN b j) ω) atTop
        (𝓝 (∫ x, tildeField b ω (bumpTest m x) ∂ρ)) := by
  obtain ⟨L, hL0, hL⟩ := testC_exists_vanish (d12 (bumpTest m 0))
  set A : ℝ := ∫ y, |d12 (bumpTest m 0) y| with hA
  have hA0 : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  obtain ⟨M, hM⟩ := exists_nat_ge (R + L)
  have hU := tendstoUniformlyOn_Ylim b hω M
  set T : ℂ → ℝ := fun x => tildeField b ω (bumpTest m x) with hTdef
  set S : ℕ → ℂ → ℝ := fun j x => ∫ y, d12 (bumpTest m x) y * fieldSum b (subN b j) ω y
    with hSdef
  have hT : ∀ x, T x = ∫ y, d12 (bumpTest m x) y * Ylim b ω y := fun x => by
    simp only [hTdef, tildeField_apply, Yfield_of_mem b hω]
  -- the key uniform estimate
  have hkey : ∀ ε > 0, ∀ᶠ j in atTop, ∀ x ∈ closedBall (0 : ℂ) R, |T x - S j x| ≤ A * ε := by
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU ε hε] with j hj x hx
    rw [hT x]
    have hi1 : Integrable fun y => d12 (bumpTest m x) y * Ylim b ω y :=
      integrable_d12_mul_slice _ _ (continuous_Ylim b hω)
    have hi2 : Integrable fun y => d12 (bumpTest m x) y * fieldSum b (subN b j) ω y :=
      integrable_d12_mul_slice _ _ (continuous_fieldSum b _ ω)
    have hdi : Integrable fun y => |d12 (bumpTest m x) y| := (GFFInv.integrable_test _).abs
    simp only [hSdef]
    rw [← integral_sub hi1 hi2]
    calc |∫ y, (d12 (bumpTest m x) y * Ylim b ω y -
          d12 (bumpTest m x) y * fieldSum b (subN b j) ω y)|
        ≤ ∫ y, |d12 (bumpTest m x) y * Ylim b ω y -
          d12 (bumpTest m x) y * fieldSum b (subN b j) ω y| := abs_integral_le_integral_abs
      _ ≤ ∫ y, |d12 (bumpTest m x) y| * ε := by
          refine integral_mono (hi1.sub hi2).abs (hdi.mul_const ε) fun y => ?_
          rw [← mul_sub, abs_mul]
          by_cases hy : y ∈ closedBall (0 : ℂ) M
          · have := hj y hy
            rw [Real.dist_eq] at this
            exact mul_le_mul_of_nonneg_left this.le (abs_nonneg _)
          · have hy' : (M : ℝ) < ‖y‖ := by
              simpa [mem_closedBall, dist_zero_right, not_le] using hy
            have hx' : ‖x‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at hx
            have hyx : L < ‖y - x‖ := by
              have := norm_sub_norm_le y x
              linarith
            rw [d12_bumpTest, hL _ hyx, abs_zero, zero_mul, zero_mul]
      _ = A * ε := by rw [integral_mul_const, integral_abs_d12_bumpTest]
  -- measurability
  have hTm : Measurable T := by
    have e : T = fun x => ∫ y, d12 (bumpTest m x) y * Ylim b ω y := funext hT
    rw [e]
    exact measurable_integral_d12_bump m (continuous_Ylim b hω)
  have hSm : ∀ j, Measurable (S j) := fun j =>
    measurable_integral_d12_bump m (continuous_fieldSum b _ ω)
  -- the partial sums
  have hSe : ∀ j x, S j x = ∑ k ∈ Finset.range (subN b j),
      ω k * ∫ y, bumpTest m x y * frameFun0 (b k) y := fun j x =>
    integral_d12_mul_fieldSum b hb (bumpTest m x) _ ω
  have hIk : ∀ k, Integrable (fun x => ∫ y, bumpTest m x y * frameFun0 (b k) y) ρ := by
    intro k
    obtain ⟨B, hB⟩ := exists_bound_frameFun0 (hb k)
    exact integrable_of_bounded (measurable_integral_bump_mul m (continuous_frameFun0 (hb k)))
      fun x => abs_integral_bump_mul_le m x (continuous_frameFun0 (hb k)) hB
  have hSi : ∀ j, Integrable (S j) ρ := by
    intro j
    have e : S j = fun x => ∑ k ∈ Finset.range (subN b j),
        ω k * ∫ y, bumpTest m x y * frameFun0 (b k) y := funext (hSe j)
    rw [e]
    exact integrable_finsetSum _ fun k _ => (hIk k).const_mul (ω k)
  have hSint : ∀ j, ∫ x, S j x ∂ρ = psum (pairCoef b m ρ) (subN b j) ω := by
    intro j
    simp_rw [hSe j]
    rw [integral_finsetSum _ fun k _ => (hIk k).const_mul (ω k)]
    simp only [psum, pairCoef, integral_const_mul]
  -- integrability of `T`
  have hTi : Integrable T ρ := by
    obtain ⟨j, hj⟩ := (hkey 1 one_pos).exists
    refine ((hSi j).abs.add (integrable_const (A * 1))).mono' hTm.aestronglyMeasurable ?_
    filter_upwards [ae_norm_le_of_compl_closedBall_eq_zero hR] with x hx
    have h := hj x (by rwa [mem_closedBall, dist_zero_right])
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    have := abs_sub_abs_le_abs_sub (T x) (S j x)
    linarith
  refine ⟨hTi, ?_⟩
  -- dominated convergence
  have hlim : ∀ x ∈ closedBall (0 : ℂ) R, Tendsto (fun j => S j x) atTop (𝓝 (T x)) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε' : 0 < ε / (A + 1) := div_pos hε (by linarith)
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hkey (ε / (A + 1)) hε')
    refine ⟨J, fun j hj => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    have h1 := hJ j hj x hx
    have h2 : A * (ε / (A + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := ρ) (l := atTop)
    (F := S) (f := T) (fun x => |T x| + A * 1)
    (Eventually.of_forall fun j => (hSm j).aestronglyMeasurable)
    (by
      filter_upwards [hkey 1 one_pos] with j hj
      filter_upwards [ae_norm_le_of_compl_closedBall_eq_zero hR] with x hx
      have h := hj x (by rwa [mem_closedBall, dist_zero_right])
      rw [Real.norm_eq_abs]
      have := abs_sub_abs_le_abs_sub (S j x) (T x)
      rw [abs_sub_comm] at h
      linarith)
    (hTi.abs.add (integrable_const _))
    (by
      filter_upwards [ae_norm_le_of_compl_closedBall_eq_zero hR] with x hx
      exact hlim x (by rwa [mem_closedBall, dist_zero_right]))
  simp_rw [hSint] at hconv
  exact hconv

end Realization
end GaussianLQG
