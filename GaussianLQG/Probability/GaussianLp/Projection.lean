import GaussianLQG.Probability.GaussianLp.CoordDeriv
import GaussianLQG.Probability.GaussianLp.FiniteDim

/-!
# Projection to `n` coordinates

Blueprint Proposition `prop:gaussian-Lp`, step "Projection to `n` coordinates". Write
`ω = (x, y)` with `x ∈ ℝⁿ` (`joinN`), so that `P = γₙ ⊗ P`. Under (H):

* `ae_abs_sub_joinN_le`: for a.e. `y`, `|F(x, y) - F(x', y)| ≤ ∑_{i<n} L_i |x_i - x'_i|` for
  *all* `x, x'` (hypothesis (H) at a point `(x₀, y) ∈ 𝒢`);
* `projF F n x = ∫ F(x, y) dP(y)` is defined by an integrable integrand for *every* `x`
  (`integrable_joinN`), is Lipschitz (`lipschitzWith_projF`) and has mean `E F`
  (`integral_projF`);
* `hasDerivAt_projF`: for a.e. `x`, `∂_j F_n(x) = ∫ ∂_j F(x, y) dP(y)` (dominated convergence:
  the difference quotients are bounded by `L_j`);
* `gradient_bound`: Minkowski's inequality in `ℝⁿ` and Jensen give
  `|∇F_n(x)|^p ≤ ∫ Γ(x, y)^p dP(y)` with `Γ = (∑_j |∂_j F|²)^{1/2}` (valued in `[0, ∞]`);
* `lintegral_projF_sub_le`: the finite-dimensional inequality then gives
  `E|F_n - E F|^p ≤ (π/2)^p E|N|^p E Γ^p`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

namespace GaussLp

/-- The projection `F_n(x) = ∫ F(x, y) dP(y)` of `F` onto the first `n` coordinates. -/
def projF (F : Coord → ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ := ∫ y, F (joinN n x y) ∂stdP

/-- `Γ^p = (∑_j |∂_j F|²)^{p/2}`, valued in `[0, ∞]`. -/
def gradPow (F : Coord → ℝ) (p : ℝ) (ω : Coord) : ℝ≥0∞ :=
  (∑' j, ENNReal.ofReal (coordDeriv F j ω ^ 2)) ^ (p / 2)

lemma measurable_joinN_left (n : ℕ) (x : Fin n → ℝ) : Measurable fun y : Coord => joinN n x y :=
  (measurable_joinN n).comp (measurable_const.prodMk measurable_id)

lemma measurable_comp_joinN_left {F : Coord → ℝ} (hF : Measurable F) (n : ℕ) (x : Fin n → ℝ) :
    Measurable fun y : Coord => F (joinN n x y) :=
  hF.comp (measurable_joinN_left n x)

section Projection

variable {F : Coord → ℝ} {𝒢 : Set Coord} {L : ℕ → ℝ}

lemma integrable_prod_joinN (hFi : Integrable F stdP) (n : ℕ) :
    Integrable (fun z : (Fin n → ℝ) × Coord => F (joinN n z.1 z.2)) ((gaussPi n).prod stdP) :=
  ((measurePreserving_joinN n).integrable_comp hFi.aestronglyMeasurable).2 hFi

/-- For a.e. `y`, `|F(x, y) - F(x', y)| ≤ ∑_{i<n} L_i |x_i - x'_i|` for all `x, x'`. -/
lemma ae_abs_sub_joinN_le (h𝒢 : MeasurableSet 𝒢) (h𝒢c : stdP 𝒢ᶜ = 0)
    (hH : ShiftLipschitzOn F 𝒢 L) (n : ℕ) :
    ∀ᵐ y ∂stdP, ∀ x x' : Fin n → ℝ,
      |F (joinN n x y) - F (joinN n x' y)| ≤ ∑ i : Fin n, L i * |x i - x' i| := by
  filter_upwards [ae_exists_joinN_mem h𝒢 h𝒢c n] with y hy
  obtain ⟨x₀, hx₀⟩ := hy
  exact hH.joinN_le hx₀

/-- `y ↦ F(x, y)` is integrable for *every* `x ∈ ℝⁿ`. -/
lemma integrable_joinN (hF : Measurable F) (hFi : Integrable F stdP) (h𝒢 : MeasurableSet 𝒢)
    (h𝒢c : stdP 𝒢ᶜ = 0) (hH : ShiftLipschitzOn F 𝒢 L) (n : ℕ) (x : Fin n → ℝ) :
    Integrable (fun y => F (joinN n x y)) stdP := by
  obtain ⟨x₁, hx₁⟩ := (integrable_prod_joinN hFi n).prod_right_ae.exists
  have hx₁' : Integrable (fun y => F (joinN n x₁ y)) stdP := hx₁
  refine Integrable.mono' (hx₁'.abs.add (integrable_const (∑ i : Fin n, L i * |x i - x₁ i|)))
    (hF.comp (measurable_joinN_left n x)).aestronglyMeasurable ?_
  filter_upwards [ae_abs_sub_joinN_le h𝒢 h𝒢c hH n] with y hy
  have h1 := hy x x₁
  have h2 := abs_sub_abs_le_abs_sub (F (joinN n x y)) (F (joinN n x₁ y))
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  linarith

/-- `|F_n(x) - F_n(x')| ≤ ∑_{i<n} L_i |x_i - x'_i|`. -/
lemma abs_projF_sub_le (hF : Measurable F) (hFi : Integrable F stdP) (h𝒢 : MeasurableSet 𝒢)
    (h𝒢c : stdP 𝒢ᶜ = 0) (hH : ShiftLipschitzOn F 𝒢 L) (n : ℕ) (x x' : Fin n → ℝ) :
    |projF F n x - projF F n x'| ≤ ∑ i : Fin n, L i * |x i - x' i| := by
  unfold projF
  rw [← integral_sub (integrable_joinN hF hFi h𝒢 h𝒢c hH n x)
    (integrable_joinN hF hFi h𝒢 h𝒢c hH n x'), ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := stdP)
    (f := fun y => F (joinN n x y) - F (joinN n x' y)) (C := ∑ i : Fin n, L i * |x i - x' i|)
    (by
      filter_upwards [ae_abs_sub_joinN_le h𝒢 h𝒢c hH n] with y hy
      rw [Real.norm_eq_abs]
      exact hy x x')
  rwa [probReal_univ, mul_one] at h

/-- `F_n` is Lipschitz on `ℝⁿ`. -/
lemma lipschitzWith_projF (hF : Measurable F) (hFi : Integrable F stdP) (h𝒢 : MeasurableSet 𝒢)
    (h𝒢c : stdP 𝒢ᶜ = 0) (hH : ShiftLipschitzOn F 𝒢 L) (hL : ∀ i, 0 ≤ L i) (n : ℕ) :
    LipschitzWith (∑ i : Fin n, L i).toNNReal (projF F n) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [Real.dist_eq, Real.coe_toNNReal (∑ i : Fin n, L i) (Finset.sum_nonneg fun i _ => hL i)]
  exact (abs_projF_sub_le hF hFi h𝒢 h𝒢c hH n x x').trans (sum_mul_abs_le_mul_dist hL x x')

/-- `E F_n = E F`. -/
lemma integral_projF (hFi : Integrable F stdP) (n : ℕ) :
    ∫ x, projF F n x ∂gaussPi n = ∫ ω, F ω ∂stdP := by
  unfold projF
  calc ∫ x, ∫ y, F (joinN n x y) ∂stdP ∂gaussPi n
      = ∫ z, F (joinN n z.1 z.2) ∂(gaussPi n).prod stdP :=
        (integral_prod _ (integrable_prod_joinN hFi n)).symm
    _ = ∫ ω, F ω ∂stdP :=
        (measurePreserving_joinN n).integral_comp (measurableEmbedding_joinN n) F

/-- `∂_j F(x, y)` is a.e. strongly measurable on the product. -/
lemma aestronglyMeasurable_coordDeriv_joinN (hF : Measurable F) (h𝒢 : MeasurableSet 𝒢)
    (h𝒢c : stdP 𝒢ᶜ = 0) (hH : ShiftLipschitzOn F 𝒢 L) (n j : ℕ) :
    AEStronglyMeasurable (fun z : (Fin n → ℝ) × Coord => coordDeriv F j (joinN n z.1 z.2))
      ((gaussPi n).prod stdP) :=
  (aestronglyMeasurable_coordDeriv hF h𝒢 h𝒢c hH j).comp_measurePreserving
    (measurePreserving_joinN n)

/-- **Differentiation under the integral sign**: for a.e. `x`,
`∂_j F_n(x) = ∫ ∂_j F(x, y) dP(y)` for every `j < n`. -/
lemma hasDerivAt_projF (hF : Measurable F) (hFi : Integrable F stdP) (h𝒢 : MeasurableSet 𝒢)
    (h𝒢c : stdP 𝒢ᶜ = 0) (hH : ShiftLipschitzOn F 𝒢 L) (hL : ∀ i, 0 ≤ L i) (n : ℕ) :
    ∀ᵐ x ∂gaussPi n, ∀ j : Fin n, HasDerivAt (fun t : ℝ => projF F n (x + t • Pi.single j 1))
      (∫ y, coordDeriv F j (joinN n x y) ∂stdP) 0 := by
  rw [ae_all_iff]
  intro j
  have hdiff : ∀ᵐ z ∂(gaussPi n).prod stdP,
      HasDerivAt (fun t : ℝ => F (shiftBy (joinN n z.1 z.2) (Finsupp.single j t)))
        (coordDeriv F j (joinN n z.1 z.2)) 0 :=
    ae_joinN_of_ae n ((ae_differentiableAt_coord hF h𝒢 h𝒢c hH j).mono fun ω hω => hω.hasDerivAt)
  filter_upwards [Measure.ae_ae_of_ae_prod hdiff,
    (aestronglyMeasurable_coordDeriv_joinN hF h𝒢 h𝒢c hH n j).prodMk_left] with x hx hxm
  have hj : (j : ℕ) < n := j.isLt
  have hline : ∀ (y : Coord) (t : ℝ), F (shiftBy (joinN n x y) (Finsupp.single j t)) =
      F (joinN n (x + t • Pi.single j 1) y) := by
    intro y t
    rw [shiftBy_joinN_single hj]
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := stdP) (𝕜 := ℝ)
    (F := fun t y => F (joinN n (x + t • Pi.single j 1) y))
    (F' := fun y => coordDeriv F j (joinN n x y)) (x₀ := 0) (s := Set.univ)
    (bound := fun _ => L j) Filter.univ_mem
    (Eventually.of_forall fun t =>
      (measurable_comp_joinN_left hF n (x + t • Pi.single j 1)).aestronglyMeasurable)
    (integrable_joinN hF hFi h𝒢 h𝒢c hH n _) hxm ?_ (integrable_const _) ?_
  · exact key.2
  · filter_upwards [ae_exists_joinN_mem h𝒢 h𝒢c n] with y hy
    obtain ⟨x₀, hx₀⟩ := hy
    have hlip := hH.lipschitzWith_line_joinN hL hj hx₀ x
    rw [Real.nnabs_of_nonneg (hL j)]
    simp only [hline] at hlip
    exact hlip.lipschitzOnWith
  · filter_upwards [hx] with y hy
    simp only [hline] at hy
    exact hy

/-- `ofReal (∑_{j<n} a_j²) ≤ ∑'_j ofReal (a_j²)`. -/
lemma ofReal_sum_sq_le_tsum (n : ℕ) (a : ℕ → ℝ) :
    ENNReal.ofReal (∑ j : Fin n, a j ^ 2) ≤ ∑' j, ENNReal.ofReal (a j ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _,
    Fin.sum_univ_eq_sum_range (fun j => ENNReal.ofReal (a j ^ 2)) n]
  exact ENNReal.sum_le_tsum _

/-- **Minkowski and Jensen**: for a.e. `x`,
`(∑_{j<n} (∫ ∂_j F(x, y) dP(y))²)^{p/2} ≤ ∫ Γ(x, y)^p dP(y)`. -/
lemma gradient_bound (hF : Measurable F) (h𝒢 : MeasurableSet 𝒢) (h𝒢c : stdP 𝒢ᶜ = 0)
    (hH : ShiftLipschitzOn F 𝒢 L) (hL : ∀ i, 0 ≤ L i) (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    ∀ᵐ x ∂gaussPi n,
      ENNReal.ofReal (∑ j : Fin n, (∫ y, coordDeriv F j (joinN n x y) ∂stdP) ^ 2) ^ (p / 2) ≤
        ∫⁻ y, gradPow F p (joinN n x y) ∂stdP := by
  have hp0 : 0 ≤ p := by linarith
  have hmeas : ∀ᵐ x ∂gaussPi n, ∀ j : Fin n,
      AEStronglyMeasurable (fun y => coordDeriv F j (joinN n x y)) stdP :=
    ae_all_iff.2 fun j => (aestronglyMeasurable_coordDeriv_joinN hF h𝒢 h𝒢c hH n j).prodMk_left
  filter_upwards [hmeas] with x hx
  set W : Coord → (Fin n → ℝ) := fun y j => coordDeriv F j (joinN n x y) with hW
  set e := EuclideanSpace.equiv (Fin n) ℝ
  -- each component is bounded by `L_j`, hence integrable
  have hWi : ∀ j : Fin n, Integrable (fun y => W y j) stdP := by
    intro j
    refine Integrable.of_bound (hx j) (L j) ?_
    filter_upwards [ae_exists_joinN_mem h𝒢 h𝒢c n] with y hy
    obtain ⟨x₀, hx₀⟩ := hy
    rw [Real.norm_eq_abs]
    have h := abs_coordDeriv_le_of_lipschitzWith (hH.lipschitzWith_line_joinN hL j.isLt hx₀ x)
    rwa [Real.coe_toNNReal _ (hL j)] at h
  have hWint : Integrable W stdP := Integrable.of_eval hWi
  set V : Coord → EuclideanSpace ℝ (Fin n) := fun y => e.symm (W y) with hV
  have hVi : Integrable V stdP := (e.symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)).integrable_comp hWint
  have hnormV : ∀ y, ‖V y‖ ^ 2 = ∑ j : Fin n, W y j ^ 2 := by
    intro y
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hintV : ∫ y, V y ∂stdP = e.symm (∫ y, W y ∂stdP) :=
    e.symm.integral_comp_comm W
  have hnormI : ‖∫ y, V y ∂stdP‖ ^ 2 = ∑ j : Fin n, (∫ y, coordDeriv F j (joinN n x y) ∂stdP) ^ 2 := by
    rw [hintV, EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (e.symm (∫ y, W y ∂stdP)).ofLp j = (∫ y, W y ∂stdP) j from rfl,
      eval_integral hWi j]
  have hVm : AEMeasurable (fun y => ENNReal.ofReal ‖V y‖) stdP :=
    hVi.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
  calc ENNReal.ofReal (∑ j : Fin n, (∫ y, coordDeriv F j (joinN n x y) ∂stdP) ^ 2) ^ (p / 2)
      = ENNReal.ofReal ‖∫ y, V y ∂stdP‖ ^ p := by
        rw [ofReal_rpow_eq_ofReal_sq_rpow (norm_nonneg _) hp0, hnormI]
    _ ≤ ENNReal.ofReal (∫ y, ‖V y‖ ∂stdP) ^ p :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)) hp0
    _ = (∫⁻ y, ENNReal.ofReal ‖V y‖ ∂stdP) ^ p := by
        rw [ofReal_integral_eq_lintegral_ofReal hVi.norm (ae_of_all _ fun y => norm_nonneg _)]
    _ ≤ ∫⁻ y, ENNReal.ofReal ‖V y‖ ^ p ∂stdP := lintegral_rpow_le_of_prob hVm hp
    _ ≤ ∫⁻ y, gradPow F p (joinN n x y) ∂stdP := by
        refine lintegral_mono fun y => ?_
        rw [ofReal_rpow_eq_ofReal_sq_rpow (norm_nonneg _) hp0, hnormV, gradPow]
        exact ENNReal.rpow_le_rpow
          (ofReal_sum_sq_le_tsum n fun k => coordDeriv F k (joinN n x y)) (by positivity)

/-- `Γ^p` is a.e. measurable on the product. -/
lemma aemeasurable_gradPow_joinN (hF : Measurable F) (h𝒢 : MeasurableSet 𝒢)
    (h𝒢c : stdP 𝒢ᶜ = 0) (hH : ShiftLipschitzOn F 𝒢 L) (n : ℕ) (p : ℝ) :
    AEMeasurable (fun z : (Fin n → ℝ) × Coord => gradPow F p (joinN n z.1 z.2))
      ((gaussPi n).prod stdP) := by
  unfold gradPow
  refine AEMeasurable.pow_const (AEMeasurable.tsum fun k => ?_) _
  exact ((aestronglyMeasurable_coordDeriv_joinN hF h𝒢 h𝒢c hH n k).aemeasurable.pow_const
    2).ennreal_ofReal

/-- **Projection step**: `E|F_n - E F|^p ≤ (π/2)^p E|N|^p E Γ^p`. -/
theorem lintegral_projF_sub_le (hF : Measurable F) (hFi : Integrable F stdP)
    (h𝒢 : MeasurableSet 𝒢) (h𝒢c : stdP 𝒢ᶜ = 0) (hH : ShiftLipschitzOn F 𝒢 L)
    (hL : ∀ i, 0 ≤ L i) (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖projF F n x - ∫ ω, F ω ∂stdP‖ₑ ^ p ∂gaussPi n ≤
      ENNReal.ofReal (Real.pi / 2) ^ p * (∫⁻ t, ‖t‖ₑ ^ p ∂gaussianReal 0 1) *
        ∫⁻ ω, gradPow F p ω ∂stdP := by
  have h := lintegral_rpow_sub_integral_le_gaussPi (lipschitzWith_projF hF hFi h𝒢 h𝒢c hH hL n)
    hp (hasDerivAt_projF hF hFi h𝒢 h𝒢c hH hL n)
  rw [integral_projF hFi n] at h
  refine h.trans ?_
  gcongr
  calc ∫⁻ x, ENNReal.ofReal (∑ j : Fin n, (∫ y, coordDeriv F j (joinN n x y) ∂stdP) ^ 2) ^ (p / 2)
        ∂gaussPi n
      ≤ ∫⁻ x, ∫⁻ y, gradPow F p (joinN n x y) ∂stdP ∂gaussPi n :=
        lintegral_mono_ae (gradient_bound hF h𝒢 h𝒢c hH hL n hp)
    _ = ∫⁻ z, gradPow F p (joinN n z.1 z.2) ∂(gaussPi n).prod stdP :=
        (lintegral_prod _ (aemeasurable_gradPow_joinN hF h𝒢 h𝒢c hH n p)).symm
    _ = ∫⁻ ω, gradPow F p ω ∂stdP :=
        (measurePreserving_joinN n).lintegral_comp_emb (measurableEmbedding_joinN n) _

end Projection

end GaussLp

end GaussianLQG
