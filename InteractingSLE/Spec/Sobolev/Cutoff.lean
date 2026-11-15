import InteractingSLE.Spec.Sobolev.Gagliardo
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Small-norm cutoffs near a set of zero `(2 - 2ε)`-dimensional Hausdorff measure

Source: `source/spec/p049-096.md`, proof of Aux. lemma 12 (`#aux-12-proof`, pp. 84–85): bumps
`v_j` on a finite ball cover with `Σ r_j^{2-2ε} < δ` satisfy `‖v_j‖²₂ + [v_j]²_ε ≤ C r_j^{2-2ε}`
("scaling in (SR4)"); `v = max_j v_j` satisfies (SR5); the mollification of `v` keeps the bound
("Jensen's inequality in (SR4)"); multiplication by a fixed test function is bounded on `H^ε`.

## Main results

* `gagJ`, `gagJ_lt_top`, `gagJ_div` : `J_ε(M) = ∫ min(1, M²|z|²) |z|^{-2-2ε} dz`, finite, and
  `J_ε(M / r) = r^{-2ε} J_ε(M)`;
* `gagSq_le_of_lipschitz` : `[w]²_ε ≤ 2 |B(c, R)| J_ε(M)` for `0 ≤ w ≤ 1`, `M`-Lipschitz, supported
  in `B(c, R)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function Real Metric
open scoped Distributions ContDiff ENNReal NNReal RealInnerProductSpace

namespace InteractingSLE.Sobolev

open LQGMetric TopologicalSpace

/-! ### The radial constant `J_ε(M)` -/

/-- `g_{ε,M}(z) = min(1, M²|z|²) |z|^{-2-2ε}`. -/
def gagG (ε M : ℝ) (z : ℂ) : ℝ := min 1 (M ^ 2 * ‖z‖ ^ 2) * gagKer ε z

theorem gagG_nonneg (ε M : ℝ) (z : ℂ) : 0 ≤ gagG ε M z :=
  mul_nonneg (le_min zero_le_one (by positivity)) (gagKer_nonneg _ _)

theorem measurable_gagG (ε M : ℝ) : Measurable (gagG ε M) :=
  (((continuous_const.min (continuous_const.mul (continuous_norm.pow 2)))).measurable).mul
    (measurable_gagKer ε)

/-- `J_ε(M) = ∫ min(1, M²|z|²) |z|^{-2-2ε} dz`. -/
def gagJ (ε M : ℝ) : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (gagG ε M z)

theorem integrable_gagG {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (M : ℝ) : Integrable (gagG ε M) := by
  have hmeas := (measurable_gagG ε M).aestronglyMeasurable (μ := volume)
  have h1 : IntegrableOn (gagG ε M) (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := M ^ 2) (α := 2 * ε)
      (by simp) (by simp; linarith) (Eventually.of_forall fun z => ?_) hmeas
    rw [Real.norm_eq_abs, abs_of_nonneg (gagG_nonneg _ _ _), gagG, gagKer]
    rcases eq_or_ne z 0 with rfl | hz
    · rw [norm_zero, Real.zero_rpow (by linarith : -(2 + 2 * ε) ≠ 0),
        Real.zero_rpow (by linarith : -(2 * ε) ≠ 0)]
      simp
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    calc min 1 (M ^ 2 * ‖z‖ ^ 2) * ‖z‖ ^ (-(2 + 2 * ε))
        ≤ M ^ 2 * ‖z‖ ^ 2 * ‖z‖ ^ (-(2 + 2 * ε)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = M ^ 2 * ‖z‖ ^ (-(2 * ε)) := by
          rw [mul_assoc, show (‖z‖ ^ 2 : ℝ) = ‖z‖ ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
            ← Real.rpow_add hz0]
          congr 2
          push_cast
          ring
  have h2 : IntegrableOn (gagG ε M) (ball (0 : ℂ) 1)ᶜ := by
    have hint := (integrable_one_add_norm (μ := volume) (E := ℂ) (r := 2 + 2 * ε)
      (by simp; linarith)).const_mul ((2 : ℝ) ^ (2 + 2 * ε))
    refine (hint.integrableOn).mono' hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_ball.compl).2 (Eventually.of_forall fun z hz => ?_)
    rw [mem_compl_iff, mem_ball_zero_iff, not_lt] at hz
    rw [Real.norm_eq_abs, abs_of_nonneg (gagG_nonneg _ _ _), gagG, gagKer]
    have hz0 : 0 < ‖z‖ := by linarith
    calc min 1 (M ^ 2 * ‖z‖ ^ 2) * ‖z‖ ^ (-(2 + 2 * ε)) ≤ 1 * ‖z‖ ^ (-(2 + 2 * ε)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = (2 * ‖z‖) ^ (-(2 + 2 * ε)) * 2 ^ (2 + 2 * ε) := by
          rw [one_mul, Real.mul_rpow (by norm_num) hz0.le, mul_comm ((2 : ℝ) ^ (-(2 + 2 * ε))),
            mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel,
            Real.rpow_zero, mul_one]
      _ ≤ (1 + ‖z‖) ^ (-(2 + 2 * ε)) * 2 ^ (2 + 2 * ε) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      _ = 2 ^ (2 + 2 * ε) * (1 + ‖z‖) ^ (-(2 + 2 * ε)) := mul_comm _ _
  have h := h1.union h2
  rw [union_compl_self, integrableOn_univ] at h
  exact h

theorem gagJ_lt_top {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (M : ℝ) : gagJ ε M < ⊤ :=
  (integrable_gagG hε0 hε1 M).lintegral_lt_top

/-- Scaling: `∫ F(z) dz = r² ∫ F(r z) dz` on `ℂ`. -/
theorem lintegral_eq_mul_lintegral_smul (F : ℂ → ℝ≥0∞) (hF : Measurable F) {r : ℝ} (hr : 0 < r) :
    ∫⁻ z, F z = ENNReal.ofReal (r ^ 2) * ∫⁻ z, F (r • z) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hr.ne'
  have h1 : ∫⁻ z, F (r • z) = ENNReal.ofReal |(r ^ 2)⁻¹| * ∫⁻ z, F z := by
    rw [← lintegral_map hF (measurable_const_smul r), hmap, lintegral_smul_measure]
    simp
  rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
    mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- `J_ε(M / r) = r^{-2ε} J_ε(M)`. -/
theorem gagJ_div {ε : ℝ} (M : ℝ) {r : ℝ} (hr : 0 < r) :
    gagJ ε (M / r) = ENNReal.ofReal (r ^ (-(2 * ε))) * gagJ ε M := by
  rw [gagJ, lintegral_eq_mul_lintegral_smul (fun z => ENNReal.ofReal (gagG ε (M / r) z))
    (ENNReal.measurable_ofReal.comp (measurable_gagG ε (M / r))) hr, gagJ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [gagG, gagKer, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  rw [Real.mul_rpow hr.le (norm_nonneg _), div_pow, mul_pow]
  have hr2 : r ^ 2 = r ^ (2 : ℝ) := (Real.rpow_two r).symm
  have e1 : M ^ 2 / r ^ 2 * (r ^ 2 * ‖z‖ ^ 2) = M ^ 2 * ‖z‖ ^ 2 := by field_simp
  rw [e1]
  have e2 : r ^ 2 * r ^ (-(2 + 2 * ε)) = r ^ (-(2 * ε)) := by
    rw [hr2, ← Real.rpow_add hr]; ring_nf
  calc r ^ 2 * (min 1 (M ^ 2 * ‖z‖ ^ 2) * (r ^ (-(2 + 2 * ε)) * ‖z‖ ^ (-(2 + 2 * ε))))
      = (r ^ 2 * r ^ (-(2 + 2 * ε))) * (min 1 (M ^ 2 * ‖z‖ ^ 2) * ‖z‖ ^ (-(2 + 2 * ε))) := by
        ring
    _ = _ := by rw [e2]

/-! ### Lipschitz bumps -/

/-- `[w]²_ε ≤ 2 |B(c, R)| J_ε(M)` for `w` with values in `[0, 1]`, `M`-Lipschitz, vanishing off
`B(c, R)`. -/
theorem gagSq_le_of_lipschitz {ε : ℝ} {w : ℂ → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {M : ℝ} (hwL : ∀ x y, |w x - w y| ≤ M * ‖x - y‖) {c : ℂ} {R : ℝ}
    (hsupp : ∀ x, x ∉ ball c R → w x = 0) :
    gagSq ε w ≤ 2 * volume (ball c R) * gagJ ε M := by
  have hM : 0 ≤ M := by
    have := hwL 1 0
    by_contra h
    push Not at h
    have : M * ‖(1 : ℂ) - 0‖ < 0 := by simp; linarith
    linarith [abs_nonneg (w 1 - w 0)]
  set B := ball c R
  have hpt : ∀ x y, ENNReal.ofReal ((w x - w y) ^ 2 * gagKer ε (x - y)) ≤
      B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) +
        B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y)) := by
    intro x y
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, Pi.one_apply, one_mul]
      refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
      refine mul_le_mul_of_nonneg_right ?_ (gagKer_nonneg _ _)
      refine le_min ?_ ?_
      · have : |w x - w y| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith [hw1 x, hw0 y],
          by linarith [hw1 y, hw0 x]⟩
        nlinarith [abs_nonneg (w x - w y), sq_abs (w x - w y)]
      · have h := hwL x y
        have := pow_le_pow_left₀ (abs_nonneg _) h 2
        rw [sq_abs, mul_pow] at this
        exact this
    · by_cases hy : y ∈ B
      · rw [indicator_of_mem hy, Pi.one_apply, one_mul]
        refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
        refine mul_le_mul_of_nonneg_right ?_ (gagKer_nonneg _ _)
        refine le_min ?_ ?_
        · have : |w x - w y| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith [hw1 x, hw0 y],
            by linarith [hw1 y, hw0 x]⟩
          nlinarith [abs_nonneg (w x - w y), sq_abs (w x - w y)]
        · have h := hwL x y
          have := pow_le_pow_left₀ (abs_nonneg _) h 2
          rw [sq_abs, mul_pow] at this
          exact this
      · rw [hsupp x hx, hsupp y hy]; simp
  have hmG : Measurable (uncurry fun (x y : ℂ) => ENNReal.ofReal (gagG ε M (x - y))) :=
    ENNReal.measurable_ofReal.comp ((measurable_gagG ε M).comp measurable_sub)
  have hind : Measurable (B.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator measurableSet_ball
  have hA : ∫⁻ x, ∫⁻ y, B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) =
      volume B * gagJ ε M := by
    have : ∀ x, ∫⁻ y, B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) =
        B.indicator 1 x * gagJ ε M := fun x => by
      rw [lintegral_const_mul' _ _ (by by_cases hx : x ∈ B <;> simp [hx]),
        lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (gagG ε M z)) x, gagJ]
    simp_rw [this]
    rw [lintegral_mul_const _ hind, lintegral_indicator_one measurableSet_ball]
  have hB : ∫⁻ x, ∫⁻ y, B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y)) =
      volume B * gagJ ε M := by
    rw [lintegral_lintegral_swap ((hind.comp measurable_snd).mul hmG).aemeasurable]
    have : ∀ y, ∫⁻ x, B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y)) =
        B.indicator 1 y * gagJ ε M := fun y => by
      rw [lintegral_const_mul' _ _ (by by_cases hy : y ∈ B <;> simp [hy]),
        lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (gagG ε M z)) y, gagJ]
    simp_rw [this]
    rw [lintegral_mul_const _ hind, lintegral_indicator_one measurableSet_ball]
  calc gagSq ε w ≤ ∫⁻ x, ∫⁻ y, (B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) +
        B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y))) :=
        lintegral_mono fun x => lintegral_mono fun y => hpt x y
    _ = (∫⁻ x, ∫⁻ y, B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y))) +
          ∫⁻ x, ∫⁻ y, B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y)) := by
        rw [← lintegral_add_left]
        · congr 1; funext x
          exact lintegral_add_left
            (f := fun y => B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)))
            (measurable_const.mul (ENNReal.measurable_ofReal.comp
              ((measurable_gagG ε M).comp (measurable_const.sub measurable_id)))) _
        · exact (((hind.comp measurable_fst).mul hmG).lintegral_prod_right')
    _ = 2 * volume B * gagJ ε M := by rw [hA, hB]; ring

/-! ### The maximum of finitely many functions: (SR5) -/

/-- `max(0, a₀, …, a_{n-1})`. -/
def finMax : {n : ℕ} → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | _ + 1, a => max (a 0) (finMax fun i => a i.succ)

theorem finMax_nonneg : ∀ {n : ℕ} (a : Fin n → ℝ), 0 ≤ finMax a
  | 0, _ => le_rfl
  | _ + 1, _ => le_max_of_le_right (finMax_nonneg _)

theorem finMax_le : ∀ {n : ℕ} (a : Fin n → ℝ) {c : ℝ}, 0 ≤ c → (∀ i, a i ≤ c) → finMax a ≤ c
  | 0, _, _, hc, _ => hc
  | _ + 1, _, _, hc, h => max_le (h 0) (finMax_le _ hc fun i => h i.succ)

theorem le_finMax : ∀ {n : ℕ} (a : Fin n → ℝ) (i : Fin n), a i ≤ finMax a
  | _ + 1, a, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_max_left _ _
    · exact (le_finMax (fun i => a i.succ) j).trans (le_max_right _ _)

theorem sq_finMax_le : ∀ {n : ℕ} (a : Fin n → ℝ), (∀ i, 0 ≤ a i) → finMax a ^ 2 ≤ ∑ i, a i ^ 2
  | 0, _, _ => by simp [finMax]
  | _ + 1, a, h => by
    rw [Fin.sum_univ_succ]
    have ih := sq_finMax_le (fun i => a i.succ) fun i => h i.succ
    have h0 := h 0
    have hm := finMax_nonneg fun i => a i.succ
    show max (a 0) (finMax fun i => a i.succ) ^ 2 ≤ _
    rcases le_total (a 0) (finMax fun i => a i.succ) with hle | hle
    · rw [max_eq_right hle]; nlinarith [sq_nonneg (a 0)]
    · rw [max_eq_left hle]; nlinarith [sq_nonneg (finMax fun i => a i.succ)]

/-- **(SR5)**: `|max_j a_j - max_j b_j|² ≤ Σ_j |a_j - b_j|²`. -/
theorem sq_finMax_sub_le : ∀ {n : ℕ} (a b : Fin n → ℝ),
    (finMax a - finMax b) ^ 2 ≤ ∑ i, (a i - b i) ^ 2
  | 0, _, _ => by simp [finMax]
  | _ + 1, a, b => by
    rw [Fin.sum_univ_succ]
    have ih := sq_finMax_sub_le (fun i => a i.succ) (fun i => b i.succ)
    show (max (a 0) (finMax fun i => a i.succ) - max (b 0) (finMax fun i => b i.succ)) ^ 2 ≤ _
    have h1 := abs_max_sub_max_le_max (a 0) (finMax fun i => a i.succ) (b 0)
      (finMax fun i => b i.succ)
    have h2 : (max (a 0) (finMax fun i => a i.succ) - max (b 0) (finMax fun i => b i.succ)) ^ 2 ≤
        (max |a 0 - b 0| |finMax (fun i => a i.succ) - finMax fun i => b i.succ|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    rcases le_total |a 0 - b 0| |finMax (fun i => a i.succ) - finMax fun i => b i.succ|
      with hle | hle
    · rw [max_eq_right hle, sq_abs]; nlinarith [sq_nonneg (a 0 - b 0)]
    · rw [max_eq_left hle, sq_abs]; nlinarith [sq_nonneg (finMax (fun i => a i.succ) -
        finMax fun i => b i.succ)]

theorem continuous_finMax : ∀ {n : ℕ} {f : Fin n → ℂ → ℝ}, (∀ i, Continuous (f i)) →
    Continuous (fun x => finMax fun i => f i x)
  | 0, _, _ => continuous_const
  | _ + 1, f, h => (h 0).max (continuous_finMax (f := fun i => f i.succ) fun i => h i.succ)

theorem measurable_gagIntegrand' {f : ℂ → ℝ} (hf : Continuous f) (ε : ℝ) :
    Measurable (uncurry fun (x y : ℂ) => ENNReal.ofReal ((f x - f y) ^ 2 * gagKer ε (x - y))) :=
  ENNReal.measurable_ofReal.comp ((((hf.comp continuous_fst).sub (hf.comp continuous_snd)).pow 2
    ).measurable.mul ((measurable_gagKer ε).comp measurable_sub))

/-- `[max_j f_j]²_ε ≤ Σ_j [f_j]²_ε`. -/
theorem gagSq_finMax_le {n : ℕ} {f : Fin n → ℂ → ℝ} (hf : ∀ i, Continuous (f i)) (ε : ℝ) :
    gagSq ε (fun x => finMax fun i => f i x) ≤ ∑ i, gagSq ε (f i) := by
  have hpt : ∀ x y, ENNReal.ofReal (((finMax fun i => f i x) - finMax fun i => f i y) ^ 2 *
      gagKer ε (x - y)) ≤ ∑ i, ENNReal.ofReal ((f i x - f i y) ^ 2 * gagKer ε (x - y)) := by
    intro x y
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (gagKer_nonneg _ _)),
      ← Finset.sum_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (sq_finMax_sub_le _ _)
      (gagKer_nonneg _ _))
  calc gagSq ε (fun x => finMax fun i => f i x)
      ≤ ∫⁻ x, ∫⁻ y, ∑ i, ENNReal.ofReal ((f i x - f i y) ^ 2 * gagKer ε (x - y)) :=
        lintegral_mono fun x => lintegral_mono fun y => hpt x y
    _ = ∑ i, gagSq ε (f i) := by
        have hin : ∀ x, ∫⁻ y, ∑ i, ENNReal.ofReal ((f i x - f i y) ^ 2 * gagKer ε (x - y)) =
            ∑ i, ∫⁻ y, ENNReal.ofReal ((f i x - f i y) ^ 2 * gagKer ε (x - y)) := fun x =>
          lintegral_finsetSum _ fun i _ =>
            (measurable_gagIntegrand' (hf i) ε).comp (measurable_const.prodMk measurable_id)
        simp_rw [hin]
        exact lintegral_finsetSum
          (f := fun i x => ∫⁻ y, ENNReal.ofReal ((f i x - f i y) ^ 2 * gagKer ε (x - y))) _
          fun i _ => (measurable_gagIntegrand' (hf i) ε).lintegral_prod_right'

theorem l2Sq_finMax_le {n : ℕ} {f : Fin n → ℂ → ℝ} (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i x, 0 ≤ f i x) : l2Sq (fun x => finMax fun i => f i x) ≤ ∑ i, l2Sq (f i) := by
  calc l2Sq (fun x => finMax fun i => f i x) ≤ ∫⁻ x, ∑ i, ENNReal.ofReal (f i x ^ 2) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (sq_finMax_le _ fun i => hf0 i x)
    _ = ∑ i, l2Sq (f i) := lintegral_finsetSum _ fun i _ =>
        ENNReal.measurable_ofReal.comp ((hf i).pow 2).measurable

/-! ### The scaled bumps -/

/-- The base bump: `1` on the closed unit disc, supported in the disc of radius `2`. -/
def bump0 : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩

theorem exists_lipschitz_bump0 : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |bump0 x - bump0 y| ≤ L * ‖x - y‖ := by
  have hc : Continuous (fun x => fderiv ℝ (bump0 : ℂ → ℝ) x) :=
    (bump0.contDiff (n := ⊤)).continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (bump0.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hL : LipschitzWith ⟨C, hC0⟩ (bump0 : ℂ → ℝ) :=
    lipschitzWith_of_nnnorm_fderiv_le ((bump0.contDiff (n := ⊤)).differentiable (by simp))
      fun x => hC x
  refine ⟨C, hC0, fun x y => ?_⟩
  have := hL.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm] at this

/-- `bumpAt c r x = bump0 ((x - c)/r)`: `1` on `closedBall c r`, supported in `ball c (2r)`. -/
def bumpAt (c : ℂ) (r : ℝ) (x : ℂ) : ℝ := bump0 (r⁻¹ • (x - c))

theorem bumpAt_nonneg (c : ℂ) (r : ℝ) (x : ℂ) : 0 ≤ bumpAt c r x := bump0.nonneg

theorem bumpAt_le_one (c : ℂ) (r : ℝ) (x : ℂ) : bumpAt c r x ≤ 1 := bump0.le_one

theorem contDiff_bumpAt (c : ℂ) (r : ℝ) : ContDiff ℝ ∞ (bumpAt c r) :=
  bump0.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)

theorem bumpAt_eq_one {c : ℂ} {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ∈ closedBall c r) :
    bumpAt c r x = 1 := by
  refine bump0.one_of_mem_closedBall ?_
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  rw [mem_closedBall, dist_eq_norm] at hx
  show r⁻¹ * ‖x - c‖ ≤ 1
  rw [inv_mul_le_iff₀ hr, mul_one]
  exact hx

theorem bumpAt_eq_zero {c : ℂ} {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ∉ ball c (2 * r)) :
    bumpAt c r x = 0 := by
  refine bump0.zero_of_le_dist ?_
  rw [mem_ball, dist_eq_norm, not_lt] at hx
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  show 2 ≤ r⁻¹ * ‖x - c‖
  rw [le_inv_mul_iff₀ hr]
  linarith

theorem bumpAt_lipschitz {L : ℝ} (hL : ∀ x y, |bump0 x - bump0 y| ≤ L * ‖x - y‖) (c : ℂ) {r : ℝ}
    (hr : 0 < r) (x y : ℂ) : |bumpAt c r x - bumpAt c r y| ≤ L / r * ‖x - y‖ := by
  refine (hL _ _).trans (le_of_eq ?_)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    show x - c - (y - c) = x - y by ring]
  ring

/-- `[bumpAt c r]²_ε ≤ 8π J_ε(L) r^{2-2ε}`. -/
theorem gagSq_bumpAt_le {ε L : ℝ} (hL : ∀ x y, |bump0 x - bump0 y| ≤ L * ‖x - y‖) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    gagSq ε (bumpAt c r) ≤ ENNReal.ofReal (8 * π * r ^ (2 - 2 * ε)) * gagJ ε L := by
  refine (gagSq_le_of_lipschitz (bumpAt_nonneg c r) (bumpAt_le_one c r)
    (bumpAt_lipschitz hL c hr) (fun x hx => bumpAt_eq_zero hr hx)).trans (le_of_eq ?_)
  rw [Complex.volume_ball, gagJ_div L hr, ← mul_assoc]
  congr 1
  rw [ENNReal.coe_nnreal_eq, NNReal.coe_real_pi, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show 2 - 2 * ε = (2 : ℕ) + -(2 * ε) by push_cast; ring, Real.rpow_add hr,
    Real.rpow_natCast]
  ring

/-- `‖bumpAt c r‖²₂ ≤ 4π r²`. -/
theorem l2Sq_bumpAt_le (c : ℂ) {r : ℝ} (hr : 0 < r) :
    l2Sq (bumpAt c r) ≤ ENNReal.ofReal (4 * π * r ^ 2) := by
  calc l2Sq (bumpAt c r) ≤ ∫⁻ x, (ball c (2 * r)).indicator 1 x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ ball c (2 * r)
        · rw [indicator_of_mem hx, Pi.one_apply, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [bumpAt_nonneg c r x, bumpAt_le_one c r x]
        · rw [bumpAt_eq_zero hr hx]; simp
    _ = ENNReal.ofReal (4 * π * r ^ 2) := by
        rw [lintegral_indicator_one measurableSet_ball, Complex.volume_ball,
          ENNReal.coe_nnreal_eq, NNReal.coe_real_pi, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ### Mollification: Jensen's inequality in (SR4) -/

/-- Jensen: `(∫ ρ d)² ≤ ∫ ρ d²` for a probability density `ρ`. -/
theorem ofReal_sq_integral_mul_le {ρ d : ℂ → ℝ} (hρ : Continuous ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hρ1 : ∫⁻ t, ENNReal.ofReal (ρ t) = 1) (hd : Continuous d) :
    ENNReal.ofReal ((∫ t, ρ t * d t) ^ 2) ≤ ∫⁻ t, ENNReal.ofReal (ρ t * d t ^ 2) := by
  set F : ℂ → ℝ≥0∞ := fun t => ENNReal.ofReal (√(ρ t))
  set G : ℂ → ℝ≥0∞ := fun t => ENNReal.ofReal (√(ρ t) * |d t|)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp hρ.sqrt.measurable
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (hρ.sqrt.mul hd.abs).measurable
  have hFG : ∀ t, ‖ρ t * d t‖ₑ = F t * G t := fun t => by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← mul_assoc,
      Real.mul_self_sqrt (hρ0 t), abs_mul, abs_of_nonneg (hρ0 t)]
  have hF2 : ∀ t, F t ^ 2 = ENNReal.ofReal (ρ t) := fun t => by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hρ0 t)]
  have hG2 : ∀ t, G t ^ 2 = ENNReal.ofReal (ρ t * d t ^ 2) := fun t => by
    rw [← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt (hρ0 t), sq_abs]
  have h1 : ENNReal.ofReal ((∫ t, ρ t * d t) ^ 2) = ‖∫ t, ρ t * d t‖ₑ ^ 2 := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [h1]
  calc ‖∫ t, ρ t * d t‖ₑ ^ 2 ≤ (∫⁻ t, ‖ρ t * d t‖ₑ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (enorm_integral_le_lintegral_enorm _) 2
    _ = (∫⁻ t, F t * G t) ^ 2 := by simp_rw [hFG]
    _ ≤ (∫⁻ t, F t ^ 2) * ∫⁻ t, G t ^ 2 := sq_lintegral_mul_le hF.aemeasurable hG.aemeasurable
    _ = ∫⁻ t, ENNReal.ofReal (ρ t * d t ^ 2) := by simp_rw [hF2, hG2]; rw [hρ1, one_mul]

/-- The mollifier bump of radius `η`. -/
def mollBump {η : ℝ} (hη : 0 < η) : ContDiffBump (0 : ℂ) := ⟨η / 2, η, by positivity, by linarith⟩

/-- The mollifier `ρ_η`. -/
def mollKer {η : ℝ} (hη : 0 < η) : ℂ → ℝ := (mollBump hη).normed volume

theorem mollKer_nonneg {η : ℝ} (hη : 0 < η) (t : ℂ) : 0 ≤ mollKer hη t :=
  (mollBump hη).nonneg_normed t

theorem continuous_mollKer {η : ℝ} (hη : 0 < η) : Continuous (mollKer hη) :=
  (mollBump hη).continuous_normed

theorem lintegral_mollKer {η : ℝ} (hη : 0 < η) : ∫⁻ t, ENNReal.ofReal (mollKer hη t) = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal (mollBump hη).integrable_normed
    (Eventually.of_forall (mollKer_nonneg hη))
  rw [(mollBump hη).integral_normed, ENNReal.ofReal_one] at h
  exact h.symm

/-- `v_η = ρ_η ⋆ v`. -/
def mollify {η : ℝ} (hη : 0 < η) (v : ℂ → ℝ) : ℂ → ℝ :=
  convolution (mollKer hη) v (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem mollify_apply {η : ℝ} (hη : 0 < η) (v : ℂ → ℝ) (x : ℂ) :
    mollify hη v x = ∫ t, mollKer hη t * v (x - t) := by
  simp [mollify, convolution_def]

theorem contDiff_mollify {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ} (hv : Continuous v) :
    ContDiff ℝ ∞ (mollify hη v) :=
  HasCompactSupport.contDiff_convolution_left (n := ⊤) _ (mollBump hη).hasCompactSupport_normed
    (mollBump hη).contDiff_normed hv.locallyIntegrable

theorem mollify_eq_of_const {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ} {x : ℂ}
    (h : ∀ y ∈ ball x η, v y = v x) : mollify hη v x = v x :=
  (mollBump hη).normed_convolution_eq_right h

theorem integrable_mollKer_mul {η : ℝ} (hη : 0 < η) {d : ℂ → ℝ} (hd : Continuous d) :
    Integrable (fun t => mollKer hη t * d t) :=
  ((continuous_mollKer hη).mul hd).integrable_of_hasCompactSupport
    (mollBump hη).hasCompactSupport_normed.mul_right

theorem mollify_nonneg {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ} (hv0 : ∀ x, 0 ≤ v x) (x : ℂ) :
    0 ≤ mollify hη v x := by
  rw [mollify_apply]
  exact integral_nonneg fun t => mul_nonneg (mollKer_nonneg hη t) (hv0 _)

theorem mollify_le_one {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ} (hv : Continuous v)
    (hv1 : ∀ x, v x ≤ 1) (x : ℂ) : mollify hη v x ≤ 1 := by
  rw [mollify_apply]
  calc ∫ t, mollKer hη t * v (x - t) ≤ ∫ t, mollKer hη t * 1 :=
        integral_mono (integrable_mollKer_mul hη (hv.comp (continuous_const.sub continuous_id)))
          (integrable_mollKer_mul hη continuous_const)
          fun t => mul_le_mul_of_nonneg_left (hv1 _) (mollKer_nonneg hη t)
    _ = 1 := by simp only [mul_one]; exact (mollBump hη).integral_normed

theorem mollify_sub {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ} (hv : Continuous v) (x y : ℂ) :
    mollify hη v x - mollify hη v y = ∫ t, mollKer hη t * (v (x - t) - v (y - t)) := by
  have h1 : Integrable (fun t => mollKer hη t * v (x - t)) :=
    integrable_mollKer_mul hη (hv.comp (continuous_const.sub continuous_id))
  have h2 : Integrable (fun t => mollKer hη t * v (y - t)) :=
    integrable_mollKer_mul hη (hv.comp (continuous_const.sub continuous_id))
  rw [mollify_apply, mollify_apply, ← integral_sub h1 h2]
  congr 1; funext t; ring

/-- Jensen in (SR4): `[ρ_η ⋆ v]²_ε ≤ [v]²_ε`. -/
theorem gagSq_mollify_le {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ} (hv : Continuous v) (ε : ℝ) :
    gagSq ε (mollify hη v) ≤ gagSq ε v := by
  set ρ := mollKer hη
  set H : ℂ → ℂ → ℂ → ℝ≥0∞ := fun x y t =>
    ENNReal.ofReal (ρ t * ((v (x - t) - v (y - t)) ^ 2 * gagKer ε (x - y)))
  have hH : Measurable (fun p : (ℂ × ℂ) × ℂ => H p.1.1 p.1.2 p.2) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ((continuous_mollKer hη).measurable.comp
      measurable_snd) (Measurable.mul ?_ ((measurable_gagKer ε).comp
        (measurable_fst.fst.sub measurable_fst.snd))))
    exact (((hv.comp (continuous_fst.fst.sub continuous_snd)).sub
      (hv.comp (continuous_fst.snd.sub continuous_snd))).pow 2).measurable
  have hpt : ∀ x y, ENNReal.ofReal ((mollify hη v x - mollify hη v y) ^ 2 * gagKer ε (x - y)) ≤
      ∫⁻ t, H x y t := by
    intro x y
    rw [ENNReal.ofReal_mul (sq_nonneg _), mollify_sub hη hv]
    calc ENNReal.ofReal ((∫ t, ρ t * (v (x - t) - v (y - t))) ^ 2) *
          ENNReal.ofReal (gagKer ε (x - y))
        ≤ (∫⁻ t, ENNReal.ofReal (ρ t * (v (x - t) - v (y - t)) ^ 2)) *
            ENNReal.ofReal (gagKer ε (x - y)) := by
          gcongr
          exact ofReal_sq_integral_mul_le (continuous_mollKer hη) (mollKer_nonneg hη)
            (lintegral_mollKer hη) ((hv.comp (continuous_const.sub continuous_id)).sub
              (hv.comp (continuous_const.sub continuous_id)))
      _ = ∫⁻ t, H x y t := by
          have hm : Measurable (fun t => ENNReal.ofReal (ρ t * (v (x - t) - v (y - t)) ^ 2)) :=
            ENNReal.measurable_ofReal.comp (((continuous_mollKer hη).mul
              (((hv.comp (continuous_const.sub continuous_id)).sub
                (hv.comp (continuous_const.sub continuous_id))).pow 2)).measurable)
          rw [← lintegral_mul_const _ hm]
          congr 1; funext t
          rw [← ENNReal.ofReal_mul (mul_nonneg (mollKer_nonneg hη t) (sq_nonneg _))]
          congr 1; ring
  have hC : ∀ t, ∫⁻ x, ∫⁻ y, H x y t = ENNReal.ofReal (ρ t) * gagSq ε v := by
    intro t
    have h1 : ∀ x, ∫⁻ y, H x y t = ENNReal.ofReal (ρ t) *
        ∫⁻ y, ENNReal.ofReal ((v (x - t) - v y) ^ 2 * gagKer ε (x - t - y)) := by
      intro x
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (ρ t) *
          ENNReal.ofReal ((v (x - t) - v y) ^ 2 * gagKer ε (x - t - y))) t]
      congr 1; funext y
      rw [← ENNReal.ofReal_mul (mollKer_nonneg hη t)]
      rw [show x - t - (y - t) = x - y by ring]
    calc ∫⁻ x, ∫⁻ y, H x y t
        = ∫⁻ x, ENNReal.ofReal (ρ t) *
            ∫⁻ y, ENNReal.ofReal ((v (x - t) - v y) ^ 2 * gagKer ε (x - t - y)) := by
          simp_rw [h1]
      _ = ∫⁻ x, ENNReal.ofReal (ρ t) *
            ∫⁻ y, ENNReal.ofReal ((v x - v y) ^ 2 * gagKer ε (x - y)) :=
          lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (ρ t) *
            ∫⁻ y, ENNReal.ofReal ((v x - v y) ^ 2 * gagKer ε (x - y))) t
      _ = ENNReal.ofReal (ρ t) * gagSq ε v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc gagSq ε (mollify hη v) ≤ ∫⁻ x, ∫⁻ y, ∫⁻ t, H x y t :=
        lintegral_mono fun x => lintegral_mono fun y => hpt x y
    _ = ∫⁻ x, ∫⁻ t, ∫⁻ y, H x y t := by
        congr 1; funext x
        exact lintegral_lintegral_swap
          ((hH.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).aemeasurable)
    _ = ∫⁻ t, ∫⁻ x, ∫⁻ y, H x y t := lintegral_lintegral_swap
        ((hH.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
          ).lintegral_prod_right'.aemeasurable)
    _ = ∫⁻ t, ENNReal.ofReal (ρ t) * gagSq ε v := by simp_rw [hC]
    _ = gagSq ε v := by
        have hm : Measurable (fun t => ENNReal.ofReal (ρ t)) :=
          ENNReal.measurable_ofReal.comp (continuous_mollKer hη).measurable
        rw [lintegral_mul_const _ hm, lintegral_mollKer hη, one_mul]

/-- `‖ρ_η ⋆ v‖²₂ ≤ ‖v‖²₂`. -/
theorem l2Sq_mollify_le {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ} (hv : Continuous v) :
    l2Sq (mollify hη v) ≤ l2Sq v := by
  set ρ := mollKer hη
  have hmeas : Measurable (uncurry fun (x t : ℂ) => ENNReal.ofReal (ρ t * v (x - t) ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((continuous_mollKer hη).comp continuous_snd).mul
      ((hv.comp (continuous_fst.sub continuous_snd)).pow 2)).measurable
  calc l2Sq (mollify hη v) ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ t * v (x - t) ^ 2) := by
        refine lintegral_mono fun x => ?_
        rw [mollify_apply]
        exact ofReal_sq_integral_mul_le (continuous_mollKer hη) (mollKer_nonneg hη)
          (lintegral_mollKer hη) (hv.comp (continuous_const.sub continuous_id))
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ t * v (x - t) ^ 2) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ t, ENNReal.ofReal (ρ t) * l2Sq v := by
        congr 1; funext t
        rw [l2Sq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (ρ t) * ENNReal.ofReal (v x ^ 2)) t]
        congr 1; funext x
        rw [ENNReal.ofReal_mul (mollKer_nonneg hη t)]
    _ = l2Sq v := by
        have hm : Measurable (fun t => ENNReal.ofReal (ρ t)) :=
          ENNReal.measurable_ofReal.comp (continuous_mollKer hη).measurable
        rw [lintegral_mul_const _ hm, lintegral_mollKer hη, one_mul]

/-! ### Multiplication by a fixed test function is bounded on `H^ε` -/

theorem sq_sub_le_mul_min {φ : ℂ → ℝ} {M L : ℝ} (hM : ∀ x, |φ x| ≤ M)
    (hL : ∀ x y, |φ x - φ y| ≤ L * ‖x - y‖) (x y : ℂ) :
    (φ x - φ y) ^ 2 ≤ max 1 (4 * M ^ 2) * min 1 (L ^ 2 * ‖x - y‖ ^ 2) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have h1 : (φ x - φ y) ^ 2 ≤ 4 * M ^ 2 := by
    have : |φ x - φ y| ≤ 2 * M := (abs_sub _ _).trans (by linarith [hM x, hM y])
    nlinarith [abs_nonneg (φ x - φ y), sq_abs (φ x - φ y)]
  have h2 : (φ x - φ y) ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) (hL x y) 2
    rwa [sq_abs, mul_pow] at this
  rcases le_total 1 (L ^ 2 * ‖x - y‖ ^ 2) with h | h
  · rw [min_eq_left h, mul_one]; exact h1.trans (le_max_right _ _)
  · rw [min_eq_right h]
    calc (φ x - φ y) ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := h2
      _ ≤ max 1 (4 * M ^ 2) * (L ^ 2 * ‖x - y‖ ^ 2) :=
        le_mul_of_one_le_left (by positivity) (le_max_left _ _)

/-- `[φv]²_ε ≤ 2M² [v]²_ε + 2 max(1, 4M²) J_ε(L) ‖v‖²₂` for `|φ| ≤ M`, `φ` `L`-Lipschitz. -/
theorem gagSq_mul_le {φ v : ℂ → ℝ} (hv : Continuous v) {M L : ℝ}
    (hM : ∀ x, |φ x| ≤ M) (hL : ∀ x y, |φ x - φ y| ≤ L * ‖x - y‖) (ε : ℝ) :
    gagSq ε (fun x => φ x * v x) ≤ ENNReal.ofReal (2 * M ^ 2) * gagSq ε v +
      ENNReal.ofReal (2 * max 1 (4 * M ^ 2)) * gagJ ε L * l2Sq v := by
  set A := max 1 (4 * M ^ 2)
  have hA : 0 ≤ A := le_max_of_le_left zero_le_one
  have hpt : ∀ x y, ENNReal.ofReal ((φ x * v x - φ y * v y) ^ 2 * gagKer ε (x - y)) ≤
      ENNReal.ofReal (2 * M ^ 2) * ENNReal.ofReal ((v x - v y) ^ 2 * gagKer ε (x - y)) +
        ENNReal.ofReal (2 * A) * (ENNReal.ofReal (v y ^ 2) * ENNReal.ofReal (gagG ε L (x - y))) := by
    intro x y
    have hK := gagKer_nonneg ε (x - y)
    have e1 : φ x * v x - φ y * v y = φ x * (v x - v y) + v y * (φ x - φ y) := by ring
    have h1 : (φ x * v x - φ y * v y) ^ 2 ≤
        2 * M ^ 2 * (v x - v y) ^ 2 + 2 * A * (v y ^ 2 * min 1 (L ^ 2 * ‖x - y‖ ^ 2)) := by
      rw [e1]
      have hφx : φ x ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
      have hs := sq_sub_le_mul_min hM hL x y
      nlinarith [sq_nonneg (φ x * (v x - v y) - v y * (φ x - φ y)), sq_nonneg (v x - v y),
        sq_nonneg (v y), mul_le_mul_of_nonneg_left hs (sq_nonneg (v y)),
        mul_le_mul_of_nonneg_right hφx (sq_nonneg (v x - v y))]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (gagG_nonneg _ _ _)))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right h1 hK
    simp only [gagG] at this ⊢
    nlinarith [this]
  have hm1 : Measurable (uncurry fun (x y : ℂ) =>
      ENNReal.ofReal (2 * M ^ 2) * ENNReal.ofReal ((v x - v y) ^ 2 * gagKer ε (x - y))) :=
    measurable_const.mul (measurable_gagIntegrand' hv ε)
  have hm2 : Measurable (uncurry fun (x y : ℂ) => ENNReal.ofReal (2 * A) *
      (ENNReal.ofReal (v y ^ 2) * ENNReal.ofReal (gagG ε L (x - y)))) :=
    measurable_const.mul ((ENNReal.measurable_ofReal.comp ((hv.pow 2).measurable.comp
      measurable_snd)).mul (ENNReal.measurable_ofReal.comp ((measurable_gagG ε L).comp
        measurable_sub)))
  calc gagSq ε (fun x => φ x * v x)
      ≤ ∫⁻ x, ∫⁻ y, (ENNReal.ofReal (2 * M ^ 2) * ENNReal.ofReal ((v x - v y) ^ 2 * gagKer ε (x - y)) +
          ENNReal.ofReal (2 * A) * (ENNReal.ofReal (v y ^ 2) * ENNReal.ofReal (gagG ε L (x - y)))) :=
        lintegral_mono fun x => lintegral_mono fun y => hpt x y
    _ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (2 * M ^ 2) * ENNReal.ofReal ((v x - v y) ^ 2 * gagKer ε (x - y))) +
          ∫⁻ x, ∫⁻ y, ENNReal.ofReal (2 * A) *
            (ENNReal.ofReal (v y ^ 2) * ENNReal.ofReal (gagG ε L (x - y))) := by
        rw [← lintegral_add_left (f := fun x => ∫⁻ y, ENNReal.ofReal (2 * M ^ 2) *
          ENNReal.ofReal ((v x - v y) ^ 2 * gagKer ε (x - y))) hm1.lintegral_prod_right']
        congr 1; funext x
        exact lintegral_add_left (hm1.comp (measurable_const.prodMk measurable_id)) _
    _ = ENNReal.ofReal (2 * M ^ 2) * gagSq ε v + ENNReal.ofReal (2 * A) * gagJ ε L * l2Sq v := by
        congr 1
        · rw [gagSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1; funext x
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        · rw [lintegral_lintegral_swap hm2.aemeasurable]
          have hin : ∀ y, ∫⁻ x, ENNReal.ofReal (2 * A) *
              (ENNReal.ofReal (v y ^ 2) * ENNReal.ofReal (gagG ε L (x - y))) =
              ENNReal.ofReal (2 * A) * gagJ ε L * ENNReal.ofReal (v y ^ 2) := by
            intro y
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _
              ENNReal.ofReal_ne_top, lintegral_sub_right_eq_self
                (fun z => ENNReal.ofReal (gagG ε L z)) y, gagJ]
            ring
          simp_rw [hin]
          have hm : Measurable (fun y => ENNReal.ofReal (v y ^ 2)) :=
            ENNReal.measurable_ofReal.comp (hv.pow 2).measurable
          rw [l2Sq, lintegral_const_mul _ hm]

theorem l2Sq_mul_le {φ v : ℂ → ℝ} {M : ℝ} (hM : ∀ x, |φ x| ≤ M) :
    l2Sq (fun x => φ x * v x) ≤ ENNReal.ofReal (M ^ 2) * l2Sq v := by
  rw [l2Sq, l2Sq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_pow]
  have : φ x ^ 2 ≤ M ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-! ### Finite ball covers of a compact set of zero Hausdorff measure -/

theorem max_rpow_le_add {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ^ d ≤ a ^ d + b ^ d := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; linarith [Real.rpow_nonneg ha d]
  · rw [max_eq_left h]; linarith [Real.rpow_nonneg hb d]

/-- "The existence of a countable such cover is the definition of zero `(2 - 2ε)`-dimensional
Hausdorff measure; compactness permits a finite subcover": a compact `E₀` with `μH[d] E₀ = 0`
is covered by finitely many balls `B(c_i, r_i)`, `0 < r_i ≤ 1`, with `Σ r_i^d ≤ δ`. -/
theorem exists_finite_ball_cover {d : ℝ} (hd : 0 < d) {E₀ : Set ℂ} (hE₀ : IsCompact E₀)
    (hH : μH[d] E₀ = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ), (∀ i, 0 < r i ∧ r i ≤ 1) ∧
      E₀ ⊆ ⋃ i, ball (c i) (r i) ∧ ∑ i, r i ^ d ≤ δ := by
  set δ' : ℝ := min 1 (δ / (2 ^ d + 2)) with hδ'
  have hδ'0 : 0 < δ' := lt_min one_pos (by positivity)
  have hδ'1 : δ' ≤ 1 := min_le_left _ _
  have hδ'2 : (2 ^ d + 2) * δ' ≤ δ := by
    have := min_le_right 1 (δ / (2 ^ d + 2))
    rw [← hδ'] at this
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  -- a countable cover by sets of diameter `≤ 1/2` with `Σ diam^d < δ'`
  have h1 := le_iSup₂ (f := fun (R : ℝ≥0∞) (_ : 0 < R) => ⨅ (t : ℕ → Set ℂ),
    ⨅ (_ : E₀ ⊆ ⋃ n, t n), ⨅ (_ : ∀ n, Metric.ediam (t n) ≤ R),
      ∑' n, ⨆ (_ : (t n).Nonempty), Metric.ediam (t n) ^ d) (1 / 2 : ℝ≥0∞) (by norm_num)
  rw [← Measure.hausdorffMeasure_apply, hH] at h1
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 (lt_of_le_of_lt h1 (ENNReal.ofReal_pos.2 hδ'0))
  obtain ⟨hcov, ht⟩ := iInf_lt_iff.1 ht
  obtain ⟨hdiam, hsum⟩ := iInf_lt_iff.1 ht
  -- centres and radii
  classical
  set c : ℕ → ℂ := fun n => if h : (t n).Nonempty then h.some else 0
  set D : ℕ → ℝ := fun n => (Metric.ediam (t n)).toReal
  set θ : ℕ → ℝ := fun n => (δ' * (1 / 2) ^ (n + 1)) ^ (1 / d)
  set r : ℕ → ℝ := fun n => max (2 * D n) (θ n)
  have hdiam' : ∀ n, Metric.ediam (t n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top (by norm_num) (hdiam n)
  have hD0 : ∀ n, 0 ≤ D n := fun n => ENNReal.toReal_nonneg
  have hD1 : ∀ n, 2 * D n ≤ 1 := fun n => by
    have : D n ≤ 1 / 2 := by
      have := ENNReal.toReal_mono (by norm_num) (hdiam n)
      simpa [D] using this
    linarith
  have hθ0 : ∀ n, 0 < θ n := fun n => Real.rpow_pos_of_pos (by positivity) _
  have hθd : ∀ n, θ n ^ d = δ' * (1 / 2) ^ (n + 1) := fun n => by
    simp only [θ]
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hd.ne', Real.rpow_one]
  have hθ1 : ∀ n, θ n ≤ 1 := fun n => by
    have h : θ n ^ d ≤ 1 := by
      rw [hθd]
      calc δ' * (1 / 2) ^ (n + 1) ≤ 1 * 1 :=
            mul_le_mul hδ'1 (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity) zero_le_one
        _ = 1 := one_mul 1
    by_contra hθ
    push Not at hθ
    have := Real.one_lt_rpow hθ hd
    linarith
  have hr0 : ∀ n, 0 < r n := fun n => lt_max_of_lt_right (hθ0 n)
  have hr1 : ∀ n, r n ≤ 1 := fun n => max_le (hD1 n) (hθ1 n)
  have hsub : ∀ n, t n ⊆ ball (c n) (r n) := by
    intro n x hx
    have hne : (t n).Nonempty := ⟨x, hx⟩
    have hc : c n = hne.some := by simp [c, hne]
    rw [mem_ball, hc]
    have h1 : edist x hne.some ≤ Metric.ediam (t n) :=
      Metric.edist_le_ediam_of_mem hx hne.some_mem
    have h2 : dist x hne.some ≤ D n := by
      rw [dist_edist]; exact ENNReal.toReal_mono (hdiam' n) h1
    rcases (hD0 n).lt_or_eq with hpos | hzero
    · exact lt_of_le_of_lt h2 (lt_max_of_lt_left (by linarith))
    · rw [← hzero] at h2; exact lt_of_le_of_lt h2 (hr0 n)
  -- the sum bound
  have hrd : ∀ n, ENNReal.ofReal (r n ^ d) ≤ ENNReal.ofReal (2 ^ d) * (⨆ (_ : (t n).Nonempty),
      Metric.ediam (t n) ^ d) + ENNReal.ofReal δ' * (1 / 2) ^ (n + 1) := by
    intro n
    have hDd : ENNReal.ofReal (D n ^ d) ≤ ⨆ (_ : (t n).Nonempty), Metric.ediam (t n) ^ d := by
      by_cases hne : (t n).Nonempty
      · rw [iSup_pos hne, ← ENNReal.ofReal_rpow_of_nonneg (hD0 n) hd.le, ENNReal.ofReal_toReal
          (hdiam' n)]
      · rw [not_nonempty_iff_eq_empty] at hne
        have : D n = 0 := by simp [D, hne, Metric.ediam_empty]
        rw [this, Real.zero_rpow hd.ne', ENNReal.ofReal_zero]
        exact bot_le
    calc ENNReal.ofReal (r n ^ d) ≤ ENNReal.ofReal ((2 * D n) ^ d + θ n ^ d) :=
          ENNReal.ofReal_le_ofReal (max_rpow_le_add (by linarith [hD0 n]) (hθ0 n).le)
      _ = ENNReal.ofReal (2 ^ d) * ENNReal.ofReal (D n ^ d) +
            ENNReal.ofReal δ' * (1 / 2) ^ (n + 1) := by
          rw [ENNReal.ofReal_add (by positivity) (Real.rpow_nonneg (hθ0 n).le _),
            Real.mul_rpow (by norm_num) (hD0 n), ENNReal.ofReal_mul (by positivity), hθd,
            ENNReal.ofReal_mul hδ'0.le, ENNReal.ofReal_pow (by norm_num),
            show ENNReal.ofReal (1 / 2) = 1 / 2 by
              rw [one_div, one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]]
      _ ≤ _ := by gcongr
  have htsum : ∑' n, ENNReal.ofReal (r n ^ d) ≤ ENNReal.ofReal δ := by
    calc ∑' n, ENNReal.ofReal (r n ^ d)
        ≤ ∑' n, (ENNReal.ofReal (2 ^ d) * (⨆ (_ : (t n).Nonempty), Metric.ediam (t n) ^ d) +
            ENNReal.ofReal δ' * (1 / 2) ^ (n + 1)) := ENNReal.tsum_le_tsum hrd
      _ = ENNReal.ofReal (2 ^ d) * (∑' n, ⨆ (_ : (t n).Nonempty), Metric.ediam (t n) ^ d) +
            ENNReal.ofReal δ' * ∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ (n + 1) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal (2 ^ d) * ENNReal.ofReal δ' + ENNReal.ofReal δ' * 1 := by
          gcongr
          all_goals first
            | exact hsum.le
            | (rw [ENNReal.tsum_geometric_add_one]; norm_num)
      _ = ENNReal.ofReal ((2 ^ d + 1) * δ') := by
          rw [mul_one, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            hδ'0.le]
          ring_nf
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by nlinarith)
  -- a finite subcover
  have hcover : E₀ ⊆ ⋃ n, ball (c n) (r n) :=
    hcov.trans (iUnion_mono fun n => hsub n)
  obtain ⟨S, hS⟩ := hE₀.elim_finite_subcover (fun n => ball (c n) (r n)) (fun n => isOpen_ball)
    hcover
  set e := S.equivFin
  refine ⟨S.card, fun i => c (e.symm i), fun i => r (e.symm i), fun i => ⟨hr0 _, hr1 _⟩,
    fun x hx => ?_, ?_⟩
  · obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.1 (hS hx)
    exact mem_iUnion.2 ⟨e ⟨m, hm⟩, by simpa using hxm⟩
  · have hsumS : ∑ i, r (e.symm i) ^ d = ∑ m ∈ S, r m ^ d := by
      rw [e.symm.sum_comp (fun m : S => r m ^ d), Finset.sum_coe_sort S (fun m => r m ^ d)]
    rw [hsumS]
    have h2 : ENNReal.ofReal (∑ m ∈ S, r m ^ d) ≤ ENNReal.ofReal δ := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => Real.rpow_nonneg (hr0 m).le _)]
      exact (ENNReal.sum_le_tsum S).trans htsum
    exact (ENNReal.ofReal_le_ofReal_iff hδ.le).1 h2

/-! ### The cutoff -/

/-- **Small-norm cutoffs** (proof of Aux. lemma 12): if `E₀` is compact with
`μH[2-2ε](E₀) = 0`, there is a constant `C < ∞` such that for every `δ > 0` some smooth
`v : ℂ → [0, 1]` equals `1` on an open neighbourhood of `E₀` and `‖v‖²₂ + [v]²_ε ≤ C δ`. -/
theorem exists_small_cutoff {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {E₀ : Set ℂ} (hE₀ : IsCompact E₀)
    (hH : μH[2 - 2 * ε] E₀ = 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∃ v : ℂ → ℝ, ContDiff ℝ ∞ v ∧
      (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧ (∃ O, IsOpen O ∧ E₀ ⊆ O ∧ EqOn v 1 O) ∧
      l2Sq v + gagSq ε v ≤ C * ENNReal.ofReal δ := by
  obtain ⟨L, -, hL⟩ := exists_lipschitz_bump0
  set C : ℝ≥0∞ := ENNReal.ofReal (4 * π) + ENNReal.ofReal (8 * π) * gagJ ε L
  refine ⟨C, ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (gagJ_lt_top hε0 hε1 L).ne⟩, fun δ hδ => ?_⟩
  obtain ⟨n, c, r, hr, hcov, hsum⟩ :=
    exists_finite_ball_cover (d := 2 - 2 * ε) (by linarith) hE₀ hH hδ
  set w : ℂ → ℝ := fun x => finMax fun i => bumpAt (c i) (r i) x
  have hbc : ∀ i, Continuous (bumpAt (c i) (r i)) := fun i => (contDiff_bumpAt _ _).continuous
  have hwc : Continuous w := continuous_finMax hbc
  have hw0 : ∀ x, 0 ≤ w x := fun x => finMax_nonneg _
  have hw1 : ∀ x, w x ≤ 1 := fun x => finMax_le _ zero_le_one fun i => bumpAt_le_one _ _ _
  set O' := ⋃ i, ball (c i) (r i)
  have hwO : ∀ y ∈ O', w y = 1 := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    refine le_antisymm (hw1 y) ?_
    calc (1 : ℝ) = bumpAt (c i) (r i) y := (bumpAt_eq_one (hr i).1 (ball_subset_closedBall hi)).symm
      _ ≤ w y := le_finMax (fun i => bumpAt (c i) (r i) y) i
  obtain ⟨δ₁, hδ₁, hthick⟩ :=
    hE₀.exists_thickening_subset_open (isOpen_iUnion fun i => isOpen_ball) hcov
  have hη : 0 < δ₁ / 2 := half_pos hδ₁
  refine ⟨mollify hη w, contDiff_mollify hη hwc,
    fun x => ⟨mollify_nonneg hη hw0 x, mollify_le_one hη hwc hw1 x⟩,
    ⟨thickening (δ₁ / 2) E₀, isOpen_thickening, self_subset_thickening hη E₀, fun x hx => ?_⟩, ?_⟩
  · have hxO : x ∈ O' := hthick (thickening_mono (by linarith) E₀ hx)
    have hconst : ∀ y ∈ ball x (δ₁ / 2), w y = w x := by
      intro y hy
      have hy' : y ∈ thickening δ₁ E₀ := by
        have := thickening_thickening_subset (δ₁ / 2) (δ₁ / 2) E₀
          (mem_thickening_iff.2 ⟨x, hx, hy⟩)
        rwa [add_halves] at this
      rw [hwO y (hthick hy'), hwO x hxO]
    rw [mollify_eq_of_const hη hconst, hwO x hxO]
    rfl
  · have hbump : ∀ i, l2Sq (bumpAt (c i) (r i)) + gagSq ε (bumpAt (c i) (r i)) ≤
        C * ENNReal.ofReal (r i ^ (2 - 2 * ε)) := by
      intro i
      have hr2 : r i ^ 2 ≤ r i ^ (2 - 2 * ε) := by
        rw [← Real.rpow_two]
        exact Real.rpow_le_rpow_of_exponent_ge (hr i).1 (hr i).2 (by linarith)
      calc l2Sq (bumpAt (c i) (r i)) + gagSq ε (bumpAt (c i) (r i))
          ≤ ENNReal.ofReal (4 * π * r i ^ 2) +
              ENNReal.ofReal (8 * π * r i ^ (2 - 2 * ε)) * gagJ ε L :=
            add_le_add (l2Sq_bumpAt_le _ (hr i).1) (gagSq_bumpAt_le hL _ (hr i).1)
        _ ≤ ENNReal.ofReal (4 * π) * ENNReal.ofReal (r i ^ (2 - 2 * ε)) +
              ENNReal.ofReal (8 * π) * ENNReal.ofReal (r i ^ (2 - 2 * ε)) * gagJ ε L := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            gcongr
        _ = C * ENNReal.ofReal (r i ^ (2 - 2 * ε)) := by ring
    calc l2Sq (mollify hη w) + gagSq ε (mollify hη w) ≤ l2Sq w + gagSq ε w :=
          add_le_add (l2Sq_mollify_le hη hwc) (gagSq_mollify_le hη hwc ε)
      _ ≤ (∑ i, l2Sq (bumpAt (c i) (r i))) + ∑ i, gagSq ε (bumpAt (c i) (r i)) :=
          add_le_add (l2Sq_finMax_le hbc fun i x => bumpAt_nonneg _ _ _) (gagSq_finMax_le hbc ε)
      _ = ∑ i, (l2Sq (bumpAt (c i) (r i)) + gagSq ε (bumpAt (c i) (r i))) :=
          Finset.sum_add_distrib.symm
      _ ≤ ∑ i, C * ENNReal.ofReal (r i ^ (2 - 2 * ε)) := Finset.sum_le_sum fun i _ => hbump i
      _ = C * ENNReal.ofReal (∑ i, r i ^ (2 - 2 * ε)) := by
          rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
            (fun i _ => Real.rpow_nonneg (hr i).1.le _)]
      _ ≤ C * ENNReal.ofReal δ := by gcongr

end InteractingSLE.Sobolev
