import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarPsiFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR-PSI, part 2: `fmPsi` on the unit circle, and the node `FMPsiStmt`

On `‖y‖ = 1` we get `fmPsi y = π Re y` as the limit of `fmPsi (r y) = π r Re y` for `r ↑ 1`
(dominated convergence; the logarithmic singularity is integrable by mathlib's
`circleIntegrable_log_norm_sub_const`, and `‖r y - e‖² = (1 - r)² + r ‖y - e‖²` gives the
domination). Hence `fmPsi y = π Re (G y)` with `G y = y` on the closed disc and
`G y = y / ‖y‖²` outside; `G` maps into the closed unit disc and is `1`-Lipschitz, which gives
`FMPsiStmt`. Own elementary proof.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real RealInnerProductSpace

namespace QuantumZipper
namespace D3Plus

lemma fmPsi_sq_identity (y e : ℂ) (hy : ‖y‖ = 1) (he : ‖e‖ = 1) (r : ℝ) :
    ‖(r : ℂ) * y - e‖ ^ 2 = (1 - r) ^ 2 + r * ‖y - e‖ ^ 2 := by
  rw [show (r : ℂ) * y = r • y from (Complex.real_smul).symm, norm_sub_sq_real, norm_sub_sq_real,
    real_inner_smul_left, norm_smul, hy, he, Real.norm_eq_abs, mul_one, sq_abs]
  ring

lemma fmPsi_log_bound (y e : ℂ) (hy : ‖y‖ = 1) (he : ‖e‖ = 1) (hne : e ≠ y) (r : ℝ)
    (hr : 1 / 2 < r) (hr1 : r < 1) :
    |Real.log ‖(r : ℂ) * y - e‖| ≤ |Real.log ‖y - e‖| + 2 := by
  have hid := fmPsi_sq_identity y e hy he r
  have hs0 : 0 < ‖y - e‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  have hs4 : ‖y - e‖ ≤ 2 := (norm_sub_le y e).trans (by rw [hy, he]; norm_num)
  set s := ‖y - e‖ ^ 2 with hs
  have hspos : 0 < s := by positivity
  have hs4' : s ≤ 4 := by rw [hs]; nlinarith
  set q := ‖(r : ℂ) * y - e‖ ^ 2 with hq
  have hqlow : s / 2 ≤ q := by rw [hid]; nlinarith [sq_nonneg (1 - r)]
  have hqup : q ≤ 5 := by rw [hid]; nlinarith
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hqlow
  have hA : Real.log q = 2 * Real.log ‖(r : ℂ) * y - e‖ := by
    rw [hq, Real.log_pow]; push_cast; ring
  have hB : Real.log s = 2 * Real.log ‖y - e‖ := by
    rw [hs, Real.log_pow]; push_cast; ring
  have h1 : Real.log q ≤ 4 := (Real.log_le_sub_one_of_pos hqpos).trans (by linarith)
  have h2 : Real.log s - Real.log 2 ≤ Real.log q := by
    rw [← Real.log_div hspos.ne' two_ne_zero]
    exact Real.log_le_log (by positivity) hqlow
  have h3 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
  have hB' := le_abs_self (Real.log ‖y - e‖)
  have hB'' := neg_abs_le (Real.log ‖y - e‖)
  rw [abs_le]
  constructor <;> linarith

/-- `fmPsi y = π Re y` on the unit circle (limit from inside). -/
lemma fmPsi_of_norm_eq_one (y : ℂ) (hy : ‖y‖ = 1) : fmPsi y = π * y.re := by
  have hae : ∀ᵐ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ≠ y := by
    have h0 := ((countable_singleton y).preimage_circleMap 0 one_ne_zero).measure_zero
      (volume : Measure ℝ)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with θ hθ
    intro h
    apply hθ
    simp [circleMap_zero, h]
  have hint : IntervalIntegrable (fun θ : ℝ => Real.log ‖y - Complex.exp ((θ : ℂ) * Complex.I)‖)
      volume 0 (2 * π) := by
    have h := (circleIntegrable_def _ _ _).1
      (circleIntegrable_log_norm_sub_const (a := y) (c := 0) 1)
    have hf : (fun θ : ℝ => Real.log ‖circleMap 0 1 θ - y‖) =
        fun θ : ℝ => Real.log ‖y - Complex.exp ((θ : ℂ) * Complex.I)‖ := by
      funext θ; rw [circleMap_zero, norm_sub_rev]; simp
    exact hf ▸ h
  have hlim : Tendsto (fun r : ℝ => fmPsi ((r : ℂ) * y)) (𝓝[<] 1) (𝓝 (fmPsi y)) := by
    unfold fmPsi
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ => |Real.log ‖y - Complex.exp ((θ : ℂ) * Complex.I)‖| + 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun r => (by fun_prop : Measurable fun θ : ℝ =>
        Real.cos θ * -Real.log ‖(r : ℂ) * y - Complex.exp ((θ : ℂ) * Complex.I)‖).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with r hr
      filter_upwards [hae] with θ hθ _
      have he : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
      have hb := fmPsi_log_bound y _ hy he hθ r hr.1 hr.2
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      calc |Real.cos θ| * |Real.log ‖(r : ℂ) * y - Complex.exp ((θ : ℂ) * Complex.I)‖|
          ≤ 1 * |Real.log ‖(r : ℂ) * y - Complex.exp ((θ : ℂ) * Complex.I)‖| :=
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hb
    · exact hint.abs.add intervalIntegrable_const
    · filter_upwards [hae] with θ hθ _
      have hc : ContinuousAt (fun r : ℝ => Real.cos θ *
          -Real.log ‖(r : ℂ) * y - Complex.exp ((θ : ℂ) * Complex.I)‖) 1 := by
        refine continuousAt_const.mul (ContinuousAt.neg (ContinuousAt.log (by fun_prop) ?_))
        simpa using sub_ne_zero.2 (Ne.symm hθ)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun r : ℝ => fmPsi ((r : ℂ) * y)) (𝓝[<] 1) (𝓝 (π * y.re)) := by
    have hc : Continuous fun r : ℝ => π * ((r : ℂ) * y).re := by fun_prop
    have h1 := hc.tendsto 1
    simp only [Complex.ofReal_one, one_mul] at h1
    refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    rw [fmPsi_of_norm_lt_one]
    rw [norm_mul, hy, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    exact hr.2
  exact tendsto_nhds_unique hlim hlim2

/-- The map `y ↦ y` on the closed disc, `y ↦ y / ‖y‖²` outside. -/
def fmPsiG (y : ℂ) : ℂ := if ‖y‖ ≤ 1 then y else (‖y‖ ^ 2)⁻¹ • y

lemma fmPsi_eq_G (y : ℂ) : fmPsi y = π * (fmPsiG y).re := by
  unfold fmPsiG
  split_ifs with h
  · rcases h.lt_or_eq with h | h
    · exact fmPsi_of_norm_lt_one y h
    · exact fmPsi_of_norm_eq_one y h
  · rw [fmPsi_of_one_lt_norm y (not_le.1 h), Complex.smul_re, smul_eq_mul]
    ring

lemma fmPsiG_norm_le (y : ℂ) : ‖fmPsiG y‖ ≤ 1 := by
  unfold fmPsiG
  split_ifs with h
  · exact h
  · have h1 : 1 < ‖y‖ := not_le.1 h
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, abs_norm, sq, mul_inv,
      mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
    exact inv_le_one_of_one_le₀ h1.le

lemma fmPsiG_mixed (y y' : ℂ) (hy : ‖y‖ ≤ 1) (hy' : 1 < ‖y'‖) :
    ‖y - (‖y'‖ ^ 2)⁻¹ • y'‖ ≤ ‖y - y'‖ := by
  set a := ‖y'‖ ^ 2 with ha
  set t := a⁻¹ with ht
  have ha1 : 1 < a := by rw [ha]; nlinarith
  have hat : a * t = 1 := mul_inv_cancel₀ (by positivity)
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ ha1.le
  have htpos : 0 ≤ t := by positivity
  have h1 : ‖y - t • y'‖ ^ 2 = ‖y‖ ^ 2 - 2 * (t * ⟪y, y'⟫) + t ^ 2 * a := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h2 : ‖y - y'‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, y'⟫ + a := norm_sub_sq_real y y'
  have h3 : 0 ≤ ‖y - y'‖ ^ 2 := sq_nonneg _
  have h4 : t ^ 2 * a = t := by
    rw [show t ^ 2 * a = t * (a * t) by ring, hat, mul_one]
  have hn : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, h1, h4]
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) (show 0 ≤ a + 1 - 2 * ⟪y, y'⟫ by linarith)]

lemma fmPsiG_outside (y y' : ℂ) (hy : 1 < ‖y‖) (hy' : 1 < ‖y'‖) :
    ‖(‖y‖ ^ 2)⁻¹ • y - (‖y'‖ ^ 2)⁻¹ • y'‖ ≤ ‖y - y'‖ := by
  have hy0 : ‖y‖ ≠ 0 := by positivity
  have hy0' : ‖y'‖ ≠ 0 := by positivity
  have key : ‖(‖y‖ ^ 2)⁻¹ • y - (‖y'‖ ^ 2)⁻¹ • y'‖ ^ 2 =
      ((‖y‖ ^ 2) * (‖y'‖ ^ 2))⁻¹ * ‖y - y'‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_inv, abs_pow,
      abs_pow, abs_norm, abs_norm]
    field_simp
    ring
  have hab : ((‖y‖ ^ 2) * (‖y'‖ ^ 2))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le (by nlinarith) (by nlinarith))
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, key]
  exact mul_le_of_le_one_left (sq_nonneg _) hab

lemma fmPsiG_lip (y y' : ℂ) : ‖fmPsiG y - fmPsiG y'‖ ≤ ‖y - y'‖ := by
  unfold fmPsiG
  split_ifs with h h' h'
  · exact le_rfl
  · exact fmPsiG_mixed y y' h (not_le.1 h')
  · rw [norm_sub_rev, norm_sub_rev y]; exact fmPsiG_mixed y' y h' (not_le.1 h)
  · exact fmPsiG_outside y y' (not_le.1 h) (not_le.1 h')

/-- **Node FM-PSI holds.** -/
theorem fmPsiStmt_holds : FMPsiStmt := by
  refine ⟨fun y => ?_, fun y y' => ?_⟩
  · rw [fmPsi_eq_G, abs_mul, abs_of_pos Real.pi_pos]
    calc π * |(fmPsiG y).re| ≤ π * 1 :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (fmPsiG_norm_le y))
            Real.pi_pos.le
      _ = π := mul_one π
  · rw [fmPsi_eq_G, fmPsi_eq_G, ← mul_sub, abs_mul, abs_of_pos Real.pi_pos, ← Complex.sub_re]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (fmPsiG_lip y y'))
      Real.pi_pos.le

end D3Plus
end QuantumZipper
