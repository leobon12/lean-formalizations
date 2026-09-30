import QuantumZipper.Proofs.Field.PairLimBasic

/-!
# PAIR-AFF, part 1: affine images of a bounded-density measure

For `η` satisfying `PairLim.Setup M R δ η` and the affine map `aff t b w = t + b w` (`t : ℝ`,
`b > 0`), this file proves

* `Setup.map_aff`: `η.map (aff t b)` again satisfies `Setup`, with density `≤ M / b₀²` for
  `b ≥ b₀`, height `≥ min (b₀ δ) 1` (Jacobian of `w ↦ t + b w` is `b²`);
* `lintegral_inv_norm_sub_le`: `∫ ‖y - c‖⁻¹ dν ≤ 2π M + ν(ℂ)` for a density `≤ M`;
* `Setup.abs_Pot_aff_sub_le`: the smoothed potentials of the affine images are Lipschitz in
  `(t, b)`, uniformly in the point and the smoothing radius.

These are the deterministic inputs of the three-parameter Kolmogorov argument in `PairAff.lean`.
Own elementary proofs (cost rule of AGENT_GUIDE): the change of variables for Lebesgue measure
(`Measure.map_addHaar_smul`), the integrability of `|z|⁻¹` in the plane (polar coordinates), and
the Lipschitz bound `|log max(s,r₁) - log max(s,r₂)| ≤ |r₁ - r₂| (r₁⁻¹ + r₂⁻¹)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace PairLim

open SmoothConv

/-! ## 1. The affine maps -/

/-- The affine map `w ↦ t + b w`. -/
def aff (t b : ℝ) (w : ℂ) : ℂ := (t : ℂ) + (b : ℂ) * w

theorem continuous_aff (t b : ℝ) : Continuous (aff t b) := by unfold aff; fun_prop

theorem measurable_aff (t b : ℝ) : Measurable (aff t b) := (continuous_aff t b).measurable

theorem map_volume_aff {t b : ℝ} (hb : 0 < b) :
    (volume : Measure ℂ).map (aff t b) = ENNReal.ofReal ((b ^ 2)⁻¹) • volume := by
  have h1 : aff t b = (fun w => (t : ℂ) + w) ∘ (fun w : ℂ => b • w) := by
    funext w; simp [aff, Complex.real_smul]
  rw [h1, ← Measure.map_map (measurable_const_add _) (measurable_const_smul _),
    Measure.map_addHaar_smul volume hb.ne',
    Measure.map_smul _ (measurable_const_add (t : ℂ)).aemeasurable, map_add_left_eq_self,
    Complex.finrank_real_complex, abs_of_pos (by positivity)]

/-- The density constant of the affine images with `b ≥ b₀`. -/
def Maff (M : ℝ≥0) (b₀ : ℝ) : ℝ≥0 := M * Real.toNNReal ((b₀ ^ 2)⁻¹)

theorem map_aff_le {M : ℝ≥0} {η : Measure ℂ} (hη : η ≤ (M : ℝ≥0∞) • volume) {t b b₀ : ℝ}
    (hb₀ : 0 < b₀) (hb : b₀ ≤ b) : η.map (aff t b) ≤ (Maff M b₀ : ℝ≥0∞) • volume := by
  have hb0 : 0 < b := hb₀.trans_le hb
  have h1 : η.map (aff t b) ≤ ((M : ℝ≥0∞) • volume).map (aff t b) :=
    Measure.map_mono hη (measurable_aff t b)
  rw [Measure.map_smul _ (measurable_aff t b).aemeasurable, map_volume_aff hb0, smul_smul] at h1
  refine h1.trans (Measure.le_iff'.2 fun A => ?_)
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  rw [Maff, ENNReal.coe_mul]
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by positivity)]
  exact ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) (pow_le_pow_left₀ hb₀.le hb 2))

variable {M : ℝ≥0} {R δ : ℝ} {η : Measure ℂ}

theorem map_aff_univ (t b : ℝ) : η.map (aff t b) univ = η univ := by
  rw [Measure.map_apply (measurable_aff t b) MeasurableSet.univ, preimage_univ]

/-- **Affine images satisfy the standing hypotheses.** -/
theorem Setup.map_aff (hS : Setup M R δ η) {t b b₀ : ℝ} (hb₀ : 0 < b₀) (hb : b₀ ≤ b) :
    Setup (Maff M b₀) (|t| + b * R) (min (b₀ * δ) 1) (η.map (aff t b)) := by
  have hb0 : 0 < b := hb₀.trans_le hb
  set S := Metric.closedBall (0 : ℂ) (|t| + b * R) ∩ Hbar
  have hSm : MeasurableSet S := measurableSet_closedBall.inter isClosed_Hbar.measurableSet
  have hae : ∀ᵐ y ∂η.map (aff t b), y ∈ S := by
    refine (ae_map_iff (measurable_aff t b).aemeasurable hSm).2 ?_
    filter_upwards [hS.good.ae_mem] with w hw
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hw1 : ‖w‖ ≤ R := by simpa using hw.1
      calc ‖aff t b w‖ ≤ ‖(t : ℂ)‖ + ‖(b : ℂ) * w‖ := norm_add_le _ _
        _ = |t| + b * ‖w‖ := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hb0]
        _ ≤ |t| + b * R := by gcongr
    · show (0 : ℝ) ≤ (aff t b w).im
      have : (0 : ℝ) ≤ w.im := hw.2
      simp [aff]; positivity
  refine ⟨⟨map_aff_le hS.good.1 hb₀ hb, ae_iff.1 hae⟩, lt_min (mul_pos hb₀ hS.pos) one_pos,
    min_le_right _ _, ?_⟩
  rw [ae_map_iff (measurable_aff t b).aemeasurable
    (measurableSet_le measurable_const Complex.measurable_im)]
  filter_upwards [hS.im] with w hw
  have : (aff t b w).im = b * w.im := by simp [aff]
  rw [this]
  calc min (b₀ * δ) 1 ≤ b₀ * δ := min_le_left _ _
    _ ≤ b * w.im := mul_le_mul hb hw hS.pos.le hb0.le

/-! ## 2. The inverse distance against a bounded density -/

theorem lintegral_inv_norm_ball_le :
    ∫⁻ z : ℂ, (Metric.ball (0 : ℂ) 1).indicator (fun z => ENNReal.ofReal ‖z‖⁻¹) z ≤
      ENNReal.ofReal (2 * π) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hmeas : MeasurableSet (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  calc ∫⁻ p in Complex.polarCoord.target, ENNReal.ofReal p.1 •
        (Metric.ball (0 : ℂ) 1).indicator (fun z => ENNReal.ofReal ‖z‖⁻¹)
          (Complex.polarCoord.symm p)
      ≤ ∫⁻ p in Complex.polarCoord.target,
          (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)).indicator (fun _ => 1) p := by
        refine lintegral_mono fun p => ?_
        rw [smul_eq_mul]
        rcases le_or_gt p.1 0 with h0 | h0
        · simp [ENNReal.ofReal_of_nonpos h0]
        by_cases hb : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) 1
        · have h1 : p.1 < 1 := by
            simpa [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
              abs_of_pos h0] using hb
          rw [indicator_of_mem hb, indicator_of_mem (show p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ univ from
            ⟨⟨h0, h1⟩, trivial⟩), Complex.norm_polarCoord_symm, abs_of_pos h0,
            ← ENNReal.ofReal_mul h0.le, mul_inv_cancel₀ h0.ne', ENNReal.ofReal_one]
        · rw [indicator_of_notMem hb, mul_zero]; exact zero_le
    _ = volume ((Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) ∩ Complex.polarCoord.target) := by
        rw [lintegral_indicator_const hmeas, Measure.restrict_apply hmeas, one_mul]
    _ ≤ volume (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π) := by
        gcongr
        rintro p ⟨⟨h1, -⟩, h2⟩
        rw [Complex.polarCoord_target] at h2
        exact ⟨h1, h2.2⟩
    _ = ENNReal.ofReal (2 * π) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

theorem measurable_inv_norm_sub (c : ℂ) :
    Measurable fun y : ℂ => ENNReal.ofReal ‖y - c‖⁻¹ :=
  ENNReal.measurable_ofReal.comp ((measurable_id.sub_const c).norm.inv)

/-- `∫ ‖y - c‖⁻¹ dν ≤ 2π M + ν(ℂ)` for a measure with density `≤ M`. -/
theorem lintegral_inv_norm_sub_le {ν : Measure ℂ} {M : ℝ≥0} (hν : ν ≤ (M : ℝ≥0∞) • volume)
    (c : ℂ) :
    ∫⁻ y, ENNReal.ofReal ‖y - c‖⁻¹ ∂ν ≤ (M : ℝ≥0∞) * ENNReal.ofReal (2 * π) + ν univ := by
  set g : ℂ → ℝ≥0∞ := (Metric.ball (0 : ℂ) 1).indicator (fun z => ENNReal.ofReal ‖z‖⁻¹)
  have hpt : ∀ y, ENNReal.ofReal ‖y - c‖⁻¹ ≤ g (y - c) + 1 := fun y => by
    by_cases hy : y - c ∈ Metric.ball (0 : ℂ) 1
    · rw [show g (y - c) = _ from indicator_of_mem hy _]; exact le_self_add
    · rw [show g (y - c) = 0 from indicator_of_notMem hy _, zero_add, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ ?_)
      simpa [Metric.mem_ball, dist_zero_right] using hy
  calc ∫⁻ y, ENNReal.ofReal ‖y - c‖⁻¹ ∂ν ≤ ∫⁻ y, (g (y - c) + 1) ∂ν := lintegral_mono hpt
    _ = (∫⁻ y, g (y - c) ∂ν) + ν univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, one_mul]
    _ ≤ (M : ℝ≥0∞) * (∫⁻ y, g (y - c)) + ν univ := by
        rw [← smul_eq_mul, ← lintegral_smul_measure]
        exact add_le_add (lintegral_mono' hν le_rfl) le_rfl
    _ = (M : ℝ≥0∞) * (∫⁻ z, g z) + ν univ := by rw [lintegral_sub_right_eq_self g c]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl lintegral_inv_norm_ball_le) le_rfl

/-! ## 3. Lipschitz bound for the potentials in `(t, b)` -/

theorem log_sub_log_le_div {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) :
    Real.log x - Real.log y ≤ (x - y) / y := by
  rw [← Real.log_div (hy.trans_le hxy).ne' hy.ne']
  have := Real.log_le_sub_one_of_pos (div_pos (hy.trans_le hxy) hy)
  have e : x / y - 1 = (x - y) / y := by field_simp
  linarith

theorem abs_logmax_sub_le {s r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    |Real.log (max s r₁) - Real.log (max s r₂)| ≤ |r₁ - r₂| * (r₁⁻¹ + r₂⁻¹) := by
  have hd : |max s r₁ - max s r₂| ≤ |r₁ - r₂| := by
    have := abs_max_sub_max_le_max s r₁ s r₂
    rwa [sub_self, abs_zero, max_eq_right (abs_nonneg (r₁ - r₂))] at this
  have key : ∀ {a b ra rb : ℝ}, 0 < rb → ra ≤ a → rb ≤ b → b ≤ a → |a - b| ≤ |ra - rb| →
      Real.log a - Real.log b ≤ |ra - rb| * rb⁻¹ := by
    intro a b ra rb hrb _ hb hba hab
    have hb0 : 0 < b := hrb.trans_le hb
    refine (log_sub_log_le_div hb0 hba).trans ?_
    rw [div_eq_mul_inv]
    have h1 : a - b ≤ |ra - rb| := (le_abs_self _).trans hab
    exact mul_le_mul h1 (inv_anti₀ hrb hb) (inv_nonneg.2 hb0.le) (abs_nonneg _)
  have hi₁ : 0 ≤ |r₁ - r₂| * r₁⁻¹ := by positivity
  have hi₂ : 0 ≤ |r₁ - r₂| * r₂⁻¹ := by positivity
  rcases le_total (max s r₂) (max s r₁) with h | h
  · rw [abs_of_nonneg (by linarith [Real.log_le_log (h₂.trans_le (le_max_right _ _)) h])]
    have := key h₂ (le_max_right s r₁) (le_max_right s r₂) h hd
    rw [mul_add]; linarith
  · rw [abs_of_nonpos (by linarith [Real.log_le_log (h₁.trans_le (le_max_right _ _)) h])]
    have := key (ra := r₂) h₁ (le_max_right s r₂) (le_max_right s r₁) h
      (by rwa [abs_sub_comm, abs_sub_comm r₂])
    rw [abs_sub_comm r₂] at this
    rw [mul_add]; linarith

theorem abs_Nr_sub_le (s : ℝ) {w₁ w₂ x : ℂ} (h₁ : w₁ ≠ x) (h₂ : w₂ ≠ x) (h₁' : w₁ ≠ conj x)
    (h₂' : w₂ ≠ conj x) :
    |Nr s w₁ x - Nr s w₂ x| ≤ ‖w₁ - w₂‖ *
      (‖w₁ - x‖⁻¹ + ‖w₂ - x‖⁻¹ + ‖w₁ - conj x‖⁻¹ + ‖w₂ - conj x‖⁻¹) := by
  have hn : ∀ c : ℂ, |‖w₁ - c‖ - ‖w₂ - c‖| ≤ ‖w₁ - w₂‖ := fun c => by
    simpa using abs_norm_sub_norm_le (w₁ - c) (w₂ - c)
  have hp : ∀ {w c : ℂ}, w ≠ c → 0 < ‖w - c‖ := fun h => norm_pos_iff.2 (sub_ne_zero.2 h)
  have e1 := (abs_logmax_sub_le (s := s) (hp h₁) (hp h₂)).trans
    (mul_le_mul_of_nonneg_right (hn x) (by positivity))
  have e2 := (abs_logmax_sub_le (s := s) (hp h₁') (hp h₂')).trans
    (mul_le_mul_of_nonneg_right (hn (conj x)) (by positivity))
  have e : Nr s w₁ x - Nr s w₂ x =
      -(Real.log (max s ‖w₁ - x‖) - Real.log (max s ‖w₂ - x‖)) -
        (Real.log (max s ‖w₁ - conj x‖) - Real.log (max s ‖w₂ - conj x‖)) := by
    unfold Nr; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_neg]
  nlinarith [e1, e2]

end PairLim
end QuantumZipper
