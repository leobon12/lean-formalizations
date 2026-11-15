/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetZoneKoebe
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofCover

/-!
# Proposition 3.8 in a chart: the moment bound and Borel–Cantelli on random sets

Packet PROVE-T15-RET6 (Aux. lemma 82, supplement pp. 296–297). Two probabilistic steps of the landed Proposition 3.8
(`LocalSets.lintegral_indicator_exp_meanDiff_le`, `LocalSets.ae_eventually_abs_lt_of_layer`), restated so that the
patches may be random chart patches:

* **`lintegral_indicator_exp_mean_sub_le`**: if an observable `X` is conditionally Gaussian given `𝒢 ≤ 𝒥` with
  means `μ₂`, `μ₁` and variances `V₂`, `V₁` (`Sec6.Prop65.IsCondGaussian`), and `V₂ − V₁ ≤ κ` on `E ∩ F` with `E ∈ 𝒥`,
  `F ∈ 𝒢`, then `E[1_{E∩F} e^{λ(μ₁ − μ₂)}] ≤ e^{λ²κ/2}` (the argument of `lintegral_indicator_exp_meanDiff_le`, with
  conditional laws given by `IsCondGaussian`, as `Sec7.FlatClockProof.isCondGaussian_of_cover` supplies them for
  history-marked local sets);
* **`ae_eventually_abs_lt_of_sets`**: the Borel–Cantelli step of `ae_eventually_abs_lt_of_layer` for arbitrary
  jointly measurable random sets `L n ⊆ Ω × B(c, 3R)` in place of the Euclidean dyadic layers: almost surely, for all
  large `n`, `|u| < η` at every `w` whose ball `B̄(w, 2^{-n-2})` lies in the `ω`-section of `L n`.

No Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal

open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)
open InteractingSLE.GFF (eventually_params eight_pow_mul_half_pow_sq ofReal_exp_mul_le_lintegral_of_harmonic
  bumpMass bumpMass_pos)

namespace InteractingSLE

namespace RLC

namespace RetZone

open Sec6.Prop65

/-! ### Exponential moments of a difference of two conditional means -/

section Moment

variable {Ω : Type*} {𝒢 𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Exponential moments of the difference of two conditional means.** Let `X` be conditionally Gaussian given
`𝒥` (mean `μ₁`, variance `V₁`) and given `𝒢 ≤ 𝒥` (mean `μ₂`, variance `V₂`). If `V₂ − V₁ ≤ κ` almost surely on
`E ∩ F`, with `E ∈ 𝒥` and `F ∈ 𝒢`, then `E[1_{E∩F} e^{λ (μ₁ − μ₂)}] ≤ e^{λ² κ/2}`. -/
theorem lintegral_indicator_exp_mean_sub_le (h𝒢𝒥 : 𝒢 ≤ 𝒥)
    {X μ₁ μ₂ V₁ V₂ : Ω → ℝ} {K₁ K₂ : ℝ} (h₁ : IsCondGaussian 𝒥 P X μ₁ V₁ K₁) (h₂ : IsCondGaussian 𝒢 P X μ₂ V₂ K₂)
    {E F : Set Ω} (hE : MeasurableSet[𝒥] E) (hF : MeasurableSet[𝒢] F) {κ : ℝ}
    (hκ : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ F → V₂ ω - V₁ ω ≤ κ) (lam : ℝ) :
    ∫⁻ ω, (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (lam * (μ₁ ω - μ₂ ω)))) ω ∂P ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * κ / 2)) := by
  set Y₀ : Ω → ℝ := fun ω => X ω - μ₁ ω with hY₀
  set Y₂ : Ω → ℝ := fun ω => X ω - μ₂ ω with hY₂
  set D : Ω → ℝ := fun ω => μ₁ ω - μ₂ ω with hD
  have hDm : Measurable[𝒥] D := h₁.measurable_mean.sub (h₂.measurable_mean.mono h𝒢𝒥 le_rfl)
  have hY₀m : Measurable Y₀ := h₁.measurable_X.sub h₁.measurable_mean'
  have hY₂m : Measurable Y₂ := h₂.measurable_X.sub h₂.measurable_mean'
  have hc₀ := h₁.centered
  have hc₂ := h₂.centered
  set a : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-(lam ^ 2 * (V₂ ω - κ)) / 2)) with ha
  set e₁ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (lam * D ω)) with he₁
  have ham : Measurable[𝒢] a := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact ((measurable_const.mul (h₂.measurable_var.sub measurable_const)).neg).div_const _
  have he₁m : Measurable[𝒥] e₁ :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hDm))
  set W : Ω → ℝ≥0∞ := (E ∩ F).indicator fun ω => a ω * e₁ ω with hW
  have hWm : Measurable[𝒥] W := ((ham.mono h𝒢𝒥 le_rfl).mul he₁m).indicator (hE.inter (h𝒢𝒥 _ hF))
  set W' : Ω → ℝ≥0∞ := F.indicator a with hW'
  have hW'm : Measurable[𝒢] W' := ham.indicator hF
  have step1 : ∫⁻ ω, (E ∩ F).indicator e₁ ω ∂P ≤
      ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₁ ω / 2)) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hκ] with ω hω
    by_cases hωEF : ω ∈ E ∩ F
    · rw [hW, indicator_of_mem hωEF, indicator_of_mem hωEF]
      have hk := hω hωEF.1 hωEF.2
      have hge : 1 ≤ a ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₁ ω / 2)) := by
        rw [ha, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
        have : 0 ≤ lam ^ 2 * (V₁ ω - (V₂ ω - κ)) := mul_nonneg (sq_nonneg _) (by linarith)
        linarith
      calc e₁ ω = e₁ ω * 1 := (mul_one _).symm
        _ ≤ e₁ ω * (a ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₁ ω / 2))) := by gcongr
        _ = a ω * e₁ ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₁ ω / 2)) := by ring
    · rw [indicator_of_notMem hωEF]; exact zero_le
  have step2 := LocalSets.lintegral_mul_exp_of_condCharFun h₁.le hY₀m h₁.measurable_var'
    (Eventually.of_forall h₁.nonneg) hc₀ hWm lam
  have step3 : ∀ ω, W ω * ENNReal.ofReal (Real.exp (lam * Y₀ ω)) ≤
      W' ω * ENNReal.ofReal (Real.exp (lam * Y₂ ω)) := by
    intro ω
    by_cases hωEF : ω ∈ E ∩ F
    · rw [hW, hW', indicator_of_mem hωEF, indicator_of_mem hωEF.2, mul_assoc, he₁]
      simp only
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine le_of_eq (congrArg (fun x => a ω * ENNReal.ofReal (Real.exp x)) ?_)
      simp only [hD, hY₀, hY₂]; ring
    · rw [hW, indicator_of_notMem hωEF, zero_mul]; exact zero_le
  have step4 := LocalSets.lintegral_mul_exp_of_condCharFun h₂.le hY₂m h₂.measurable_var'
    (Eventually.of_forall h₂.nonneg) hc₂ hW'm lam
  have step5 : ∀ ω, W' ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₂ ω / 2)) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * κ / 2)) := by
    intro ω
    by_cases hωF : ω ∈ F
    · rw [hW', indicator_of_mem hωF, ha, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine le_of_eq (congrArg (fun x => ENNReal.ofReal (Real.exp x)) ?_)
      ring
    · rw [hW', indicator_of_notMem hωF, zero_mul]; exact zero_le
  calc ∫⁻ ω, (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (lam * (μ₁ ω - μ₂ ω)))) ω ∂P
      = ∫⁻ ω, (E ∩ F).indicator e₁ ω ∂P := rfl
    _ ≤ ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₁ ω / 2)) ∂P := step1
    _ = ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam * Y₀ ω)) ∂P := step2.symm
    _ ≤ ∫⁻ ω, W' ω * ENNReal.ofReal (Real.exp (lam * Y₂ ω)) ∂P := lintegral_mono step3
    _ = ∫⁻ ω, W' ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₂ ω / 2)) ∂P := step4
    _ ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (lam ^ 2 * κ / 2)) ∂P := lintegral_mono step5
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 * κ / 2)) := by
        rw [lintegral_const, measure_univ, mul_one]

end Moment

/-! ### Borel–Cantelli on random sets -/

section BC

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Borel–Cantelli on random sets** (the step `LocalSets.ae_eventually_abs_lt_of_layer`, with jointly measurable
random sets `L n ⊆ Ω × B(c, 3R)` in place of the dyadic layers). Let `u(ω)` be harmonic on open sets `U(ω)` containing
the sections of `L n`, with jointly measurable versions `G n` on `L n`, and suppose the pointwise exponential moments
`E[1_{(·, y) ∈ L n} e^{l G_n(·, y)}] ≤ e` hold for `2 l² τ_n ≤ 1`, `τ_n = (4·2^{-n}/(c R'))^{1/C₂}`. Then for every
`η > 0`, almost surely, for all large `n`, `|u ω w| < η` whenever `B̄(w, 2^{-n-2})` lies in the section of `L n`. -/
theorem ae_eventually_abs_lt_of_sets {L : ℕ → Set (Ω × ℂ)} (hL : ∀ n, MeasurableSet (L n)) {c : ℂ} {R : ℝ}
    (hLc : ∀ n, ∀ p ∈ L n, p.2 ∈ ball c (3 * R)) {u : Ω → ℂ → ℝ} {U : Ω → Set ℂ} {G : ℕ → Ω × ℂ → ℝ}
    (hGm : ∀ n, Measurable (G n)) {R' : ℝ} (hR' : 0 < R') {n₁ : ℕ}
    (hu : ∀ᵐ ω ∂P, IsOpen (U ω) ∧ InnerProductSpace.HarmonicOnNhd (u ω) (U ω) ∧
      ∀ n ≥ n₁, ∀ y : ℂ, (ω, y) ∈ L n → y ∈ U ω ∧ G n (ω, y) = u ω y)
    (hmom : ∀ n ≥ n₁, ∀ y : ℂ, ∀ l : ℝ,
      2 * l ^ 2 * (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R')) ^ koebeDistExp⁻¹ ≤ 1 →
      ∫⁻ ω, {ω | (ω, y) ∈ L n}.indicator (fun ω => ENNReal.ofReal (Real.exp (l * G n (ω, y)))) ω ∂P ≤
        ENNReal.ofReal (Real.exp 1))
    {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℂ, closedBall w ((1 / 2 : ℝ) ^ (n + 2)) ⊆ {y | (ω, y) ∈ L n} →
      |u ω w| < η := by
  set lam : ℕ → ℝ := fun n => n * Real.log 8 / η with hlam
  set e₁ := expNegInvGlue 1 with he₁
  set f : ℕ → ℝ → Ω × ℂ → ℝ≥0∞ := fun n l => (L n).indicator
    fun p => ENNReal.ofReal (Real.exp (l * G n p)) with hf
  have hfm : ∀ n l, Measurable (f n l) := fun n l =>
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (hGm n)))).indicator (hL n)
  set I : ℕ → ℝ → Ω → ℝ≥0∞ := fun n l ω => ∫⁻ y, f n l (ω, y) with hI
  have hIm : ∀ n l, Measurable (I n l) := fun n l => (hfm n l).lintegral_prod_right'
  set X : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1) * volume (ball c (3 * R)) with hX
  have hEI : ∀ n ≥ n₁, ∀ l : ℝ,
      2 * l ^ 2 * (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R')) ^ koebeDistExp⁻¹ ≤ 1 →
      ∫⁻ ω, I n l ω ∂P ≤ X := by
    intro n hn l hl
    show ∫⁻ ω, (∫⁻ y, f n l (ω, y)) ∂P ≤ X
    rw [lintegral_lintegral_swap (f := fun ω y => f n l (ω, y)) (hfm n l).aemeasurable]
    calc ∫⁻ y, ∫⁻ ω, f n l (ω, y) ∂P
        ≤ ∫⁻ y, (ball c (3 * R)).indicator (fun _ => ENNReal.ofReal (Real.exp 1)) y := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ ball c (3 * R)
          · rw [indicator_of_mem hy]
            refine le_trans (le_of_eq ?_) (hmom n hn y l hl)
            congr 1
          · rw [indicator_of_notMem hy]
            have h0 : ∀ ω, f n l (ω, y) = 0 := fun ω =>
              indicator_of_notMem (fun h => hy (hLc n _ h)) _
            simp only [h0, lintegral_zero, le_refl]
      _ = X := by rw [lintegral_indicator_const measurableSet_ball, hX]
  set F : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal (Real.exp (lam n * η) *
      (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) ≤
      ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω)} with hF
  obtain ⟨n₀', hn₀'⟩ := eventually_atTop.1 (eventually_params hR' η)
  set n₀ := max n₀' n₁ with hn₀def
  set K : ℝ≥0∞ := ENNReal.ofReal e₁ * (X + X) / ENNReal.ofReal (bumpMass / 16) with hK
  have hc₁ := bumpMass_pos
  have hPF : ∀ n ≥ n₀, P (F n) ≤ K * 2⁻¹ ^ n := by
    intro n hn
    obtain ⟨-, -, hl⟩ := hn₀' n (le_of_max_le_left hn)
    have hn1 : n ≥ n₁ := le_of_max_le_right hn
    have hl' : 2 * (-lam n) ^ 2 *
        (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R')) ^ koebeDistExp⁻¹ ≤ 1 := by
      rwa [neg_sq]
    have h1 := hEI n hn1 (lam n) hl
    have h2 := hEI n hn1 (-lam n) hl'
    have hexp : Real.exp (lam n * η) = 8 ^ n := by
      have : lam n * η = n * Real.log 8 := by simp only [hlam]; field_simp
      rw [this, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hden : ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) =
        ENNReal.ofReal (bumpMass / 16) * 2 ^ n := by
      rw [hexp, ← mul_assoc, eight_pow_mul_half_pow_sq, show (2 : ℝ) ^ n / 16 * bumpMass =
        bumpMass / 16 * 2 ^ n by ring, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    have ha0 : ENNReal.ofReal (bumpMass / 16) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hden0 : ENNReal.ofReal (bumpMass / 16) * 2 ^ n ≠ 0 :=
      mul_ne_zero ha0 (pow_ne_zero _ two_ne_zero)
    have hdentop : ENNReal.ofReal (bumpMass / 16) * 2 ^ n ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    have hgm : Measurable fun ω => ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω) :=
      measurable_const.mul ((hIm n _).add (hIm n _))
    have hFn : F n = {ω | ENNReal.ofReal (bumpMass / 16) * 2 ^ n ≤
        ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω)} := by
      simp only [hF, hden]
    calc P (F n) ≤ (∫⁻ ω, ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω) ∂P) /
          (ENNReal.ofReal (bumpMass / 16) * 2 ^ n) := by
          rw [hFn]
          exact meas_ge_le_lintegral_div hgm.aemeasurable hden0 hdentop
      _ = ENNReal.ofReal e₁ * ((∫⁻ ω, I n (lam n) ω ∂P) + ∫⁻ ω, I n (-lam n) ω ∂P) /
          (ENNReal.ofReal (bumpMass / 16) * 2 ^ n) := by
          rw [lintegral_const_mul (f := fun ω => I n (lam n) ω + I n (-lam n) ω) _ ((hIm n _).add (hIm n _)),
            lintegral_add_left (hIm n _)]
      _ ≤ ENNReal.ofReal e₁ * (X + X) / (ENNReal.ofReal (bumpMass / 16) * 2 ^ n) := by
          gcongr
      _ = K * 2⁻¹ ^ n := by
          rw [hK, div_eq_mul_inv, ENNReal.mul_inv (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top),
            ENNReal.inv_pow, ← mul_assoc, ← div_eq_mul_inv]
  have hKtop : K ≠ ⊤ := by
    refine ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have : X ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    exact ENNReal.add_ne_top.2 ⟨this, this⟩
  have hsum : ∑' k, P (F (k + n₀)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, K * 2⁻¹ ^ k) ?_ (ENNReal.tsum_le_tsum fun k =>
      (hPF (k + n₀) (by omega)).trans (mul_le_mul_right
        (pow_le_pow_of_le_one zero_le (ENNReal.inv_le_one.2 one_le_two) (Nat.le_add_right k n₀))
        K))
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_ne_top hKtop ENNReal.ofNat_ne_top
  -- Borel–Cantelli
  filter_upwards [ae_eventually_notMem hsum, hu] with ω hev hωu
  obtain ⟨hUo, hharm, hGu⟩ := hωu
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
  refine ⟨K₀ + n₀, fun n hn w hball => ?_⟩
  have hn' : n₀ ≤ n := by omega
  have hnotF : ω ∉ F n := by
    have := hK₀ (n - n₀) (by omega)
    rwa [Nat.sub_add_cancel hn'] at this
  have hn1 : n ≥ n₁ := le_trans (le_max_right _ _) hn'
  set N : Set ℂ := {y | (ω, y) ∈ L n} with hNdef
  have hBU : closedBall w ((1 / 2 : ℝ) ^ (n + 2)) ⊆ U ω := fun y hy => (hGu n hn1 y (hball hy)).1
  have hIeq : ∀ l, ∫⁻ y in N, ENNReal.ofReal (Real.exp (l * u ω y)) = I n l ω := by
    intro l
    have hLm : MeasurableSet N := measurable_prodMk_left (hL n)
    rw [hI, ← lintegral_indicator hLm]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ N
    · rw [indicator_of_mem hy]
      simp only [hf]
      rw [indicator_of_mem (show (ω, y) ∈ L n from hy), (hGu n hn1 y hy).2]
    · rw [indicator_of_notMem hy]
      simp only [hf]
      rw [indicator_of_notMem (show (ω, y) ∉ L n from hy)]
  have hJ := fun l => ofReal_exp_mul_le_lintegral_of_harmonic hUo hharm (by positivity) hBU l hball
  by_contra hlt
  push Not at hlt
  apply hnotF
  show ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) ≤
    ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω)
  have hlam0 : 0 ≤ lam n := by simp only [hlam]; positivity
  have hpos : 0 ≤ ((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass := by positivity
  rcases le_abs'.1 hlt with hneg | hpos'
  · calc ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass))
        ≤ ENNReal.ofReal (Real.exp (-lam n * u ω w) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.2 (by nlinarith)) hpos)
      _ ≤ ENNReal.ofReal e₁ * I n (-lam n) ω := by rw [← hIeq]; exact hJ (-lam n)
      _ ≤ _ := by gcongr; exact le_add_self
  · calc ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass))
        ≤ ENNReal.ofReal (Real.exp (lam n * u ω w) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.2 (by nlinarith)) hpos)
      _ ≤ ENNReal.ofReal e₁ * I n (lam n) ω := by rw [← hIeq]; exact hJ (lam n)
      _ ≤ _ := by gcongr; exact le_self_add

end BC

end RetZone

end RLC

end InteractingSLE
