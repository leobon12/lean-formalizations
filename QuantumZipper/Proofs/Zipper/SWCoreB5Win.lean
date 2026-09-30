import QuantumZipper.Proofs.Zipper.SWCoreB5Cmp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B5 (3): window sandwich of the comparison integral, for one map and one scale

Task SWC-B5 (`handoff/SW-CORE.md`). For a map `ψ` of a boundary class, a finite partition of unity
`(ρ_n)` in the target variable, weights `F_n` and window indices `J_n` such that, on the pieces,
`f ≤ F_n` (resp. `F⁻_n ≤ f`) and the scale `2^{-k}|ψ'|` lies in the window `J_n`, the comparison
integral `cmpInt` is bounded above by `∑ F_n ∫ ρ_n · bSupWin_{J_n}` and below by
`∑ F⁻_n ∫ ρ_n · bInfWin_{J_n}` (change of variables `u = Re ψ(t)`, mathlib
`lintegral_image_eq_lintegral_abs_deriv_mul`). This is the sandwich of
`F1.tendsto_lintegral_bdryVarScale` (SW proof of Thm 4.2/4.3, p. 19), with the partition taken
**independent of the map**, so that the window limits can be used uniformly over the class.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

variable {a b ρ M m : ℝ} {ψ : ℂ → ℂ}

/-- Change of variables `u = Re ψ(t)` on an inner interval. -/
theorem lintegral_cov_of_class (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {a' b' : ℝ}
    (ha : a < a') (hb : b' < b) (H : ℝ → ℝ≥0∞) :
    ∫⁻ t in Icc a' b', ENNReal.ofReal ‖deriv ψ t‖ * H (ψ t).re =
      ∫⁻ u in (fun t : ℝ => (ψ t).re) '' Icc a' b', H u := by
  have hsubI : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha.le hb.le
  have hJU : ∀ s ∈ Icc a b, (s : ℂ) ∈ thickening ρ (segC a b) := fun s hs =>
    self_subset_thickening hρ _ (ofReal_mem_segC hs)
  have hderiv : ∀ t ∈ Icc a' b', HasDerivWithinAt (fun t : ℝ => (ψ t).re) (deriv ψ t).re
      (Icc a' b') t := fun t ht =>
    ((hψ.1.differentiableAt (isOpen_thickening.mem_nhds (hJU t (hsubI ht)))).hasDerivAt
      ).real_of_complex.hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderiv
    (hψ.2.2.2.1.injOn.mono hsubI)]
  refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  have him := (deriv_facts_of_class hψ hρ ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).1
  rw [Complex.abs_re_eq_norm.2 him]

/-- A.e.-measurability of the integrands on `[a',b']`. -/
theorem aemeasurable_cov (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {a' b' : ℝ}
    (ha : a < a') (hb : b' < b) {H : ℝ → ℝ≥0∞} (hH : Measurable H) (c : ℝ≥0∞) :
    AEMeasurable (fun t : ℝ => c * (ENNReal.ofReal ‖deriv ψ t‖ * H (ψ t).re))
      (volume.restrict (Icc a' b')) := by
  have hsubI : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha.le hb.le
  have hJU : ∀ s ∈ Icc a b, (s : ℂ) ∈ thickening ρ (segC a b) := fun s hs =>
    self_subset_thickening hρ _ (ofReal_mem_segC hs)
  have hc1 : ContinuousOn (fun t : ℝ => ψ t) (Icc a' b') :=
    hψ.1.continuousOn.comp Complex.continuous_ofReal.continuousOn fun t ht => hJU t (hsubI ht)
  have hc2 : ContinuousOn (fun t : ℝ => deriv ψ t) (Icc a' b') :=
    (hψ.1.deriv isOpen_thickening).continuousOn.comp Complex.continuous_ofReal.continuousOn
      fun t ht => hJU t (hsubI ht)
  have m1 : AEMeasurable (fun t : ℝ => (ψ t).re) (volume.restrict (Icc a' b')) :=
    (Complex.continuous_re.comp_continuousOn hc1).aemeasurable measurableSet_Icc
  have m2 : AEMeasurable (fun t : ℝ => ENNReal.ofReal ‖deriv ψ t‖)
      (volume.restrict (Icc a' b')) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hc2.norm.aemeasurable measurableSet_Icc)
  exact aemeasurable_const.mul (m2.mul (hH.comp_aemeasurable m1))

variable {γ : ℝ} {x : FieldSample} {N : ℕ} {k : ℕ} {f : ℝ → ℝ} {a' b' : ℝ}
  {T : Finset ℤ} {φ : T → ℝ → ℝ}

/-- **Upper window bound** of the comparison integral. -/
theorem cmpInt_le_win (hx : IsRegularSample x) (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ)
    (ha : a < a') (hb : b' < b) (hf0 : ∀ t, 0 ≤ f t) (hφc : ∀ n, Continuous (φ n))
    (hφ0 : ∀ n u, 0 ≤ φ n u) (F : T → ℝ) (J : T → ℕ)
    (hsum : ∀ t ∈ Icc a' b', ∑ n, φ n (ψ t).re = 1)
    (hpt : ∀ t ∈ Icc a' b', ∀ n, φ n (ψ t).re ≠ 0 → f t ≤ F n ∧
      radius k * ‖deriv ψ t‖ ∈ Icc (winLo N (J n)) (winHi N (J n))) :
    cmpInt γ x ψ f a' b' k ≤
      ∑ n, ENNReal.ofReal (F n) * ∫⁻ u, F1.bSupWin γ x N (J n) u * ENNReal.ofReal (φ n u) := by
  set H : T → ℝ → ℝ≥0∞ := fun n u => F1.bSupWin γ x N (J n) u * ENNReal.ofReal (φ n u)
    with hH
  have hHm : ∀ n, Measurable (H n) := fun n =>
    (F1.measurable_bSupWin hx γ N (J n)).mul (ENNReal.measurable_ofReal.comp (hφc n).measurable)
  have step : ∀ t ∈ Icc a' b', ENNReal.ofReal
      (‖deriv ψ t‖ * f t * bdryDens γ x (radius k * ‖deriv ψ t‖) (ψ t).re) ≤
      ∑ n, ENNReal.ofReal (F n) * (ENNReal.ofReal ‖deriv ψ t‖ * H n (ψ t).re) := by
    intro t ht
    set d := ‖deriv ψ t‖
    set B := bdryDens γ x (radius k * d) (ψ t).re
    have hB0 : 0 ≤ B := by
      unfold B bdryDens
      exact mul_nonneg (Real.rpow_nonneg (mul_nonneg (radius_pos k).le (norm_nonneg _)) _)
        (Real.exp_pos _).le
    have e1 : d * f t * B = ∑ n, d * f t * B * φ n (ψ t).re := by
      rw [← Finset.mul_sum, hsum t ht, mul_one]
    rw [e1, ENNReal.ofReal_sum_of_nonneg fun n _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (hf0 t)) hB0) (hφ0 n _)]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases h0 : φ n (ψ t).re = 0
    · simp [h0]
    obtain ⟨hfF, hwin⟩ := hpt t ht n h0
    have hF0 : 0 ≤ F n := (hf0 t).trans hfF
    have hBle : ENNReal.ofReal B ≤ F1.bSupWin γ x N (J n) (ψ t).re :=
      le_iSup₂_of_le (radius k * d) hwin le_rfl
    simp only [hH]
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (norm_nonneg _) (hf0 t)) hB0),
      ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (hf0 t)),
      ENNReal.ofReal_mul (norm_nonneg _)]
    calc ENNReal.ofReal d * ENNReal.ofReal (f t) * ENNReal.ofReal B *
          ENNReal.ofReal (φ n (ψ t).re) ≤ ENNReal.ofReal d * ENNReal.ofReal (F n) *
          F1.bSupWin γ x N (J n) (ψ t).re * ENNReal.ofReal (φ n (ψ t).re) := by
          gcongr
      _ = ENNReal.ofReal (F n) * (ENNReal.ofReal d *
          (F1.bSupWin γ x N (J n) (ψ t).re * ENNReal.ofReal (φ n (ψ t).re))) := by ring
  unfold cmpInt
  calc _ ≤ ∫⁻ t in Icc a' b', ∑ n, ENNReal.ofReal (F n) *
        (ENNReal.ofReal ‖deriv ψ t‖ * H n (ψ t).re) :=
        setLIntegral_mono' measurableSet_Icc step
    _ = ∑ n, ENNReal.ofReal (F n) * ∫⁻ t in Icc a' b',
        ENNReal.ofReal ‖deriv ψ t‖ * H n (ψ t).re := by
        rw [lintegral_finsetSum' _ fun n _ => aemeasurable_cov hψ hρ ha hb (hHm n) _]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∑ n, ENNReal.ofReal (F n) * ∫⁻ u, H n u := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [lintegral_cov_of_class hψ hρ ha hb]
        exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- **Lower window bound** of the comparison integral. -/
theorem win_le_cmpInt (hx : IsRegularSample x) (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ)
    (ha : a < a') (hb : b' < b) (hf0 : ∀ t, 0 ≤ f t) (hφc : ∀ n, Continuous (φ n))
    (hφ0 : ∀ n u, 0 ≤ φ n u) (F : T → ℝ) (hF0 : ∀ n, 0 ≤ F n) (J : T → ℕ)
    (hsum : ∀ u, ∑ n, φ n u ≤ 1)
    (hsupp : ∀ n, 0 < F n → ∀ u, φ n u ≠ 0 → u ∈ (fun t : ℝ => (ψ t).re) '' Icc a' b')
    (hpt : ∀ t ∈ Icc a' b', ∀ n, φ n (ψ t).re ≠ 0 → F n ≤ f t ∧
      radius k * ‖deriv ψ t‖ ∈ Icc (winLo N (J n)) (winHi N (J n))) :
    ∑ n, ENNReal.ofReal (F n) * ∫⁻ u, F1.bInfWin γ x N (J n) u * ENNReal.ofReal (φ n u) ≤
      cmpInt γ x ψ f a' b' k := by
  set H : T → ℝ → ℝ≥0∞ := fun n u => F1.bInfWin γ x N (J n) u * ENNReal.ofReal (φ n u)
    with hH
  have hHm : ∀ n, Measurable (H n) := fun n =>
    (F1.measurable_bInfWin hx γ N (J n)).mul (ENNReal.measurable_ofReal.comp (hφc n).measurable)
  have step : ∀ t ∈ Icc a' b',
      ∑ n, ENNReal.ofReal (F n) * (ENNReal.ofReal ‖deriv ψ t‖ * H n (ψ t).re) ≤
      ENNReal.ofReal (‖deriv ψ t‖ * f t * bdryDens γ x (radius k * ‖deriv ψ t‖) (ψ t).re) := by
    intro t ht
    set d := ‖deriv ψ t‖
    set B := bdryDens γ x (radius k * d) (ψ t).re
    have hB0 : 0 ≤ B := by
      unfold B bdryDens
      exact mul_nonneg (Real.rpow_nonneg (mul_nonneg (radius_pos k).le (norm_nonneg _)) _)
        (Real.exp_pos _).le
    have hP : 0 ≤ d * f t * B := mul_nonneg (mul_nonneg (norm_nonneg _) (hf0 t)) hB0
    have e1 : ∑ n, d * f t * B * φ n (ψ t).re ≤ d * f t * B := by
      rw [← Finset.mul_sum]
      calc d * f t * B * ∑ n, φ n (ψ t).re ≤ d * f t * B * 1 := by gcongr; exact hsum _
        _ = d * f t * B := mul_one _
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal e1)
    rw [ENNReal.ofReal_sum_of_nonneg fun n _ => mul_nonneg hP (hφ0 n _)]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases h0 : φ n (ψ t).re = 0
    · simp [hH, h0]
    obtain ⟨hfF, hwin⟩ := hpt t ht n h0
    have hBle : F1.bInfWin γ x N (J n) (ψ t).re ≤ ENNReal.ofReal B :=
      iInf₂_le_of_le (radius k * d) hwin le_rfl
    simp only [hH]
    rw [ENNReal.ofReal_mul hP, ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (hf0 t)),
      ENNReal.ofReal_mul (norm_nonneg _)]
    calc ENNReal.ofReal (F n) * (ENNReal.ofReal d *
          (F1.bInfWin γ x N (J n) (ψ t).re * ENNReal.ofReal (φ n (ψ t).re))) =
          ENNReal.ofReal d * ENNReal.ofReal (F n) *
          F1.bInfWin γ x N (J n) (ψ t).re * ENNReal.ofReal (φ n (ψ t).re) := by ring
      _ ≤ ENNReal.ofReal d * ENNReal.ofReal (f t) * ENNReal.ofReal B *
          ENNReal.ofReal (φ n (ψ t).re) := by gcongr
  unfold cmpInt
  calc _ ≤ ∑ n, ENNReal.ofReal (F n) * ∫⁻ t in Icc a' b',
        ENNReal.ofReal ‖deriv ψ t‖ * H n (ψ t).re := by
        refine Finset.sum_le_sum fun n _ => ?_
        rcases (hF0 n).eq_or_lt with h | h
        · rw [← h]; simp
        rw [lintegral_cov_of_class hψ hρ ha hb]
        refine le_of_eq (congrArg _ (setLIntegral_eq_of_support_subset ?_).symm)
        intro u hu
        refine hsupp n h u fun h0 => hu ?_
        simp [h0]
    _ = ∫⁻ t in Icc a' b', ∑ n, ENNReal.ofReal (F n) *
        (ENNReal.ofReal ‖deriv ψ t‖ * H n (ψ t).re) := by
        rw [lintegral_finsetSum' _ fun n _ => aemeasurable_cov hψ hρ ha hb (hHm n) _]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := setLIntegral_mono' measurableSet_Icc step

end SWCore
end QuantumZipper
