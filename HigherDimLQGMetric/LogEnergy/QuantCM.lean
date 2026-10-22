import HigherDimLQGMetric.LogEnergy.QuantLap

/-!
# Quantitative Cameron–Martin estimate

The private Fourier pairing steps are repeated locally because the upstream
CM module only exports an existential bound. The estimate below exposes a
uniform constant for families controlled in ordinary squared integrals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory FourierTransform
open HigherDimLFPP (Rd)
open scoped SchwartzMap FourierTransform RealInnerProductSpace
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- A compact smooth real function, viewed as a complex Schwartz function. -/
def compactComplexSchwartz {F : Rd d → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F) :
    𝓢(Rd d, ℂ) :=
  (hc.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hF)

theorem compactComplexSchwartz_apply {F : Rd d → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (x : Rd d) : compactComplexSchwartz hF hc x = (F x : ℂ) := rfl

/-- A Schwartz function has finite squared Fourier mass with any natural polynomial weight. -/
private theorem integrable_schwartz_weight_sq (f : 𝓢(Rd d, ℂ)) (n : ℕ) :
    Integrable (fun ζ : Rd d => ‖ζ‖ ^ n * ‖f ζ‖ ^ 2) := by
  have hf : Integrable (fun ζ : Rd d => ‖ζ‖ ^ n * ‖f ζ‖) :=
    f.integrable_pow_mul volume n
  let M : ℝ := SchwartzMap.seminorm ℂ 0 0 f
  have hM : ∀ ζ, ‖f ζ‖ ≤ M := SchwartzMap.norm_le_seminorm ℂ f
  apply Integrable.mono' (hf.const_mul M)
  · fun_prop
  · exact ae_of_all _ fun ζ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc
        ‖ζ‖ ^ n * ‖f ζ‖ ^ 2 = ‖f ζ‖ * (‖ζ‖ ^ n * ‖f ζ‖) := by ring
        _ ≤ M * (‖ζ‖ ^ n * ‖f ζ‖) :=
          mul_le_mul_of_nonneg_right (hM ζ) (by positivity)

/-- The positive homogeneous Sobolev energy of a compact smooth shift is finite. -/
private theorem integrable_compact_fourier_weight {F : Rd d → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F) :
    Integrable (fun ζ : Rd d => ‖ζ‖ ^ (d : ℝ) *
      ‖𝓕 (fun x : Rd d => (F x : ℂ)) ζ‖ ^ 2) := by
  have h := integrable_schwartz_weight_sq
    (𝓕 (compactComplexSchwartz hF hc)) d
  convert h using 1
  ext ζ
  rw [Real.rpow_natCast, SchwartzMap.fourier_coe]
  rfl

/-- Real pairings are the complex Fourier pairings supplied by Parseval. -/
private theorem integral_real_mul_eq_integral_fourier_inner {F : Rd d → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (φ : TestRd d) :
    ((∫ x, F x * φ x : ℝ) : ℂ) =
      ∫ ζ : Rd d, inner ℂ (𝓕 (fun x : Rd d => (F x : ℂ)) ζ)
        (𝓕 (fun x : Rd d => (φ x : ℂ)) ζ) := by
  let f := compactComplexSchwartz hF hc
  let g := testComplexSchwartz φ
  have hp := SchwartzMap.integral_inner_fourier_fourier f g
  have hr : ((∫ x, F x * φ x : ℝ) : ℂ) =
      ∫ x : Rd d, inner ℂ (f x) (g x) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change (↑(F x * φ x) : ℂ) = inner ℂ (↑(F x) : ℂ) (↑(φ x) : ℂ)
    simp [Complex.ofReal_mul, mul_comm]
  rw [hr, ← hp]
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  rfl

/-- Parseval followed by the pointwise inner-product estimate. -/
private theorem abs_integral_mul_le_fourier_norm {F : Rd d → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (φ : TestRd d) :
    |∫ x, F x * φ x| ≤ ∫ ζ : Rd d,
      ‖𝓕 (fun x : Rd d => (F x : ℂ)) ζ‖ *
        ‖𝓕 (fun x : Rd d => (φ x : ℂ)) ζ‖ := by
  let f : 𝓢(Rd d, ℂ) := 𝓕 (compactComplexSchwartz hF hc)
  let g : 𝓢(Rd d, ℂ) := 𝓕 (testComplexSchwartz φ)
  have hf : MemLp f 2 volume := f.memLp 2 volume
  have hg : MemLp g 2 volume := g.memLp 2 volume
  have hinner : Integrable (fun ζ : Rd d => inner ℂ (f ζ) (g ζ)) := by
    have h := hf.star.integrable_mul hg
    convert h using 1
    ext ζ
    simp [mul_comm]
  have hprod : Integrable (fun ζ : Rd d => ‖f ζ‖ * ‖g ζ‖) :=
    hf.norm.integrable_mul hg.norm
  calc
    |∫ x, F x * φ x| = ‖((∫ x, F x * φ x : ℝ) : ℂ)‖ := by simp
    _ = ‖∫ ζ : Rd d, inner ℂ (f ζ) (g ζ)‖ := by
      rw [integral_real_mul_eq_integral_fourier_inner hF hc φ]
      rfl
    _ ≤ ∫ ζ : Rd d, ‖inner ℂ (f ζ) (g ζ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ζ : Rd d, ‖f ζ‖ * ‖g ζ‖ :=
      integral_mono hinner.norm hprod (fun ζ => norm_inner_le_norm _ _)
    _ = _ := by
      apply integral_congr_ae
      refine ae_of_all _ fun ζ => ?_
      simp only [f, g, SchwartzMap.fourier_coe]
      rfl

/-- Weighted Cauchy–Schwarz on the Fourier side. -/
private theorem fourier_norm_cauchy_schwarz (hd : 1 ≤ d) {F : Rd d → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (φ : TestRd0 d) :
    (∫ ζ : Rd d, ‖𝓕 (fun x : Rd d => (F x : ℂ)) ζ‖ *
      ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖) ≤
      Real.sqrt (∫ ζ : Rd d, ‖ζ‖ ^ (d : ℝ) *
        ‖𝓕 (fun x : Rd d => (F x : ℂ)) ζ‖ ^ 2) *
      Real.sqrt (∫ ζ : Rd d, ‖ζ‖ ^ (-(d : ℝ)) *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let f : 𝓢(Rd d, ℂ) := 𝓕 (compactComplexSchwartz hF hc)
  let g : 𝓢(Rd d, ℂ) := 𝓕 (testComplexSchwartz φ.1)
  let a : Rd d → ℝ := fun ζ => Real.sqrt (‖ζ‖ ^ (d : ℝ)) * ‖f ζ‖
  let b : Rd d → ℝ := fun ζ => Real.sqrt (‖ζ‖ ^ (-(d : ℝ))) * ‖g ζ‖
  have ha2 : Integrable (fun ζ : Rd d => a ζ ^ 2) := by
    convert integrable_compact_fourier_weight hF hc using 1
    ext ζ
    simp only [a, mul_pow, Real.sq_sqrt (Real.rpow_nonneg (norm_nonneg _) _),
      f, SchwartzMap.fourier_coe]
    rfl
  have hb2 : Integrable (fun ζ : Rd d => b ζ ^ 2) := by
    convert integrable_test_fourier_weight hd φ using 1
    ext ζ
    simp only [b, mul_pow, Real.sq_sqrt (Real.rpow_nonneg (norm_nonneg _) _),
      g, SchwartzMap.fourier_coe]
    rfl
  have hameas : Measurable a := by
    dsimp [a]
    simp_rw [Real.rpow_natCast]
    fun_prop
  have hbmeas : Measurable b := by
    dsimp [b]
    simp_rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    fun_prop
  have ha : MemLp a 2 volume :=
    (memLp_two_iff_integrable_sq hameas.aestronglyMeasurable).2 ha2
  have hb : MemLp b 2 volume :=
    (memLp_two_iff_integrable_sq hbmeas.aestronglyMeasurable).2 hb2
  have heq : (fun ζ : Rd d => ‖f ζ‖ * ‖g ζ‖) =ᵐ[volume]
      (fun ζ => a ζ * b ζ) := by
    filter_upwards [Measure.ae_ne volume (0 : Rd d)] with ζ hζ
    have hr : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    have hp : ‖ζ‖ ^ (d : ℝ) * ‖ζ‖ ^ (-(d : ℝ)) = 1 := by
      rw [← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero]
    have hs : Real.sqrt (‖ζ‖ ^ (d : ℝ)) *
        Real.sqrt (‖ζ‖ ^ (-(d : ℝ))) = 1 := by
      rw [← Real.sqrt_mul (Real.rpow_nonneg hr.le _), hp, Real.sqrt_one]
    dsimp [a, b]
    calc
      ‖f ζ‖ * ‖g ζ‖ = (Real.sqrt (‖ζ‖ ^ (d : ℝ)) *
          Real.sqrt (‖ζ‖ ^ (-(d : ℝ)))) * (‖f ζ‖ * ‖g ζ‖) := by rw [hs, one_mul]
      _ = _ := by ring
  have hholder : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  calc
    (∫ ζ : Rd d, ‖𝓕 (fun x : Rd d => (F x : ℂ)) ζ‖ *
      ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖) = ∫ ζ : Rd d, a ζ * b ζ := by
      rw [← integral_congr_ae heq]
      rfl
    _ ≤ (∫ ζ : Rd d, a ζ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ ζ : Rd d, b ζ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
      integral_mul_le_Lp_mul_Lq_of_nonneg hholder
        (ae_of_all _ fun ζ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
        (ae_of_all _ fun ζ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
        (by simpa using ha) (by simpa using hb)
    _ = _ := by
      simp only [Real.rpow_natCast]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      congr 1
      · congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun ζ => by
          change (Real.sqrt (‖ζ‖ ^ (d : ℝ)) *
            ‖𝓕 (compactComplexSchwartz hF hc) ζ‖) ^ 2 =
            ‖ζ‖ ^ d * ‖𝓕 (fun x : Rd d => (F x : ℂ)) ζ‖ ^ 2
          simp [mul_pow, SchwartzMap.fourier_coe, Real.rpow_natCast]
          left
          rfl
      · congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun ζ => by
          change (Real.sqrt (‖ζ‖ ^ (-(d : ℝ))) *
            ‖𝓕 (testComplexSchwartz φ.1) ζ‖) ^ 2 =
            ‖ζ‖ ^ (-(d : ℝ)) *
              ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2
          simp [mul_pow, SchwartzMap.fourier_coe]
          left
          rfl

/-- A single dimension-dependent constant controls all compact smooth shifts
through the ordinary energies of the shift and its iterated Laplacian. -/
theorem exists_isCMBounded_quantLap (hd : 1 ≤ d) (m : ℕ) (hdm : d ≤ 4 * m) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {F : Rd d → ℝ}
        (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
        (hc : HasCompactSupport F),
        IsCMBounded F (K * Real.sqrt
          ((∫ x : Rd d, ‖compactComplexSchwartz hF hc x‖ ^ 2) +
            (∫ x : Rd d, ‖iterLap m (compactComplexSchwartz hF hc) x‖ ^ 2))) := by
  obtain ⟨κd, hκd, hFL⟩ := logCovRd_eq_fourier hd
  let K : ℝ := (Real.sqrt κd)⁻¹
  have hκs : 0 < Real.sqrt κd := Real.sqrt_pos.2 hκd
  refine ⟨K, inv_pos.mpr hκs, ?_⟩
  intro F hF hc φ
  let f : 𝓢(Rd d, ℂ) := compactComplexSchwartz hF hc
  let A : ℝ := ∫ ζ : Rd d, ‖ζ‖ ^ (d : ℝ) *
    ‖𝓕 (fun x : Rd d => (F x : ℂ)) ζ‖ ^ 2
  let W : ℝ := (∫ x : Rd d, ‖f x‖ ^ 2) +
    (∫ x : Rd d, ‖iterLap m f x‖ ^ 2)
  let B : ℝ := ∫ ζ : Rd d, ‖ζ‖ ^ (-(d : ℝ)) *
    ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2
  have hAW : A ≤ W := by
    have h := fourier_energy_le_iterLap f m hdm
    have hf : (f : Rd d → ℂ) = fun x => (F x : ℂ) := by
      funext x
      rfl
    simpa only [A, W, f, Real.rpow_natCast, SchwartzMap.fourier_coe,
      hf, compactComplexSchwartz_apply] using h
  have hA : 0 ≤ A := integral_nonneg fun ζ =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)
  have hB : 0 ≤ B := integral_nonneg fun ζ =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)
  have hC : Real.sqrt A / Real.sqrt κd ≤ K * Real.sqrt W := by
    have hs := Real.sqrt_le_sqrt hAW
    dsimp [K]
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.sqrt W * (Real.sqrt κd)⁻¹ :=
        mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hκs.le)
      _ = _ := mul_comm _ _
  calc
    |∫ x, F x * φ.1 x| ≤ ∫ ζ : Rd d,
        ‖𝓕 (fun x : Rd d => (F x : ℂ)) ζ‖ *
          ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ :=
      abs_integral_mul_le_fourier_norm hF hc φ.1
    _ ≤ Real.sqrt A * Real.sqrt B := fourier_norm_cauchy_schwarz hd hF hc φ
    _ = (Real.sqrt A / Real.sqrt κd) * logNorm φ.1 := by
      rw [logNorm, hFL φ, Real.sqrt_mul hκd.le]
      dsimp [A, B]
      field_simp
    _ ≤ (K * Real.sqrt W) * logNorm φ.1 :=
      mul_le_mul_of_nonneg_right hC (logNorm_nonneg _)

/-- Monotonicity of a Cameron–Martin bound in its constant. -/
theorem IsCMBounded.mono {F : Rd d → ℝ} {C C' : ℝ}
    (hF : IsCMBounded F C) (hCC' : C ≤ C') : IsCMBounded F C' := by
  intro φ
  exact (hF φ).trans (mul_le_mul_of_nonneg_right hCC' (logNorm_nonneg _))

/-- A quantitative bound for compact smooth functions on one finite-volume
support. The two pointwise bounds are on the function and its `m`-fold
Laplacian; they are suited to smooth parameter families. -/
theorem exists_isCMBounded_quantSup (hd : 1 ≤ d) (m : ℕ) (hdm : d ≤ 4 * m)
    (S : Set (Rd d)) (hS : MeasurableSet S) (hfin : volume S ≠ ∞) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {F : Rd d → ℝ}
        (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
        (hc : HasCompactSupport F)
        (_hs : tsupport F ⊆ S)
        {M : ℝ} (_hM : 0 ≤ M)
        (_h0 : ∀ x, |F x| ≤ M)
        (_hm : ∀ x, ‖iterLap m (compactComplexSchwartz hF hc) x‖ ≤ M),
        IsCMBounded F (C * M) := by
  obtain ⟨K, hK, hquant⟩ := exists_isCMBounded_quantLap hd m hdm
  let V : ℝ := (volume S).toReal
  let C : ℝ := K * (1 + Real.sqrt (2 * V))
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hC : 0 < C := mul_pos hK (by positivity)
  refine ⟨C, hC, ?_⟩
  intro F hF hc hs M hM h0 hm
  let f : 𝓢(Rd d, ℂ) := compactComplexSchwartz hF hc
  have hts : tsupport (f : Rd d → ℂ) ⊆ S := by
    change tsupport (fun x : Rd d => (F x : ℂ)) ⊆ S
    exact (tsupport_comp_subset Complex.ofReal_zero F).trans hs
  have htsLap : tsupport (iterLap m f : Rd d → ℂ) ⊆ S :=
    (tsupport_iterLap_subset m f).trans hts
  have h0' : ∀ x, ‖f x‖ ≤ M := by
    intro x
    simpa only [f, compactComplexSchwartz_apply, Complex.norm_real, Real.norm_eq_abs]
      using h0 x
  have h0int := integral_norm_sq_le_of_support f S hS hfin hts h0'
  have hlint := integral_norm_sq_le_of_support (iterLap m f) S hS hfin htsLap hm
  let W : ℝ := (∫ x : Rd d, ‖f x‖ ^ 2) +
    (∫ x : Rd d, ‖iterLap m f x‖ ^ 2)
  have hW : W ≤ 2 * V * M ^ 2 := by
    dsimp [W, V]
    linarith only [h0int, hlint]
  have hbound : K * Real.sqrt W ≤ C * M := by
    have hsqrt := Real.sqrt_le_sqrt hW
    have hroot : Real.sqrt (2 * V * M ^ 2) = Real.sqrt (2 * V) * M := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg hM]
    calc
      K * Real.sqrt W ≤ K * Real.sqrt (2 * V * M ^ 2) :=
        mul_le_mul_of_nonneg_left hsqrt hK.le
      _ = K * (Real.sqrt (2 * V) * M) := by rw [hroot]
      _ ≤ C * M := by
        dsimp [C]
        nlinarith [mul_nonneg hK.le hM]
  exact (hquant hF hc).mono hbound

/-- The order `⌊d/2⌋+1` used in the appendix satisfies the quantitative
Laplacian estimate. -/
theorem exists_isCMBounded_quantSup_dim (hd : 1 ≤ d)
    (S : Set (Rd d)) (hS : MeasurableSet S) (hfin : volume S ≠ ∞) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {F : Rd d → ℝ}
        (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
        (hc : HasCompactSupport F)
        (_hs : tsupport F ⊆ S)
        {M : ℝ} (_hM : 0 ≤ M)
        (_h0 : ∀ x, |F x| ≤ M)
        (_hm : ∀ x,
          ‖iterLap (d / 2 + 1) (compactComplexSchwartz hF hc) x‖ ≤ M),
        IsCMBounded F (C * M) := by
  exact exists_isCMBounded_quantSup hd (d / 2 + 1)
    (by omega) S hS hfin

end HigherDimLQGMetric
