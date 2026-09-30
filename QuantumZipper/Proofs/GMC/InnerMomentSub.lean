import QuantumZipper.Proofs.GMC.InnerMomentReduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GMC-INNERMOM (2): the sub-window fractional moment bound `SubFracStmt γ p`, `p ∈ (0,1]`

For a sub-window `J' = [a − ℓ/2, a + ℓ/2] ⊆ S = [t − δ/2, t + δ/2]` with `2·2^{-k} < ℓ`, the inner
field of `(t, δ)` on `J'` is `G + Y'`, where `G = X(fc(a,ℓ)) − X(fc(t,δ))` is Gaussian of
variance `2 log(δ/ℓ)` and independent of the inner field `Y'` of `(a, ℓ)` (kernel identities
K3), so `W(J') = e^{(γ/2)G} (ℓ/δ)^{γ²/4} W'` (`ae_innerMeasure_bI_sub_eq`), and Jensen
(`E W'^p ≤ (E W')^p = ℓ^p`) gives `E W(J')^p ≤ (ℓ/δ)^{ζ(p)} δ^p`. A general interval of
length `ℓ ≤ δ` meets `S` inside such a `J'`.

This is the argument of `FracMom.lintegral_bdryApprox_rpow_le` (M4-P3(b)) with the base circle
`fc(0,R)` replaced by `fc(t,δ)`; own adaptation of the repository argument (the exact scaling
relation of boundary GMC; Rhodes–Vargas arXiv:1305.6221, §3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace GMCMoments

open FracMom BdryExist GaussTK KernelId TwoRadius

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- `G = X(fc(a,ℓ)) − X(fc(t,δ))`. -/
def subAvg (X : Ω → FieldSample) (t δ a ℓ : ℝ) (ω : Ω) : ℝ :=
  fcPairVal X ((a : ℂ), ℓ, (t : ℂ), δ) ω

theorem fcPairCov_inner_sub {t δ a ℓ u r : ℝ} (hℓ : 0 < ℓ) (hr : 0 < r) (hur : |u| + r ≤ 1)
    (hsub : |a - t| + ℓ ≤ δ) :
    fcPairCov (innerIdx a ℓ u r) ((a : ℂ), ℓ, (t : ℂ), δ) = 0 := by
  have hℓr : 0 < ℓ * r := mul_pos hℓ hr
  have hin : |a + ℓ * u - a| + ℓ * r ≤ ℓ := by
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hℓ]
    nlinarith
  have hin2 : |a + ℓ * u - t| + ℓ * r ≤ δ := by
    have h := abs_add_le (a - t) (ℓ * u)
    rw [abs_mul, abs_of_pos hℓ] at h
    rw [show a + ℓ * u - t = a - t + ℓ * u by ring]
    nlinarith
  simp only [fcPairCov, kernelCov2, innerIdx]
  rw [kernelCov_fc_real_nested' hℓr hin, kernelCov_fc_real_nested' hℓr hin2,
    kernelCov_fc_real_sameCenter hℓ hℓ, max_self, kernelCov_fc_real_nested' hℓ hsub]
  ring

theorem indepFun_subAvg_innerSample (hX : IsFreeGFFModConstH X P) {t δ a ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsub : |a - t| + ℓ ≤ δ) : IndepFun (subAvg X t δ a ℓ) (innerSample X a ℓ) P := by
  have hδ : 0 < δ := by linarith [abs_nonneg (a - t)]
  have hI := indepFun_fcPair hX (fun q : InnerQ => ⟨_, good_real (mul_pos hℓ q.2.1) hℓ⟩)
    (fun _ : Unit => (⟨((a : ℂ), ℓ, (t : ℂ), δ), good_real hℓ hδ⟩ : {p : FcIdx // p.Good}))
    (fun q _ => fcPairCov_inner_sub hℓ q.2.1 q.2.2 hsub)
  exact hI.symm.comp (measurable_pi_apply ()) (measurable_innerRebuild a ℓ)

theorem hasLaw_subAvg (hX : IsFreeGFFModConstH X P) {t δ a ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsub : |a - t| + ℓ ≤ δ) :
    HasLaw (subAvg X t δ a ℓ) (gaussianReal 0 (2 * log δ - 2 * log ℓ).toNNReal) P := by
  have hδ : 0 < δ := by linarith [abs_nonneg (a - t)]
  have := hasLaw_fcPairVal hX (good_real (s := a) (t := t) hℓ hδ)
  rwa [fcPairCov_innerU_self hℓ hsub] at this

theorem bI_subset_of_sub {t δ a ℓ : ℝ} (hsub : |a - t| + ℓ / 2 ≤ δ / 2) :
    bI a ℓ ⊆ bI t δ := by
  have h := abs_le.1 (show |a - t| ≤ δ / 2 - ℓ / 2 by linarith)
  exact Icc_subset_Icc (by linarith [h.1]) (by linarith [h.2])

/-- **Decomposition on a sub-window.** -/
theorem ae_innerMeasure_bI_sub_eq (hX : IsFreeGFFModConstH X P) (γ : ℝ) {t δ a ℓ : ℝ}
    (hℓ : 0 < ℓ) (hsub : |a - t| + ℓ / 2 ≤ δ / 2) {k : ℕ} (hk : 2 * radius k < ℓ) :
    ∀ᵐ ω ∂P, innerMeasure γ X t δ k ω (bI a ℓ) =
      ENNReal.ofReal (exp (γ / 2 * subAvg X t δ a ℓ ω) * (ℓ / δ) ^ (γ ^ 2 / 4)) *
        innerMass γ X a ℓ k ω := by
  have hℓδ : ℓ ≤ δ := by linarith [abs_nonneg (a - t)]
  have hδ : 0 < δ := by linarith
  have hkδ : 2 * radius k < δ := by linarith
  have hS := bI_subset_of_sub hsub
  filter_upwards [(ae_avgReg_spec hX k).1] with ω h1
  rw [innerMeasure, withDensity_apply _ (measurableSet_bI a ℓ),
    Measure.restrict_restrict (measurableSet_bI a ℓ), inter_eq_left.2 hS, innerMass, massFun,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_bI a ℓ) fun s hs => ?_
  have hs1 := mem_bI_bound (hS hs) hkδ
  have hs2 := mem_bI_bound hs hk
  have hr := radius_pos k
  rw [← ENNReal.ofReal_mul (mul_nonneg (exp_pos _).le (rpow_nonneg (div_pos hℓ hδ).le _))]
  congr 1
  simp only [wDens]
  rw [avgReg_innerSample_eq hδ hs1 (h1 _ (ofReal_mem_Hbar s)),
    avgReg_innerSample_eq hℓ hs2 (h1 _ (ofReal_mem_Hbar s)),
    show radius k / δ = (ℓ / δ) * (radius k / ℓ) by field_simp,
    mul_rpow (div_pos hℓ hδ).le (div_pos hr hℓ).le]
  simp only [subAvg, fcPairVal]
  set A := avgReg (X ω) k (s : ℂ)
  set Xa := X ω (foldedCircle (a : ℂ) ℓ)
  set Xt := X ω (foldedCircle (t : ℂ) δ)
  rw [show γ / 2 * (A - Xt) = γ / 2 * (Xa - Xt) + γ / 2 * (A - Xa) by ring, exp_add]
  ring

/-- Gaussian factor: `E[(e^{(γ/2)G} c^{γ²/4})^p] = c^{pγ²/4} e^{v (pγ/2)²/2}`. -/
theorem lintegral_gauss_factor_rpow {G : Ω → ℝ} {v : ℝ≥0} (hL : HasLaw G (gaussianReal 0 v) P)
    (γ : ℝ) {c p : ℝ} (hc : 0 < c) (hp0 : 0 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (exp (γ / 2 * G ω) * c ^ (γ ^ 2 / 4)) ^ p ∂P =
      ENNReal.ofReal (c ^ (p * (γ ^ 2 / 4)) * exp (v * (p * γ / 2) ^ 2 / 2)) := by
  have hpt : ∀ ω, ENNReal.ofReal (exp (γ / 2 * G ω) * c ^ (γ ^ 2 / 4)) ^ p =
      ENNReal.ofReal (c ^ (p * (γ ^ 2 / 4)) * exp (p * γ / 2 * G ω)) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0, mul_rpow (exp_pos _).le
      (rpow_pos_of_pos hc _).le, ← exp_mul, ← rpow_mul hc.le, mul_comm]
    congr 3 <;> ring
  simp_rw [hpt]
  have hi : Integrable (fun ω => exp (0 + p * γ / 2 * G ω)) P :=
    hL.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (p * γ / 2) 0)
  simp only [zero_add] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _)
    (ae_of_all _ fun ω => by simp only [Pi.zero_apply]; positivity), integral_const_mul]
  have h2 := integral_exp_mul_add_gaussianReal v (p * γ / 2) 0
  simp only [zero_add] at h2
  rw [← h2]
  congr 2
  exact hL.integral_comp (f := fun x => exp (p * γ / 2 * x)) (by fun_prop)

/-- **Sub-window fractional moment**, `J' ⊆ S`. -/
theorem lintegral_innerMeasure_bI_sub_rpow_le [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (γ : ℝ) {t δ a ℓ p : ℝ} (hℓ : 0 < ℓ)
    (hsub : |a - t| + ℓ / 2 ≤ δ / 2) (hp0 : 0 < p) (hp1 : p ≤ 1) {k : ℕ}
    (hk : 2 * radius k < ℓ) :
    ∫⁻ ω, innerMeasure γ X t δ k ω (bI a ℓ) ^ p ∂P ≤
      ENNReal.ofReal ((ℓ / δ) ^ zeta γ p) * ENNReal.ofReal δ ^ p := by
  have hℓδ : ℓ ≤ δ := by linarith [abs_nonneg (a - t)]
  have hδ : 0 < δ := by linarith
  have hsub' : |a - t| + ℓ ≤ δ := by linarith
  set A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (exp (γ / 2 * subAvg X t δ a ℓ ω) * (ℓ / δ) ^ (γ ^ 2 / 4)) ^ p with hA
  set W : Ω → ℝ≥0∞ := fun ω => innerMass γ X a ℓ k ω ^ p with hW
  have hφ : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (γ / 2 * x) * (ℓ / δ) ^ (γ ^ 2 / 4)) ^ p) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).pow_const p
  have hψ : Measurable (fun x : FieldSample => massFun γ a ℓ k x ^ p) :=
    (measurable_massFun γ a ℓ k).pow_const p
  have hind : IndepFun A W P := (indepFun_subAvg_innerSample hX hℓ hsub').comp hφ hψ
  have hAm : Measurable A := hφ.comp (measurable_fcPairVal hX _)
  have hWm : Measurable W := hψ.comp (measurable_innerSample hX a ℓ)
  have hJ := lintegral_rpow_le_rpow_lintegral (measurable_innerMass hX γ a ℓ k).aemeasurable
    (μ := P) hp0 hp1
  have hv : ((2 * log δ - 2 * log ℓ).toNNReal : ℝ) = 2 * log δ - 2 * log ℓ :=
    Real.coe_toNNReal _ (by linarith [log_le_log hℓ hℓδ])
  calc ∫⁻ ω, innerMeasure γ X t δ k ω (bI a ℓ) ^ p ∂P
      = ∫⁻ ω, (A * W) ω ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_innerMeasure_bI_sub_eq hX γ (P := P) hℓ hsub hk] with ω hω
        rw [hω, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rfl
    _ = (∫⁻ ω, A ω ∂P) * ∫⁻ ω, W ω ∂P :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hAm hWm hind
    _ ≤ (∫⁻ ω, A ω ∂P) * (∫⁻ ω, innerMass γ X a ℓ k ω ∂P) ^ p := by gcongr
    _ = _ := by
        rw [hA, lintegral_gauss_factor_rpow (hasLaw_subAvg hX hℓ hsub') γ (div_pos hℓ hδ) hp0.le,
          lintegral_innerMass hX γ hℓ hk, ENNReal.ofReal_rpow_of_nonneg hℓ.le hp0.le,
          ENNReal.ofReal_rpow_of_nonneg hδ.le hp0.le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hv, rpow_def_of_pos (div_pos hℓ hδ), rpow_def_of_pos hℓ,
          rpow_def_of_pos (div_pos hℓ hδ), rpow_def_of_pos hδ, log_div hℓ.ne' hδ.ne',
          ← exp_add, ← exp_add, ← exp_add]
        congr 1
        unfold zeta
        ring

/-- **`SubFracBound` with constant `1`**, for `p ∈ (0,1]`. -/
theorem subFracBound_holds [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : SubFracBound γ p X P 1 := by
  intro t δ k a ℓ hδ hk hkℓ hℓδ
  have hℓ : 0 < ℓ := by linarith [radius_pos k]
  set a' := max (t - (δ - ℓ) / 2) (min a (t + (δ - ℓ) / 2)) with ha'
  have hsub : |a' - t| + ℓ / 2 ≤ δ / 2 := by
    have h1 : a' ≤ t + (δ - ℓ) / 2 := max_le (by linarith) (min_le_right _ _)
    have h2 : t - (δ - ℓ) / 2 ≤ a' := le_max_left _ _
    have := abs_sub_le_iff.2 ⟨(by linarith : a' - t ≤ (δ - ℓ) / 2),
      (by linarith : t - a' ≤ (δ - ℓ) / 2)⟩
    linarith
  have hmono : ∀ ω, innerMeasure γ X t δ k ω (Icc (a - ℓ / 2) (a + ℓ / 2)) ≤
      innerMeasure γ X t δ k ω (bI a' ℓ) := by
    intro ω
    rw [innerMeasure, withDensity_apply _ measurableSet_Icc,
      withDensity_apply _ (measurableSet_bI a' ℓ), Measure.restrict_restrict measurableSet_Icc,
      Measure.restrict_restrict (measurableSet_bI a' ℓ)]
    refine lintegral_mono_set ?_
    rintro u ⟨hu1, hu2⟩
    refine ⟨?_, hu2⟩
    simp only [bI, mem_Icc] at hu1 hu2 ⊢
    constructor
    · have := max_le_iff.2 ⟨(show t - (δ - ℓ) / 2 ≤ u + ℓ / 2 by linarith),
        (show min a (t + (δ - ℓ) / 2) ≤ u + ℓ / 2 by
          linarith [min_le_left a (t + (δ - ℓ) / 2)])⟩
      linarith
    · have := le_min (show u - ℓ / 2 ≤ a by linarith)
        (show u - ℓ / 2 ≤ t + (δ - ℓ) / 2 by linarith)
      linarith [le_max_right (t - (δ - ℓ) / 2) (min a (t + (δ - ℓ) / 2))]
  calc ∫⁻ ω, innerMeasure γ X t δ k ω (Icc (a - ℓ / 2) (a + ℓ / 2)) ^ p ∂P
      ≤ ∫⁻ ω, innerMeasure γ X t δ k ω (bI a' ℓ) ^ p ∂P :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (hmono ω) hp0.le
    _ ≤ ENNReal.ofReal ((ℓ / δ) ^ zeta γ p) * ENNReal.ofReal δ ^ p :=
        lintegral_innerMeasure_bI_sub_rpow_le hX γ hℓ hsub hp0 hp1 hkℓ
    _ = _ := by rw [one_mul]

theorem subFracStmt_holds (γ : ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : SubFracStmt γ p := by
  refine ⟨1, ENNReal.one_ne_top, ?_⟩
  intro Ω _ P _ X hX
  exact subFracBound_holds hX γ hp0 hp1

/-- **`InnerMomentStmt` from the Palm inequality alone** (`0 < γ`, `1 < q ≤ 2`, `q < 4/γ²`). -/
theorem innerMomentStmt_of_palm {γ q : ℝ} (hγ : 0 < γ) (hq : 1 < q) (hq2 : q ≤ 2)
    (hqγ : q < 4 / γ ^ 2) (h1 : PalmRootedStmt γ q) : InnerMomentStmt γ q :=
  innerMomentStmt_of_palm_subFrac hγ hq hq2 hqγ h1
    (subFracStmt_holds γ (by linarith) (by linarith))

end GMCMoments
end QuantumZipper
