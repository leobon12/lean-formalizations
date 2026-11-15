import InteractingSLE.GFF.LocalSets.SubdomainMGF

/-!
# Proposition 3.8, first step: exponential moments of `𝒞_A − 𝒞_{A₂}`

Specification §3.2, proof of Proposition 3.8 (pp. 59–60; transcription
`source/spec/p049-096.md#prop-3.8-proof`), packet PROVE-LS-C.

The specification bounds `E[1_E sup_Q |𝒞_B|^p]` in the conditional domain `O = D ∖ A₂` through
`𝒞_B = E[q | ℬ]` and conditional Jensen. Here the same bound is obtained on `ℍ` from the two
conditional Gaussian laws (own argument, ruling R34): given `𝒥 ⊇ 𝒜₂` the field is
`𝒞_A + GFF_{ℍ∖A}` and given `𝒜₂` it is `𝒞_{A₂} + GFF_{ℍ∖A₂}`, so with `D = 𝒞_A − 𝒞_{A₂}`,

`E[W e^{λ D(ψ)} e^{λ (h − 𝒞_A)(ψ)}] = E[W e^{λ D(ψ)} e^{λ² σ²_{ℍ∖A}(ψ)/2}]` (`W` `𝒥`-measurable),
`E[W' e^{λ (h − 𝒞_{A₂})(ψ)}] = E[W' e^{λ² σ²_{ℍ∖A₂}(ψ)/2}]` (`W'` `𝒜₂`-measurable)

(`lintegral_mul_exp_of_condCharFun`). If `σ²_{ℍ∖A₂}(ψ) − σ²_{ℍ∖A}(ψ) ≤ κ` on `E ∩ F`
(`E ∈ 𝒥`, `F ∈ σ(A₂)`), choosing `W = 1_{E∩F} e^{−λ²(σ²_{ℍ∖A₂}(ψ) − κ)/2} e^{λD(ψ)}` gives

`E[1_{E∩F} e^{λ D(ψ)}] ≤ e^{λ² κ / 2}` (`lintegral_indicator_exp_meanDiff_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper LQGMetric

variable {Ω : Type*} {𝒢 𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The conditional characteristic functions of `(X − M)(ψ)` at all frequencies, from
`IsCondZeroBoundaryGFF` and the scaling of the Green variance. -/
theorem condCharFun_of_isCondZeroBoundaryGFF {X M : Ω → DistOn upperHalfPlaneOpens}
    {U : Ω → Set ℂ} (hc : IsCondZeroBoundaryGFF P 𝒢 U fun ω => X ω - M ω)
    (hU : ∀ᵐ ω ∂P, IsOpen (U ω) ∧ U ω ⊆ H) (ψ : TestOn upperHalfPlaneOpens) {V : Ω → ℝ}
    (hV : ∀ᵐ ω ∂P, V ω = zeroGFFTestCov (U ω) ψ ψ) (t : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((t * (X ω ψ - M ω ψ) : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ) := by
  have e : (fun ω => Complex.exp (Complex.I * ((t * (X ω ψ - M ω ψ) : ℝ) : ℂ))) =
      fun ω => Complex.exp (Complex.I * (((X ω - M ω) (t • ψ) : ℝ) : ℂ)) := by
    funext ω
    rw [map_smul, smul_eq_mul, sub_apply]
  rw [e]
  refine (hc (t • ψ)).trans ?_
  filter_upwards [hU, hV] with ω ⟨ho, hs⟩ hv
  rw [zeroGFFTestCov_smul_self ho hs, hv]

omit [IsProbabilityMeasure P] in
/-- The Green variance through the relative closure is `σ(A)`-measurable and almost surely the
variance on `ℍ ∖ A`. -/
lemma ae_zeroGFFTestCov_relClosureH {A : Ω → Set ℂ} (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, zeroGFFTestCov (H \ relClosureH (A ω)) ψ ψ = zeroGFFTestCov (H \ A ω) ψ ψ := by
  filter_upwards [hAc] with ω ⟨hs, ho⟩
  rw [relClosureH_eq hs ho]

omit [IsProbabilityMeasure P] in
lemma ae_isOpen_subset_H {A : Ω → Set ℂ} (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) :
    ∀ᵐ ω ∂P, IsOpen (H \ A ω) ∧ H \ A ω ⊆ H := by
  filter_upwards [hAc] with ω ⟨_, ho⟩ using ⟨ho, sdiff_subset⟩

/-- **Exponential moments of the difference of the two local-set means** (proof of
Proposition 3.8). Let the field be `g₀ + GFF_{ℍ∖A}` given `𝒥` and `g₂ + GFF_{ℍ∖A₂}` given
`𝒜₂ ⊆ 𝒥`. If `σ²_{ℍ∖A₂}(ψ) − σ²_{ℍ∖A}(ψ) ≤ κ` almost surely on `E ∩ F`, with `E ∈ 𝒥` and
`F ∈ σ(A₂)`, then `E[1_{E∩F} e^{λ (g₀ − g₂)(ψ)}] ≤ e^{λ² κ/2}`. -/
theorem lintegral_indicator_exp_meanDiff_le {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A A₂ : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hA₂c : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (h𝒥 : 𝒥 ≤ mΩ) (h₂𝒥 : germSigma A₂ h ≤ 𝒥) {g₀ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg₀m : Measurable[𝒥] g₀)
    (hg₀c : IsCondZeroBoundaryGFF P 𝒥 (fun ω => H \ A ω) fun ω => h ω - g₀ ω)
    (hg₂ : IsLocalSetMean A₂ h P g₂) (ψ : TestOn upperHalfPlaneOpens) {E F : Set Ω}
    (hE : MeasurableSet[𝒥] E) (hF : MeasurableSet[MeasurableSpace.comap A₂ hittingSigma] F)
    {κ : ℝ}
    (hκ : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ F →
      zeroGFFTestCov (H \ A₂ ω) ψ ψ - zeroGFFTestCov (H \ A ω) ψ ψ ≤ κ) (lam : ℝ) :
    ∫⁻ ω, (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (lam * (g₀ ω ψ - g₂ ω ψ)))) ω ∂P ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * κ / 2)) := by
  have hhm := hh.measurable
  have h₂le : germSigma A₂ h ≤ mΩ := germSigma_le hA₂ hhm
  have hF₂ : MeasurableSet[germSigma A₂ h] F := comap_le_germSigma A₂ h _ hF
  -- the variances, measurable versions
  set V₀ : Ω → ℝ := fun ω => zeroGFFTestCov (H \ relClosureH (A ω)) ψ ψ with hV₀
  set V₂ : Ω → ℝ := fun ω => zeroGFFTestCov (H \ relClosureH (A₂ ω)) ψ ψ with hV₂
  have hV₀m : Measurable V₀ :=
    (measurable_comap_zeroGFFTestCov_compl A ψ ψ).mono hA.comap_le le_rfl
  have hV₂c : Measurable[MeasurableSpace.comap A₂ hittingSigma] V₂ :=
    measurable_comap_zeroGFFTestCov_compl A₂ ψ ψ
  have hV₂m : Measurable V₂ := hV₂c.mono hA₂.comap_le le_rfl
  have hV₀e := ae_zeroGFFTestCov_relClosureH hAc ψ
  have hV₂e := ae_zeroGFFTestCov_relClosureH hA₂c ψ
  have hV₀0 : ∀ᵐ ω ∂P, 0 ≤ V₀ ω := Eventually.of_forall fun ω =>
    zeroGFFTestCov_self_nonneg (isOpen_H_diff_relClosureH _) sdiff_subset ψ
  have hV₂0 : ∀ᵐ ω ∂P, 0 ≤ V₂ ω := Eventually.of_forall fun ω =>
    zeroGFFTestCov_self_nonneg (isOpen_H_diff_relClosureH _) sdiff_subset ψ
  -- the residuals and the difference of the means
  set Y₀ : Ω → ℝ := fun ω => h ω ψ - g₀ ω ψ with hY₀
  set Y₂ : Ω → ℝ := fun ω => h ω ψ - g₂ ω ψ with hY₂
  set D : Ω → ℝ := fun ω => g₀ ω ψ - g₂ ω ψ with hD
  have hhψ : Measurable fun ω => h ω ψ := (measurable_distOn_apply ψ).comp hhm
  have hg₀ψ : Measurable[𝒥] fun ω => g₀ ω ψ := (measurable_distOn_apply ψ).comp hg₀m
  have hg₂ψ : Measurable[germSigma A₂ h] fun ω => g₂ ω ψ := (measurable_distOn_apply ψ).comp hg₂.1
  have hDm : Measurable[𝒥] D := hg₀ψ.sub (hg₂ψ.mono h₂𝒥 le_rfl)
  have hY₀m : Measurable Y₀ := hhψ.sub (hg₀ψ.mono h𝒥 le_rfl)
  have hY₂m : Measurable Y₂ := hhψ.sub (hg₂ψ.mono h₂le le_rfl)
  have hc₀ := condCharFun_of_isCondZeroBoundaryGFF hg₀c (ae_isOpen_subset_H hAc) ψ
    (V := V₀) hV₀e
  have hc₂ := condCharFun_of_isCondZeroBoundaryGFF hg₂.2.2 (ae_isOpen_subset_H hA₂c) ψ
    (V := V₂) hV₂e
  -- the factors
  set a : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-(lam ^ 2 * (V₂ ω - κ)) / 2)) with ha
  set e₁ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (lam * D ω)) with he₁
  have ham : Measurable[MeasurableSpace.comap A₂ hittingSigma] a := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact ((measurable_const.mul (hV₂c.sub measurable_const)).neg).div_const _
  have he₁m : Measurable[𝒥] e₁ :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hDm))
  set W : Ω → ℝ≥0∞ := (E ∩ F).indicator fun ω => a ω * e₁ ω with hW
  have hWm : Measurable[𝒥] W :=
    ((ham.mono ((comap_le_germSigma A₂ h).trans h₂𝒥) le_rfl).mul he₁m).indicator
      (hE.inter (h₂𝒥 _ hF₂))
  set W' : Ω → ℝ≥0∞ := F.indicator a with hW'
  have hW'm : Measurable[germSigma A₂ h] W' :=
    (ham.mono (comap_le_germSigma A₂ h) le_rfl).indicator hF₂
  -- step 1: insert the factor `a · e^{λ² V₀/2} ≥ 1` on `E ∩ F`
  have step1 : ∫⁻ ω, (E ∩ F).indicator e₁ ω ∂P ≤
      ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₀ ω / 2)) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hκ, hV₀e, hV₂e] with ω hω h0 h2
    by_cases hωEF : ω ∈ E ∩ F
    · rw [hW, indicator_of_mem hωEF, indicator_of_mem hωEF]
      have hk := hω hωEF.1 hωEF.2
      rw [← h0, ← h2] at hk
      have hge : 1 ≤ a ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₀ ω / 2)) := by
        rw [ha, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
        have : 0 ≤ lam ^ 2 * (V₀ ω - (V₂ ω - κ)) := mul_nonneg (sq_nonneg _) (by linarith)
        linarith
      calc e₁ ω = e₁ ω * 1 := (mul_one _).symm
        _ ≤ e₁ ω * (a ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₀ ω / 2))) := by gcongr
        _ = a ω * e₁ ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₀ ω / 2)) := by ring
    · rw [indicator_of_notMem hωEF]; exact zero_le
  -- step 2: the `𝒥`-law
  have step2 := lintegral_mul_exp_of_condCharFun h𝒥 hY₀m hV₀m hV₀0 hc₀ hWm lam
  -- step 3: `e^{λ D} e^{λ Y₀} = e^{λ Y₂}`
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
  -- step 4: the `𝒜₂`-law
  have step4 := lintegral_mul_exp_of_condCharFun h₂le hY₂m hV₂m hV₂0 hc₂ hW'm lam
  -- step 5: evaluate
  have step5 : ∀ ω, W' ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₂ ω / 2)) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * κ / 2)) := by
    intro ω
    by_cases hωF : ω ∈ F
    · rw [hW', indicator_of_mem hωF, ha, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      refine le_of_eq (congrArg (fun x => ENNReal.ofReal (Real.exp x)) ?_)
      ring
    · rw [hW', indicator_of_notMem hωF, zero_mul]; exact zero_le
  calc ∫⁻ ω, (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (lam * (g₀ ω ψ - g₂ ω ψ)))) ω ∂P
      = ∫⁻ ω, (E ∩ F).indicator e₁ ω ∂P := rfl
    _ ≤ ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₀ ω / 2)) ∂P := step1
    _ = ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam * Y₀ ω)) ∂P := step2.symm
    _ ≤ ∫⁻ ω, W' ω * ENNReal.ofReal (Real.exp (lam * Y₂ ω)) ∂P := lintegral_mono step3
    _ = ∫⁻ ω, W' ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V₂ ω / 2)) ∂P := step4
    _ ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (lam ^ 2 * κ / 2)) ∂P := lintegral_mono step5
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 * κ / 2)) := by
        rw [lintegral_const, measure_univ, mul_one]

end LocalSets
end InteractingSLE
