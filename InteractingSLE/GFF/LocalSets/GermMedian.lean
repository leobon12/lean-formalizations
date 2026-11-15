import InteractingSLE.GFF.LocalSets.GermLaw

/-!
# The conditional means given the germ σ-algebra form a random distribution

Specification §3.2, p. 54 ("We justify that the conditional expectations in this formula define
one random distribution"). The source uses `H^{-s}`-valued conditional expectations of `ζ h`. Here
the version step is LQGMetric's `exists_version` (inverting the measurable embedding `pairJ` of
`𝒟'(ℍ)`), whose input is that almost surely the countably many conditional means
`(M(comb c))_c` lie in `rangeSet` (additive, consistent, of finite order on each compact `K_n`).
The finite-order bound is obtained by a median argument instead of Sobolev norms (own argument):

* conditionally on `𝒜`, `h(ψ) − M(ψ)` has a symmetric law (`charFun_germResidual`: its restricted
  characteristic functions are real), so `P(G) ≤ 2 P(G ∩ {|M(ψ)| ≤ |h(ψ)|})` for `G ∈ 𝒜`
  (`measure_le_two_mul_abs_le`);
* every realization `h(ω)` is a distribution, so the events `E_k` = "order-`k` bound on `K_n`"
  increase to `Ω`; almost surely some `E_k` has conditional probability `> 1/2`
  (`ae_exists_condExp_gt_half`), and then the median bound transfers the order-`k` bound from
  `h(ψ)` to `M(ψ)` (`measure_eq_zero_of_condExp_gt_half`) for all countably many `ψ = comb c`.

## Main results

* `tendsto_zeroGFFTestCov_of_tendsto` : `ψ_k → 0` in `𝓓(ℍ)` gives `σ²_ℍ(ψ_k) → 0`;
* `IsGermMeanFamily`, `charFun_germResidual`, `measure_le_two_mul_abs_le`;
* `ae_mem_rangeSet_germMean` : the admissibility of the conditional means.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB

section Field

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
theorem integral_sq_field (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (χ : TestOn upperHalfPlaneOpens) : ∫ ω, (h ω χ) ^ 2 ∂P = zeroGFFTestCov H χ χ := by
  have hm : AEMeasurable (fun ω => h ω χ) P :=
    ((measurable_distOn_apply χ).comp hh.measurable).aemeasurable
  rw [← variance_of_integral_eq_zero hm (hh.process.centered χ), ← covariance_self hm,
    hh.process.covariance_eq χ χ]
  rfl

theorem integral_exp_field (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (χ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (h ω χ : ℂ)) ∂P =
      ((Real.exp (-(1 / 2) * zeroGFFTestCov H χ χ) : ℝ) : ℂ) := by
  have hm : AEMeasurable (fun ω => h ω χ) P :=
    ((measurable_distOn_apply χ).comp hh.measurable).aemeasurable
  rw [GFF.integral_exp_I_mul_of_hasGaussianLaw (hh.process.gaussian.hasGaussianLaw_eval χ)
    (hh.process.centered χ), variance_of_integral_eq_zero hm (hh.process.centered χ),
    integral_sq_field hh χ]

/-- **Continuity of the variance** on test functions, from the continuity of each realization and
Gaussianity: if `ψ_k → 0` in `𝓓(ℍ)` then `σ²_ℍ(ψ_k) → 0`. -/
theorem tendsto_zeroGFFTestCov_of_tendsto (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {ψ : ℕ → TestOn upperHalfPlaneOpens} (hψ : Tendsto ψ atTop (𝓝 0)) :
    Tendsto (fun k => zeroGFFTestCov H (ψ k) (ψ k)) atTop (𝓝 0) := by
  have hhm := hh.measurable
  have h1 : Tendsto (fun k => ∫ ω, Complex.exp (Complex.I * (h ω (ψ k) : ℂ)) ∂P) atTop
      (𝓝 (∫ _ω, (1 : ℂ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k =>
      (GFF.measurable_exp_I_mul ((measurable_distOn_apply (ψ k)).comp hhm)).aestronglyMeasurable)
      (integrable_const 1) (fun k => Eventually.of_forall fun ω =>
        (Complex.norm_exp_I_mul_ofReal _).le) (Eventually.of_forall fun ω => ?_)
    have : Tendsto (fun k => h ω (ψ k)) atTop (𝓝 0) := by
      have h0 := ((h ω).continuous.tendsto 0).comp hψ
      convert h0 using 2
      · rfl
      · exact (map_zero (h ω)).symm
    have hc : Tendsto (fun k => Complex.exp (Complex.I * (h ω (ψ k) : ℂ))) atTop
        (𝓝 (Complex.exp (Complex.I * ((0 : ℝ) : ℂ)))) :=
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).tendsto
        (0 : ℝ)).comp this
    simpa using hc
  simp_rw [integral_exp_field hh] at h1
  rw [integral_const, probReal_univ, one_smul] at h1
  have h2 : Tendsto (fun k => Real.exp (-(1 / 2) * zeroGFFTestCov H (ψ k) (ψ k))) atTop (𝓝 1) := by
    have := (Complex.continuous_re.tendsto _).comp h1
    simp only [Function.comp_def, Complex.ofReal_re, Complex.one_re] at this
    exact this
  have h3 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h2)
  simp only [Function.comp_def, Real.log_exp, Real.log_one] at h3
  have := h3.const_mul (-2)
  simpa [← mul_assoc] using this

end Field

section Median

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The conditional variance of the field given `𝒜`. -/
def germVar (A : Ω → Set ℂ) (φ : TestOn upperHalfPlaneOpens) (ω : Ω) : ℝ :=
  zeroGFFTestCov (H \ relClosureH (A ω)) φ φ

omit mΩ in
lemma germVar_neg (A : Ω → Set ℂ) (φ : TestOn upperHalfPlaneOpens) (ω : Ω) :
    germVar A (-φ) ω = germVar A φ ω := by
  have hV := isOpen_H_diff_relClosureH (A ω)
  have hVH : H \ relClosureH (A ω) ⊆ H := sdiff_subset
  unfold germVar
  rw [zeroGFFTestCov_eq_inner_covVec hV hVH, zeroGFFTestCov_eq_inner_covVec hV hVH]
  have : covVec (H \ relClosureH (A ω)) ⇑(-φ) = -covVec (H \ relClosureH (A ω)) φ := by
    have := covVec_sub hV hVH 0 φ
    rw [zero_sub, covVec_zero _ hV hVH, zero_sub] at this
    exact this
  rw [this, inner_neg_neg]

/-- The hypotheses on a family of versions `M ψ` of `E[h(ψ) | 𝒜]` delivered by
`exists_condExp_germSigma`. -/
def IsGermMeanFamily (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω)
    (M : TestOn upperHalfPlaneOpens → Ω → ℝ) : Prop :=
  ∀ ψ, Measurable[germSigma A h] (M ψ) ∧ M ψ =ᵐ[P] P[fun ω => h ω ψ | germSigma A h] ∧
    (fun ω => Complex.exp (Complex.I * (M ψ ω : ℂ)) *
        ((Real.exp (-(1 / 2) * germVar A ψ ω) : ℝ) : ℂ)) =ᵐ[P]
      P[fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) | germSigma A h]

/-- **The residual `h(ψ) − M(ψ)` is conditionally Gaussian**: on every event `G'` of `𝒜`, the
characteristic function of the law of `h(ψ) − M(ψ)` restricted to `G'` is
`t ↦ ∫_{G'} e^{−σ²_{ℍ∖A}(tψ)/2}` (real). -/
theorem charFun_germResidual (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) {M : TestOn upperHalfPlaneOpens → Ω → ℝ}
    (hM : IsGermMeanFamily A h P M) (ψ : TestOn upperHalfPlaneOpens) {G' : Set Ω}
    (hG' : MeasurableSet[germSigma A h] G') (t : ℝ) :
    charFun ((P.restrict G').map fun ω => h ω ψ - M ψ ω) t =
      ((∫ ω in G', Real.exp (-(1 / 2) * germVar A (t • ψ) ω) ∂P : ℝ) : ℂ) := by
  have hhm := hh.measurable
  have hle := germSigma_le hA hhm
  obtain ⟨hMm, hMc, -⟩ := hM ψ
  obtain ⟨hMtm, hMtc, hMte⟩ := hM (t • ψ)
  have hDm : Measurable fun ω => h ω ψ - M ψ ω :=
    ((measurable_distOn_apply ψ).comp hhm).sub (hMm.mono hle le_rfl)
  rw [charFun_apply_real, integral_map hDm.aemeasurable (by fun_prop)]
  -- `M(tψ) = t M(ψ)` almost surely
  have hlin : M (t • ψ) =ᵐ[P] fun ω => t * M ψ ω := by
    have hc : P[fun ω => h ω (t • ψ) | germSigma A h] =ᵐ[P]
        fun ω => t * (P[fun ω => h ω ψ | germSigma A h]) ω := by
      have : (fun ω => h ω (t • ψ)) = t • fun ω => h ω ψ := by
        funext ω; simp [map_smul]
      rw [this]
      exact (condExp_smul t _ _).trans (Eventually.of_forall fun ω => by simp)
    filter_upwards [hMtc, hc, hMc] with ω h1 h2 h3
    rw [h1, h2, h3]
  set W : Ω → ℂ := fun ω => Complex.exp (-(Complex.I * ((t * M ψ ω : ℝ) : ℂ)))
  have hWm : StronglyMeasurable[germSigma A h] W :=
    (Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.mul hMm))).neg)).stronglyMeasurable
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 := fun ω => by
    simp only [W, neg_mul_eq_mul_neg, ← Complex.ofReal_neg, Complex.norm_exp_I_mul_ofReal]; rfl
  have e1 : ∀ ω, Complex.exp (((t : ℝ) : ℂ) * ((h ω ψ - M ψ ω : ℝ) : ℂ) * Complex.I) =
      W ω * Complex.exp (Complex.I * (h ω (t • ψ) : ℂ)) := fun ω => by
    simp only [W, map_smul, smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast; ring
  simp_rw [e1]
  have hF : Integrable (fun ω => Complex.exp (Complex.I * (h ω (t • ψ) : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply _).comp hhm)
  have hWi : StronglyMeasurable[germSigma A h] (G'.indicator W) := hWm.indicator hG'
  have hWib : ∀ ω, ‖G'.indicator W ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ G'
    · rw [indicator_of_mem hω]; exact hWb ω
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hpull := integral_mul_condExp_of_bdd (P := P) hle hWi hWib hF
  have e2 : ∫ ω in G', W ω * Complex.exp (Complex.I * (h ω (t • ψ) : ℂ)) ∂P =
      ∫ ω, G'.indicator W ω * Complex.exp (Complex.I * (h ω (t • ψ) : ℂ)) ∂P := by
    rw [← integral_indicator (hle _ hG')]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ G' <;> simp [hω]
  rw [e2, hpull, ← integral_complex_ofReal]
  rw [← integral_indicator (hle _ hG')]
  refine integral_congr_ae ?_
  filter_upwards [hMte, hlin] with ω h1 h2
  rw [← h1]
  by_cases hω : ω ∈ G'
  · simp only [indicator_of_mem hω, W, h2, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, one_mul]
  · simp [indicator_of_notMem hω]

/-- **Conditional symmetry of the residual**: on every `G' ∈ 𝒜`, `h(ψ) − M(ψ)` is at least as
likely to be `≥ 0` as `< 0`, and vice versa. -/
theorem measure_le_two_mul_germResidual (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) {M : TestOn upperHalfPlaneOpens → Ω → ℝ}
    (hM : IsGermMeanFamily A h P M) (ψ : TestOn upperHalfPlaneOpens) {G' : Set Ω}
    (hG' : MeasurableSet[germSigma A h] G') :
    P G' ≤ 2 * P ({ω | M ψ ω ≤ h ω ψ} ∩ G') ∧ P G' ≤ 2 * P ({ω | h ω ψ ≤ M ψ ω} ∩ G') := by
  have hhm := hh.measurable
  have hle := germSigma_le hA hhm
  have hMm := (hM ψ).1
  set D : Ω → ℝ := fun ω => h ω ψ - M ψ ω
  have hDm : Measurable D := ((measurable_distOn_apply ψ).comp hhm).sub (hMm.mono hle le_rfl)
  set ν : Measure ℝ := (P.restrict G').map D
  have hsym : ν = ν.map Neg.neg := by
    refine Measure.ext_of_charFun (funext fun t => ?_)
    have e1 : charFun (ν.map Neg.neg) t = charFun ν (-t) := by
      rw [charFun_apply_real, charFun_apply_real, integral_map measurable_neg.aemeasurable
        (by fun_prop)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Complex.ofReal_neg]; ring_nf
    rw [e1, charFun_germResidual hh hA hM ψ hG', charFun_germResidual hh hA hM ψ hG',
      show (-t) • ψ = -(t • ψ) from neg_smul t ψ]
    simp only [germVar_neg]
  have hIci : ν (Ici 0) = ν (Iic 0) := by
    conv_lhs => rw [hsym]
    rw [Measure.map_apply measurable_neg measurableSet_Ici]
    congr 1
    ext x; simp
  have huniv : ν univ ≤ 2 * ν (Ici 0) := by
    calc ν univ ≤ ν (Ici 0 ∪ Iic 0) := measure_mono fun x _ => (le_total 0 x).elim
          (fun h => Or.inl h) (fun h => Or.inr h)
      _ ≤ ν (Ici 0) + ν (Iic 0) := measure_union_le _ _
      _ = 2 * ν (Ici 0) := by rw [← hIci, two_mul]
  have hνu : ν univ = P G' := by
    rw [Measure.map_apply hDm MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
  have hν1 : ν (Ici 0) = P ({ω | M ψ ω ≤ h ω ψ} ∩ G') := by
    rw [Measure.map_apply hDm measurableSet_Ici, Measure.restrict_apply (hDm measurableSet_Ici)]
    congr 1; ext ω; simp [D, sub_nonneg]
  have hν2 : ν (Iic 0) = P ({ω | h ω ψ ≤ M ψ ω} ∩ G') := by
    rw [Measure.map_apply hDm measurableSet_Iic, Measure.restrict_apply (hDm measurableSet_Iic)]
    congr 1; ext ω; simp [D]
  refine ⟨?_, ?_⟩
  · rw [← hνu, ← hν1]; exact huniv
  · rw [← hνu, ← hν2, ← hIci]; exact huniv

/-- **The median bound**: for `G ∈ 𝒜`, `P(G) ≤ 2 P(G ∩ {|M(ψ)| ≤ |h(ψ)|})`. -/
theorem measure_le_two_mul_abs_le (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) {M : TestOn upperHalfPlaneOpens → Ω → ℝ}
    (hM : IsGermMeanFamily A h P M) (ψ : TestOn upperHalfPlaneOpens) {G : Set Ω}
    (hG : MeasurableSet[germSigma A h] G) :
    P G ≤ 2 * P (G ∩ {ω | |M ψ ω| ≤ |h ω ψ|}) := by
  have hhm := hh.measurable
  have hle := germSigma_le hA hhm
  have hMm := (hM ψ).1
  have hG1 : MeasurableSet[germSigma A h] ({ω | 0 ≤ M ψ ω} ∩ G) :=
    (measurableSet_le measurable_const hMm).inter hG
  have hG2 : MeasurableSet[germSigma A h] ({ω | M ψ ω < 0} ∩ G) :=
    (measurableSet_lt hMm measurable_const).inter hG
  have hsplit : P G = P ({ω | 0 ≤ M ψ ω} ∩ G) + P ({ω | M ψ ω < 0} ∩ G) := by
    rw [← measure_union _ (hle _ hG2)]
    · congr 1; ext ω; simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro h1; rcases le_or_gt 0 (M ψ ω) with h2 | h2
        · exact Or.inl ⟨h2, h1⟩
        · exact Or.inr ⟨h2, h1⟩
      · rintro (⟨-, h1⟩ | ⟨-, h1⟩) <;> exact h1
    · exact Set.disjoint_left.2 fun ω h1 h2 => by
        simp only [mem_inter_iff, mem_ofPred_eq] at h1 h2; linarith [h1.1, h2.1]
  have h1 := (measure_le_two_mul_germResidual hh hA hM ψ hG1).1
  have h2 := (measure_le_two_mul_germResidual hh hA hM ψ hG2).2
  have hsub1 : {ω | M ψ ω ≤ h ω ψ} ∩ ({ω | 0 ≤ M ψ ω} ∩ G) ⊆
      (G ∩ {ω | |M ψ ω| ≤ |h ω ψ|}) ∩ {ω | 0 ≤ M ψ ω} := by
    rintro ω ⟨ha, hb, hc⟩
    simp only [mem_ofPred_eq] at ha hb
    refine ⟨⟨hc, ?_⟩, hb⟩
    simp only [mem_ofPred_eq]
    rw [abs_of_nonneg hb]; exact ha.trans (le_abs_self _)
  have hsub2 : {ω | h ω ψ ≤ M ψ ω} ∩ ({ω | M ψ ω < 0} ∩ G) ⊆
      (G ∩ {ω | |M ψ ω| ≤ |h ω ψ|}) \ {ω | 0 ≤ M ψ ω} := by
    rintro ω ⟨ha, hb, hc⟩
    simp only [mem_ofPred_eq] at ha hb
    refine ⟨⟨hc, ?_⟩, by simp only [mem_ofPred_eq, not_le]; exact hb⟩
    simp only [mem_ofPred_eq]
    rw [abs_of_neg hb]
    have := neg_le_abs (h ω ψ)
    linarith
  have hmeasD : MeasurableSet {ω | 0 ≤ M ψ ω} := measurableSet_le measurable_const (hMm.mono hle le_rfl)
  calc P G = P ({ω | 0 ≤ M ψ ω} ∩ G) + P ({ω | M ψ ω < 0} ∩ G) := hsplit
    _ ≤ 2 * P ((G ∩ {ω | |M ψ ω| ≤ |h ω ψ|}) ∩ {ω | 0 ≤ M ψ ω}) +
        2 * P ((G ∩ {ω | |M ψ ω| ≤ |h ω ψ|}) \ {ω | 0 ≤ M ψ ω}) :=
      add_le_add (h1.trans (mul_le_mul' le_rfl (measure_mono hsub1)))
        (h2.trans (mul_le_mul' le_rfl (measure_mono hsub2)))
    _ = 2 * P (G ∩ {ω | |M ψ ω| ≤ |h ω ψ|}) := by
      rw [← mul_add, measure_inter_add_sdiff _ hmeasD]

end Median

section Generic

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

lemma setIntegral_condExp_indicator (hm : m ≤ mΩ) {E G : Set Ω} (hE : MeasurableSet E)
    (hG : MeasurableSet[m] G) : ∫ ω in G, (P⟦E|m⟧) ω ∂P = P.real (G ∩ E) := by
  rw [setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator hE) hG,
    integral_indicator hE, Measure.restrict_restrict hE, setIntegral_const, smul_eq_mul, mul_one,
    inter_comm]

/-- If `G ∈ m` has conditional probability `> 1/2` of `E`, satisfies the median bound for `D`, and
`G ∩ E ∩ D = ∅`, then `P(G) = 0`. -/
lemma measure_eq_zero_of_condExp_gt_half (hm : m ≤ mΩ) {G E D : Set Ω} (hG : MeasurableSet[m] G)
    (hE : MeasurableSet E) (hD : MeasurableSet D) (hGED : G ∩ E ∩ D = ∅)
    (hmed : P G ≤ 2 * P (G ∩ D)) (hπ : ∀ ω ∈ G, 1 / 2 < (P⟦E|m⟧) ω) : P G = 0 := by
  by_contra hpos
  have hG' : MeasurableSet G := hm _ hG
  have hπi : Integrable (P⟦E|m⟧) P := integrable_condExp
  have h1 : P.real G / 2 < P.real (G ∩ E) := by
    rw [← setIntegral_condExp_indicator hm hE hG]
    have hpos' : 0 < ∫ ω in G, ((P⟦E|m⟧) ω - 1 / 2) ∂P := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae]
      · have : Function.support (fun ω => (P⟦E|m⟧) ω - 1 / 2) ∩ G = G := by
          refine inter_eq_right.2 fun ω hω => ?_
          simp only [Function.mem_support]; linarith [hπ ω hω]
        rw [this]; exact pos_iff_ne_zero.2 hpos
      · exact (ae_restrict_iff' hG').2 (Eventually.of_forall fun ω hω => by
          simp only [Pi.zero_apply]; linarith [hπ ω hω])
      · exact (hπi.sub (integrable_const _)).integrableOn
    rw [integral_sub hπi.integrableOn (integrable_const _).integrableOn, setIntegral_const,
      smul_eq_mul] at hpos'
    linarith
  have h2 : P.real G ≤ 2 * P.real (G ∩ D) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _)) hmed
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
  have h3 : P.real (G ∩ E) + P.real (G ∩ D) ≤ P.real G := by
    have hu := measure_union_add_inter (μ := P) (G ∩ E) (hG'.inter hD)
    have he : (G ∩ E) ∩ (G ∩ D) = ∅ := by
      rw [← hGED]; ext ω; simp only [mem_inter_iff]; tauto
    rw [he, measure_empty, add_zero] at hu
    have : P (G ∩ E) + P (G ∩ D) ≤ P G := by
      rw [← hu]; exact measure_mono (union_subset inter_subset_left inter_subset_left)
    have := ENNReal.toReal_mono (measure_ne_top P G) this
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
  linarith

/-- If `E_k ↑ Ω`, then almost surely some `E_k` has conditional probability `> 1/2`. -/
lemma ae_exists_condExp_gt_half (hm : m ≤ mΩ) {E : ℕ → Set Ω} (hE : ∀ k, MeasurableSet (E k))
    (hmono : Monotone E) (hcov : ⋃ k, E k = univ) :
    ∀ᵐ ω ∂P, ∃ k, 1 / 2 < (P⟦E k|m⟧) ω := by
  set F : Set Ω := {ω | ∀ k, (P⟦E k|m⟧) ω ≤ 1 / 2}
  have hF : MeasurableSet[m] F := by
    have : F = ⋂ k, {ω | (P⟦E k|m⟧) ω ≤ 1 / 2} := by ext ω; simp [F]
    rw [this]
    exact MeasurableSet.iInter fun k =>
      measurableSet_le stronglyMeasurable_condExp.measurable measurable_const
  have hb : ∀ k, P.real (F ∩ E k) ≤ P.real F / 2 := fun k => by
    rw [← setIntegral_condExp_indicator hm (hE k) hF]
    calc ∫ ω in F, (P⟦E k|m⟧) ω ∂P ≤ ∫ ω in F, (1 / 2 : ℝ) ∂P :=
          setIntegral_mono_on integrable_condExp.integrableOn (integrable_const _).integrableOn
            (hm _ hF) fun ω hω => hω k
      _ = P.real F / 2 := by rw [setIntegral_const, smul_eq_mul]; ring
  have hlim : Tendsto (fun k => P.real (F ∩ E k)) atTop (𝓝 (P.real F)) := by
    have hmono' : Monotone fun k => F ∩ E k := fun a b hab => inter_subset_inter_right _ (hmono hab)
    have := tendsto_measure_iUnion_atTop (μ := P) hmono'
    rw [← inter_iUnion, hcov, inter_univ] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top P F)).comp this
  have hle : P.real F ≤ P.real F / 2 := le_of_tendsto' hlim hb
  have h0 : P F = 0 := by
    have : P.real F = 0 := le_antisymm (by linarith [measureReal_nonneg (μ := P) (s := F)])
      measureReal_nonneg
    rwa [measureReal_eq_zero_iff] at this
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  simp only [F, mem_ofPred_eq, not_forall, not_le] at hω
  exact hω

end Generic

section Admissible

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The seminorm bound of order `k` on `K_n` for the coordinate `c`. -/
def coordSem (n k : ℕ) (c : CoordJ)
    (hc : tsupport (comb upperHalfPlaneOpens c : ℂ → ℝ) ⊆ exhaustK upperHalfPlaneOpens n) : ℝ :=
  ContDiffMapSupportedIn.supSeminorm ℝ ℂ ℝ ⊤ (exhaustK upperHalfPlaneOpens n) k
    (mkT upperHalfPlaneOpens _ hc)

lemma coordSem_mono {n k k' : ℕ} (hk : k ≤ k') (c : CoordJ)
    (hc : tsupport (comb upperHalfPlaneOpens c : ℂ → ℝ) ⊆ exhaustK upperHalfPlaneOpens n) :
    (k : ℝ) * coordSem n k c hc ≤ k' * coordSem n k' c hc :=
  mul_le_mul (by exact_mod_cast hk) (Seminorm.le_def.1 (supSeminorm_mono _ hk) _)
    (apply_nonneg _ _) (by positivity)

/-- The realizations satisfying the bound of order `k` on `K_n`. -/
def boundSet (h : Ω → DistOn upperHalfPlaneOpens) (n k : ℕ) : Set Ω :=
  {ω | ∀ c : {c : CoordJ // tsupport (comb upperHalfPlaneOpens c : ℂ → ℝ) ⊆
    exhaustK upperHalfPlaneOpens n}, |h ω (comb upperHalfPlaneOpens c.1)| ≤ k * coordSem n k c.1 c.2}

omit [IsProbabilityMeasure P] in
lemma measurableSet_boundSet (hh : Measurable h) (n k : ℕ) : MeasurableSet (boundSet h n k) := by
  have : boundSet h n k = ⋂ c : {c : CoordJ // tsupport (comb upperHalfPlaneOpens c : ℂ → ℝ) ⊆
      exhaustK upperHalfPlaneOpens n}, {ω | |h ω (comb upperHalfPlaneOpens c.1)| ≤
        k * coordSem n k c.1 c.2} := by ext ω; simp [boundSet]
  rw [this]
  exact MeasurableSet.iInter fun c =>
    measurableSet_le (continuous_abs.measurable.comp ((measurable_distOn_apply _).comp hh))
      measurable_const

omit mΩ in
lemma boundSet_mono (h : Ω → DistOn upperHalfPlaneOpens) (n : ℕ) : Monotone (boundSet h n) :=
  fun _ _ hk _ hω c => (hω c).trans (coordSem_mono hk c.1 c.2)

omit mΩ in
lemma iUnion_boundSet (h : Ω → DistOn upperHalfPlaneOpens) (n : ℕ) :
    ⋃ k, boundSet h n k = univ := by
  refine eq_univ_of_forall fun ω => mem_iUnion.2 ?_
  have hr := range_pairJ_subset upperHalfPlaneOpens ⟨h ω, rfl⟩
  have h3 := mem_iInter.1 hr.2 n
  obtain ⟨C, hC⟩ := mem_iUnion.1 h3
  obtain ⟨N, hN⟩ := mem_iUnion.1 hC
  refine ⟨max C N, fun c => ?_⟩
  have := hN c.1 c.2
  refine this.trans ?_
  exact mul_le_mul (by exact_mod_cast le_max_left C N)
    (Seminorm.le_def.1 (supSeminorm_mono _ (le_max_right C N)) _) (apply_nonneg _ _) (by positivity)

/-- **The conditional means are almost surely the pairings of a distribution** (`rangeSet`):
additive, consistent, and of finite order on each compact `K_n`, by the median bound. -/
theorem ae_mem_rangeSet_germMean (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) {M : TestOn upperHalfPlaneOpens → Ω → ℝ}
    (hM : IsGermMeanFamily A h P M) :
    ∀ᵐ ω ∂P, (fun c => M (comb upperHalfPlaneOpens c) ω) ∈ rangeSet upperHalfPlaneOpens := by
  have hhm := hh.measurable
  have hle := germSigma_le hA hhm
  have hint : ∀ ψ, Integrable (fun ω => h ω ψ) P := fun ψ =>
    (hh.process.gaussian.hasGaussianLaw_eval ψ).memLp_two.integrable one_le_two
  -- additivity
  have hadd : ∀ᵐ ω ∂P, ∀ c c' : CoordJ, M (comb upperHalfPlaneOpens (c + c')) ω =
      M (comb upperHalfPlaneOpens c) ω + M (comb upperHalfPlaneOpens c') ω := by
    refine ae_all_iff.2 fun c => ae_all_iff.2 fun c' => ?_
    have e : (fun ω => h ω (comb upperHalfPlaneOpens (c + c'))) =
        (fun ω => h ω (comb upperHalfPlaneOpens c)) + fun ω => h ω (comb upperHalfPlaneOpens c') := by
      funext ω; simp [map_add]
    have hc := condExp_add (m := germSigma A h) (hint (comb upperHalfPlaneOpens c))
      (hint (comb upperHalfPlaneOpens c'))
    filter_upwards [(hM (comb upperHalfPlaneOpens (c + c'))).2.1, (hM (comb upperHalfPlaneOpens c)).2.1,
      (hM (comb upperHalfPlaneOpens c')).2.1, hc] with ω h1 h2 h3 h4
    rw [h1, e, h4, Pi.add_apply, h2, h3]
  -- the bounds
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ k : ℕ, ∀ c : {c : CoordJ // tsupport (comb upperHalfPlaneOpens c :
      ℂ → ℝ) ⊆ exhaustK upperHalfPlaneOpens n},
        |M (comb upperHalfPlaneOpens c.1) ω| ≤ k * coordSem n k c.1 c.2 := by
    intro n
    have hex := ae_exists_condExp_gt_half (P := P) hle (measurableSet_boundSet hhm n)
      (boundSet_mono h n) (iUnion_boundSet h n)
    have hk : ∀ k : ℕ, ∀ c : {c : CoordJ // tsupport (comb upperHalfPlaneOpens c : ℂ → ℝ) ⊆
        exhaustK upperHalfPlaneOpens n}, ∀ᵐ ω ∂P,
          1 / 2 < (P⟦boundSet h n k|germSigma A h⟧) ω →
            |M (comb upperHalfPlaneOpens c.1) ω| ≤ k * coordSem n k c.1 c.2 := by
      intro k c
      set ψ := comb upperHalfPlaneOpens c.1
      have hMm := (hM ψ).1
      set G : Set Ω := {ω | 1 / 2 < (P⟦boundSet h n k|germSigma A h⟧) ω} ∩
        {ω | (k : ℝ) * coordSem n k c.1 c.2 < |M ψ ω|}
      have hG : MeasurableSet[germSigma A h] G :=
        (measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable).inter
          (measurableSet_lt measurable_const (continuous_abs.measurable.comp hMm))
      have hD : MeasurableSet {ω | |M ψ ω| ≤ |h ω ψ|} :=
        measurableSet_le (continuous_abs.measurable.comp (hMm.mono hle le_rfl))
          (continuous_abs.measurable.comp ((measurable_distOn_apply ψ).comp hhm))
      have h0 := measure_eq_zero_of_condExp_gt_half hle hG (measurableSet_boundSet hhm n k) hD
        (Set.eq_empty_of_forall_notMem fun ω ⟨⟨⟨_, h2⟩, h3⟩, h4⟩ => by
          have := h3 c
          simp only [mem_ofPred_eq] at h2 h4
          linarith)
        (measure_le_two_mul_abs_le hh hA hM ψ hG) (fun ω hω => hω.1)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω h1
      simp only [G, mem_inter_iff, mem_ofPred_eq, not_and, not_lt] at hω
      exact hω h1
    filter_upwards [hex, ae_all_iff.2 fun k => ae_all_iff.2 (hk k)] with ω ⟨k, hk1⟩ h2
    exact ⟨k, fun c => h2 k c hk1⟩
  filter_upwards [hadd, ae_all_iff.2 hbd] with ω h1 h2
  refine ⟨⟨h1, fun c c' e => congrArg (fun ψ => M ψ ω) e⟩, mem_iInter.2 fun n => ?_⟩
  obtain ⟨k, hk⟩ := h2 n
  exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨k, fun c hc => hk ⟨c, hc⟩⟩⟩

end Admissible

end LocalSets
end InteractingSLE
