import HigherDimLQGContinuity.ConvTransfer.MedianProb

/-!
# Uniform median comparison at real cutoffs
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd WN e₁)
open HigherDimLQGMetric.DGZ

/-- The convolution sphere mean has a variance bound independent of the
realization of the normalized LGF. -/
theorem convUniform_sphereMean_variance {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ V : ℝ, 0 ≤ V ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε ∈ Ioo (0 : ℝ) 1,
        Var[fun ω => l6a_convSphereMean κ ε (h ω); P] ≤ V := by
  obtain ⟨V, hV0, hV⟩ := l6a_uniform_meanTrunc_logCov hd hκ
  refine ⟨V, hV0, ?_⟩
  intro Ω _ P _ h hh ε hε
  have hlim := (l6a_gaussianClosure_sphereMean hd κ hκ P h hh hε.1).2.2
  have hbound (n : ℕ) :
      Var[(fun ω => h ω (l6a_meanCenteredTest hd hκ hε.1 n).1); P] ≤ V := by
    have hcov := hV ε ⟨hε.1, hε.2.le⟩ n
    change |logCovRd (l6a_meanCenteredTest hd hκ hε.1 n).1
      (l6a_meanCenteredTest hd hκ hε.1 n).1| ≤ V at hcov
    have hvar : Var[(fun ω => h ω (l6a_meanCenteredTest hd hκ hε.1 n).1); P] =
        logCovRd (l6a_meanCenteredTest hd hκ hε.1 n).1
          (l6a_meanCenteredTest hd hκ hε.1 n).1 := by
      rw [← hh.1.covariance_eq, covariance_self
        (hh.1.gaussian.hasGaussianLaw_eval
          (l6a_meanCenteredTest hd hκ hε.1 n)).aemeasurable]
    rw [hvar]
    exact (le_abs_self _).trans hcov
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

/-- Uniform exponential moments of the sphere mean on every normalized LGF
probability space. -/
theorem convUniform_sphereMean_exp_moment {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ V : ℝ, 0 ≤ V ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ l : ℝ,
        ∫⁻ ω, ENNReal.ofReal (Real.exp (l * |l6a_convSphereMean κ ε (h ω)|)) ∂P ≤
          ENNReal.ofReal (2 * Real.exp (V * l ^ 2 / 2)) := by
  obtain ⟨V, hV, hVar⟩ := convUniform_sphereMean_variance hd hκ
  refine ⟨V, hV, ?_⟩
  intro Ω _ P _ h hh ε hε l
  obtain ⟨hG, h0⟩ := l6a_hasGaussianLaw_sphereMean hd κ hκ P h hh hε.1
  exact convEnv_lintegral_exp_abs_gauss hG h0 (hVar P h hh ε hε) l

/-- An absolute sphere-mean tail, uniform in the cutoff and in the LGF
realization. -/
theorem convUniform_sphereMean_tail {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∀ ε ∈ Ioo (0 : ℝ) 1,
        P {ω | L < |l6a_convSphereMean κ ε (h ω)|} ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
  obtain ⟨V, hV0, hVar⟩ := convUniform_sphereMean_variance hd hκ
  let L : ℝ := 8 * V + 1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro Ω _ P _ h hh ε hε
  obtain ⟨hG, hmean⟩ :=
    l6a_hasGaussianLaw_sphereMean hd κ hκ P h hh hε.1
  have hcheb := meas_ge_le_variance_div_sq
    (hG.memLp (by simp : (2 : ℝ≥0∞) ≠ ⊤)) hL
  change P {ω | L ≤ |l6a_convSphereMean κ ε (h ω) -
      ∫ ω', l6a_convSphereMean κ ε (h ω') ∂P|} ≤
    ENNReal.ofReal (Var[fun ω => l6a_convSphereMean κ ε (h ω); P] / L ^ 2) at hcheb
  rw [hmean] at hcheb
  simp only [sub_zero] at hcheb
  have hVL : V / L ^ 2 ≤ (1 / 8 : ℝ) := by
    have hL1 : 1 ≤ L := by dsimp [L]; linarith
    have hVL1 : V ≤ L / 8 := by dsimp [L]; linarith
    apply (div_le_iff₀ (sq_pos_of_pos hL)).2
    nlinarith
  calc
    P {ω | L < |l6a_convSphereMean κ ε (h ω)|} ≤
        P {ω | L ≤ |l6a_convSphereMean κ ε (h ω)|} :=
          measure_mono (fun ω hw => by
            change L < |l6a_convSphereMean κ ε (h ω)| at hw
            change L ≤ |l6a_convSphereMean κ ε (h ω)|
            exact hw.le)
    _ ≤ ENNReal.ofReal (Var[fun ω => l6a_convSphereMean κ ε (h ω); P] / L ^ 2) :=
      hcheb
    _ ≤ ENNReal.ofReal (V / L ^ 2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hVar P h hh ε hε)
        (sq_nonneg L))
    _ ≤ ENNReal.ofReal (1 / 8 : ℝ) := ENNReal.ofReal_le_ofReal hVL

/-- The convolution LFPP lower median is comparable to the dyadic median
at the real-cutoff scale. The scale and dyadic realization are supplied by
`convModel_law`. -/
theorem aEps_comparable_model_unif {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hT : UHolderTightShape d κ) (hN : UNondegShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (ξ : ℝ), UHyp d κ b μ ξ →
      ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∃ N : ℕ, ∃ r : ℝ, 1 / 2 < r ∧ r ≤ 1 ∧
        ε = ((2 : ℝ)⁻¹ ^ N) * r ∧
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
          (W₀ W' : WN d → Ω' → ℝ) (H : ℕ → Rd d → Ω' → ℝ)
          (T I : Rd d → Ω' → ℝ) (m : Ω' → ℝ),
          IsProbabilityMeasure P' ∧
          HigherDimLFPP.IsWhiteNoise P' W₀ ∧
          IsDyadicRealization κ P' W' H ∧
          HigherDimLFPP.IsBandVersion P' W' κ 1 (1 / r) T ∧
          (∀ ω', Continuous fun x => I x ω') ∧
          (∀ x, Measurable (I x)) ∧ Measurable m ∧
          (∀ x, I x =ᵐ[P'] W₀ (HigherDimLFPP.bandVecM κ (Ioi 1)
            (Measure.dirac x) (unitSphereProb d))) ∧
          (∀ ω', m ω' = W₀ (HigherDimLFPP.bandVecM κ (Ioo ε 1)
            (unitSphereProb d) 0) ω') ∧
          (∀ᵐ ω ∂P, Continuous (convMollifyNorm κ ε (h ω))) ∧
          ∃ (Φ : Rd d → Ω' → ℝ) (hΦc : ∀ ω', Continuous fun x => Φ x ω'),
            (∀ z ω', Φ (r • z) ω' = H N z ω' + T z ω' - m ω' + I (r • z) ω') ∧
            (∀ A : Set C(Rd d, ℝ), MeasurableSet A →
              P {ω | l6a_toFieldCMap (convMollifyNorm κ ε (h ω)) ∈ A} =
                P' {ω' | (⟨fun x => Φ x ω', hΦc ω'⟩ : C(Rd d, ℝ)) ∈ A}) ∧
            c * r * aQ P' H ξ N 2⁻¹ ≤ aEps κ ξ ε ∧
            aEps κ ξ ε ≤ C * r * aQ P' H ξ N 2⁻¹ := by
  obtain ⟨mB, MB, hmB, hMB, hBtail⟩ :=
    convModel_point_uniform_tail hd hκ hT hN hb hμ
  obtain ⟨LX, hLX, hXtail⟩ := convUniform_sphereMean_tail hd hκ
  let m : ℝ := min (Real.exp (-(b * LX))) mB
  let M : ℝ := max (Real.exp (b * LX)) MB
  have hm : 0 < m := lt_min (Real.exp_pos _) hmB
  have hM : 0 < M := lt_max_of_lt_left (Real.exp_pos _)
  refine ⟨m ^ 2, M ^ 2, sq_pos_of_pos hm, sq_pos_of_pos hM, ?_⟩
  intro ξ hU ε hε Ω _ P _ h hh
  obtain ⟨N, r, hr, hr1, hεeq, Ω', inst', P', W₀, W', H, T, I, m₀,
    hP', hW₀, hH, hBand, hIc, hIm, hmm, hIeq, hm₀, hZc,
    Φ, hΦc, hΦeq, hLaw⟩ := convModel_law hd hκ hε P h hh
  letI : MeasurableSpace Ω' := inst'
  letI : IsProbabilityMeasure P' := hP'
  let a : ℝ := r * aQ P' H ξ N 2⁻¹
  have haQ : 0 < aQ P' H ξ N 2⁻¹ :=
    tight_aQ_pos (by omega : 0 < d) hH ξ N (by norm_num) (by norm_num)
  have ha : 0 < a := mul_pos (by linarith : 0 < r) haQ
  have hA : P {ω | Real.exp (ξ * l6a_convSphereMean κ ε (h ω)) < m ∨
      M < Real.exp (ξ * l6a_convSphereMean κ ε (h ω))} ≤ (8⁻¹ : ℝ≥0∞) := by
    have hsub : {ω | Real.exp (ξ * l6a_convSphereMean κ ε (h ω)) < m ∨
        M < Real.exp (ξ * l6a_convSphereMean κ ε (h ω))} ⊆
        {ω | LX < |l6a_convSphereMean κ ε (h ω)|} := by
      intro ω hw
      by_contra hn
      have hXb : |l6a_convSphereMean κ ε (h ω)| ≤ LX := le_of_not_gt hn
      have hprod : |ξ * l6a_convSphereMean κ ε (h ω)| ≤ b * LX := by
        rw [abs_mul, abs_of_pos hU.base.xi_pos]
        exact (mul_le_mul_of_nonneg_left hXb hU.base.xi_pos.le).trans
          (mul_le_mul_of_nonneg_right hU.le_b hLX.le)
      have hlo : Real.exp (-(b * LX)) ≤
          Real.exp (ξ * l6a_convSphereMean κ ε (h ω)) :=
        Real.exp_le_exp.mpr (neg_le_of_abs_le hprod)
      have hhi : Real.exp (ξ * l6a_convSphereMean κ ε (h ω)) ≤
          Real.exp (b * LX) :=
        Real.exp_le_exp.mpr (le_of_abs_le hprod)
      rcases hw with hw | hw
      · exact (not_lt_of_ge ((min_le_left _ _).trans hlo)) hw
      · exact (not_lt_of_ge (hhi.trans (le_max_left _ _))) hw
    have ht := (measure_mono hsub).trans (hXtail P h hh ε hε)
    simpa only [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
      ENNReal.ofReal_ofNat] using ht
  have hB : P {ω | a⁻¹ * HigherDimLFPP.lfppDistOn ξ
        (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d) < m ∨
      M < a⁻¹ * HigherDimLFPP.lfppDistOn ξ
        (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d)} ≤ (8⁻¹ : ℝ≥0∞) := by
    let B : Set ℝ := Iio (mB * a) ∪ Ioi (MB * a)
    have hBm : MeasurableSet B := isOpen_Iio.measurableSet.union isOpen_Ioi.measurableSet
    have hsub : {ω | a⁻¹ * HigherDimLFPP.lfppDistOn ξ
        (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d) < m ∨
      M < a⁻¹ * HigherDimLFPP.lfppDistOn ξ
        (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d)} ⊆
      {ω | lfppMetric ξ (convMollifyNorm κ ε (h ω)) 0 (e₁ d) ∈ B} := by
      intro ω hw
      change a⁻¹ * lfppMetric ξ (convMollifyNorm κ ε (h ω)) 0 (e₁ d) < m ∨
        M < a⁻¹ * lfppMetric ξ (convMollifyNorm κ ε (h ω)) 0 (e₁ d) at hw
      change lfppMetric ξ (convMollifyNorm κ ε (h ω)) 0 (e₁ d) < mB * a ∨
        MB * a < lfppMetric ξ (convMollifyNorm κ ε (h ω)) 0 (e₁ d)
      rcases hw with hw | hw
      · exact Or.inl (by simpa only [mul_comm] using
          (inv_mul_lt_iff₀ ha).mp (lt_of_lt_of_le hw (min_le_right _ _)))
      · exact Or.inr (by simpa only [mul_comm] using
          (lt_inv_mul_iff₀ ha).mp (lt_of_le_of_lt (le_max_right _ _) hw))
    have hLawPoint := convModel_pointDist_law ξ P P' h hZc hΦc hLaw B hBm
    have hModel : P' {ω' | lfppMetric ξ (fun x => Φ x ω') 0 (e₁ d) ∈ B} ≤
        ENNReal.ofReal (1 / 8 : ℝ) := by
      simpa only [B, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, a, mul_assoc,
        mul_left_comm, mul_comm] using
        hBtail ξ hU hε hr hr1 H hW₀ hH hBand hIc hIeq m₀ hmm hm₀
          N Φ hΦc hΦeq
    have ht := (measure_mono hsub).trans (hLawPoint.le.trans hModel)
    simpa only [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
      ENNReal.ofReal_ofNat] using ht
  have hmed := l6a_aEps_bounds_of_factor_tails hd hκ ξ hε.1
    P h hh ha hm.le hM.le hA hB
  refine ⟨N, r, hr, hr1, hεeq, Ω', inst', P', W₀, W', H, T, I, m₀,
    hP', hW₀, hH, hBand, hIc, hIm, hmm, hIeq, hm₀, hZc,
    Φ, hΦc, hΦeq, hLaw, ?_, ?_⟩
  · simpa only [a, mul_assoc] using hmed.1
  · simpa only [a, mul_assoc] using hmed.2

/-- The uniform comparison, with only the scale and dyadic median retained. -/
theorem aEps_comparable_unif {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hT : UHolderTightShape d κ) (hN : UNondegShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (ξ : ℝ), UHyp d κ b μ ξ →
      ∀ ε ∈ Ioo (0 : ℝ) 1,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
      ∃ N : ℕ, ∃ r : ℝ, 1 / 2 < r ∧ r ≤ 1 ∧
        ε = ((2 : ℝ)⁻¹ ^ N) * r ∧
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
          (W : WN d → Ω' → ℝ) (H : ℕ → Rd d → Ω' → ℝ),
          IsProbabilityMeasure P' ∧ IsDyadicRealization κ P' W H ∧
          c * r * aQ P' H ξ N 2⁻¹ ≤ aEps κ ξ ε ∧
          aEps κ ξ ε ≤ C * r * aQ P' H ξ N 2⁻¹ := by
  obtain ⟨c, C, hc, hC, hmodel⟩ :=
    aEps_comparable_model_unif hd hκ hT hN hb hμ
  refine ⟨c, C, hc, hC, ?_⟩
  intro ξ hU ε hε Ω _ P _ h hh
  obtain ⟨N, r, hr, hr1, heq, Ω', inst', P', W₀, W', H, T, I, m,
    hP', hW₀, hH, hBand, hIc, hIm, hmm, hIeq, hm, hZc,
    Φ, hΦc, hΦeq, hLaw, hlo, hhi⟩ := hmodel ξ hU ε hε P h hh
  exact ⟨N, r, hr, hr1, heq, Ω', inst', P', W', H, hP', hH, hlo, hhi⟩

end HigherDimLQGContinuity
