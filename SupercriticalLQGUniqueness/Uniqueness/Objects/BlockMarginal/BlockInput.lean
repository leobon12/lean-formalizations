import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.GeomInputs
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockOptimalCmp
import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.OmegaComparison
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.Centre
import SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality.ShieldUnionLocal




 












set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

theorem ae_optimal_allPairs_sample {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (E (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (E (h ω)) = cPlus) :
    ∀ᵐ ω ∂P, ∀ p : ℂ × ℂ, cMinus * D (h ω) p ≤ E (h ω) p ∧ E (h ω) p ≤ cPlus * D (h ω) p := by
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D E hD hE
  have hwhole : LQGMetric.IsGFFPlusCont h P := LQGMetric.GM.detGFFPlusCont hGFF.1
  have hB : ∀ᵐ ω ∂P, OptimalConstants.Ratios.BiLipBound (D (h ω)) (E (h ω))
      (ENNReal.ofReal K)⁻¹ (ENNReal.ofReal K) := by
    filter_upwards [hEBL P h hwhole] with ω hb
    exact OptimalConstants.Determinism.biLipBound_of_symmetric_ebl K hK (D (h ω)) (E (h ω)) hb
  have hPair := OptimalConstants.Determinism.ae_finitePair_of_tightness ξ Q D hD P h hGFF
  have hAll := OptimalConstants.Ratios.ae_allPairs_of_ae_optima P (fun ω => D (h ω)) (fun ω => E (h ω))
    (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) hB hPair hMinus hPlus
  filter_upwards [hAll] with ω hω p
  exact hω p.1 p.2

 

theorem ae_comparison_field {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hm0 : 0 < cMinus) (hmTop : cMinus < ⊤) (hp0 : 0 < cPlus) (hpTop : cPlus < ⊤)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (E (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (E (h ω)) = cPlus) :
    ∀ᵐ g ∂(P.map h), (∀ p : ℂ × ℂ, E g p ≤ ENNReal.ofReal cPlus.toReal * D g p) ∧
      (∀ p : ℂ × ℂ, D g p ≤ ENNReal.ofReal cMinus⁻¹.toReal * E g p) := by
  have hInvTop : cMinus⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hm0.ne'
  have hInvPos : 0 < cMinus⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_pos.mpr hmTop.ne).ne' hInvTop
  have hCp : 0 < cPlus.toReal := ENNReal.toReal_pos hp0.ne' hpTop.ne
  have hm1 := Objects.RadiusResidual.measurableSet_metric_upper cPlus.toReal hCp D E hD.1 hE.1
  have hm2 := Objects.RadiusResidual.measurableSet_metric_upper cMinus⁻¹.toReal hInvPos E D hE.1 hD.1
  have hmeas := hm1.inter hm2
  have hsample := ae_optimal_allPairs_sample P h ξ Q D E hD hE hGFF cMinus cPlus hMinus hPlus
  have hmap := (ae_map_iff hGFF.1.measurable.aemeasurable hmeas).2 (by
    filter_upwards [hsample] with ω hω
    refine ⟨fun u v => ?_, fun u v => ?_⟩
    · rw [ENNReal.ofReal_toReal hpTop.ne]
      exact (hω (u, v)).2
    · rw [ENNReal.ofReal_toReal hInvTop]
      calc D (h ω) (u, v) = cMinus⁻¹ * (cMinus * D (h ω) (u, v)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hm0.ne' hmTop.ne, one_mul]
        _ ≤ cMinus⁻¹ * E (h ω) (u, v) := by gcongr; exact (hω (u, v)).1)
  filter_upwards [hmap] with g hg
  exact ⟨fun p => hg.1 p.1 p.2, fun p => hg.2 p.1 p.2⟩

 

theorem blockWindow_balls (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (hρr : 0 < T.rho * T.r) :
    ∀ k ∈ Finset.Icc 1 Ksh, ball (0 : ℂ) (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆
      (ball (0 : ℂ) (3 * (3 * 8 ^ Ksh) * (T.rho * T.r)) : Set ℂ) := by
  intro k _
  apply ball_subset_ball
  have h8 : (8 : ℝ) ^ (Ksh - k) ≤ 8 ^ Ksh := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  nlinarith

theorem blockWindow_shape (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (hρr : 0 < T.rho * T.r)
    (hn : ‖T.orientation‖ = 1) :
    closure (Objects.Excursions.blockShape T) ⊆ ball (0 : ℂ) (3 * (3 * 8 ^ Ksh) * (T.rho * T.r)) := by
  refine (closure_minimal (Objects.Excursions.blockShape_subset hn hρr) isClosed_closedBall).trans ?_
  apply closedBall_subset_ball
  have h8 : (1 : ℝ) ≤ 8 ^ Ksh := one_le_pow₀ (by norm_num)
  nlinarith

theorem blockWindow_circle (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (hρr : 0 < T.rho * T.r) {c : ℂ}
    (hc : ‖c‖ ≤ T.rho * T.r) (hs : T.blockRadius ≤ T.rho * T.r) :
    closedBall c T.blockRadius ⊆ ball (0 : ℂ) (3 * (3 * 8 ^ Ksh) * (T.rho * T.r)) := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  rw [mem_ball, dist_zero_right]
  have h8 : (1 : ℝ) ≤ 8 ^ Ksh := one_le_pow₀ (by norm_num)
  have t := norm_le_insert' x c
  nlinarith

theorem norm_cU_le (T : Objects.CorrectedEvent.TubeData) (hn : ‖T.orientation‖ = 1) (hρr : 0 < T.rho * T.r)
    (hα0 : 0 ≤ T.alpha) (hα1 : T.alpha ≤ 1) : ‖Objects.Excursions.cU T‖ ≤ T.rho * T.r := by
  rw [Objects.Excursions.cU, norm_mul, norm_mul, Complex.norm_real, hn, mul_one, Objects.CorrectedEvent.uNorm, Objects.Producer.norm_polar,
    Real.norm_eq_abs, abs_of_pos hρr, abs_of_nonneg hα0]
  nlinarith

theorem norm_cV_le (T : Objects.CorrectedEvent.TubeData) (hn : ‖T.orientation‖ = 1) (hρr : 0 < T.rho * T.r) :
    ‖Objects.Excursions.cV T‖ ≤ T.rho * T.r := by
  rw [Objects.Excursions.cV, norm_mul, norm_mul, Complex.norm_real, hn, mul_one, Objects.CorrectedEvent.vNorm, Objects.Producer.norm_polar,
    Real.norm_eq_abs, abs_of_pos hρr, abs_one, mul_one]

 
theorem aeEventIn_blockRaw_window {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hm0 : 0 < cMinus) (hmTop : cMinus < ⊤) (hp0 : 0 < cPlus) (hpTop : cPlus < ⊤)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T) (Ksh : ℕ) (Cmid0 : ℝ)
    (hE : C.A_endpt ≤ 1) (hK0 : 0 ≤ C.K_ann) (hLam : C.lamConst < 1)
    (hSmall : C.lamConst * cPlus.toReal / cMinus.toReal < 1) :
    AEEventIn (P.map h) (fieldSigma0On (id : DistC → DistC)
        (ball (0 : ℂ) (3 * (3 * 8 ^ Ksh) * (T.rho * T.r))))
      {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g} := by
  have hμ := Objects.ProbabilityS7S9.normalizedGFF_id_map' P h hGFF
  have : IsProbabilityMeasure (P.map h) :=
    (Measure.isProbabilityMeasure_map_iff hGFF.1.measurable.aemeasurable).2 inferInstance
  have hr : T.r = C.r := hData.1
  have hρ : T.rho = C.ρ := hData.2.1
  have hα : T.alpha = C.K_ann := hData.2.2.2.2.1
  have hn := Objects.Producer.norm_orientation hData.2.2.2.2.2.2.1
  have hρr : 0 < T.rho * T.r := by rw [hρ, hr]; exact mul_pos C.rhoPos C.rPos
  obtain ⟨hb0, hb1⟩ := Objects.Producer.blockRadius_bounds C T hData hE
  have hb1' : T.blockRadius ≤ T.rho * T.r := by rw [hρ, hr]; exact hb1
  have hK1 := Objects.Producer.kann_lt_one C
  obtain hCmp := ae_comparison_field P h ξ Q D D' hD hD' hGFF cMinus cPlus hm0 hmTop hp0 hpTop
    hMinus hPlus
  have hInvTop : cMinus⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hm0.ne'
  have hCi : 0 < cMinus⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_pos.mpr hmTop.ne).ne' hInvTop
  have hCp : 0 < cPlus.toReal := ENNReal.toReal_pos hp0.ne' hpTop.ne
  have hRatio := Objects.BlockCoding.shield_ratio_of_optima cMinus cPlus hp0 hpTop C.lamConst C.lamPos.le hSmall
  have hUne : ((⟨ball (0 : ℂ) (3 * (3 * 8 ^ Ksh) * (T.rho * T.r)), isOpen_ball⟩ :
      TopologicalSpace.Opens ℂ) : Set ℂ).Nonempty :=
    ⟨0, mem_ball_self (by positivity)⟩
  exact Objects.BlockCoding.aeEventIn_blockRaw_modConst (P.map h) hμ ξ Q D D' hD hD' cPlus.toReal
    cMinus⁻¹.toReal hCp hCi hCmp C T Ksh Cmid0 hρr hn hb0.le hLam hRatio
    ⟨ball (0 : ℂ) (3 * (3 * 8 ^ Ksh) * (T.rho * T.r)), isOpen_ball⟩ hUne
    (blockWindow_balls T Ksh hρr)
    (fun k hk => Objects.ShieldLocality.shieldWindow_subset_bigBall T Ksh k hρr hk)
    (blockWindow_shape T Ksh hρr hn)
    (blockWindow_circle T Ksh hρr (norm_cU_le T hn hρr (hα ▸ hK0) (hα ▸ hK1.le)) hb1')
    (blockWindow_circle T Ksh hρr (norm_cV_le T hn hρr) hb1')

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
