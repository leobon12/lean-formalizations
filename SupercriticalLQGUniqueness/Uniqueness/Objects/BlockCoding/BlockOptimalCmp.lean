import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockTranslateLocal
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Determinism.HDet




set_option autoImplicit false
noncomputable section
open MeasureTheory Set LQGMetric.Blueprint
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

open LQGMetric (DistC)

 

theorem ae_optimal_allPairs
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ g ∂μ, OptimalConstants.Ratios.lowerOptimal (D g) (E g) = cMinus)
    (hPlus : ∀ᵐ g ∂μ, OptimalConstants.Ratios.upperOptimal (D g) (E g) = cPlus) :
    ∀ᵐ g ∂μ, ∀ p : ℂ × ℂ,
      cMinus * D g p ≤ E g p ∧ E g p ≤ cPlus * D g p := by
  obtain ⟨K,hK,hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D E hD hE
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.detGFFPlusCont hμ.1
  have hB : ∀ᵐ g ∂μ,
      OptimalConstants.Ratios.BiLipBound (D g) (E g)
        (ENNReal.ofReal K)⁻¹ (ENNReal.ofReal K) := by
    filter_upwards [hEBL μ id hwhole] with g hb
    exact OptimalConstants.Determinism.biLipBound_of_symmetric_ebl K hK (D g) (E g) hb
  have hPair := OptimalConstants.Determinism.ae_finitePair_of_tightness ξ Q D hD μ id hμ
  have hAll := OptimalConstants.Ratios.ae_allPairs_of_ae_optima μ D E
    (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) hB hPair hMinus hPlus
  filter_upwards [hAll] with g hg p
  exact hg p.1 p.2

 

theorem ae_optimal_comparison_real
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (cMinus cPlus : ℝ≥0∞) (hm0 : 0 < cMinus) (hmTop : cMinus < ⊤)
    (hp0 : 0 < cPlus) (hpTop : cPlus < ⊤)
    (hMinus : ∀ᵐ g ∂μ, OptimalConstants.Ratios.lowerOptimal (D g) (E g) = cMinus)
    (hPlus : ∀ᵐ g ∂μ, OptimalConstants.Ratios.upperOptimal (D g) (E g) = cPlus) :
    let Cp := cPlus.toReal
    let Ci := cMinus⁻¹.toReal
    0 < Cp ∧ 0 < Ci ∧
      (∀ᵐ g ∂μ, (∀ p : ℂ × ℂ,
        E g p ≤ ENNReal.ofReal Cp * D g p) ∧
        (∀ p : ℂ × ℂ,
        D g p ≤ ENNReal.ofReal Ci * E g p)) := by
  dsimp
  have hInvPos : 0 < cMinus⁻¹ := ENNReal.inv_pos.mpr hmTop.ne
  have hInvTop : cMinus⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hm0.ne'
  refine ⟨ENNReal.toReal_pos hp0.ne' hpTop.ne,
    ENNReal.toReal_pos hInvPos.ne' hInvTop, ?_⟩
  filter_upwards [ae_optimal_allPairs μ hμ ξ Q D E hD hE
    cMinus cPlus hMinus hPlus] with g hg
  constructor
  · intro p
    simpa only [ENNReal.ofReal_toReal hpTop.ne] using (hg p).2
  · intro p
    calc
      D g p = cMinus⁻¹ * (cMinus * D g p) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hm0.ne' hmTop.ne, one_mul]
      _ ≤ cMinus⁻¹ * E g p := by gcongr; exact (hg p).1
      _ = ENNReal.ofReal cMinus⁻¹.toReal * E g p := by
        rw [ENNReal.ofReal_toReal hInvTop]

 

theorem shield_ratio_of_optima
    (cMinus cPlus : ℝ≥0∞)
    (hp0 : 0 < cPlus) (hpTop : cPlus < ⊤)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hsmall : lam * cPlus.toReal / cMinus.toReal < 1) :
    ENNReal.ofReal cPlus.toReal * ENNReal.ofReal lam *
      ENNReal.ofReal cMinus⁻¹.toReal < 1 := by
  have hCp : 0 ≤ cPlus.toReal := (ENNReal.toReal_pos hp0.ne' hpTop.ne).le
  calc
    ENNReal.ofReal cPlus.toReal * ENNReal.ofReal lam *
        ENNReal.ofReal cMinus⁻¹.toReal =
        ENNReal.ofReal (cPlus.toReal * lam * cMinus⁻¹.toReal) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hCp hlam),
            ENNReal.ofReal_mul hCp]
    _ = ENNReal.ofReal (lam * cPlus.toReal / cMinus.toReal) := by
      rw [ENNReal.toReal_inv, div_eq_mul_inv]
      congr 1
      ring
    _ < 1 := ENNReal.ofReal_lt_one.mpr hsmall

 

theorem aeEventIn_blockEvent_of_optima
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (cMinus cPlus : ℝ≥0∞)
    (hm0 : 0 < cMinus) (hmTop : cMinus < ⊤)
    (hp0 : 0 < cPlus) (hpTop : cPlus < ⊤)
    (hMinus : ∀ᵐ g ∂μ, OptimalConstants.Ratios.lowerOptimal (D g) (E g) = cMinus)
    (hPlus : ∀ᵐ g ∂μ, OptimalConstants.Ratios.upperOptimal (D g) (E g) = cPlus)
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (hR : 0 < T.rho * T.r) (hn : ‖T.orientation‖ = 1)
    (hRad : 0 ≤ T.blockRadius)
    (hLamPos : 0 ≤ C.lamConst) (hLam : C.lamConst < 1)
    (hSmall : C.lamConst * cPlus.toReal / cMinus.toReal < 1)
    (U : TopologicalSpace.Opens ℂ) (hUne : (U : Set ℂ).Nonempty)
    (hW : ∀ k ∈ Finset.Icc 1 Ksh,
      Metric.ball (0 : ℂ) (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆ U)
    (hWin : ∀ k ∈ Finset.Icc 1 Ksh,
      (Objects.ShieldLocality.shieldWindow (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) : Set ℂ) ⊆ U)
    (hKW : closure (Objects.Excursions.blockShape T) ⊆ U)
    (hCU : Metric.closedBall (Objects.Excursions.cU T) T.blockRadius ⊆ U)
    (hCV : Metric.closedBall (Objects.Excursions.cV T) T.blockRadius ⊆ U)
    (z : ℂ) :
    AEEventIn μ (fieldSigma0On id {y | y - z ∈ U})
      {g | Objects.Excursions.blockEvent C T Ksh Cmid0 D E z g} := by
  obtain ⟨hCp,hCi,hCmp⟩ := ae_optimal_comparison_real μ hμ ξ Q
    D E hD hE cMinus cPlus hm0 hmTop hp0 hpTop hMinus hPlus
  have hRatio := shield_ratio_of_optima cMinus cPlus hp0 hpTop
    C.lamConst hLamPos hSmall
  exact aeEventIn_blockEvent_modConst μ hμ ξ Q D E hD hE
    cPlus.toReal cMinus⁻¹.toReal hCp hCi hCmp C T Ksh Cmid0
    hR hn hRad hLam hRatio U hUne hW hWin hKW hCU hCV z

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
