import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleArithmetic

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_dyadic_two_sided_tight_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W)
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w) :
    SupercriticalLQGUniqueness.IsTwoSidedTight P
      (fun n : ℕ => fun ω =>
        ENNReal.ofReal (lambdaN ξ W P n)⁻¹ *
          lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w) := by
  constructor
  · intro n
    have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
    have hDm := pt_dist_measurable_lfppDOn_open (ξ : ℝ)
      U hU z w hφ.cont hφ.meas
    exact (measurable_const.mul hDm).aemeasurable
  · intro ε hε
    obtain ⟨Mup, hMup, hup⟩ :=
      pt_dist_dyadic_upper_tail_small_of_inputs
        hPerc hExp hPos ξ Q hQ P W hW U hU hUc z w hz hw ε hε
    obtain ⟨T, hT, hlow⟩ :=
      pt_dist_dyadic_lower_tail_small_of_inputs hPerc ξ U z w hzw ε hε
    let M : ℝ := max Mup T
    have hM : 0 < M := hMup.trans_le (le_max_left _ _)
    have hMupLe : Mup ≤ M := le_max_left _ _
    have hTLe : T ≤ M := le_max_right _ _
    refine ⟨M, hM, ?_⟩
    intro n
    let lam : ℝ := lambdaN ξ W P n
    have hlam : 0 < lam := lambdaN_pos hW n
    have hUpperSub :
        {ω | ENNReal.ofReal M < ENNReal.ofReal lam⁻¹ *
          lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w} ⊆
        {ω | ¬ lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w ≤
          ENNReal.ofReal (Mup * lam)} := by
      intro ω hω hgood
      have hnorm := pt_dist_rescale_upper_bound lam Mup hlam hMup.le _ hgood
      have hMle : ENNReal.ofReal Mup ≤ ENNReal.ofReal M :=
        ENNReal.ofReal_le_ofReal hMupLe
      exact (not_le_of_gt hω) (hnorm.trans hMle)
    have hInv : M⁻¹ ≤ T⁻¹ := inv_anti₀ (by linarith : 0 < T) hTLe
    have hLowerSub :
        {ω | ENNReal.ofReal lam⁻¹ *
          lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w <
            ENNReal.ofReal M⁻¹} ⊆
        {ω | lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w <
          ENNReal.ofReal (T⁻¹ * lam)} := by
      intro ω hω
      apply pt_dist_rescale_lower_event lam T hlam (by linarith)
      exact hω.trans_le (ENNReal.ofReal_le_ofReal hInv)
    constructor
    · exact (measure_mono hUpperSub).trans (hup n)
    · exact (measure_mono hLowerSub).trans (hlow (Ω := Ω) P W hW n)

end SupercriticalLQGUniqueness.B2.DG20Pt
