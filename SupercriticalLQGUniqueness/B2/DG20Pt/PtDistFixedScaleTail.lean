import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRealTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_fixed_scale_upper_tail_small
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ξ : Ioi (0 : ℝ))
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧
      P {ω | ¬ lfppDOn (ξ : ℝ)
        (fun y => phiMN W P 0 n y ω) U z w ≤
          ENNReal.ofReal (M * lambdaN ξ W P n)} ≤
        ENNReal.ofReal ε := by
  let D : Ω → ℝ≥0∞ := fun ω =>
    lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w
  let lam : ℝ := lambdaN ξ W P n
  have hlam : 0 < lam := lambdaN_pos hW n
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hDm : Measurable D :=
    pt_dist_measurable_lfppDOn_open (ξ : ℝ) U hU z w hφ.cont hφ.meas
  have hDfin (ω : Ω) : D ω ≠ ∞ :=
    pt_dist_internal_finite_of_open_connected (ξ : ℝ)
      (fun y => phiMN W P 0 n y ω) (hφ.cont ω) U hU hUc z w hz hw
  let f : Ω → ℝ := fun ω => (D ω).toReal / lam
  have hfm : Measurable f := hDm.ennreal_toReal.div_const lam
  obtain ⟨M, hM, htail⟩ :=
    pt_dist_measurable_real_upper_tail_small P f hfm ε hε
  refine ⟨M, hM, ?_⟩
  have hsub : {ω | ¬ D ω ≤ ENNReal.ofReal (M * lam)} ⊆
      {ω | M < f ω} := by
    intro ω hω
    have hbad : ENNReal.ofReal (M * lam) < D ω := lt_of_not_ge hω
    have hreal : M * lam < (D ω).toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (hDfin ω)).mp hbad
    dsimp [f]
    exact (lt_div_iff₀ hlam).mpr hreal
  exact (measure_mono hsub).trans htail

end SupercriticalLQGUniqueness.B2.DG20Pt
