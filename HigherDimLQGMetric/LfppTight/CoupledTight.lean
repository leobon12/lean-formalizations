import HigherDimLQGMetric.LfppTight.CoupledHolderAll
import HigherDimLQGMetric.LfppTight.CoupledLaw
import HigherDimLQGMetric.DGZ.TightCompact

/-! Tightness of the explicitly coupled centred LFPP metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM)

theorem l6a_coupled_tight {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε))
    (Ψ : Rd d → Ω → ℝ) (hΨc : ∀ ω, Continuous fun z => Ψ z ω)
    (hΨm : ∀ z, Measurable (Ψ z)) :
    IsTightMeasureSet {μ : Measure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ioo (0 : ℝ) 1,
        μ = P.map (fun ω => DGZ.normMetricC ξ
          (l6a_coupledPhi κ W G Ψ ε · ω) (DGZ.aHat P G ξ ε))} := by
  have hd0 : 0 < d := by have := hDGZ.dim; omega
  have hξ : 0 < ξ := hDGZ.xi_pos
  have hgap : 0 < ξ * (Q - Real.sqrt (2 * d)) :=
    mul_pos hξ (by linarith [hDGZ.subcritical])
  let β : ℝ := min (1 / 2) (ξ * (Q - Real.sqrt (2 * d)) / 2)
  have hβ0 : 0 < β := lt_min (by norm_num) (by positivity)
  have hβ1 : β ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hβ : β < ξ * (Q - Real.sqrt (2 * d)) :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let S : Set (Measure C(Rd d × Rd d, ℝ)) :=
    {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
      μ = P.map (fun ω => DGZ.normMetricC ξ
        (l6a_coupledPhi κ W G Ψ ε · ω) (DGZ.aHat P G ξ ε))}
  change IsTightMeasureSet S
  have hmet : ∀ μ ∈ S, μ {f : C(Rd d × Rd d, ℝ) |
      ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z,
        f (x, z) ≤ f (x, y) + f (y, z))} = 0 := by
    rintro μ ⟨ε, hε, rfl⟩
    have hΦc (ω : Ω) : Continuous fun z => l6a_coupledPhi κ W G Ψ ε z ω :=
      ((hG ε hε).continuous ω).sub continuous_const |>.add (hΨc ω)
    have hΦm (z : Rd d) : Measurable fun ω => l6a_coupledPhi κ W G Ψ ε z ω :=
      ((hG ε hε).measurable z).sub (hW.measurable _) |>.add (hΨm z)
    have hFm := DGZ.measurable_normMetricC hΦc hΦm ξ (DGZ.aHat P G ξ ε)
    have hmeas := (DGZ.tc_isClosed_metricCond (X := Rd d)).isOpen_compl.measurableSet
    rw [show {f : C(Rd d × Rd d, ℝ) |
      ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z,
        f (x, z) ≤ f (x, y) + f (y, z))} =
      {f : C(Rd d × Rd d, ℝ) |
        (∀ x, f (x, x) = 0) ∧ ∀ x y z,
          f (x, z) ≤ f (x, y) + f (y, z)}ᶜ from rfl,
      Measure.map_apply hFm hmeas]
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    apply hω
    have ha : 0 ≤ (DGZ.aHat P G ξ ε)⁻¹ :=
      (inv_pos.2 (DGZ.aHat_pos hd0 hW (hG ε hε) ξ)).le
    refine ⟨fun x => ?_, fun x y z => ?_⟩
    · rw [DGZ.normMetricC_apply (hΦc ω), DGZ.lfppMetric_self, mul_zero]
    · rw [DGZ.normMetricC_apply (hΦc ω), DGZ.normMetricC_apply (hΦc ω),
        DGZ.normMetricC_apply (hΦc ω), ← mul_add]
      exact mul_le_mul_of_nonneg_left (DGZ.lfppMetric_triangle (hΦc ω) x y z) ha
  have hloc : ∀ (j : ℕ) (θ : ℝ), 0 < θ → ∃ Mj : ℝ, 0 ≤ Mj ∧ ∀ μ ∈ S,
      μ {f : C(Rd d × Rd d, ℝ) | ¬ ∀ x ∈ closedBall (0 : Rd d) j,
        ∀ y ∈ closedBall (0 : Rd d) j, f (x, y) ≤ Mj * dist x y ^ β} ≤
          ENNReal.ofReal θ := by
    intro j θ hθ
    obtain ⟨Mj, hMj, hbound⟩ := l6a_coupled_holder_all hDGZ hAdapter
      hβ0 hβ1 hβ P W hW G hG Ψ hΨc hΨm
      (r := (j : ℝ) + 1) (θ := θ) (by positivity) hθ
    refine ⟨Mj, hMj, ?_⟩
    rintro μ ⟨ε, hε, rfl⟩
    have hΦc (ω : Ω) : Continuous fun z => l6a_coupledPhi κ W G Ψ ε z ω :=
      ((hG ε hε).continuous ω).sub continuous_const |>.add (hΨc ω)
    have hΦm (z : Rd d) : Measurable fun ω => l6a_coupledPhi κ W G Ψ ε z ω :=
      ((hG ε hε).measurable z).sub (hW.measurable _) |>.add (hΨm z)
    have hFm := DGZ.measurable_normMetricC hΦc hΦm ξ (DGZ.aHat P G ξ ε)
    have hmeas := (DGZ.tc_isClosed_holderCond
      (β := β) (closedBall (0 : Rd d) j) Mj).isOpen_compl.measurableSet
    rw [show {f : C(Rd d × Rd d, ℝ) | ¬ ∀ x ∈ closedBall (0 : Rd d) j,
        ∀ y ∈ closedBall (0 : Rd d) j, f (x, y) ≤ Mj * dist x y ^ β} =
      {f : C(Rd d × Rd d, ℝ) | ∀ x ∈ closedBall (0 : Rd d) j,
        ∀ y ∈ closedBall (0 : Rd d) j, f (x, y) ≤ Mj * dist x y ^ β}ᶜ from rfl,
      Measure.map_apply hFm hmeas]
    refine le_trans (measure_mono fun ω hω => ?_) (hbound ε hε)
    change ¬ ∀ x ∈ closedBall (0 : Rd d) j,
      ∀ y ∈ closedBall (0 : Rd d) j,
        DGZ.normMetricC ξ (l6a_coupledPhi κ W G Ψ ε · ω)
          (DGZ.aHat P G ξ ε) (x, y) ≤ Mj * dist x y ^ β at hω
    push Not at hω
    obtain ⟨x, hx, y, hy, hlt⟩ := hω
    have ha := DGZ.aHat_pos hd0 hW (hG ε hε) ξ
    rw [DGZ.normMetricC_apply (hΦc ω), dist_eq_norm] at hlt
    refine ⟨x, closedBall_subset_closedBall (by norm_num) hx,
      y, closedBall_subset_closedBall (by norm_num) hy, ?_⟩
    have := (lt_inv_mul_iff₀ ha).1 hlt
    show Mj * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
      DGZ.lfppMetric ξ (l6a_coupledPhi κ W G Ψ ε · ω) x y
    linarith
  exact DGZ.isTightMeasureSet_of_holderBounds DGZ.tc_closedBall_mono
    DGZ.tc_closedBall_mem_nhds hβ0 hmet hloc

end HigherDimLQGMetric
