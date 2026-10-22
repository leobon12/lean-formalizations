import HigherDimLQGMetric.LfppTight.CoupledPoint

/-! Quantitative two-sided point-distance tails for the coupled centered LFPP metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM e₁)

theorem l6a_coupled_point_tails {d : ℕ} {κ : Rd d → ℝ} {ξ Q β : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε))
    (Ψ : Rd d → Ω → ℝ) (hΨc : ∀ ω, Continuous fun z => Ψ z ω)
    (hΨm : ∀ z, Measurable (Ψ z))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ m M ε₀ : ℝ, 0 < m ∧ 0 ≤ M ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        P {ω | DGZ.lfppMetric ξ (fun z => G ε z ω -
          W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω)
          0 (e₁ d) < m * DGZ.aHat P G ξ ε ∨
          M * DGZ.aHat P G ξ ε <
            DGZ.lfppMetric ξ (fun z => G ε z ω -
              W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω)
              0 (e₁ d)} ≤ ENNReal.ofReal θ := by
  have hq : 0 < θ / 2 := by positivity
  obtain ⟨m, εs, hm, hεs, hs⟩ :=
    l6a_coupled_shell_tail hDGZ hAdapter hβ0 hβ P W hW G hG Ψ hΨc hΨm hq
  obtain ⟨M, εh, hεh, hh⟩ :=
    l6a_coupled_holder_tail hDGZ hAdapter hβ0 hβ P W hW G hG Ψ hΨc hΨm
      (r := 2) (θ := θ / 2) (by norm_num) hq
  let M' : ℝ := max M 1
  let ε₀ : ℝ := min εs (min εh (1 / 2))
  have hM' : 0 ≤ M' := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hε₀ : 0 < ε₀ := lt_min hεs (lt_min hεh (by norm_num))
  refine ⟨m, M', ε₀, hm, hM', hε₀, ?_⟩
  intro ε hε
  have hεs' : ε ∈ Ioo (0 : ℝ) εs :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hεh' : ε ∈ Ioo (0 : ℝ) εh :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨hε.1, hε.2.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (by norm_num)))⟩
  have hd0 : 0 < d := by have hd2 := hDGZ.dim; omega
  let D : Ω → ℝ := fun ω => DGZ.lfppMetric ξ (fun z => G ε z ω -
      W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) 0 (e₁ d)
  let E₁ : Set Ω := {ω | DGZ.lfppSetDist ξ
    (fun z => G ε z ω -
      W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω)
    univ (sphere (0 : Rd d) (1 / 2)) (sphere 0 1) ≤
      m * DGZ.aHat P G ξ ε}
  let E₂ : Set Ω := {ω | ∃ x ∈ closedBall (0 : Rd d) 2,
    ∃ y ∈ closedBall (0 : Rd d) 2,
      M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
        DGZ.lfppMetric ξ (fun z => G ε z ω -
          W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y}
  have hsub : {ω | D ω < m * DGZ.aHat P G ξ ε ∨
      M' * DGZ.aHat P G ξ ε < D ω} ⊆ E₁ ∪ E₂ := by
    intro ω hw
    rcases hw with hw | hw
    · left
      exact (l6a_shell_le_point hDGZ.dim ξ _
        (((hG ε hε1).continuous ω).sub continuous_const |>.add (hΨc ω))).trans hw.le
    · right
      refine ⟨0, mem_closedBall_self (by norm_num), e₁ d, ?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right, HigherDimLFPP.norm_e₁ hd0]
        norm_num
      · have hnorm : ‖(0 : Rd d) - e₁ d‖ ^ β = 1 := by
          rw [zero_sub, norm_neg, HigherDimLFPP.norm_e₁ hd0]
          simp
        rw [hnorm, mul_one]
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right (le_max_left M 1) (le_of_lt
            (DGZ.aHat_pos hd0 hW (hG ε hε1) ξ))) hw
  calc
    P {ω | D ω < m * DGZ.aHat P G ξ ε ∨
      M' * DGZ.aHat P G ξ ε < D ω} ≤ P (E₁ ∪ E₂) := measure_mono hsub
    _ ≤ P E₁ + P E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
      add_le_add (hs ε hεs') (hh ε hεh')
    _ = ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_add hq.le hq.le]
      congr 1
      ring

end HigherDimLQGMetric
