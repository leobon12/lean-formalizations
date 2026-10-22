import HigherDimLQGMetric.LfppTight.CoupledHolderTail
import HigherDimLQGMetric.LfppTight.CoupledFarHolder

/-! A7(3): one Hölder tail for every real cutoff below one. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM)

theorem l6a_coupled_holder_all {d : ℕ} {κ : Rd d → ℝ} {ξ Q β : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε))
    (Ψ : Rd d → Ω → ℝ) (hΨc : ∀ ω, Continuous fun z => Ψ z ω)
    (hΨm : ∀ z, Measurable (Ψ z))
    {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x ∈ closedBall (0 : Rd d) r, ∃ y ∈ closedBall (0 : Rd d) r,
        M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
          DGZ.lfppMetric ξ (fun z => G ε z ω -
            W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y} ≤
        ENNReal.ofReal θ := by
  obtain ⟨Ms, εs, hεs, hs⟩ := l6a_coupled_holder_tail hDGZ hAdapter
    hβ0 hβ P W hW G hG Ψ hΨc hΨm hr hθ
  let a₀ : ℝ := min εs (1 / 4)
  have ha₀ : 0 < a₀ := lt_min hεs (by norm_num)
  have ha₀1 : a₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨Mf, hMf, hf⟩ := l6a_coupled_holder_far hDGZ hβ0 hβ1 P W hW G hG
    Ψ hΨc hΨm ha₀ ha₀1 hr hθ
  let M : ℝ := max (max Ms Mf) 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M, hM, ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 := hε
  have hA : 0 < DGZ.aHat P G ξ ε :=
    DGZ.aHat_pos (by have := hDGZ.dim; omega) hW (hG ε hε1) ξ
  have hscale (m : ℝ) (hm : m ≤ M) :
      {ω | ∃ x ∈ closedBall (0 : Rd d) r,
        ∃ y ∈ closedBall (0 : Rd d) r,
          M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
            DGZ.lfppMetric ξ (fun z => G ε z ω -
              W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y} ⊆
      {ω | ∃ x ∈ closedBall (0 : Rd d) r,
        ∃ y ∈ closedBall (0 : Rd d) r,
          m * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
            DGZ.lfppMetric ξ (fun z => G ε z ω -
              W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y} := by
    rintro ω ⟨x, hx, y, hy, hxy⟩
    refine ⟨x, hx, y, hy, ?_⟩
    have hpow : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hm hA.le) hpow) hxy
  by_cases hsmall : ε < εs
  · exact (measure_mono (hscale Ms (le_trans (le_max_left _ _) (le_max_left _ _)))).trans
      (hs ε ⟨hε.1, hsmall⟩)
  · have hεfar : ε ∈ Ico a₀ 1 :=
      ⟨(min_le_left _ _).trans (le_of_not_gt hsmall), hε1.2⟩
    exact (measure_mono (hscale Mf (le_trans (le_max_right _ _) (le_max_left _ _)))).trans
      (hf ε hεfar)

end HigherDimLQGMetric
