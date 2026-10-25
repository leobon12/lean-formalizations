import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4GoodMax

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneA4_good_conditional_gaussian_le
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) {K n : ℕ} (hKn : K ≤ n)
    (b : ℤ × ℤ) (ξ β : ℝ)
    (F E : Set Ω) (Y : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hhit : F ∩ E ⊆
      {ω | phiMN W P 0 K (T20.dyCenter K b) ω ≤
        β * ((K : ℝ) * Real.log 2)})
    (hregular : ∀ ω ∈ E, Y ω ≤ c * ENNReal.ofReal
      (Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω))) :
    ∀ᵐ ω ∂P,
      (∫⁻ x, (F ∩ E).indicator Y x
        ∂(condExpKernel P (MeasurableSpace.comap
          (fun ω z => psiMN Qψ W P K n z ω)
          (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) ≤
      c * ENNReal.ofReal (Real.exp
        ((ξ * min ξ β - (min ξ β) ^ 2 / 2) *
          ((K : ℝ) * Real.log 2))) := by
  let Φ : Ω → ℝ := fun ω => phiMN W P 0 K (T20.dyCenter K b) ω
  let H : Set Ω := {ω | Φ ω ≤ β * ((K : ℝ) * Real.log 2)}
  let X : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (ξ * Φ ω))
  have hΦm : Measurable Φ :=
    (isPhiVersion_phiMN hW (Nat.zero_le K)).meas _
  have hHm : MeasurableSet H := measurableSet_le hΦm measurable_const
  have hXm : Measurable X :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul hΦm))
  have hmain (ω : Ω) :
      (∫⁻ x, (F ∩ E).indicator Y x
        ∂(condExpKernel P (MeasurableSpace.comap
          (fun ω z => psiMN Qψ W P K n z ω)
          (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) ≤
      c * (∫⁻ x, H.indicator X x
        ∂(condExpKernel P (MeasurableSpace.comap
          (fun ω z => psiMN Qψ W P K n z ω)
          (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) :=
    laneA4_good_conditional_integral_le _ F E H X Y c
      hHm hXm hhit hregular
  have hgauss := laneA4_conditional_coarse_phi_truncated_upper
    P W hW Qψ hKn b ξ β
  filter_upwards [hgauss] with ω hg
  have hsame : (fun x => H.indicator X x) =
      (fun x => ENNReal.ofReal
        (H.indicator (fun y => Real.exp (ξ * Φ y)) x)) := by
    funext x
    by_cases hx : x ∈ H <;> simp [H, X, hx]
  have hgauss' :
      (∫⁻ x, H.indicator X x
        ∂(condExpKernel P (MeasurableSpace.comap
          (fun ω z => psiMN Qψ W P K n z ω)
          (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) ≤
      ENNReal.ofReal (Real.exp
        ((ξ * min ξ β - (min ξ β) ^ 2 / 2) *
          ((K : ℝ) * Real.log 2))) := by
    rw [hsame]
    simpa only [H, Φ] using hg
  exact (hmain ω).trans (mul_le_mul_of_nonneg_left hgauss' bot_le)

end SupercriticalLQGUniqueness.B2.DG20Conc
