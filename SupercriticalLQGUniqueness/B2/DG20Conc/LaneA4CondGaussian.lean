import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4Gaussian
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCoarseFineIndep

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneA4_conditional_coarse_phi_truncated_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) {K n : ℕ} (hKn : K ≤ n)
    (b : ℤ × ℤ) (ξ β : ℝ) :
    let X : Ω → ℝ := fun ω => phiMN W P 0 K (T20.dyCenter K b) ω
    let E : Set Ω := {ω | X ω ≤ β * ((K : ℝ) * Real.log 2)}
    ∀ᵐ ω ∂P,
      (∫⁻ x, ENNReal.ofReal
        (E.indicator (fun y => Real.exp (ξ * X y)) x)
        ∂(condExpKernel P (MeasurableSpace.comap
          (fun ω z => psiMN Qψ W P K n z ω)
          (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) ≤
      ENNReal.ofReal (Real.exp
        ((ξ * min ξ β - (min ξ β) ^ 2 / 2) *
          ((K : ℝ) * Real.log 2))) := by
  let X : Ω → ℝ := fun ω => phiMN W P 0 K (T20.dyCenter K b) ω
  let E : Set Ω := {ω | X ω ≤ β * ((K : ℝ) * Real.log 2)}
  let f : Ω → ℝ := E.indicator (fun y => Real.exp (ξ * X y))
  have hXm : Measurable X :=
    (isPhiVersion_phiMN hW (Nat.zero_le K)).meas _
  have hψ : Measurable (fun ω z => psiMN Qψ W P K n z ω) :=
    measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Qψ) hW hKn).meas
  have hE : @MeasurableSet Ω mΩ E := measurableSet_le hXm measurable_const
  obtain ⟨v, hv, hLaw⟩ := hasLaw_phiMN hW K (T20.dyCenter K b)
  have hIntExp : Integrable (fun ω => Real.exp (ξ * X ω)) P :=
    hLaw.integrable_comp (f := fun x => Real.exp (ξ * x))
      (integrable_exp_mul_gaussianReal ξ)
  have hInt : Integrable f P := hIntExp.integrableOn.integrable_indicator hE
  let mφ : MeasurableSpace Ω :=
    MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)
  have hXφ : @Measurable Ω ℝ mφ _ X := comap_measurable X
  have hEφ : @MeasurableSet Ω mφ E :=
    measurableSet_le hXφ measurable_const
  have hf : StronglyMeasurable[mφ] f :=
    ((hXφ.const_mul ξ).exp.stronglyMeasurable).indicator hEφ
  letI : MeasurableSpace Ω := mΩ
  have hInd : Indep mφ (MeasurableSpace.comap
      (fun ω z => psiMN Qψ W P K n z ω)
      (inferInstance : MeasurableSpace (ℂ → ℝ))) P :=
    laneC_indep_coarse_point_fine_field P W hW Qψ hKn b
  have hcond := laneC_conditional_lintegral_eq_of_indep P
    hXm.comap_le hψ.comap_le hf hInd hInt (by
      intro ω
      by_cases hω : ω ∈ E <;> simp [f, hω, Real.exp_nonneg])
  have hgauss := laneA4_coarse_phi_truncated_upper hW K
    (T20.dyCenter K b) ξ β
  filter_upwards [hcond] with ω hc
  change (∫⁻ x, ENNReal.ofReal (f x) ∂(condExpKernel P
    (MeasurableSpace.comap (fun ω z => psiMN Qψ W P K n z ω)
      (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) ≤
    ENNReal.ofReal (Real.exp
      ((ξ * min ξ β - (min ξ β) ^ 2 / 2) *
        ((K : ℝ) * Real.log 2)))
  rw [hc]
  have hrewrite : (∫⁻ x, ENNReal.ofReal (f x) ∂P) =
      ∫⁻ x in E, ENNReal.ofReal (Real.exp (ξ * X x)) ∂P := by
    rw [← lintegral_indicator hE]
    congr 1
    funext x
    by_cases hx : x ∈ E <;> simp [f, hx]
  rw [hrewrite]
  simpa only [X, E, hv] using hgauss

end SupercriticalLQGUniqueness.B2.DG20Conc
