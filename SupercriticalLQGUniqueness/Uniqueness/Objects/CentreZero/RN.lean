import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T58c




 





set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero

open SupercriticalLQGUniqueness
open LQGMetric (DistC)

 

theorem rn_of_corrected_event {ξ : Set.Ioi (0 : ℝ)} {par : EndSaving.Interfaces.Parameters ξ}
    {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {hData : Objects.CorrectedEvent.DataMatch C T}
    {F : ℂ → DistC → Prop} {D D' : DistC → LSCMetric} {g : DistC}
    (h : Objects.CorrectedEvent.correctedEvent C T hData F D D' g)
    {Emax : ℝ} (hEnergy : LQGMetric.gradEnergy T.bump ≤ Emax)
    (hCrn : par.Crn = Real.exp (C.A_RN + Emax / 2)) :
    par.Crn⁻¹ ≤ LQGMetric.cmDensity T.bump (LQGMetric.pair0 g) ∧
      LQGMetric.cmDensity T.bump (LQGMetric.pair0 g) ≤ par.Crn := by
  have hWindow := Objects.CorrectedEvent.event_rn_window h Emax hEnergy
  have hEmax : 0 ≤ Emax :=
    (Objects.CorrectedEvent.bump_energy_nonneg T.bump).trans hEnergy
  constructor
  · simpa only [hCrn] using hWindow.1
  · rw [hCrn]
    exact hWindow.2.trans (Real.exp_le_exp.mpr (by linarith))

 

theorem rn_input_of_t57 {D D' : DistC → LSCMetric} {ξ : Set.Ioi (0 : ℝ)}
    {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ} {r : Set.Ioi (0 : ℝ)}
    {U₀ V₀ : TopologicalSpace.Opens ℂ} {f₀ : LQGMetric.TestC}
    {Target : Set DistC}
    (I : Objects.Producer.T57Inputs D D' ξ Q cMid par r U₀ V₀
      (LQGMetric.testCont f₀) Target)
    {Emax : ℝ} (hEnergy : LQGMetric.gradEnergy I.T.bump ≤ Emax)
    (hCrn : par.Crn = Real.exp (I.C.A_RN + Emax / 2))
    (hBump : f₀ = I.T.bump) :
    ∀ g ∈ Target, par.Crn⁻¹ ≤ LQGMetric.cmDensity f₀ (LQGMetric.pair0 g) ∧
      LQGMetric.cmDensity f₀ (LQGMetric.pair0 g) ≤ par.Crn := by
  intro g hg
  rw [hBump]
  exact rn_of_corrected_event (I.event g hg) hEnergy hCrn

end SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero
