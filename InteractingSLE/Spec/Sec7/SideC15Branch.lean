/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15ChartMeas
import InteractingSLE.Spec.Sec7.Aux119LiftMeas

/-!
# R90a: a measurable source branch for a general change pocket

PROVE-SIDE-COLLAR2. Use the existing measurable two-arc lift theorem in
the conjugate of the principal-logarithm pocket chart. The branch is
measurable for the same record as the walls and the original chart.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.SideC15

open SideC13 PocketStopField Lemma725RefChart Aux119Bdry PocketJordan PocketCoord

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The original flow branch is a measurable integer, with no constancy
assertion. This applies to every change pocket, independently of R.5's
particular test family. -/
theorem exists_measurable_branch_conjugate_pChart
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {A : Set Ω} {C : Ω → Set ℂ} {ψ Ψ : Ω → ℂ → ℂ}
    (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0)
    (hLm : ∀ t, Measurable fun ω => L ω t)
    (hA : MeasurableSet A) (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, SupercriticalConformalCovariance.IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hC : ∀ ω ∈ A, C ω = cfPocket (R ω) (L ω) r)
    (hF : ∀ ω ∈ A, IsFlowChart (R ω) (L ω) r (Ψ ω)
      (conjugateFlowChart (pChart A C ψ ω))) :
    ∃ n : Ω → ℤ, Measurable n ∧ ∀ ω ∈ A,
      Lemma71N.IsPocketBranch (L ω) (R ω) (conjugateFlowChart (pChart A C ψ ω)) (n ω) := by
  let c := pChart A C ψ
  have hc : ∀ ω, (c ω).IsConformal := fun ω => (pChart_props hCo hCH hψ ω).2.2.1
  have hm := measurableSet_mem_dom_pChart hCo hCH hψ hA hCm
  have hf := measurable_fwd_pChart hCo hCH hψ hA hψm
  have hl : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z) := by
    intro z
    have h0 := measurable_lift_shiftChart hCo hCH hψ hA hCm hψm
      (measurable_const (a := (0 : ℤ))) z
    simpa only [shiftChart, Int.cast_zero, mul_zero, sub_zero] using h0
  apply Aux119Lift.exists_measurable_isPocketBranch hLc hL0 hLm
    (fun ω => isConformal_conjugate (hc ω)) (fun _ => rfl)
    (measurableSet_mem_dom_conjugate hc hm) (measurable_fwd_conjugate hc hm hf)
    (measurable_lift_conjugate hc hm hf hl)
  intro ω hω
  have hD : IsDomainChart (cfPocket (R ω) (L ω) r) (c ω) := by
    refine ⟨hc ω, (hc ω).coe_dom.symm.trans ?_, pLog A C ψ ω, ?_, fun _ _ => rfl⟩
    · rw [(pChart_props hCo hCH hψ ω).2.2.2, ← hC ω hω]
      ext z
      simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]
    · rw [← hC ω hω]
      exact isDerivLog_pLog hCo hψ hω
  have hD' := isDomainChart_conjugate_pocket hD
  obtain ⟨ℓ, hℓ, hlift⟩ := hD'.2.2
  rw [hD'.coe_dom]
  exact ⟨⟨_, _, _, _, (hF ω hω).isTwoArcFrame⟩, ℓ, hℓ, fun z hz => hlift hz⟩

end InteractingSLE.Sec7.SideC15
