/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVStmt
import InteractingSLE.Spec.Restart.StoppedK2Evol
import InteractingSLE.Spec.Restart.StoppedK2ClauseLaw
import InteractingSLE.Spec.Restart.StoppedK2Wire

/-!
# The converse kernel passes to the reference driving filtration

The tower argument of `Lemma71J.condExp_clause_of_isCouplingCharFun` needs
only regularity, not the full evolution. The existing regularity-only
`Aux79.exists_stopped_measurable` supplies exactly its measurability input.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open Coupling Ito
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- Restrict a pre-stop characteristic kernel to the smaller driving filtration. -/
theorem isCouplingCharFun_driving_of_le
    (hX : IsMeasurableKilledDriving W VL VR ζ) {𝓖 : Filtration ℝ≥0 mΩ}
    (hle : drivingFiltration P hX ≤ 𝓖)
    (hreg : ∀ᵐ ω ∂P, DomainMarkov.Aux79.IsForceReg W VL VR ζ ω)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
    : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P (drivingFiltration P hX) W VL VR ζ h := by
  intro τ hτ hτζ uτ huτ φ
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  obtain ⟨E', hE'm, hE'sub, hE'ae, -, -, hE'sm⟩ :=
    DomainMarkov.Aux79.exists_stopped_measurable hreg
      (Coupling.adaptedBefore_killedDriving_W hX)
      (Coupling.adaptedBefore_killedDriving_VL hX)
      (Coupling.adaptedBefore_killedDriving_VR hX) φ hτ hτζ uτ huτ
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((LQGMetric.measurable_distOn_apply φ).comp hh)))
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => (Coupling.norm_cexp_I_mul_ofReal _).le)
  have hτ𝓖 : IsStoppingTime 𝓖 τ := fun t => hle t _ (hτ t)
  have hσle := Ito.measurableSpace_le_of_filtration_le hle hτ hτ𝓖
  have hcl := hcf _ hτ𝓖 hτζ uτ huτ φ
  set g : Ω → ℂ := E'.indicator (Coupling.frozenRHS κ W uτ φ τ') with hg
  have hgm : StronglyMeasurable[hτ.measurableSpace] g := hE'sm
  have hE'mΩ : MeasurableSet E' := hτ.measurableSpace_le _ hE'm
  have hE'τ' : MeasurableSet[hτ𝓖.measurableSpace] E' := hσle _ hE'm
  -- on the larger σ-algebra, the indicator of the identity
  have h1 : condExp hτ𝓖.measurableSpace P (E'.indicator f) =ᵐ[P] g := by
    filter_upwards [condExp_indicator (m := hτ𝓖.measurableSpace) (μ := P) hfint hE'τ', hcl]
      with ω hω hω'
    rw [hω, hg]
    by_cases hmem : ω ∈ E'
    · rw [indicator_of_mem hmem, indicator_of_mem hmem]
      exact hω' (hE'sub hmem)
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem]
  have hgint : Integrable g P := (integrable_condExp).congr h1
  -- the tower property
  have h2 : condExp hτ.measurableSpace P (E'.indicator f) =ᵐ[P] g := by
    have ht := condExp_condExp_of_le (μ := P) (f := E'.indicator f) hσle hτ𝓖.measurableSpace_le
    refine ht.symm.trans ?_
    refine (condExp_congr_ae h1).trans ?_
    rw [condExp_of_stronglyMeasurable hτ.measurableSpace_le hgm hgint]
  have hind := condExp_indicator (m := hτ.measurableSpace) (μ := P) hfint hE'm
  filter_upwards [h2, hind, hE'ae] with ω hω2 hωi hω3 hdis
  have hω : ω ∈ E' := hω3 hdis
  have e1 : condExp hτ.measurableSpace P f ω = E'.indicator (condExp hτ.measurableSpace P f) ω :=
    (indicator_of_mem hω _).symm
  rw [e1, ← hωi, hω2, hg, indicator_of_mem hω]
  rfl

end InteractingSLE.Restart.FlowStopIdentCMI
