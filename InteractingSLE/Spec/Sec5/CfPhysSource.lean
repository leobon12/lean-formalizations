/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysField
import InteractingSLE.Spec.Sec5.CfCarryUpper

/-!
# Raw physical locality on the original probability space

Packet PROVE-CFCHART2. The reference theorem determines the flow's coarse data
from the field. Therefore the given joint law and the glued law agree on the
coarse product. Transfer the proved glued raw locality through that equality,
then use the exact sign and angle-shift identity for the image field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfPhys

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q CfGiven CfConv CfChart
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47 CrossCond.Theta
open Exist Exist.Staged Exist.StagedLaw
open Restart.DomainMarkov Restart.DomainMarkov.K2

/-- The exact raw physical member assertion, from the original couplings and
field-determined flow histories. No locality input is assumed. -/
theorem hasSafeMembers_imgField_coarse {κ θ : ℝ} {nL nR mL mR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h h' : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h')
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (h' ω))
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hreg : ∀ ω, IsRegularDriver ((fun t => W t ω), ζ ω))
    {N : Set Ω} (hN : P N = 0) (hm : coarseSigma h' W VL VR ζ N ≤ mΩ)
    {s : ℝ≥0} {E : Set (Coarse (coarseSigma h' W VL VR ζ N) × HistorySpace 0 0)}
    (hE : MeasurableSet E) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hEae : ∀ᵐ ω ∂P, (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω) ∈ E) :
    HasSafeMembers P
      (Coupling.filtrationComap
        (qRaw (Ω := Coarse (coarseSigma h' W VL VR ζ N)) xL' xR' W VL VR ζ s E)
        ((measurable_toCoarse hm).prodMk
          (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf))))
      univ (fun ω => qT W VL VR ζ s E
        (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω))
      (fun t ω => qW W VL VR ζ s E t
        (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω))
      (fun ω => imgField κ (recOf (s : ℝ≥0∞) ((fun t => W t ω), ζ ω)) (h ω)) := by
  have hXe : (fun ω => cfFieldT κ θ (h' ω)) = h := funext fun ω => by
    rw [Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)]
    exact RestartGen.cfFieldT_flowField κ θ (h ω)
  have hcf' : IsCenteredCounterflowDriver κ P (fun ω => cfFieldT κ θ (h' ω)) W' ζ' := by
    rw [hXe]
    exact hcf
  have hY := measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)
  have hXm : Measurable fun ω => cfFieldT κ θ (h' ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  let k := condDistrib (cfHistory W' ζ') (fun ω => cfFieldT κ θ (h' ω)) P
  have hk : P.map (fun ω => (cfFieldT κ θ (h' ω), cfHistory W' ζ' ω)) =
      P.map (fun ω => cfFieldT κ θ (h' ω)) ⊗ₘ k :=
    (compProd_map_condDistrib hXm.aemeasurable hY.aemeasurable).symm
  obtain ⟨Ψ, hΨm, hΨ⟩ := Sec7.Lemma71H.hasFieldDeterminedHistories_of_cond44
    href hκ hκ4 hF h44 P 𝓕 W VL VR B ζ h' hC
  have hinv : ∀ f : DistOn upperHalfPlaneOpens, Exist.flowField 0 (θ * chiC κ) (cfFieldT κ θ f) = f := by
    intro f
    rw [cfFieldT, flowField_zero_flowField_zero, add_neg_cancel, flowField_zero_zero]
  have hmX : coarseSigma h' W VL VR ζ N ≤ fieldNullSigma P (fun ω => cfFieldT κ θ (h' ω)) := by
    refine coarseSigma_le_fieldNullSigma (g := Exist.flowField 0 (θ * chiC κ))
      (Exist.measurable_flowField _ _) (ae_of_all _ fun ω => (hinv (h' ω)).symm) hN
      (Ψ := fun x => Ψ (Exist.flowField 0 (θ * chiC κ) x))
      (hΨm.comp (Exist.measurable_flowField _ _)) ?_
    filter_upwards [hΨ] with ω hω
    simpa only [hinv] using hω
  let μ := glueMeasure P k (fun ω => cfFieldT κ θ (h' ω)) hXm
  have hlaw : μ.map (fun p => (toCoarse (coarseSigma h' W VL VR ζ N) p.1, p.2)) =
      P.map (fun ω => (toCoarse (coarseSigma h' W VL VR ζ N) ω, cfHistory W' ζ' ω)) :=
    map_glue_coarse_eq hXm hY k hk hm hmX
  have hg₁ : Measurable fun p : Ω × HistorySpace 0 0 =>
      (toCoarse (coarseSigma h' W VL VR ζ N) p.1, p.2) :=
    ((measurable_toCoarse hm).comp measurable_fst).prodMk measurable_snd
  have hg₂ := (measurable_toCoarse hm).prodMk hY
  have hgood : ∀ᵐ p ∂μ, p ∈ E := by
    have h1 := (ae_map_iff hg₂.aemeasurable hE).2 hEae
    rw [← hlaw] at h1
    exact (ae_map_iff hg₁.aemeasurable hE).1 h1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hEae.mono fun ω hω => (hEg _ hω).1.1
  have hreg' := ae_cfRegT hκ hθb hC hcf' rfl
  have hmem := hasSafeMembers_cfGlueT (s := s) (xL' := xL') (xR' := xR')
    hC hκ hζ hcf' hreg' rfl k hk hEg hgood ((π - θ) * chiC κ) (chiC κ)
  have hneg := hasSafeMembers_neg hmem
  let X : Coarse (coarseSigma h' W VL VR ζ N) × HistorySpace 0 0 → DistOn upperHalfPlaneOpens :=
    fun p => -Chart.chartTransport
      (isConformal_fChart (W := W) (VL := VL) (VR := VR) (ζ := ζ) (s := s) p)
      1 ((π - θ) * chiC κ) (chiC κ) (h' p.1)
  have hX : Measurable X := LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((LQGMetric.measurable_distOn_apply φ).comp
      (measurable_fChart_transport (Ω := Coarse (coarseSigma h' W VL VR ζ N))
        isMeasurableKilledDriving_coarse measurable_field_coarse ((π - θ) * chiC κ) (chiC κ))).neg
  have hraw := hasSafeMembers_coarse_of_glue hY hm isMeasurableKilledDriving_coarse hE hEg hlaw hX hneg
  refine CfResume.hasSafeMembers_congr_ae hraw (ae_eq_refl _) (ae_eq_refl _) (ae_of_all _ fun _ _ => rfl) ?_
  filter_upwards [hEae] with ω hω
  exact (imgField_eq_neg_fChart hκ (hEg _ hω) (hreg ω) (htr ω)).symm

end InteractingSLE.Sec5.CfPhys
