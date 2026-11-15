/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2Wire
import InteractingSLE.Spec.Supplement.CondDriverBridge

/-!
# Stopped K2 for an SB4 switch on the original probability space

The future ordinary piece is needed only through its available stop. This adapter
uses the landed stopped K2 and its flow-word bridge directly on the given space.
It retains the evolution, safe-law, locality, and announcing-sequence hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB

open Restart Restart.StoppedK2 Restart.StoppedExtend Restart.FCDet
open Restart.DomainMarkov Restart.DomainMarkov.K2

/-- The stopped upper piece is a flow line through its stop under almost every
retained conditional law. This is the direct-space form of the landed product
bridge; no full-lifetime coupling or unproved extension is used. -/
theorem ae_stoppedFlowLine_of_k2
    {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} {X Hc : Ω → DistOn upperHalfPlaneOpens}
    {c : Ω → BoundaryWord} {γ : Ω → ℝ≥0 → ℂ} {𝓗 : Filtration ℝ≥0 mΩ}
    (hE : IsRandomWordEvolutionUpTo κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B V)
    (hcont : ∀ᵐ ω ∂P, ω ∈ F → V ω ≠ ⊤ →
      ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
        (∀ i, ContinuousOn (VL i · ω) (Iic (V ω).toNNReal)) ∧
        ∀ j, ContinuousOn (VR j · ω) (Iic (V ω).toNNReal))
    (hX : Measurable X) (hV0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < V ω)
    {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0)
    (hW' : AdaptedBefore 𝓗' V W) (hVL' : ∀ i, AdaptedBefore 𝓗' V (VL i))
    (hVR' : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR X)
    (hmem : HasSafeMembers P 𝓗' F V W X)
    (hXP : IsMeasurableKilledDriving W VL VR V)
    {σ : ℕ → Ω → WithTop ℝ≥0}
    (hσ : ∀ n, IsStoppingTime (drivingFiltration P hXP) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω)
    (hσV : ∀ᵐ ω ∂P, ω ∈ F → ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, ω ∈ F →
      Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    (htype : ∀ᵐ ω ∂P, ω ∈ F → IsFlowType κ θ (c ω) (ΘL ω) (ΘR ω) ρL ρR)
    (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (htr : ∀ᵐ ω ∂P, ω ∈ F →
      IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      IsStoppedFlowLine κ (c ω₀).fn (c ω₀).jumps 0 θ
        (condExpKernel P 𝒢 ω₀) Hc γ V := by
  have h𝒢m : 𝒢 ≤ mΩ := hE.1.trans (𝓗.le 0)
  have hK := ae_isStoppedHullCoupling_k hE hcont hX hV0 h𝒢' hW' hVL' hVR'
    hlaw hmem hXP hσ hσm hσV hσlim
  have htr' := Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢m htr
  have hFν := Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢m hE.2.1
  filter_upwards [hK, htr', htype, hFν] with ω₀ hK₀ htr₀ htype₀ hF₀ hω₀
  obtain ⟨𝓕', W', VL', VR', B', hcpl, hag⟩ := hK₀ hω₀
  refine isStoppedFlowLine_of_isStoppedHullCoupling (htype₀ hω₀) hXH hcpl ?_
  filter_upwards [hag, htr₀, hF₀ hω₀] with ω hω hgen hωF
  exact isGeneratingTrace_congr (fun t ht => ((hω t ht.le).1).symm) (hgen hωF)

end InteractingSLE.Theorem14.SB
