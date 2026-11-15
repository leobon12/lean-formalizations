/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessTraceLocal
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownian

/-!
# §7.3 / Lemma LP9: the trace of the retargeted driver

Packet PROVE-SEC7-C10 (step R5 of `planning/handoffs/PROVE-SEC7-C8.md`; Specification §7.3, p. 379: "the transformed
continuity and transience assertion has already been proved"; supplement Lemma LP9, p. 486: "Use the complete
transformed law until …"). For an integrated evolution of a distinct-position word, the retargeted driver
`W̃ = M(W) ∘ C⁻¹` (`Zhan.Retarget.newW`) is, before the new horizon `T̃ = C(τ_sep)`, the driver of a local evolution of
LP9's transformed word on `Ω × Ω` (`Zhan.Retarget.retargetEvolutionStatement`). When the transformed word is complete
and its start is separated, `W̃` almost surely has a generating trace on `[0, T̃]`, transient when `T̃ = ∞`
(`ae_newW_trace`), by `Sec2.IsSLEEvolutionUpTo.ae_trace_of_complete`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

open Zhan.Retarget

/-- An almost-sure property of the first coordinate under `P ⊗ P` holds `P`-almost surely. -/
theorem ae_of_ae_prod_fst {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Φ : Ω → Prop} (h : ∀ᵐ p ∂(P.prod P), Φ p.1) : ∀ᵐ ω ∂P, Φ ω := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with ω hω
  obtain ⟨_, h'⟩ := hω.exists
  exact h'

/-- **R5 for LP9's retargeting.** For an integrated evolution of a distinct-position word whose transformed word
(LP9) is complete and has a separated start, the retargeted driver almost surely has a generating trace on `[0, T̃]`,
`T̃` the new horizon of the separation time, transient when `T̃ = ∞`. -/
theorem ae_newW_trace {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ : 0 < κ)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hsepT : ∀ i i', LP.retargetXL xL xR i < LP.retargetXR xR i')
    (hcT : LP.IsCompleteForceWord.{u} κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
      (LP.retargetρR ρR)) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (newW xR (fun t => W t ω) (fun i t => VR i t ω))
        (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
          (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω))) η ∧
      (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
          (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω)) = ⊤ →
        Tendsto (fun t => ‖η t‖) atTop atTop) := by
  obtain ⟨𝓘, β, τ, -, hτ, hloc⟩ :=
    retargetEvolutionStatement.{u} P 𝓕 xL xR ρL ρR W VL VR B ζ hκ hD hj hE
  have hF := (LP.isDistinctForceWord_retarget hD hj).1
  have htr := hloc.ae_trace_of_complete hκ hF hsepT hcT
  have hτ' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hτ
  refine ae_of_ae_prod_fst (Φ := fun ω => ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (newW xR (fun t => W t ω) (fun i t => VR i t ω))
        (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
          (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω))) η ∧
      (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
          (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω)) = ⊤ →
        Tendsto (fun t => ‖η t‖) atTop atTop)) ?_
  filter_upwards [htr, hτ'] with p hp hτp
  rw [← hτp]
  exact hp

end Sec7

end InteractingSLE
