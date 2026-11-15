/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofAssembly

/-!
# Conditioning the stopped K2 inputs on an initial type event

Packet PROVE-RETPLUMB. Both protected Gaussian identities and local-set member
identities pass to the normalized restriction on an initial event. This removes
the `F` versus `univ` discrepancy in stopped K2 without a new mathematical input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open LQGMetric (DistOn TestOn)
open DomainMarkov DomainMarkov.K2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Normalize a set integral by intersecting its domain with the conditioning
event. No measurability or integrability of the integrand is being inferred. -/
theorem setIntegral_cond_inter {M D : Set Ω} (hD : MeasurableSet D) (f : Ω → ℂ) :
    ∫ ω in D, f ω ∂P[|M] = (P M)⁻¹.toReal • ∫ ω in D ∩ M, f ω ∂P := by
  rw [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure,
    Measure.restrict_restrict hD]

/-- K2's (S) restricts to a smaller live event. -/
theorem hasSafeLaw_mono_event {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓗 : Filtration ℝ≥0 mΩ}
    {F M : Set Ω} {V : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hMF : M ⊆ F)
    (h : HasSafeLaw κ ρL ρR P 𝓗 F V W VL VR X) :
    HasSafeLaw κ ρL ρR P 𝓗 M V W VL VR X := by
  intro ψ q D hD hsafe
  exact h ψ q D hD (hsafe.mono fun _ hω hDω => ⟨hMF (hω hDω).1, (hω hDω).2⟩)

/-- K2's (L) restricts to a smaller live event. -/
theorem hasSafeMembers_mono_event {𝓗 : Filtration ℝ≥0 mΩ} {F M : Set Ω}
    {V : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {X : Ω → DistOn upperHalfPlaneOpens}
    (hMF : M ⊆ F) (h : HasSafeMembers P 𝓗 F V W X) :
    HasSafeMembers P 𝓗 M V W X := by
  intro s Fb hFb D hD hsafe f Ξ
  exact h s Fb hFb D hD
    (hsafe.mono fun _ hω hDω => ⟨hMF (hω hDω).1, (hω hDω).2⟩) f Ξ

/-- On an initial event, K2's (S) becomes an identity on the whole conditional
probability space. In particular, no conditional Gaussian-law premise is added. -/
theorem hasSafeLaw_cond [IsFiniteMeasure P] {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓗 : Filtration ℝ≥0 mΩ}
    {M : Set Ω} {V : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hM : MeasurableSet[𝓗 0] M)
    (h : HasSafeLaw κ ρL ρR P 𝓗 M V W VL VR X) :
    HasSafeLaw κ ρL ρR P[|M] 𝓗 univ V W VL VR X := by
  have hMm : MeasurableSet M := 𝓗.le 0 _ hM
  intro ψ q D hD hsafe
  have hMq : MeasurableSet[𝓗 q] M := 𝓗.mono zero_le _ hM
  have hsafeP := FCDet.ae_imp_of_ae_cond hMm hsafe
  have he := h ψ q (D ∩ M) (hD.inter hMq)
    (hsafeP.mono fun _ hω hDM => ⟨hDM.2, (hω hDM.2 hDM.1).2⟩)
  rw [setIntegral_cond_inter (𝓗.le q _ hD), setIntegral_cond_inter (𝓗.le q _ hD), he]

/-- The same conditioning operation preserves all member identities (L). -/
theorem hasSafeMembers_cond [IsFiniteMeasure P] {𝓗 : Filtration ℝ≥0 mΩ}
    {M : Set Ω} {V : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hM : MeasurableSet[𝓗 0] M)
    (h : HasSafeMembers P 𝓗 M V W X) : HasSafeMembers P[|M] 𝓗 univ V W X := by
  have hMm : MeasurableSet M := 𝓗.le 0 _ hM
  intro s Fb hFb D hD hsafe f Ξ
  have hMs : MeasurableSet[𝓗 s] M := 𝓗.mono zero_le _ hM
  have hsafeP := FCDet.ae_imp_of_ae_cond hMm hsafe
  have he := h s Fb hFb (D ∩ M) (hD.inter hMs)
    (hsafeP.mono fun _ hω hDM => ⟨hDM.2, (hω hDM.2 hDM.1).2⟩) f Ξ
  rw [setIntegral_cond_inter (𝓗.le s _ hD), setIntegral_cond_inter (𝓗.le s _ hD), he,
    mul_smul_comm]

end InteractingSLE.Restart.RetAux79
