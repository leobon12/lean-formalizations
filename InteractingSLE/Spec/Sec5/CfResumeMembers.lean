/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvConditional

/-!
# Locality under changes of versions and retained filtrations

Packet PROVE-CFCHART2, continuation. These adapters transport K2's member identities;
they do not assume that a characteristic-functional identity implies locality.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfResume

open Restart.DomainMarkov Restart.DomainMarkov.K2 CfChart CfConv Coupling LocalSets

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓐 𝓑 : Filtration ℝ≥0 mΩ} {F F' : Set Ω} {ζ ζ' : Ω → ℝ≥0∞}
  {W W' : ℝ≥0 → Ω → ℝ} {X X' : Ω → DistOn upperHalfPlaneOpens}

/-- Member identities are unchanged by a common almost sure change of all sample data. -/
theorem hasSafeMembers_congr_ae (h : HasSafeMembers P 𝓐 F ζ W X)
    (hF : F =ᵐ[P] F') (hζ : ζ =ᵐ[P] ζ')
    (hW : ∀ᵐ ω ∂P, ∀ t, W t ω = W' t ω) (hX : X =ᵐ[P] X') :
    HasSafeMembers P 𝓐 F' ζ' W' X' := by
  intro s Fb hFb D hD hsafe f Ξ
  have hs : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ (s : ℝ≥0∞) < ζ ω ∧
      Disjoint (ballsK Fb) (QuantumZipper.fwdHull
        (fun r : ℝ => W r.toNNReal ω) (s : ℝ)) := by
    filter_upwards [hsafe, hF, hζ, hW] with ω hω hFω hζω hWω hωD
    simpa only [hFω, hζω, hWω] using hω hωD
  have he : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))) =ᵐ[P]
        (fun ω => Complex.exp (Complex.I * (X' ω φ : ℂ))) := fun φ =>
    hX.mono fun ω hω => by dsimp only; rw [hω]
  calc
    _ = ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂P :=
      integral_congr_ae ((he _).symm.filter_mono MeasureTheory.ae_restrict_le)
    _ = _ := h s Fb hFb D hD hs f Ξ
    _ = _ := congrArg (fun z => projFactor (ballsOpen Fb) f Ξ * z)
      (integral_congr_ae ((he _).filter_mono MeasureTheory.ae_restrict_le))

/-- Locality passes to a filtration whose events agree almost surely with old events. -/
theorem hasSafeMembers_of_le_aeSigma (h : HasSafeMembers P 𝓐 F ζ W X)
    (hB : ∀ t, 𝓑 t ≤ aeSigma P (𝓐 t)) : HasSafeMembers P 𝓑 F ζ W X := by
  intro s Fb hFb D hD hsafe f Ξ
  obtain ⟨D₀, hD₀, he⟩ := hB s D hD
  have hs : ∀ᵐ ω ∂P, ω ∈ D₀ → ω ∈ F ∧ (s : ℝ≥0∞) < ζ ω ∧
      Disjoint (ballsK Fb) (QuantumZipper.fwdHull
        (fun r : ℝ => W r.toNNReal ω) (s : ℝ)) := by
    filter_upwards [hsafe, he] with ω hω heω hωD
    exact hω (heω.mpr hωD)
  rw [setIntegral_congr_set he, setIntegral_congr_set he]
  exact h s Fb hFb D₀ hD₀ hs f Ξ

/-- The conull-event and record enlargements used in the chart conversion preserve locality. -/
theorem hasSafeMembers_event_record {A : Set Ω} (hA : MeasurableSet A)
    (hAe : ∀ᵐ ω ∂P, ω ∈ A) {R : Type*} [MeasurableSpace R] {r : Ω → R}
    (hr : Measurable r) (hrec : ∀ t, MeasurableSpace.comap r inferInstance ≤ aeSigma P (𝓐 t))
    (h : HasSafeMembers P 𝓐 F ζ W X) :
    HasSafeMembers P (recordFiltration (eventFiltration 𝓐 A hA) r hr) F ζ W X := by
  apply hasSafeMembers_of_le_aeSigma h
  intro t
  exact sup_le (eventFiltration_le_aeSigma 𝓐 hA hAe t) (hrec t)

end InteractingSLE.Sec5.CfResume
