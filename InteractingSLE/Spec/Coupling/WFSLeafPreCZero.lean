/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPreCLaws

/-!
# Joint field-history identification at the zero cutoff

At zero the killed history is constant. Galmarino forces the same rule to
vanish on the reference histories, and the common GFF boundary data determine
the field marginal. No conditional-law clause or approximation input is used.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- The through/full joint-law comparison is unconditional at an almost surely
zero Galmarino cutoff. -/
theorem map_field_ruleHistory_eq_of_zero
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {R : HistorySpace nL nR → ℝ≥0∞} (hRg : IsHistGalmarino R)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    (hV : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω))
    (hzero : ∀ᵐ ω ∂P, V ω = 0)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀)} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hC₀ : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀) :
    P.map (fun ω => (h ω, killedHistory W VL VR V ω)) =
      P₀.map (fun ω => (h₀ ω, killedHistory W₀ VL₀ VR₀
        (fun ω => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω)) ω)) := by
  have hc : ∀ᵐ ω ∂P, IsKilledContHist (killedHistory W VL VR V ω) := by
    filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path] with ω hp
    exact isKilledContHist_killedHistory ((continuousOn_state_of_isSLEPathUpTo hp).mono
      (fun t ht => ht.trans_le (hC.2.1 ω)))
  obtain ⟨ω, hp, hs, hz⟩ := (hc.and (hV.and hzero)).exists
  have hr : ∃ γ, IsKilledContHist γ ∧ R γ = 0 :=
    ⟨killedHistory W VL VR V ω, hp, hs.symm.trans hz⟩
  have hR₀ : ∀ᵐ ω ∂P₀, R (killedHistory W₀ VL₀ VR₀ ζ₀ ω) = 0 := by
    filter_upwards [hC₀.1.isSLEEvolutionUpTo.ae_path] with ω hp
    exact rule_eq_zero_of_exists_zero hRg hr
      (isKilledContHist_killedHistory (continuousOn_state_of_isSLEPathUpTo hp))
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  have hf : P.map h = P₀.map h₀ := Exist.map_eq_of_isGFFWithBoundaryData
    ⟨hC.2.2.1, hC.2.2.2.1⟩ ⟨hC₀.2.1, hC₀.2.2.1⟩ hu₀
  apply map_pair_eq_of_ae_const hC.2.2.1 hC₀.2.1 hf (c := (0 : HistorySpace nL nR))
  · filter_upwards [hzero] with ω hω
    simp only [killedHistory, hω, not_lt_zero, ↓reduceIte]
    rfl
  · filter_upwards [hR₀] with ω hω
    change (min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω),
      fun p => if (dyadicTime p : ℝ≥0∞) <
        min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω)
      then (W₀ (dyadicTime p) ω, fun i => VL₀ i (dyadicTime p) ω, fun i => VR₀ i (dyadicTime p) ω)
      else 0) = 0
    simp only [hω, zero_min, not_lt_zero, ↓reduceIte]
    rfl

end InteractingSLE.WFS
