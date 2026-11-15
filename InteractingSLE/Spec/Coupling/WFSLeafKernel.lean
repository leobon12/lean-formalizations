/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafLaw
import InteractingSLE.Spec.Sec7.Aux50Kernel

/-!
# The full-reference WFS kernel and the remaining through comparison

Theorem 1.5 may use Theorems 1.2–1.3 (R48). They already imply the
full-coupling clause of WFS at every measurable rule, including terminal rules.
No explicit terminal mean or covariance formula is required for that clause.

The final theorem is conditional: `hJoint` is the unproved whole-field comparison
for a through coupling. Neither a driving-marginal comparison nor the full
optional-coupling determination theorem discharges this hypothesis.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- The full-reference clause of WFS, for all tests and any measurable rule,
from Theorems 1.2–1.3. The rule need not be predictable or Galmarino. -/
theorem exists_full_ruleFieldKernel
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    {R : HistorySpace nL nR → ℝ≥0∞} (hR : Measurable R) :
    ∃ G : TestOn upperHalfPlaneOpens → HistorySpace nL nR → ℂ,
      (∀ φ, Measurable (G φ)) ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
        (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
        (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
        IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
        IsHistoryFieldKernel P h
          (killedHistory W VL VR (fun ω => min (R (killedHistory W VL VR ζ ω)) (ζ ω)))
          (fun γ φ => G φ γ) := by
  obtain ⟨Ω₀, m₀, hSB₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, href⟩ :=
    WholeFieldStopped.exists_isFamilyRef.{u} (ρL := ρL) (ρR := ρR) hκ hF
  have hC₀ := href.isOptionalHullCoupling hκ
  have hX₀ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₀.1
  obtain ⟨Ψ, hΨm, hΨ⟩ := Aux50.exists_isHistoryFieldKernel P₀ h₀
    (killedHistory W₀ VL₀ VR₀ (fun ω => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω)))
  refine ⟨fun φ γ => Ψ γ φ, hΨm, ?_⟩
  intro Ω mΩ P hP 𝓕 W VL VR B ζ h hC
  have hX := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC.1
  exact Aux50.isHistoryFieldKernel_of_map_eq hC₀.2.1 (measurable_ruleHistory hX₀ hR)
    hC.2.1 (measurable_ruleHistory hX hR) hΨm hΨ
    (map_field_ruleHistory_eq (Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ hF) hR hC₀ hC)

/-- Conditional WFS assembly. The explicit input `hJoint` is the remaining
whole-field comparison through the Galmarino cutoff, not just the already
proved equality of the driving marginals. It is not proved in this module.

Once that input is available, the conditional law holds at every test, so the
exceptional set may be empty and the dimension bound may be zero. -/
theorem throughKernelStatement_of_jointLaw
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ)
    (hJoint : ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
      (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
      ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
        (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
        (B : ℝ≥0 → Ω → ℝ) (ζ V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
        IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h →
        (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
      ∀ {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
        (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W₀ : ℝ≥0 → Ω₀ → ℝ)
        (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ)
        (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞) (h₀ : Ω₀ → DistOn upperHalfPlaneOpens),
        IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ →
        P.map (fun ω => (h ω, killedHistory W VL VR V ω)) =
          P₀.map (fun ω => (h₀ ω, killedHistory W₀ VL₀ VR₀
            (fun ω => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω)) ω))) :
    ThroughKernelStatement.{u, u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg
  obtain ⟨G, hGm, hKF⟩ := exists_full_ruleFieldKernel h12 h13 hκ hF hRm
  refine ⟨fun _ => ∅, G, 0, by norm_num, ?_, ?_, hGm, ?_, ?_⟩
  · intro γ
    simp only [closure_empty, empty_inter, subset_refl]
  · intro K _
    simp only [disjoint_empty, ofPred_true]
    exact MeasurableSet.univ
  · intro Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hV
    obtain ⟨Ω₀, m₀, hSB₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, href⟩ :=
      WholeFieldStopped.exists_isFamilyRef.{u} (ρL := ρL) (ρR := ρR) hκ hF
    have hC₀ := href.isOptionalHullCoupling hκ
    have hX₀ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₀.1
    have hker := Aux50.isHistoryFieldKernel_of_map_eq hC₀.2.1 (measurable_ruleHistory hX₀ hRm)
      hC.2.2.1 (measurable_killedHistory hC.2.2.2.2.choose) hGm
      (hKF P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀)
      (hJoint xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B ζ V h hC hV
        P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀).symm
    refine ⟨fun φ => (hker φ).mono fun _ hω _ => hω, ?_⟩
    exact ae_of_all _ fun _ _ _ _ => by
      simp only [empty_inter, dimH_empty, ENNReal.ofReal_zero, le_refl]
  · intro Ω mΩ P hP 𝓕 W VL VR B ζ h hC φ
    exact (hKF P 𝓕 W VL VR B ζ h hC φ).mono fun _ hω _ => hω

end InteractingSLE.WFS
