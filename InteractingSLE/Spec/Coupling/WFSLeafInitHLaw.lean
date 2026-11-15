/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafInitHCondition

/-!
# The full history law is unchanged by an initial event

Conditioning preserves the evolution, and uniqueness in law identifies its
full killed history. Measurable real functions of that history consequently
have constant conditional expectations given any initial subalgebra.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique

/-- An observable whose law is unchanged by every nonnull conditioning event
of `m` has constant conditional mean given `m`. -/
theorem condExp_eq_integral_of_cond_map_eq
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {Z : Ω → ℝ} (hZ : Measurable[mΩ] Z)
    (hlaw : ∀ A, MeasurableSet[m] A → P A ≠ 0 → (P[|A]).map Z = P.map Z) :
    P[Z | m] =ᵐ[P] fun _ => ∫ ω, Z ω ∂P := by
  have hind : Indep (MeasurableSpace.comap Z inferInstance) m P := by
    apply LQGMetric.MarkovIndep.indep_of_map_restrict_eq hZ
    intro A hA
    change (P.restrict A).map Z = P A • P.map Z
    by_cases hPA : P A = 0
    · rw [Measure.restrict_eq_zero.2 hPA, Measure.map_zero, hPA, zero_smul]
    · have he := congrArg (fun μ : Measure ℝ => P A • μ) (hlaw A hA hPA)
      rw [ProbabilityTheory.cond, Measure.map_smul, smul_smul,
        ENNReal.mul_inv_cancel hPA (measure_ne_top P A), one_smul] at he
      exact he
      exact hZ.aemeasurable
  exact condExp_indep_eq hZ.comap_le hm (comap_measurable Z).stronglyMeasurable hind

/-- Initial-event conditioning leaves the entire full killed-history law
unchanged, by uniqueness in law for the ordered force word. -/
theorem map_killedHistory_cond_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {A : Set Ω} (hA : MeasurableSet[usualAugmentation 𝓕 P 0] A) (hPA : P A ≠ 0) :
    (P[|A]).map (killedHistory W VL VR ζ) = P.map (killedHistory W VL VR ζ) := by
  have : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hPA
  have hX := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE
  exact map_killedHistory_eq (Sec4.killedStateLawUnique_of_isOrderedForceWord hκ ρL ρR hF)
    (isIntegratedSLEEvolution_cond_initial
      (Ito.isIntegratedSLEEvolution_usualAugmentation hE) hA hPA) hX hE hX

/-- Every Borel real function of the full killed history has constant
conditional mean given an initial subalgebra of the ambient augmentation. -/
theorem condExp_history_eq_integral_initial
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hm : m ≤ usualAugmentation 𝓕 P 0)
    {f : HistorySpace nL nR → ℝ} (hf : Measurable f) :
    P[fun ω => f (killedHistory W VL VR ζ ω) | m] =ᵐ[P]
      fun _ => ∫ ω, f (killedHistory W VL VR ζ ω) ∂P := by
  have hY := measurable_killedHistory
    (Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE)
  apply condExp_eq_integral_of_cond_map_eq (hm.trans ((usualAugmentation 𝓕 P).le 0))
    (hf.comp hY)
  intro A hA hPA
  have he := congrArg (fun μ => μ.map f)
    (map_killedHistory_cond_initial hκ hF hE (hm _ hA) hPA)
  rwa [Measure.map_map hf hY, Measure.map_map hf hY] at he

end InteractingSLE.WFS
