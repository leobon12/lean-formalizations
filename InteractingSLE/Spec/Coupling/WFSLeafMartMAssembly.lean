/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafMartMLaw

/-!
# Full-evolution cylinder regularity from Douglas's separation theorem

All SLE-specific hypotheses of the functional-analytic density argument are
proved. The sole named input is Douglas's L¹ separation theorem, [RY99]
Chapter V, Theorem (4.4), p. 210. The target is the existing, unchanged
`FullEvolutionCylinderRegularityStatement`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction

universe u

namespace InteractingSLE.WFS

open LawUnique

/-- Every integrable Borel full-history observable has continuous closed
means, using Douglas separation as the sole standard theorem input. -/
theorem fullHistory_mem_continuousClosedSpace_of_douglas
    (hDouglas : DouglasL1SeparationStatement.{u})
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    {f : HistorySpace nL nR → ℝ} (hf : Measurable f)
    (hi : Integrable (fun ω => f (killedHistory W VL VR ζ ω)) P) :
    (fun ω => f (killedHistory W VL VR ζ ω)) ∈
      continuousClosedSpace (drivingFiltration P hX) P := by
  apply mem_continuousClosedSpace_of_douglas hDouglas (drivingFiltration P hX)
    (fun t => Ito.nullSets_le_usualAugmentation (killedDrivingFiltration hX) P t) hi
  intro Q hQ hQP hmeans
  have he := map_killedHistory_eq_of_continuousClosedSpace_means hκ hF hE hX hQP hmeans
  have hm := measurable_killedHistory hX
  calc
    (∫ ω, f (killedHistory W VL VR ζ ω) ∂Q) =
        ∫ γ, f γ ∂Q.map (killedHistory W VL VR ζ) :=
      (integral_map hm.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ γ, f γ ∂P.map (killedHistory W VL VR ζ) := by rw [he]
    _ = ∫ ω, f (killedHistory W VL VR ζ ω) ∂P :=
      integral_map hm.aemeasurable hf.aestronglyMeasurable

/-- The requested full-evolution cylinder regularity, with only Douglas's
standard functional-analysis theorem left as an input. No SLE regularity,
martingale representation or filtration-identification input remains. -/
theorem fullEvolutionCylinderRegularityStatement_of_douglas
    (hDouglas : DouglasL1SeparationStatement.{u}) {κ : ℝ} (hκ : 0 < κ) :
    FullEvolutionCylinderRegularityStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF Ω mΩ P hP 𝓕 W VL VR B ζ hE n g
  have hX := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE
  have hY := measurable_killedHistory hX
  exact (fullHistory_mem_continuousClosedSpace_of_douglas hDouglas hκ hF hE hX
    (g.continuous.measurable.comp (measurable_historyWindow n))
    (integrable_historyWindow_comp hY g)).2

/-- The unchanged WFS endpoint with Douglas separation as its only new
standard theorem input, besides the permitted Theorems 1.2 and 1.3. -/
theorem throughKernelStatement_of_douglas
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hDouglas : DouglasL1SeparationStatement.{u}) {κ : ℝ} (hκ : 0 < κ) :
    ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_fullEvolutionCylinders h12 h13 hκ
    (fullEvolutionCylinderRegularityStatement_of_douglas hDouglas hκ)

end InteractingSLE.WFS
