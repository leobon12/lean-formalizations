/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafInitHLaw

/-!
# WFS from continuous closed-process existence alone

The initial conditional mean is proved constant. Positive killing preserves
the initial germ, and uniqueness in law makes full-history observables
independent of the initial filtration. Galmarino reads the cutoff from that
full history. Continuous closed-process existence is the remaining input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- A self-consistent Galmarino cutoff is read unchanged from its own full
continuation history. This is the defining Galmarino test on the two histories. -/
theorem ae_rule_full_eq_of_self
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞}
    {R : HistorySpace nL nR → ℝ≥0∞} (hRg : IsHistGalmarino R)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω)
      {t | (t : ℝ≥0∞) < ζ ω})
    (hVζ : ∀ ω, V ω ≤ ζ ω)
    (hself : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) :
    ∀ᵐ ω ∂P, R (killedHistory W VL VR ζ ω) = V ω := by
  filter_upwards [hc, hself] with ω hcω hsω
  have hcV : ContinuousOn (Restart.Aux54.dState W VL VR ω)
      {t | (t : ℝ≥0∞) < V ω} :=
    hcω.mono (fun t ht => ht.trans_le (hVζ ω))
  have hR1 : R (killedHistory W VL VR V ω) ≤ (killedHistory W VL VR V ω).1 :=
    hsω ▸ le_rfl
  have hR2 : R (killedHistory W VL VR V ω) ≤ (killedHistory W VL VR ζ ω).1 :=
    hsω ▸ hVζ ω
  have he := hRg _ _ (isKilledContHist_killedHistory hcV)
    (isKilledContHist_killedHistory hcω) hR1 hR2 (fun p hp => ?_)
  · exact he.trans hsω.symm
  · have hpV : (dyadicTime p : ℝ≥0∞) < V ω := hsω ▸ hp
    simp only [killedHistory, hpV, hpV.trans_le (hVζ ω), ↓reduceIte]

/-- The initial survival-mean input is proved from the ordered evolution law,
positive cutoff, and the self-consistent Galmarino rule. -/
theorem initialSurvivalMeanStatement {κ : ℝ} (hκ : 0 < κ) :
    InitialSurvivalMeanStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos
  have hXζ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC.1
  have hm : drivingFiltration P hC.2.2.2.2.choose 0 ≤ usualAugmentation 𝓕 P 0 :=
    (drivingFiltration_zero_le_full_of_pos hXζ hC.2.2.2.2.choose hC.2.1 hpos).trans
      (Ito.drivingFiltration_le_usualAugmentation hC.1 hXζ 0)
  have hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω)
      {t | (t : ℝ≥0∞) < ζ ω} :=
    hC.1.isSLEEvolutionUpTo.ae_path.mono fun _ hp => continuousOn_state_of_isSLEPathUpTo hp
  have hR := ae_rule_full_eq_of_self hRg hc hC.2.1 hself
  have he := condExp_history_eq_integral_initial hκ hF hC.1 hm
    (measurable_survivalDiscount.comp hRm)
  refine ⟨∫ ω, survivalDiscount (R (killedHistory W VL VR ζ ω)) ∂P, ?_⟩
  apply (condExp_congr_ae ?_).trans he
  exact hR.mono fun ω hω => congrArg survivalDiscount hω.symm

/-- The unchanged WFS target with only continuous closed-process existence
left as a mathematical input, besides the permitted Theorems 1.2 and 1.3. -/
theorem throughKernelStatement_of_continuousClosedProcess
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hclosed : ContinuousClosedSurvivalProcessStatement.{u} κ) :
    ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_closedProcess_initial h12 h13 hκ hclosed
    (initialSurvivalMeanStatement hκ)

end InteractingSLE.WFS
