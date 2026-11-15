/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513WireAssembly
import InteractingSLE.Spec.Sec5.Prop513WireTips

/-! # Proposition 5.13 with the landed Proposition 5.9 piece-law tip reductions

The theorem-valued inputs are the restricted Section 4.2 result, Part A,
and the physical reverse-visit law. `TipPieceInputs` records the concrete
alternating experiments and exactly the premises consumed by Proposition 5.9.
The universe here follows the delivered piece-law reduction's `Ω : Type`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Wire
open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Restart
open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- Proposition 5.13 with its root and descendant tips reduced to the
actual alternating stage experiments and their piece laws. -/
theorem prop513_path_of_partA_reverseVisit_pieceLaw
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDiv)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    (hTips : TipPieceInputs κ P W γ
      (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime)
      (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  exact prop513_path_of_partA_reverseVisit h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit
    (fun n => hTips.tip hκ hκ4 n) (hTips.tip0 hκ hκ4)

end InteractingSLE.Sec5.Prop513Wire
