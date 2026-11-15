/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageLawProofTips

/-! # Wiring Proposition 5.9's delivered piece laws into its two tip predicates

The data below are the actual alternating stage experiment, with exactly the
piece-law, realized-system, initial-word and initial-event premises of the
landed `tip0UnboundedStatement_of_pieceLaw`/`tipUnboundedStatement_of_pieceLaw`.
No unboundedness conclusion is stored as a field.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Wire
open QuantumZipper Prop59Stage

/-- A realized alternating experiment for a specified family of physical
points. These are the data consumed by Proposition 5.9's piece-law reductions. -/
structure TipData (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (S : Ω → Set ℂ) where
  nL : ℚ → ℕ
  nR : ℚ → ℕ
  posL : ∀ r, 0 < nL r
  posR : ∀ r, 0 < nR r
  rhoL : (r : ℚ) → Fin (nL r) → ℝ
  rhoR : (r : ℚ) → Fin (nR r) → ℝ
  grid : Set ℝ≥0
  mesh : ℚ → ℕ → ℝ≥0
  times : ℚ → ℕ → ℕ → ℝ≥0
  system : (r : ℚ) → StageSys Ω (nL r) (nR r)
  pieceLaw : ∀ r : ℚ, 0 < r → Prop59StagePieceLawStatement κ P (rhoL r) (rhoR r) (system r)
  stages : ∀ r : ℚ, 0 < r → IsStageSystem P (posL r) (posR r) grid (mesh r) (times r) (system r)
    (fun ω => (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
      (S ω ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal)))
  initialWord : ∀ r : ℚ, 0 < r → IsStageInit κ (rhoL r) (rhoR r)

/-- The root and descendant experiments used in Proposition 5.13. Their
initial events are the precise ones in the two landed tip reductions. -/
structure TipPieceInputs (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (z : ℕ → Ω → ℂ) (S : ℕ → Ω → Set ℂ) where
  root : TipData κ P W (fun ω => range fun n => z n ω)
  root_active : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, ω ∈ (root.system r (fun _ => 0) 0).R
  node : ∀ n, TipData κ P W (S n)
  node_active : ∀ n, ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P,
    (r : ℝ) < traceFirstVisit (γ ω) (z n ω) → ω ∈ ((node n).system r (fun _ => 0) 0).R

/-- Proposition 5.9 at the original root, from the delivered piece laws. -/
theorem TipPieceInputs.tip0 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {S : ℕ → Ω → Set ℂ}
    (D : TipPieceInputs κ P W γ z S) : Prop59Tips.Tip0UnboundedStatement P W z :=
  tip0UnboundedStatement_of_pieceLaw hκ hκ4 D.root.pieceLaw D.root.stages
    D.root.initialWord D.root_active

/-- Proposition 5.9 at every prefix endpoint, from the delivered piece laws. -/
theorem TipPieceInputs.tip {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {S : ℕ → Ω → Set ℂ}
    (D : TipPieceInputs κ P W γ z S) (n : ℕ) : Prop59Tips.TipUnboundedStatement P W γ (z n) (S n) :=
  tipUnboundedStatement_of_pieceLaw hκ hκ4 (D.node n).pieceLaw (D.node n).stages
    (D.node n).initialWord (D.node_active n)

end InteractingSLE.Sec5.Prop513Wire
