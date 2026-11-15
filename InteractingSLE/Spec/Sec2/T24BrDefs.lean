import InteractingSLE.Spec.Sec2.MartingaleExtract
import InteractingSLE.Frozen.Spec.ForceWord_ThresholdCondition

/-!
# Theorem 2.4: local copies of the statement candidate's defining formulas

These definitions are confined to `Sec2.T24Bridge`; they do not replace frozen declarations.
Their bodies are the statement candidate's force images, threshold, and continuous local
martingale condition, allowing the provider to be checked before the anchor names are fixed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T24Bridge

/-- The right-force image formula in the statement candidate. -/
def rightForceImage (w : ℝ≥0 → ℝ) (x : ℝ) (t : ℝ≥0) : ℝ :=
  w t + sInf {v : ℝ | ∃ y : ℝ, x < y ∧
    (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) y t u) ∧
    v = (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t y).re}

/-- The left-force image formula in the statement candidate. -/
def leftForceImage (w : ℝ≥0 → ℝ) (x : ℝ) (t : ℝ≥0) : ℝ :=
  w t + sSup {v : ℝ | ∃ y : ℝ, y < x ∧
    (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) y t u) ∧
    v = (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t y).re}

/-- The geometric continuation threshold in the statement candidate. -/
def geomContinuationThreshold {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ForceWord.ThresholdCondition ρL ρR (w t)
    (fun i => leftForceImage w (xL i) t) (fun j => rightForceImage w (xR j) t)),
      (t : ℝ≥0∞)

/-- The continuous local-martingale condition, with the landed localization definition. -/
def IsContLocalMartingaleBefore {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (ζ : Ω → WithTop ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) {t | (t : WithTop ℝ≥0) < ζ ω}) ∧
    MartChar.IsLocalMartingaleBefore 𝓕 P ζ X

end InteractingSLE.Sec2.T24Bridge
