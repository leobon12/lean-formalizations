/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalAfterReg
import InteractingSLE.Spec.Supplement.SBS3MarkedReadout
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun
import InteractingSLE.Spec.Supplement.OrdFstShift

/-!
# S3: actual marked means use the canonical physical lift

Reuse the physical hull model and the normalization of every actual run
chart. Its inherited lift agrees exactly with the canonical logarithm's
imaginary part. Real recentering changes the word coordinate and chart by
the same amount and preserves the corrected physical mean.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart WalkIntCanon

/-- Every actual R51 run chart has a physical hull model whose canonical
derivative argument is exactly the inherited lift on the chart domain. -/
theorem ae_exists_canonical_runChart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∀ᵐ ω ∂P, ∃ M : HullModel (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1,
      EqOn (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2
        (fun z => (canonDerivLog M.hull z).im)
        (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom := by
  filter_upwards [hR.ae_pieceRegular] with ω hr
  have hr' := fun j (_ : j < k) => hr j
  obtain ⟨M⟩ := exists_hullModel_runChart spec (fun j => E j ω) k hr'
  refine ⟨M, ?_⟩
  rw [show ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom : Set ℂ) =
    H \ M.hull from M.dom_eq]
  exact M.lift_eq_canonDerivLog (isNormalized_runChart spec (fun j => E j ω) k hr')

/-- The identified actual mean supplies the canonical-log word readout.
The lift equality is proved from the hull model, not assumed separately. -/
theorem isChartWordMean_of_hullModel {κ : ℝ} {word : BoundaryWord} (hs : word.IsSorted)
    {c : Chart} (M : HullModel c) (hc : IsNormalized c) {v u₀ : ℂ → ℝ}
    (hmean : EqOn (fun z => v z + u₀ z + chiC κ * c.2.2 z)
      (fun z => word.mean (c.1 z)) c.dom)
    {F : Filter ℂ} (hF : F ≤ 𝓟 (c.dom : Set ℂ)) {x : ℝ}
    (hx : x ∉ word.jumps) (hq : Tendsto c.1 F (𝓝[H] (x : ℂ))) :
    IsChartWordMean κ word x F v u₀ (canonDerivLog M.hull) := by
  refine isChartWordMean_of_corrected_eqOn hs hmean ?_ hF hx hq
  intro z hz
  exact (M.lift_eq_canonDerivLog hc (by rwa [← M.dom_eq])).symm

/-- Real recentering preserves the exact corrected physical mean when the
word is recentered with the same coordinate shift. -/
theorem eqOn_corrected_mean_recenter {κ : ℝ} {word : BoundaryWord} {c : Chart} {v u₀ : ℂ → ℝ}
    (hmean : EqOn (fun z => v z + u₀ z + chiC κ * c.2.2 z)
      (fun z => word.mean (c.1 z)) c.dom) (a : ℝ) :
    EqOn (fun z => v z + u₀ z + chiC κ * (c.recenter a).2.2 z)
      (fun z => (BoundaryWord.shiftW a word).mean ((c.recenter a).1 z)) (c.recenter a).dom := by
  intro z hz
  have hz' : z ∈ c.dom := by rwa [WalkSide.dom_recenter] at hz
  have he := hmean hz'
  change v z + u₀ z + chiC κ * c.2.2 z = (BoundaryWord.shiftW a word).mean (c.1 z - a)
  rw [RLC.OrdDet.mean_shiftW, sub_add_cancel]
  exact he

end InteractingSLE.Theorem14.SB.S3
