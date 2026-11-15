/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC11Marks

/-!
# A proved initial flow-boundary family

PROVE-SIDE-COLLAR2. Construct the bounded harmonic function with the actual
incoming angle heights by reversing the raw finite-word extension with
the dual coefficient. This proves `InitialPocketFlowBoundary` outright.
Identifying this constructed function with a physical conditional mean
remains the separate frame question; no such identification is assumed here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide

variable {Ω : Type} [MeasurableSpace Ω]

/-- The canonical bounded flow-coordinate extension of the actual
incoming angle word, using the dual compatible reversal. -/
def canonicalInitialFlowMean (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (ω : Ω) : ℂ → ℝ :=
  centeredReversedMean i.kappa (MartChar.meanExt i.kappa
    (j.target i d).rhoL (j.target i d).rhoR 0
    ((j.target i d).marksL ω) ((j.target i d).marksR ω))

/-- Harmonicity and boundedness require no stochastic or frame input. -/
theorem canonicalInitialFlowMean_harmonic_bounded (j : SideTest Ω)
    (i : BothLow) (d : WordObjects Ω) (ω : Ω) :
    InnerProductSpace.HarmonicOnNhd (j.canonicalInitialFlowMean i d ω) H ∧
      ∃ C : ℝ, ∀ z ∈ H, |j.canonicalInitialFlowMean i d ω z| ≤ C := by
  have h := MartChar.isBoundedHarmonicExtension_meanExt i.kappa
    (j.target i d).rhoL (j.target i d).rhoR 0
    ((j.target i d).marksL ω) ((j.target i d).marksR ω)
  exact centeredReversedMean_harmonic_bounded h.1 h.2.1

/-- The exact flow-boundary limits of the canonical mean, at every
inverted coordinate off the actual finite set of jumps. -/
theorem canonicalInitialFlowMean_tendsto (j : SideTest Ω)
    (i : BothLow) (d : WordObjects Ω) (ω : Ω) {x : ℝ}
    (hx : x ∉ forceJumpSet ((j.target i d).marksL ω) ((j.target i d).marksR ω)) :
    Tendsto (j.canonicalInitialFlowMean i d ω) (𝓝[H] (-((x : ℂ)⁻¹)))
      (𝓝 (cf92Lower (16 / i.kappa) (j.initialFlowAngle₁ i d ω (-x⁻¹))
        (j.initialFlowAngle₂ i d ω (-x⁻¹)) (-x⁻¹))) := by
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hp : 0 < 16 / i.kappa := div_pos (by norm_num) hκ
  have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
  have hχ : chiC i.kappa = -chiC (16 / i.kappa) := by
    rw [Sec4.chiC_sixteen_div hκ, neg_neg]
  have hx0 : x ≠ 0 := fun he => hx (he ▸ Set.mem_insert 0 _)
  let y : ℝ := -x⁻¹
  have hy0 : y ≠ 0 := neg_ne_zero.2 (inv_ne_zero hx0)
  have hU := MartChar.isBoundedHarmonicExtension_meanExt i.kappa
    (j.target i d).rhoL (j.target i d).rhoR 0
    ((j.target i d).marksL ω) ((j.target i d).marksR ω)
  simp only [sub_zero] at hU
  have hInput : Tendsto (MartChar.meanExt i.kappa (j.target i d).rhoL
      (j.target i d).rhoR 0 ((j.target i d).marksL ω) ((j.target i d).marksR ω))
      (𝓝[H] (-((y : ℂ)⁻¹)))
      (𝓝 (forceBoundaryData i.kappa (j.target i d).rhoL (j.target i d).rhoR
        ((j.target i d).marksL ω) ((j.target i d).marksR ω) x)) := by
    simpa only [y, ofReal_neg, ofReal_inv, inv_neg, inv_inv, neg_neg] using hU.2.2 x hx
  have hLim := tendsto_height_through_compatible_inversion (X := chiC i.kappa)
    (c := -(π * chiC i.kappa)) hy0 hInput
  have hValue : -forceBoundaryData i.kappa (j.target i d).rhoL (j.target i d).rhoR
        ((j.target i d).marksL ω) ((j.target i d).marksR ω) x +
        chiC i.kappa * (if y < 0 then 0 else 2 * π) - π * chiC i.kappa =
      cf92Lower (16 / i.kappa) (j.initialFlowAngle₁ i d ω y)
        (j.initialFlowAngle₂ i d ω y) y := by
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hy : 0 < y := neg_pos.2 (inv_lt_zero.2 hneg)
      have hLeft := cf95_left_height hp (j.initialFlowAngle₁ i d ω y)
      rw [hd] at hLeft
      rw [forceBoundaryData, ite_eq_left hneg,
        j.initialFlowAngle₁_cumulative i d ω hneg,
        ite_eq_right (not_lt.2 hy.le), cf92Lower, ite_eq_right (not_lt.2 hy.le), hχ]
      dsimp only [sleLambda] at hLeft ⊢
      linear_combination hLeft
    · have hy : y < 0 := neg_neg_iff_pos.2 (inv_pos.2 hpos)
      have hRight := cf95_right_height hp (j.initialFlowAngle₂ i d ω y)
      rw [hd] at hRight
      rw [forceBoundaryData, ite_eq_right (not_lt.2 hpos.le),
        j.initialFlowAngle₂_cumulative i d ω hpos, ite_eq_left hy,
        cf92Lower, ite_eq_left hy, hχ]
      dsimp only [sleLambda] at hRight ⊢
      linear_combination hRight
  have hValue' := hValue
  rw [sub_eq_add_neg] at hValue'
  rw [hValue'] at hLim
  change Tendsto (fun z => -coordChange (chiC i.kappa) (fun w => -w⁻¹)
    (fun w => 2 * π * I - 2 * log w)
    (MartChar.meanExt i.kappa (j.target i d).rhoL (j.target i d).rhoR 0
      ((j.target i d).marksL ω) ((j.target i d).marksR ω)) z - π * chiC i.kappa) _ _
  simpa only [sub_eq_add_neg, y, ofReal_neg, ofReal_inv] using hLim

end InteractingSLE.Wire.Current.SideTest

namespace InteractingSLE.Wire

open Current

/-- The previous initial flow-boundary input is now a proved property
of an explicit family, for every ready side test and both pocket shapes. -/
theorem initialPocketFlowBoundary_canonical {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) :
    InitialPocketFlowBoundary i d (fun j => j.canonicalInitialFlowMean i d) := by
  intro j hj target
  refine Eventually.of_forall fun ω hω => ?_
  obtain ⟨hL, hR⟩ := j.initial_marks_signed_of_ready hj hω
  obtain ⟨hM, hBound⟩ := j.canonicalInitialFlowMean_harmonic_bounded i d ω
  exact ⟨hL, hR, hM, hBound, fun x hx => j.canonicalInitialFlowMean_tendsto i d ω hx⟩

end InteractingSLE.Wire
