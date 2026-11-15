/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC11Flow

/-!
# Exact normalization of the constructed initial flow mean

PROVE-SIDE-COLLAR2. The actual flow-boundary family gives the native word
throughout the half-plane, with no flow-boundary or weight hypothesis.
The physical frame for that family is equivalent to the original initial
mean formula. Its common offset is unique for fixed physical means.
This equivalence is an audit of the remaining obligation, not a proof
of the physical conditional-mean identification.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide

variable {Ω : Type} [MeasurableSpace Ω]

/-- The constructed flow mean has exactly the native initial extension
after compatible reversal. Both mark signs and boundary heights are proved. -/
theorem canonicalInitialFlowMean_normalization {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) :
    EqOn (centeredReversedMean (16 / i.kappa) (j.canonicalInitialFlowMean i d ω))
      (j.initialWordExtension i d ω) H := by
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨hM, hBound⟩ := j.canonicalInitialFlowMean_harmonic_bounded i d ω
  have hMean := centeredReversedMean_eq_meanExt (div_pos (by norm_num) hκ)
    (j.target i d).rhoL (j.target i d).rhoR ((j.target i d).marksL ω)
    ((j.target i d).marksR ω) (j.initialFlowAngle₁ i d ω) (j.initialFlowAngle₂ i d ω)
    hM hBound (fun x hx => j.canonicalInitialFlowMean_tendsto i d ω hx)
    (fun x _ hx => j.initialFlowAngle₁_cumulative i d ω hx)
    (fun x _ hx => j.initialFlowAngle₂_cumulative i d ω hx)
  rw [hd] at hMean
  obtain ⟨hL, hR⟩ := j.initial_marks_signed_of_ready hj hω
  rw [j.initialWordExtension_eq_raw_of_signed_marks hj hω hL hR,
    j.target_kappa_eq i d]
  exact hMean

end InteractingSLE.Wire.Current.SideTest

namespace InteractingSLE.Wire

open Current LocalSets Sec7 Sec7.PocketStopSide Sec7.Aux119Heights

/-- For the constructed flow family, the physical frame is exactly the
original conditional-mean identity. The forward implication now has no
unproved flow-boundary premise. -/
theorem initialPocketFlowFrame_canonical_iff_meanFormula
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω)) :
    InitialPocketFlowFrame i d side G (fun j => j.canonicalInitialFlowMean i d) ↔
      InitialPocketMeanFormula i d side G := by
  constructor
  · intro hFrame
    exact initialPocketMeanFormula_of_flowWord_frame i d side G
      (fun j => j.canonicalInitialFlowMean i d) (fun j => j.initialFlowAngle₁ i d)
      (fun j => j.initialFlowAngle₂ i d) hRc hLc
      (initialPocketFlowWord_of_boundary i d _ (initialPocketFlowBoundary_canonical i d)) hFrame
  · intro hFormula j hj target
    obtain ⟨hG, hFormulaω⟩ := hFormula j hj
    refine ⟨hG, ?_⟩
    filter_upwards [hFormulaω] with ω hFormulaω hω z hz
    have hBase := j.isDomainChart_baseChart hj hRc (hLc j.seed) hω
    rw [hFormulaω hω z hz, j.canonicalInitialFlowMean_normalization hj hω (hBase.fwd_mem hz)]

/-- A prescribed physical mean and flow mean determine at most one
common offset on every ready test. Arbitrary offset choices cannot all
satisfy the frame predicate. -/
theorem InitialPocketFlowFrame.offset_eq {Ω : Type} [MeasurableSpace Ω]
    {i : BothLow} {d : WordObjects Ω} {side side' : SideTest Ω → Late.SideData Ω}
    {G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens}
    {M : SideTest Ω → Ω → ℂ → ℝ}
    (h : InitialPocketFlowFrame i d side G M)
    (h' : InitialPocketFlowFrame i d side' G M)
    (j : SideTest Ω) (hj : j.Ready d) : (side j).offset = (side' j).offset := by
  have hBoth := (h j hj).2.and (h' j hj).2
  have hPA : 0 < d.measure j.event := hj.2.2.2.2.2.2.2.2.2.1
  have hFreq : ∃ᶠ ω in ae d.measure, ω ∈ j.event :=
    frequently_ae_mem_iff.2 (ne_of_gt hPA)
  obtain ⟨ω, hω, hBothω⟩ := (hFreq.and_eventually hBoth).exists
  have hωT : ω ∈ (j.target i d).event := by rwa [j.target_event i d]
  obtain ⟨z, hz, -⟩ := (j.isConformalBijection_chart_of_ready hj ω hωT).2.2.2
    (by show (I : ℂ) ∈ H; show (0 : ℝ) < (I : ℂ).im; norm_num)
  have h1 := hBothω.1 hωT z hz
  have h2 := hBothω.2 hωT z hz
  linarith only [h1, h2]

/-- Adding a nonzero constant to a valid frame's prescribed offset
destroys that frame, for the same actual local means and flow functions. -/
theorem InitialPocketFlowFrame.not_add_offset {Ω : Type} [MeasurableSpace Ω]
    {i : BothLow} {d : WordObjects Ω} {side : SideTest Ω → Late.SideData Ω}
    {G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens}
    {M : SideTest Ω → Ω → ℂ → ℝ}
    (h : InitialPocketFlowFrame i d side G M)
    (j : SideTest Ω) (hj : j.Ready d) {c : ℝ} (hc : c ≠ 0) :
    ¬ InitialPocketFlowFrame i d (fun k => {side k with offset := (side k).offset + c}) G M := by
  intro h'
  have he := h.offset_eq h' j hj
  change (side j).offset = (side j).offset + c at he
  exact hc (by linarith only [he])

/-- Audit of the source's shifted-lift route: if it gives the same
normalized mean in `shiftChart base (n ω)` with constant offset `a`, a
frame in the unshifted base chart forces precisely this offset relation.
No constancy or vanishing of the source branch integer is asserted. -/
theorem InitialPocketFlowFrame.ae_offset_eq_of_shifted_identity
    {Ω : Type} [MeasurableSpace Ω] {i : BothLow} {d : WordObjects Ω}
    {side : SideTest Ω → Late.SideData Ω}
    {G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens}
    {M : SideTest Ω → Ω → ℂ → ℝ}
    (h : InitialPocketFlowFrame i d side G M)
    (j : SideTest Ω) (hj : j.Ready d) (n : Ω → ℤ) (a : ℝ)
    (hShifted : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event →
      ∀ z ∈ (j.target i d).domain ω,
        harmRep (G j ω) (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
          chiC (j.target i d).kappa *
            (Sec7.PocketStopField.shiftChart ((j.target i d).baseChart ω) (n ω)).2.2 z =
          centeredReversedMean (16 / i.kappa) (M j ω) (((j.target i d).baseChart ω).1 z) - a) :
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event →
      (side j).offset = a - 2 * π * chiC (j.target i d).kappa * (n ω : ℝ) := by
  filter_upwards [(h j hj).2, hShifted] with ω hFrameω hShiftedω hω
  obtain ⟨z, hz, -⟩ := (j.isConformalBijection_chart_of_ready hj ω hω).2.2.2
    (by show (I : ℂ) ∈ H; show (0 : ℝ) < (I : ℂ).im; norm_num)
  have h1 := hFrameω hω z hz
  have h2 := hShiftedω hω z hz
  dsimp only [Sec7.PocketStopField.shiftChart] at h2
  linear_combination h1 - h2

/-- A constant-offset frame in the unshifted chart forces the source's
branch integer to be almost surely constant on the entire test event.
Measurability of that branch alone does not give this conclusion. -/
theorem InitialPocketFlowFrame.exists_ae_eq_branch_of_shifted_identity
    {Ω : Type} [MeasurableSpace Ω] {i : BothLow} {d : WordObjects Ω}
    {side : SideTest Ω → Late.SideData Ω}
    {G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens}
    {M : SideTest Ω → Ω → ℂ → ℝ}
    (h : InitialPocketFlowFrame i d side G M)
    (j : SideTest Ω) (hj : j.Ready d) (n : Ω → ℤ) (a : ℝ)
    (hShifted : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event →
      ∀ z ∈ (j.target i d).domain ω,
        harmRep (G j ω) (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
          chiC (j.target i d).kappa *
            (Sec7.PocketStopField.shiftChart ((j.target i d).baseChart ω) (n ω)).2.2 z =
          centeredReversedMean (16 / i.kappa) (M j ω) (((j.target i d).baseChart ω).1 z) - a) :
    ∃ N : ℤ, ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → n ω = N := by
  have hOffset := h.ae_offset_eq_of_shifted_identity j hj n a hShifted
  have hPA : 0 < d.measure ((j.target i d).event) := by
    rw [j.target_event i d]
    exact hj.2.2.2.2.2.2.2.2.2.1
  have hFreq : ∃ᶠ ω in ae d.measure, ω ∈ (j.target i d).event :=
    frequently_ae_mem_iff.2 (ne_of_gt hPA)
  obtain ⟨ω₀, hω₀, hOffset₀⟩ := (hFreq.and_eventually hOffset).exists
  have h0 := hOffset₀ hω₀
  refine ⟨n ω₀, ?_⟩
  filter_upwards [hOffset] with ω hOffsetω hω
  have h1 := hOffsetω hω
  have hχ : chiC (j.target i d).kappa ≠ 0 := by
    rw [j.target_kappa_eq i d]
    exact ne_of_lt (neg_pos.1 (Sec7.neg_chiC_pos i.kappa_gt_four))
  have hC : 2 * π * chiC (j.target i d).kappa ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hχ
  have he : (n ω : ℝ) = (n ω₀ : ℝ) := mul_left_cancel₀ hC (by
    linear_combination h1 - h0)
  exact_mod_cast he

end InteractingSLE.Wire
