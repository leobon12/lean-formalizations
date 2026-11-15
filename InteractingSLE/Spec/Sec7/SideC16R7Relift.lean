/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC16R7
import InteractingSLE.Spec.Sec7.SideC16Transport
import InteractingSLE.Spec.Sec7.PocketStopFieldChart

/-! # R98's sample-dependent relift supplies R.7's zero-offset `hInit`

PROVE-SIDE-COLLAR2. The negative-shift integer is `1 - n`, where `n`
is the source integer. It is not `n`. The chart map is unchanged and
the resulting source index is one, with exactly zero counterflow offset.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC16
open LocalSets Aux119Heights PocketStop PocketStopSide PocketStopField

/-- Integer relifting preserves the whole domain chart, including a
compatible analytic derivative logarithm. -/
theorem isDomainChart_shiftChart {C : Set ℂ} {c : Chart}
    (hc : IsDomainChart C c) (n : ℤ) : IsDomainChart C (shiftChart c n) := by
  obtain ⟨hconf, himage, L, hL, hlift⟩ := hc
  refine ⟨hconf, himage, fun z => L z - n * (2 * π * Complex.I), isDerivLog_sub_int hL n, ?_⟩
  intro z hz
  change c.2.2 z - 2 * π * n = (L z - n * (2 * π * Complex.I)).im
  have heq : c.2.2 z = (L z).im := hlift hz
  rw [im_sub_int_mul, heq]

/-- R.7's initial heights, with canonical zero offset, from the pointwise
R98 frame. The source branch may vary arbitrarily with the sample.
When it is walls-measurable, so is the installed shift `1 - n`. -/
theorem r7InitialHeights_zero_of_sampleFrame
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {n : Ω → ℤ} {h₀ G : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hBm : Measurable[mΩ, hittingSigma] (liveExt A γ C (fun _ => ∅) 0))
    (hhm : Measurable h₀) (hc : ∀ ω ∈ A, IsDomainChart (C ω) (c ω))
    (hG : IsLocalSetMean (liveExt A γ C (fun _ => ∅) 0) h₀ P G)
    (hFormula : ∀ᵐ ω ∂P, ω ∈ A → ∀ z ∈ C ω,
      harmRep (G ω) (H \ liveExt A γ C (fun _ => ∅) 0 ω) z + u z +
          chiC (16 / κ) * (c ω).2.2 z =
        MartChar.meanExt (16 / κ) ρL ρR 0 (xL ω) (xR ω) ((c ω).1 z) -
          Wire.sourceFrameOffset κ 0 (n ω))
    (X₀ : Ω → Set ℂ) :
    R5Wall.R7InitialHeights (16 / κ) ρL ρR P A γ C xL xR
      (fun ω => shiftChart (c ω) (1 - n ω)) 0 h₀ u X₀ := by
  apply SideC14.r7InitialHeights_of_initialWordFormula hBm hhm
    (fun ω hω => isDomainChart_shiftChart (hc ω hω) (1 - n ω)) hG ?_ X₀
  filter_upwards [hFormula] with ω hω hA z hz
  change harmRep (G ω) _ z + u z + chiC (16 / κ) * ((c ω).2.2 z - 2 * π * ((1 - n ω : ℤ) : ℝ)) = _
  have heq := hω hA z hz
  rw [Wire.sourceFrameOffset, zero_add, Sec4.chiC_sixteen_div hκ] at heq
  simp only [shiftChart, Int.cast_sub, Int.cast_one, Sec4.chiC_sixteen_div hκ, sub_zero]
  linear_combination heq

/-- R98's shift is measurable in exactly the original incoming record. -/
theorem measurable_canonicalShift {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : Ω → ℤ}
    (hn : Measurable n) : Measurable fun ω => (1 : ℤ) - n ω :=
  measurable_const.sub hn

end InteractingSLE.Sec7.SideC16
