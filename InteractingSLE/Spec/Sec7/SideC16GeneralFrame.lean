/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC16R7Relift
import InteractingSLE.Spec.Sec7.SideC16Word
import InteractingSLE.Spec.Sec7.SideC15Inverse

/-! # General original pocket means supply the exact R.7 frame and `hInit`

PROVE-SIDE-COLLAR2, R98. This adapter is independent of late-test labels,
angle bounds and pocket shape. Its original-flow identity is supplied by
`ae_eqOn_filledPocket_allAngles` (constant arms) or the landed two-angle
source theorem; its native word by `centeredReversedMean_eq_twoSeed_of_sourceExtension`
or the landed native-word theorem. Every physical transport is proved here.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC16
open LocalSets WholeField WangWu SideC12 PocketStop PocketStopSide Aux119Heights

/-- The R98 samplewise frame on a general pocket. `hFlow` and `hNative`
are the original source formula and the native finite-word identification,
respectively; no physical mean formula or deterministic branch is assumed. -/
theorem sampleFrame_of_originalMean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {h h' h'' g₀ : Ω → DistOn upperHalfPlaneOpens} {u₀ u₁ : ℂ → ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 0 (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₁ : InnerProductSpace.HarmonicOnNhd u₁ H)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {n : Ω → ℤ} {M : Ω → ℂ → ℝ}
    (hc : ∀ ω ∈ A, IsDomainChart (C ω) (c ω))
    (hB : ∀ ω, liveExt A γ C (fun _ => ∅) 0 ω ⊆ H ∧
      IsOpen (H \ liveExt A γ C (fun _ => ∅) 0 ω))
    (hBC : ∀ ω ∈ A, H \ liveExt A γ C (fun _ => ∅) 0 ω = C ω)
    (hg₀ : IsLocalSetMean (fun ω => negInv '' liveExt A γ C (fun _ => ∅) 0 ω)
      (centredField h u₀) P g₀)
    (hFlow : ∀ᵐ ω ∂P, ω ∈ A → ∀ z ∈ C ω,
      harmRep (g₀ ω) (H \ negInv '' liveExt A γ C (fun _ => ∅) 0 ω) (negInv z) + u₀ (negInv z) =
        M ω (conjugateFlowMap (c ω) (negInv z)) -
          chiC κ * (conjugateFlowLift (c ω) (negInv z) + 2 * π * (n ω : ℝ)))
    (hNative : ∀ ω ∈ A, EqOn (centeredReversedMean κ (M ω))
      (MartChar.meanExt (16 / κ) ρL ρR 0 (xL ω) (xR ω)) H) :
    let G := fun ω => physicalMean (-(π * chiC κ)) (chiC (16 / κ)) 0 u₀ u₁ (g₀ ω)
    IsLocalSetMean (liveExt A γ C (fun _ => ∅) 0) (centredField h'' u₁) P G ∧
      ∀ᵐ ω ∂P, ω ∈ A → ∀ z ∈ C ω,
        harmRep (G ω) (H \ liveExt A γ C (fun _ => ∅) 0 ω) z + u₁ z +
            chiC (16 / κ) * (c ω).2.2 z =
          MartChar.meanExt (16 / κ) ρL ρR 0 (xL ω) (xR ω) ((c ω).1 z) -
            Wire.sourceFrameOffset κ 0 (n ω) := by
  let G := fun ω => physicalMean (-(π * chiC κ)) (chiC (16 / κ)) 0 u₀ u₁ (g₀ ω)
  have hA := fun ω => image_negInv_relClosed (hB ω)
  have hMean := localSetMean_physicalMean hA hT hTr hu₀ hu₁ hg₀
  have hRep := ae_physicalMean_formula (a := -(π * chiC κ)) (k := chiC (16 / κ))
    (c := 0) hA hu₀ hu₁ hg₀
  simp only [image_negInv_image_negInv] at hMean hRep
  refine ⟨hMean, ?_⟩
  filter_upwards [hRep, hFlow] with ω hRepω hFlowω hω z hz
  have hComp : z ∈ H \ liveExt A γ C (fun _ => ∅) 0 ω := by
    rw [hBC ω hω]
    exact hz
  have hEq := frame_identity_of_conjugate_flow hκ (c ω) (M ω)
    (fun y => harmRep (g₀ ω) (H \ negInv '' liveExt A γ C (fun _ => ∅) 0 ω) y + u₀ y)
    (n ω) 0 z (by simpa only [add_zero] using hFlowω hω z hz)
  rw [← hNative ω hω ((hc ω hω).fwd_mem hz)]
  change harmRep (G ω) _ z + u₁ z + _ = _
  have hRepz := hRepω z hComp
  change harmRep (G ω) _ z + u₁ z = _ at hRepz
  rw [hRepz]
  exact hEq

/-- The exact R5-WALL `hInit`, with zero offset and the corrected
negative-shift integer `1 - n`, follows from the original pocket mean.
All versions and all coordinates off the actual force jumps are covered. -/
theorem r7InitialHeights_zero_of_originalMean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {h h' h'' g₀ : Ω → DistOn upperHalfPlaneOpens} {u₀ u₁ : ℂ → ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 0 (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₁ : InnerProductSpace.HarmonicOnNhd u₁ H)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {n : Ω → ℤ} {M : Ω → ℂ → ℝ}
    (hc : ∀ ω ∈ A, IsDomainChart (C ω) (c ω))
    (hB : ∀ ω, liveExt A γ C (fun _ => ∅) 0 ω ⊆ H ∧
      IsOpen (H \ liveExt A γ C (fun _ => ∅) 0 ω))
    (hBC : ∀ ω ∈ A, H \ liveExt A γ C (fun _ => ∅) 0 ω = C ω)
    (hg₀ : IsLocalSetMean (fun ω => negInv '' liveExt A γ C (fun _ => ∅) 0 ω)
      (centredField h u₀) P g₀)
    (hFlow : ∀ᵐ ω ∂P, ω ∈ A → ∀ z ∈ C ω,
      harmRep (g₀ ω) (H \ negInv '' liveExt A γ C (fun _ => ∅) 0 ω) (negInv z) + u₀ (negInv z) =
        M ω (conjugateFlowMap (c ω) (negInv z)) -
          chiC κ * (conjugateFlowLift (c ω) (negInv z) + 2 * π * (n ω : ℝ)))
    (hNative : ∀ ω ∈ A, EqOn (centeredReversedMean κ (M ω))
      (MartChar.meanExt (16 / κ) ρL ρR 0 (xL ω) (xR ω)) H)
    (hBm : Measurable[_, hittingSigma] (liveExt A γ C (fun _ => ∅) 0))
    (hhm : Measurable (centredField h'' u₁)) (X₀ : Ω → Set ℂ) :
    R5Wall.R7InitialHeights (16 / κ) ρL ρR P A γ C xL xR
      (fun ω => PocketStopField.shiftChart (c ω) (1 - n ω)) 0 (centredField h'' u₁) u₁ X₀ := by
  obtain ⟨hG, hFormula⟩ := sampleFrame_of_originalMean hκ hT hTr hu₀ hu₁ hc hB hBC hg₀ hFlow hNative
  exact r7InitialHeights_zero_of_sampleFrame hκ hBm hhm hc hG hFormula X₀

end InteractingSLE.Sec7.SideC16
