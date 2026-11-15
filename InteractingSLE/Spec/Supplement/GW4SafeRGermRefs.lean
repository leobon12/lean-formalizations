/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRGermVersions
import InteractingSLE.Spec.Sec7.PocketSideInKernelStepHeight

/-!
# GW4: countable old references at a random current line

The current chart can depend on the outcome, including through the physical
line clock. Intersect the old-chart increment statements before choosing an
incident reference. The cover contains only old own heights, geometry and
the inherited lift discrepancy; the current mean's germ is proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets Sec7.PocketStopSide Sec7.Aux119Heights

/-- **Remaining geometric/own-height input.** Every nonexceptional access
has an incident old half-disc, an old own height and a limiting inherited
lift discrepancy matching the desired word. The exceptional set is physical;
no restriction on the number of its incident prime ends is imposed. -/
def IncidentReferenceCover {Ω ι : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (k : ℝ) (A : Set Ω) (old : ι → Ω → Chart)
    (current : Ω → Chart) (gOld : ι → Ω → DistOn upperHalfPlaneOpens)
    (M : ι → Set Ω) (u : ℂ → ℝ) (J : Ω → Set ℝ) (word : Ω → ℝ → ℝ) : Prop :=
  ∀ᵐ ω ∂ν, ω ∈ A → ∃ E : Set ℂ, E.Finite ∧
    ∀ ξ : ℝ, ξ ∉ J ω → extendFrom H (current ω).2.1 (ξ : ℂ) ∉ E →
      ∃ (i : ι) (x r b ℓ : ℝ), ω ∈ M i ∧ 0 < r ∧
        (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (current ω).dom ∧
        Tendsto (fun z => (old i ω).1 ((current ω).2.1 z))
          (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (sideMean k (old i ω) u (harmRep (gOld i ω) (old i ω).dom))
          (𝓝[H] (x : ℂ)) (𝓝 b) ∧
        Tendsto (fun z => (current ω).2.2 ((current ω).2.1 z) -
            (old i ω).2.2 ((current ω).2.1 z))
          (𝓝[H] (ξ : ℂ)) (𝓝 ℓ) ∧ b + chiC k * ℓ = word ω ξ

/-- Countably many actual increment laws and old own heights supply the
current corrected limits. The current chart need not be a pocket chart at
a deterministic relative capacity. No current-mean boundary limit is assumed. -/
theorem ae_sideMean_of_incident_reference_cover {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {k : ℝ} {A : Set Ω} {old : ι → Ω → Chart} {current : Ω → Chart}
    {gOld : ι → Ω → DistOn upperHalfPlaneOpens} {g : Ω → DistOn upperHalfPlaneOpens}
    {h : Ω → DistOn upperHalfPlaneOpens} {B : Ω → Set ℂ} {M : ι → Set Ω}
    {u : ℂ → ℝ} {J : Ω → Set ℝ} {word : Ω → ℝ → ℝ}
    (hCurrent : ∀ ω ∈ A, (current ω).IsConformal)
    (hDomain : ∀ᵐ ω ∂ν, ω ∈ A → ((current ω).dom : Set ℂ) = H \ B ω)
    (hOld : ∀ i ω, ω ∈ M i → ω ∈ A ∧ (old i ω).IsConformal ∧
      ((current ω).dom : Set ℂ) ⊆ (old i ω).dom)
    (hHarmOld : ∀ i, ∀ᵐ ω ∂ν, ω ∈ M i → IsHarmonicDistOn (gOld i ω) (old i ω).dom)
    (hg : IsLocalSetMean B h ν g)
    (hLaw : ∀ i, HasOldChartIncrementLaw ν (M i) (old i) current (gOld i) g)
    (hCover : IncidentReferenceCover ν k A old current gOld M u J word) :
    ∀ᵐ ω ∂ν, ω ∈ A → ∃ E : Set ℂ, E.Finite ∧
      ∀ ξ : ℝ, ξ ∉ J ω → extendFrom H (current ω).2.1 (ξ : ℂ) ∉ E →
        Tendsto (sideMean k (current ω) u (harmRep (g ω) (H \ B ω)))
          (𝓝[H] (ξ : ℂ)) (𝓝 (word ω ξ)) := by
  have hTransfer := fun i => ae_corrected_height_of_old_chart_increment_law
    (fun ω hω => (hOld i ω hω).2.1)
    (fun ω hω => hCurrent ω (hOld i ω hω).1)
    (fun ω hω => (hOld i ω hω).2.2) (hLaw i)
  filter_upwards [ae_all_iff.2 hTransfer, ae_all_iff.2 hHarmOld, hg.2.1, hCover, hDomain]
    with ω hT hO hN hC hD hω
  obtain ⟨E, hE, hAccess⟩ := hC hω
  refine ⟨E, hE, fun ξ hξ hξE => ?_⟩
  obtain ⟨i, x, r, b, ℓ, hMi, hr, hCol, hTr, hHeight, hLift, hWord⟩ :=
    hAccess ξ hξ hξE
  obtain ⟨hvOld, hRepOld⟩ := harmRep_spec (hO i hMi)
  obtain ⟨hvNow, hRepNow⟩ := harmRep_spec hN
  have hDom := hD hω
  have hvNow' : InnerProductSpace.HarmonicOnNhd
      (harmRep (g ω) (H \ B ω)) (current ω).dom := by
    simpa only [hDom] using hvNow
  have hRepNow' : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ (current ω).dom →
        g ω φ = ∫ z, harmRep (g ω) (H \ B ω) z * φ z := by
    simpa only [hDom] using hRepNow
  rw [← hWord]
  exact hT i hMi _ _ hvOld hRepOld hvNow' hRepNow' ξ x r hr hCol hTr
    k b ℓ u hHeight hLift

end InteractingSLE.Theorem14.GW4Fix
