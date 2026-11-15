/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFaceGerm
import InteractingSLE.Spec.Sec7.PocketSideInFaceAnchor

/-!
# R.5--R.6: joint germ comparison and shared-face phase transfer

PROVE-POCKET-SIDEIN. The old-chart residual local-set mean supplies the germ
comparison. Its probability-one event is uniform in incident approaches and
current-face witnesses. Countable original-time/reference indices are
intersected before any realized nested witness is chosen.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets

/-- The R.5 germ event can be chosen simultaneously over the countable old
reference charts and original rational times. All incident coordinates and
harmonic representatives remain universally quantified on this one event. -/
theorem ae_all_incident_zero_germ_of_local_increment {Ω ι : Type*}
    [mΩ : MeasurableSpace Ω] [Countable ι] {P : Measure Ω} [IsProbabilityMeasure P]
    {h g : ι → Ω → DistOn upperHalfPlaneOpens} {A : ι → Ω → Set ℂ}
    (hh : ∀ i, IsZeroBoundaryGFF upperHalfPlaneOpens (h i) P)
    (hAm : ∀ i, Measurable[mΩ, hittingSigma] (A i))
    (hAloc : ∀ i, IsLocalSet (A i) (h i) P)
    (hIncrementMean : ∀ i, IsLocalSetMean (A i) (h i) P (g i)) :
    ∀ᵐ ω ∂P, ∀ i, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A i ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A i ω →
        g i ω φ = ∫ z, v z * φ z) → ∀ (ξ u : ℝ) (F : ℂ → ℂ),
      Tendsto F (𝓝[H] (ξ : ℂ)) (𝓝[H] (u : ℂ)) →
      (∃ r > 0, Disjoint (H ∩ ball (u : ℂ) r) (A i ω)) →
      Tendsto (fun z => v (F z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) :=
  ae_all_iff.2 fun i => ae_incident_zero_germ_of_local_increment
    (hh i) (hAm i) (hAloc i) (hIncrementMean i)

/-- R.5's exact local increment identity and R.6's actual current-face inputs
imply zero exposed phase on one event uniform in the chosen face witness.
The coordinate identity is only required near the incident exposed germ. -/
theorem ae_phase_zero_of_current_face_increment {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h g : Ω → DistOn upperHalfPlaneOpens}
    {A : Ω → Set ℂ} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A h P)
    (hIncrementMean : IsLocalSetMean A h P g) {R : Ω → ℂ → ℝ}
    (hIncrementRepresentation : ∀ᵐ ω ∂P,
      InnerProductSpace.HarmonicOnNhd (R ω) (H \ A ω) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        g ω φ = ∫ z, R ω z * φ z) :
    ∀ᵐ ω ∂P, ∀ (χ : ℝ) (c : Chart) (Γ : Set ℂ) (p : ℂ) (J : Set ℝ)
      (y₀ : ℝ) (G L : ℂ → ℂ) (bC bU ξ η b d u : ℝ) (T : ℂ → ℂ) (MC MU : ℂ → ℝ),
      χ ≠ 0 → c.IsConformal → IsClosed Γ →
      (c.dom : Set ℂ) = connectedComponentIn (H \ Γ) p →
      IsPreconnected J → IsOpen J → (∀ x ∈ J, (x : ℂ) ∉ Γ) → y₀ ∈ J →
      (y₀ : ℂ) ∈ closure (c.dom : Set ℂ) →
      ContinuousOn G ((c.dom : Set ℂ) ∪ Complex.ofReal '' J) → EqOn G c.1 c.dom →
      ContinuousOn (fun y : ℝ => L y) J →
      (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect G) y) →
      bC = bU → bU = bC + χ * (L y₀).im → ξ ∈ J →
      ContinuousWithinAt L Hbar (ξ : ℂ) →
      Tendsto G (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)) →
      Tendsto MC (𝓝[H] (ξ : ℂ)) (𝓝 (b + d)) →
      Tendsto MU (𝓝[H] (η : ℂ)) (𝓝 b) →
      Tendsto T (𝓝[H] (ξ : ℂ)) (𝓝[H] (u : ℂ)) →
      (∃ r > 0, Disjoint (H ∩ ball (u : ℂ) r) (A ω)) →
      (∀ᶠ z in 𝓝[H] (ξ : ℂ), R ω (T z) = MU (G z) - MC z - χ * (L z).im) →
      d = 0 := by
  filter_upwards [ae_incident_zero_germ_of_local_increment hh hAm hAloc hIncrementMean,
    hIncrementRepresentation] with ω hzero hrep
  intro χ c Γ p J y₀ G L bC bU ξ η b d u T MC MU hχ hc hΓ hCurrentFace hJ hJo
    hContact hy₀ hAccess hBoundaryExtension hExtensionEq hLc hexp hExactHeights
    hHeightTransform hξ hLξ hG hC hU hT hFree hCoordinateIncrement
  exact phase_eq_zero_of_current_face_germ hχ hc hΓ hCurrentFace hJ hJo hContact
    hy₀ hAccess hBoundaryExtension hExtensionEq hLc hexp hExactHeights hHeightTransform
    hξ hLξ hG hC hU ((hzero _ hrep.1 hrep.2 ξ u T hT hFree).congr' hCoordinateIncrement)

end InteractingSLE.Sec7.PocketStopSide
