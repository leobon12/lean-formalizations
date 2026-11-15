import InteractingSLE.Spec.Sec2.T24BrBefore
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# Measurable versions of an integrated evolution

Coordinate and lifetime versions agreeing simultaneously almost surely preserve the
integrated equations. Ambient measurability of the new coordinates and lifetime lets
their adapted-before events pass to the usual augmentation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T24Bridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- Measurable coordinate versions preserve adaptedness before a measurable lifetime version. -/
theorem adaptedBefore_congr_ae_usualAugmentation
    {ζ ζ' : Ω → ℝ≥0∞} {X X' : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓕 ζ X) (hζ' : Measurable ζ') (hX' : ∀ t, Measurable (X' t))
    (he : ∀ᵐ ω ∂P, ζ' ω = ζ ω ∧ ∀ t, X' t ω = X t ω) :
    AdaptedBefore (usualAugmentation 𝓕 P) ζ' X' := by
  intro t A hA
  have hm : MeasurableSet {ω | (t : ℝ≥0∞) < ζ' ω ∧ X' t ω ∈ A} :=
    (measurableSet_lt measurable_const hζ').inter (hX' t hA)
  apply measurableSet_usualAugmentation_of_ae_eq hm (hX t A hA)
  filter_upwards [he] with ω hω
  simp only [hω.1, hω.2]

/-- The integrated evolution survives simultaneous measurable modifications of its paths and lifetime. -/
theorem isIntegratedSLEEvolution_congr_ae_usualAugmentation
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W W' B : ℝ≥0 → Ω → ℝ} {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hW' : ∀ t, Measurable (W' t)) (hVL' : ∀ i t, Measurable (VL' i t))
    (hVR' : ∀ i t, Measurable (VR' i t)) (hζ' : Measurable ζ')
    (he : ∀ᵐ ω ∂P, ζ' ω = ζ ω ∧ (∀ t, W' t ω = W t ω) ∧
      (∀ i t, VL' i t ω = VL i t ω) ∧ ∀ i t, VR' i t ω = VR i t ω) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR P (usualAugmentation 𝓕 P) W' VL' VR' B ζ' := by
  refine ⟨Ito.isFilteredBrownianReal_usualAugmentation hE.1,
    adaptedBefore_congr_ae_usualAugmentation hE.2.1 hζ' hW'
      (he.mono fun _ h => ⟨h.1, h.2.1⟩),
    fun i => adaptedBefore_congr_ae_usualAugmentation (hE.2.2.1 i) hζ' (hVL' i)
      (he.mono fun _ h => ⟨h.1, h.2.2.1 i⟩),
    fun i => adaptedBefore_congr_ae_usualAugmentation (hE.2.2.2.1 i) hζ' (hVR' i)
      (he.mono fun _ h => ⟨h.1, h.2.2.2 i⟩), ?_⟩
  filter_upwards [he, hE.2.2.2.2] with ω hω hp
  have hw : (W' · ω) = (W · ω) := funext hω.2.1
  have hL : (fun i t => VL' i t ω) = fun i t => VL i t ω := funext fun i => funext (hω.2.2.1 i)
  have hR : (fun i t => VR' i t ω) = fun i t => VR i t ω := funext fun i => funext (hω.2.2.2 i)
  rwa [hω.1, hw, hL, hR]

end InteractingSLE.Sec2.T24Bridge
