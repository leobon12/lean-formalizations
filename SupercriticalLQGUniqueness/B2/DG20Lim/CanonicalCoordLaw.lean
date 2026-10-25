import SupercriticalLQGUniqueness.B2.DG20Lim.CanonicalFiniteLFPP
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel

 


set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem joint_finite_coords_law_of_pair_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : Ω → ContMetric) (hD : AEMeasurable D P)
    (h' : Ω' → DistC) (hh' : Measurable h')
    (D' : Ω' → ContMetric) (hD' : AEMeasurable D' P')
    (hlaw : P.map (fun ω => (h ω, D ω)) =
      P'.map (fun ω => (h' ω, D' ω))) :
    P.map (fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)) =
      P'.map (fun ω => (pairJ ⊤ (h' ω), measurableRatCoordsVersion D' hD' ω)) := by
  let f : Ω → DistC × ContMetric := fun ω => (h ω, D ω)
  let f' : Ω' → DistC × ContMetric := fun ω => (h' ω, D' ω)
  have hf : AEMeasurable f P := hh.aemeasurable.prodMk hD
  have hf' : AEMeasurable f' P' := hh'.aemeasurable.prodMk hD'
  let μ : Measure (DistC × ContMetric) := P.map f
  let T : DistC × ContMetric → (CoordJ → ℝ) × RatCoords :=
    fun q => (pairJ ⊤ q.1, finiteRatCoords q.2)
  have hT : AEMeasurable T μ := by
    exact ((measurable_pairJ ⊤).comp measurable_fst).aemeasurable.prodMk
      (aemeasurable_finiteRatCoords Prod.snd measurable_snd.aemeasurable)
  have hlaw' : μ = P'.map f' := hlaw
  have hT' : AEMeasurable T (P'.map f') := by
    rw [← hlaw']
    exact hT
  have he : (fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)) =ᵐ[P]
      T ∘ f := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D hD] with ω hω
    simp [T, f, hω]
  have he' : (fun ω => (pairJ ⊤ (h' ω), measurableRatCoordsVersion D' hD' ω)) =ᵐ[P']
      T ∘ f' := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D' hD'] with ω hω
    simp [T, f', hω]
  calc
    P.map (fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)) =
        P.map (T ∘ f) := Measure.map_congr he
    _ = μ.map T := (AEMeasurable.map_map_of_aemeasurable hT hf).symm
    _ = (P'.map f').map T := by rw [hlaw']
    _ = P'.map (T ∘ f') := AEMeasurable.map_map_of_aemeasurable hT' hf'
    _ = P'.map (fun ω =>
        (pairJ ⊤ (h' ω), measurableRatCoordsVersion D' hD' ω)) :=
      Measure.map_congr he'.symm

 
def canonicalNormalizedContLFPP (ξ : ℝ) (δ a : Set.Ioi (0 : ℝ))
    (g : DistC) : ContMetric :=
  normalizedContLFPP ξ a (canonicalHeatVersion δ g)

theorem measurable_canonicalNormalizedContLFPP
    (ξ : ℝ) (δ a : Set.Ioi (0 : ℝ)) :
    Measurable (canonicalNormalizedContLFPP ξ δ a) :=
  (measurable_normalizedContLFPP ξ a).comp
    (canonicalHeatVersion_measurable δ)

 
def canonicalRatCoords (ξ : ℝ) (δ a : Set.Ioi (0 : ℝ)) :
    DistC → RatCoords := by
  letI : IsProbabilityMeasure normGFFLaw :=
    B2.PfeAxioms.normalized_canonical_model.1
  exact measurableRatCoordsVersion (P := normGFFLaw)
    (canonicalNormalizedContLFPP ξ δ a)
    (measurable_canonicalNormalizedContLFPP ξ δ a).aemeasurable

theorem measurable_canonicalRatCoords (ξ : ℝ) (δ a : Set.Ioi (0 : ℝ)) :
    Measurable (canonicalRatCoords ξ δ a) := by
  letI : IsProbabilityMeasure normGFFLaw :=
    B2.PfeAxioms.normalized_canonical_model.1
  exact measurable_measurableRatCoordsVersion (P := normGFFLaw)
    (canonicalNormalizedContLFPP ξ δ a)
    (measurable_canonicalNormalizedContLFPP ξ δ a).aemeasurable

 

theorem joint_rat_coords_law_eq_canonical
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (δ a : Set.Ioi (0 : ℝ)) (ξ : ℝ)
    (X : Ω → C(ℂ, ℝ)) (hX : IsHeatSmoothing P h δ X) :
    P.map (fun ω => (pairJ ⊤ (h ω),
      measurableRatCoordsVersion
        (fun ω => normalizedContLFPP ξ a (X ω))
        (aemeasurable_normalizedContLFPP_heat_version P h hh δ a ξ X hX) ω)) =
      normGFFLaw.map (fun g => (pairJ ⊤ g, canonicalRatCoords ξ δ a g)) := by
  letI : IsProbabilityMeasure normGFFLaw :=
    B2.PfeAxioms.normalized_canonical_model.1
  let D : Ω → ContMetric := fun ω => normalizedContLFPP ξ a (X ω)
  have hD : AEMeasurable D P :=
    aemeasurable_normalizedContLFPP_heat_version P h hh δ a ξ X hX
  let Dc : DistC → ContMetric := canonicalNormalizedContLFPP ξ δ a
  have hDc : AEMeasurable Dc normGFFLaw :=
    (measurable_canonicalNormalizedContLFPP ξ δ a).aemeasurable
  have hpair : P.map (fun ω => (h ω, D ω)) =
      normGFFLaw.map (fun g => (g, Dc g)) :=
    joint_law_normalizedContLFPP_eq_canonical P h hh δ a ξ X hX
  convert joint_finite_coords_law_of_pair_law P normGFFLaw
    h hh.1.measurable D hD
    (id : DistC → DistC) measurable_id Dc hDc hpair using 1
  · rfl

end SupercriticalLQGUniqueness.B2.DG20Lim
