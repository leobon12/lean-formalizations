import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.RadiusBridges
import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.OmegaComparison




 


set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
open LQGMetric (DistC)

 


def regularizedTarget (ξ : Set.Ioi (0 : ℝ))
    (D D' : DistC → LSCMetric) (T : Objects.CorrectedEvent.TubeData)
    (cPlus : ℝ≥0∞) (E : Set DistC) : Set DistC :=
  E ∩ {g | Objects.Producer.LocalGood ξ D D' (range (Objects.CorrectedEvent.site T)) ∅ g} ∩
    {g | ∀ x y : ℂ, D' g (x, y) ≤ ENNReal.ofReal cPlus.toReal * D g (x, y)}

theorem regularizedTarget_event {ξ : Set.Ioi (0 : ℝ)}
    {D D' : DistC → LSCMetric} {T : Objects.CorrectedEvent.TubeData}
    {cPlus : ℝ≥0∞} {E : Set DistC} {g : DistC}
    (hg : g ∈ regularizedTarget ξ D D' T cPlus E) : g ∈ E := hg.1.1

theorem regularizedTarget_good {ξ : Set.Ioi (0 : ℝ)}
    {D D' : DistC → LSCMetric} {T : Objects.CorrectedEvent.TubeData}
    {cPlus : ℝ≥0∞} {E : Set DistC} {g : DistC}
    (hg : g ∈ regularizedTarget ξ D D' T cPlus E) :
    Objects.Producer.LocalGood ξ D D' (range (Objects.CorrectedEvent.site T)) ∅ g := hg.1.2

theorem regularizedTarget_comp {ξ : Set.Ioi (0 : ℝ)}
    {D D' : DistC → LSCMetric} {T : Objects.CorrectedEvent.TubeData}
    {cPlus : ℝ≥0∞} {E : Set DistC} {g : DistC}
    (hg : g ∈ regularizedTarget ξ D D' T cPlus E) :
    ∀ x y : ℂ, D' g (x, y) ≤ ENNReal.ofReal cPlus.toReal * D g (x, y) := hg.2

 
theorem measure_regularizedTarget
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (hQ : 0 < Q)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus) (hPlusFin : cPlus < ⊤)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (T : Objects.CorrectedEvent.TubeData) (E : Set DistC) :
    (P.map h) (regularizedTarget ξ D D' T cPlus E) = (P.map h) E := by
  have hreg : ∀ᵐ g ∂(P.map h),
      Objects.Producer.LocalGood ξ D D' (range (Objects.CorrectedEvent.site T)) ∅ g :=
    Objects.Producer.ae_localGood hGFF hD hD' hQ (Set.countable_range _) Set.countable_empty
  have hcomp := ae_optimal_upper_field P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hPlusPos hPlusFin hMinus hPlus
  let G : Set DistC := {g | Objects.Producer.LocalGood ξ D D' (range (Objects.CorrectedEvent.site T)) ∅ g}
  let C : Set DistC := {g | ∀ x y : ℂ,
    D' g (x, y) ≤ ENNReal.ofReal cPlus.toReal * D g (x, y)}
  have hregSet : ∀ᵐ g ∂(P.map h), g ∈ G := hreg
  have hcompSet : ∀ᵐ g ∂(P.map h), g ∈ C := hcomp
  change (P.map h) ((E ∩ G) ∩ C) = (P.map h) E
  calc
    (P.map h) ((E ∩ G) ∩ C) = (P.map h) (C ∩ (E ∩ G)) := by rw [inter_comm]
    _ = (P.map h) (E ∩ G) := Measure.measure_inter_eq_of_ae hcompSet
    _ = (P.map h) (G ∩ E) := by rw [inter_comm]
    _ = (P.map h) E := Measure.measure_inter_eq_of_ae hregSet

 
theorem regularizedTarget_crossings {ξ : Set.Ioi (0 : ℝ)}
    {D D' : DistC → LSCMetric} {T : Objects.CorrectedEvent.TubeData}
    {cPlus : ℝ≥0∞} {E : Set DistC}
    (r : Set.Ioi (0 : ℝ)) {g : DistC}
    (hg : g ∈ regularizedTarget ξ D D' T cPlus E) :
    (Objects.CorrectedEvent.ambientAcross (D g) 0 (r : ℝ) (1.5 * (r : ℝ)) =
      Objects.CorrectedEvent.acr (D g) 0 (r : ℝ) (1.5 * (r : ℝ))) ∧
    (Objects.CorrectedEvent.ambientAcross (D g) 0 (2.5 * (r : ℝ)) (3 * (r : ℝ)) =
      Objects.CorrectedEvent.acr (D g) 0 (2.5 * (r : ℝ)) (3 * (r : ℝ))) :=
  ⟨inner_across_eq_acr (regularizedTarget_good hg) r,
    outer_across_eq_acr (regularizedTarget_good hg) r⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
