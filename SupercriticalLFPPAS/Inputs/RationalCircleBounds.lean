import SupercriticalLQGUniqueness.B2.Strong.Annulus
import SupercriticalLQGUniqueness.B2.Strong.AroundFinite
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2GFFPlusCont
import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF

/-!
# Positive finite distance between fixed Euclidean circles

For disjoint circles of positive radii, compactness and lower semicontinuity give a
strictly positive set-distance.  Axiom V gives finite internal distance between the
circles; a finite-length internal path then bounds their ambient set-distance from above.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLFPPAS.Inputs.RationalCircleBounds

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Strong
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios

/-- Finite internal distance in an open set implies finite ambient set-distance. -/
theorem setDist_lt_top_of_internalSetDist_lt_top
    (d : LSCMetric) (U : Set ℂ) (K₁ K₂ : Set ℂ)
    (h : d.internalSetDist U (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < ⊤) :
    setDist d K₁ K₂ < ⊤ := by
  obtain ⟨P, a, b, hP, -, ha, hb, hlen⟩ :=
    exists_curve_of_internalSetDist_lt_top d U K₁ K₂ h
  calc
    setDist d K₁ K₂ ≤ d (P a, P b) :=
      iInf₂_le_of_le _ ha (iInf₂_le _ hb)
    _ ≤ d.len P a b := d.apply_le_len P hP.1
    _ < ⊤ := hlen

/-- Almost surely, the metric set-distance between two fixed disjoint Euclidean circles
of positive radius is strictly positive and finite for a strong LQG metric. -/
theorem ae_setDist_circle_pos_lt_top
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (c₁ c₂ : ℂ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdis : Disjoint (Metric.sphere c₁ r₁) (Metric.sphere c₂ r₂)) :
    ∀ᵐ ω ∂P,
      0 < setDist (D (h ω)) (Metric.sphere c₁ r₁) (Metric.sphere c₂ r₂) ∧
        setDist (D (h ω)) (Metric.sphere c₁ r₁) (Metric.sphere c₂ r₂) < ⊤ := by
  have hconn₁ : IsConnected (Metric.sphere c₁ r₁) :=
    ⟨(nontrivial_sphere c₁ hr₁).nonempty,
      LQGMetric.TopoCircle.isPreconnected_sphere_complex c₁ hr₁.le⟩
  have hconn₂ : IsConnected (Metric.sphere c₂ r₂) :=
    ⟨(nontrivial_sphere c₂ hr₂).nonempty,
      LQGMetric.TopoCircle.isPreconnected_sphere_complex c₂ hr₂.le⟩
  have hplus : LQGMetric.IsGFFPlusCont h P :=
    SupercriticalLQGUniqueness.B2.PfeAxioms.isGFFPlusCont_of_normalized hh
  let U : TopologicalSpace.Opens ℂ := ⊤
  have hfinite : ∀ᵐ ω ∂P,
      (D (h ω)).internalSetDist (U : Set ℂ)
        (Subtype.val ⁻¹' Metric.sphere c₁ r₁)
        (Subtype.val ⁻¹' Metric.sphere c₂ r₂) < ⊤ := by
    have hV := hD.2.2.2.2.2 P h hplus U (by simpa [U] using isConnected_univ)
      (Metric.sphere c₁ r₁) (Metric.sphere c₂ r₂)
      (isCompact_sphere c₁ r₁) (isCompact_sphere c₂ r₂)
      hconn₁ hconn₂ (nontrivial_sphere c₁ hr₁) (nontrivial_sphere c₂ hr₂)
      (by simp [U]) (by simp [U]) hdis
    exact hV
  filter_upwards [hfinite] with ω hω
  refine ⟨setDist_pos (D (h ω) : LSCMetric)
      (isCompact_sphere c₁ r₁) (isCompact_sphere c₂ r₂) hdis, ?_⟩
  exact setDist_lt_top_of_internalSetDist_lt_top (D (h ω)) (U : Set ℂ)
    (Metric.sphere c₁ r₁) (Metric.sphere c₂ r₂) hω

end SupercriticalLFPPAS.Inputs.RationalCircleBounds
