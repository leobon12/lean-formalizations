import HigherDimLQGMetric.Locality.WeylFiber
import LQGMetric.Papers.DFGPS.L2_17Core3B

/-! The exterior internal metric is measurable from a Weyl cutoff and the
intrinsic coordinate of the independent perturbed metric, modulo null sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Topology Set
open LQGMetric.GM.Bilip
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_weyl_internal_comap_le_aeClosure {d : ℕ} (ξ : ℝ)
    {U : Set (Rd d)} (hU : IsOpen U)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (ρ : Measure E) [IsProbabilityMeasure ρ]
    (D₁ D₂ : E → ContMetric d) (hD₁ : Measurable D₁)
    (F : E → C(Rd d, ℝ)) (hF : Measurable F)
    (J : E → C(U × U, ℝ)) (hJ : Measurable J)
    (hgood : ∀ᵐ e ∂ρ,
      (D₁ e).IsLength ∧
      (∃ hE : LQGMetric.MetricGeometry.IsMetricFun (J e),
        ∀ u v : U, (D₂ e).internal U u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J e) hE u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J e) hE v)) ∧
      (∀ u v : Rd d,
        ENNReal.ofReal ((D₁ e).1 (u,v)) = weylScale ξ (F e) (D₂ e) u v)) :
    MeasurableSpace.comap (fun e => (D₁ e).chainInf U) inferInstance ≤
      aeClosure ρ (MeasurableSpace.comap (fun e => (F e, J e)) inferInstance) := by
  letI := hU.locallyCompactSpace
  letI : PolishSpace C(Rd d, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  letI : PolishSpace C(U × U, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  let G : E → Rd d → Rd d → ℝ≥0∞ := fun e => (D₁ e).chainInf U
  let R : E → C(Rd d, ℝ) × C(U × U, ℝ) := fun e => (F e, J e)
  let Good : E → Prop := fun e =>
    (D₁ e).IsLength ∧
      (∃ hE : LQGMetric.MetricGeometry.IsMetricFun (J e),
        ∀ u v : U, (D₂ e).internal U u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J e) hE u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J e) hE v)) ∧
      (∀ u v : Rd d,
        ENNReal.ofReal ((D₁ e).1 (u,v)) = weylScale ξ (F e) (D₂ e) u v)
  have hG : Measurable G := by
    apply measurable_pi_iff.mpr
    intro u
    apply measurable_pi_iff.mpr
    intro v
    exact (ContMetric.measurable_chainInf U).comp
      (hD₁.prodMk (measurable_const.prodMk measurable_const))
  have hR : Measurable R := hF.prodMk hJ
  have hrep := LQGMetric.DFGPS.L217.comap_le_aeClosure_of_rep
    (P' := ρ) (Z := id) (Good := Good) measurable_id hG hR hgood
    (fun e he e' he' hRe => by
      obtain ⟨hFe, hJe⟩ := Prod.mk.inj hRe
      have hc' : ∃ hE : LQGMetric.MetricGeometry.IsMetricFun (J e),
          ∀ u v : U, (D₂ e').internal U u.1 v.1 =
            LQGMetric.MetricGeometry.internalEDist univ
              (LQGMetric.MetricGeometry.MetricFunSpace.pt (J e) hE u)
              (LQGMetric.MetricGeometry.MetricFunSpace.pt (J e) hE v) := by
        have ht := he'.2.1
        rw [← hJe] at ht
        exact ht
      have hw' : ∀ u v : Rd d,
          ENNReal.ofReal ((D₁ e').1 (u,v)) =
            weylScale ξ (F e) (D₂ e') u v := by
        simpa only [hFe] using he'.2.2
      funext u v
      change (D₁ e).chainInf U u v = (D₁ e').chainInf U u v
      rw [← (D₁ e).internal_eq_chainInf he.1 hU u v,
        ← (D₁ e').internal_eq_chainInf he'.1 hU u v]
      exact l7a_internal_fiber_of_weyl ξ hU (J e) (F e)
        (D₁ e) (D₁ e') (D₂ e) (D₂ e') he.2.1 hc'
        he.2.2 hw' u v)
  simpa only [G, R, Measure.map_id, Function.comp_id] using hrep

end HigherDimLQGMetric
