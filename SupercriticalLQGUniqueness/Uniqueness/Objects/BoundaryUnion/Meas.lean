import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.JointCompactPort
import Mathlib.MeasureTheory.Integral.CircleIntegral




 




set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnion

local instance : MeasurableSpace ℂ := borel ℂ
local instance : BorelSpace ℂ := ⟨rfl⟩
local instance : BorelSpace LSCMetric := ⟨rfl⟩
attribute [local irreducible] LSCMetric.internal

 

theorem measurable_internal_compact_moving
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    {K : Set ℂ} (hK : IsCompact K)
    (D : Ω → LSCMetric) (hD : Measurable D)
    (x : Θ → ℂ) (hx : Measurable x) (hxK : ∀ θ, x θ ∈ K) (y : K) :
    Measurable (fun p : Ω × Θ =>
      (D p.1).internal K (⟨x p.2, hxK p.2⟩, y)) := by
  have hX : Measurable (fun θ : Θ => (⟨x θ, hxK θ⟩ : K)) :=
    hx.subtype_mk
  have hp : Measurable (fun p : Ω × Θ =>
      (D p.1, ((⟨x p.2, hxK p.2⟩ : K), y))) :=
    (hD.comp measurable_fst).prodMk
      ((hX.comp measurable_snd).prodMk measurable_const)
  have hB : BorelSpace (LSCMetric × (K × K)) := inferInstance
  have hpB : @Measurable (Ω × Θ) (LSCMetric × (K × K))
      inferInstance (borel _) (fun p =>
        (D p.1, ((⟨x p.2, hxK p.2⟩ : K), y))) :=
    hp.mono le_rfl hB.measurable_eq.ge
  exact (TwoScale.S36Events.internal_compact_joint_borel hK).comp hpB

 

theorem measurable_ball_boundary_cost
    {Ω : Type*} [MeasurableSpace Ω] (D : Ω → LSCMetric) (hD : Measurable D)
    (c : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    Measurable (fun p : Ω × ℝ =>
      (D p.1).internal (Metric.closedBall c s)
        (⟨circleMap c s p.2, circleMap_mem_closedBall c hs p.2⟩,
         ⟨c, Metric.mem_closedBall_self hs⟩)) := by
  exact measurable_internal_compact_moving
    (isCompact_closedBall c s) D hD (circleMap c s)
    (continuous_circleMap c s).measurable
    (circleMap_mem_closedBall c hs)
    ⟨c, Metric.mem_closedBall_self hs⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnion
