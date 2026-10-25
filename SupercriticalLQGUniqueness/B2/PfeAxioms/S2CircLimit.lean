import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircCoupled
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLSCMetric
import SupercriticalLQGUniqueness.B2.DG20Lim.LSCConvergence
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoordEmbedding
import SupercriticalLQGUniqueness.B2.PfeWeyl.CircleLiminf

 










set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open SupercriticalLQGUniqueness.B2.DG20Lim

theorem setDistance_finiteLSCMetric (D : LQGMetric.ContMetric) (A B : Set ℂ) :
    B2.Iface.setDistance (finiteLSCMetric D) A B = LQGMetric.Blueprint.setDist D A B := by
  unfold B2.Iface.setDistance LQGMetric.Blueprint.setDist
  rw [LQGMetric.MetricGeometry.setEDist_eq_iInf]
  simp only [iInf_image]
  rfl

 
theorem limit_circleCoord_eq_setDistance
    {Y : ℕ → (LQGMetric.CoordJ → ℝ) × RatCoords} {y : (LQGMetric.CoordJ → ℝ) × RatCoords}
    (hY : Tendsto Y atTop (𝓝 y))
    (hRange : ∀ n, finiteCircleCoords (circleCoordsInv (Y n).2.1) = (Y n).2.1)
    (L : LSCMetric)
    (hLsc : LSCTendsto (fun n => finiteMetricE (circleCoordsInv (Y n).2.1)) L.toLSCFun.1)
    (R : RData) (hRa : R.across = fun O Q => y.2.1 (O, Q)) (hRb : R.around = y.2.2)
    (hRL : LSCTendsto (fun n => finiteMetricE (circleCoordsInv (Y n).2.1)) R.toLSCFun.1)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hcrossFin : ∀ n (A : RatAnnulus) (O₁ O₁' Q : RatCircle),
      A.OppositeSides O₁ O₁' → CrossesAnn Q A →
      (Y n).2.1 (O₁, Q) ≤ (Y n).2.1 (O₁, O₁') + (Y n).2.2 A)
    (hinterFin : ∀ n (O Q : RatCircle), (O.toSet ∩ Q.toSet).Nonempty → (Y n).2.1 (O, Q) = 0)
    (hGood : ∀ z : ℂ, ∃ B : ℕ → RatAnnulus,
      (∀ n, (B n).inner.Surrounds z ∧ R.around (B n) ≤ C * R.across (B n).inner (B n).outer) ∧
      (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
      Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0))
    (hvanish : ∀ Z : RatCircle, Z.radius = 0 → ∀ O : ℕ → RatCircle,
      (∀ᶠ n in atTop, (O n).Surrounds Z.center) →
      Tendsto (fun n => ((O n).radius : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n => y.2.1 (Z, O n)) atTop (𝓝 0))
    (O Q : RatCircle) :
    y.2.1 (O, Q) = B2.Iface.setDistance L O.toSet Q.toSet := by
  set G : ℕ → LSCMetric := fun n => finiteLSCMetric (circleCoordsInv (Y n).2.1) with hGdef
  have hGfun : ∀ n, (G n).toLSCFun.1 = finiteMetricE (circleCoordsInv (Y n).2.1) := fun n =>
    finiteLSCMetric_toLSCFun _
  have hGL : Tendsto G atTop (𝓝 L) := by
    rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff, LSCFun.tendsto_iff_lscTendsto]
    simpa only [Function.comp_apply, hGfun] using hLsc
  have hGR : Tendsto (fun n => (G n).toLSCFun) atTop (𝓝 R.toLSCFun) := by
    rw [LSCFun.tendsto_iff_lscTendsto]
    simpa only [hGfun] using hRL
  have hLR : L.toLSCFun = R.toLSCFun :=
    tendsto_nhds_unique (LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff.1 hGL) hGR
  have hLval : ∀ u v : ℂ, L (u, v) = R.DfromR u v := fun u v => by
    have h := congrArg (fun f : LSCFun => f.1 (u, v)) hLR
    simp only [LSCMetric.toLSCFun_apply, RData.toLSCFun] at h
    exact_mod_cast h
  have hcoord : ∀ n, (Y n).2.1 (O, Q) = B2.Iface.setDistance (G n) O.toSet Q.toSet := fun n => by
    rw [hGdef, setDistance_finiteLSCMetric]
    exact (congrFun (hRange n) (O, Q)).symm
  have hcross : ∀ (A : RatAnnulus) (O₁ O₁' Q' : RatCircle),
      A.OppositeSides O₁ O₁' → CrossesAnn Q' A →
      R.across O₁ Q' ≤ R.across O₁ O₁' + R.around A := by
    intro A O₁ O₁' Q' h₁ hQ'
    rw [hRa, hRb]
    exact limit_crossing_bound hY hcrossFin A O₁ O₁' Q' h₁ hQ'
  have hinter : ∀ O' Q' : RatCircle, (O'.toSet ∩ Q'.toSet).Nonempty → R.across O' Q' = 0 := by
    intro O' Q' h
    rw [hRa]
    exact limit_inter_zero hY hinterFin O' Q' h
  have hvanR : ∀ Z : RatCircle, Z.radius = 0 → ∀ O' : ℕ → RatCircle,
      (∀ᶠ n in atTop, (O' n).Surrounds Z.center) →
      Tendsto (fun n => ((O' n).radius : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n => R.across Z (O' n)) atTop (𝓝 0) := by
    intro Z hZ O' h1 h2
    rw [hRa]
    exact hvanish Z hZ O' h1 h2
  apply le_antisymm
  · have hyR : y.2.1 (O, Q) = R.across O Q := by rw [hRa]
    rw [hyR]
    refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
    rw [hLval]
    exact RData.across_le_DfromR_of_crossing R C hC hcross hinter hGood hvanR O Q hz hw
  · have hlim : Tendsto (fun n => B2.Iface.setDistance (G n) O.toSet Q.toSet) atTop
        (𝓝 (y.2.1 (O, Q))) := by
      have := tendsto_circleCoord hY O Q
      simpa only [hcoord] using this
    have h := PfeWeyl.setDistance_liminf_of_compact hGL (O := O.toSet) (O' := Q.toSet)
      (isCompact_sphere _ _) (isCompact_sphere _ _)
    rw [hlim.liminf_eq] at h
    exact h

end SupercriticalLQGUniqueness.B2.PfeAxioms
