import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero.Around
import SupercriticalLQGUniqueness.Uniqueness.Objects.Compare.CompareGeometry




 






set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero

open SupercriticalLQGUniqueness
open Set Metric
open scoped ENNReal

 

theorem acr_le_dist_of_endpoint_order (D : LSCMetric)
    (hL : D.IsLengthSpace) (hForget : Continuous (BiLipschitz.Barrier.forget D))
    {x y z : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hx : dist x z ≤ a) (hy : b ≤ dist y z) :
    Objects.CorrectedEvent.acr D z a b ≤ D (x, y) := by
  rw [(LSCMetric.isLengthSpace_iff_eq_iInf D).mp hL]
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t =>
    le_iInf fun hP => le_iInf fun hPs => le_iInf fun hPt => ?_
  have hCont : ContinuousOn P (Icc s t) := hForget.comp_continuousOn hP.2
  exact Objects.Compare.acr_le_curve_of_endpoint_order D hP hCont hab (hPs.symm ▸ hx) (hPt.symm ▸ hy)

 

theorem across_bound_of_corrected_event {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {par : EndSaving.Interfaces.Parameters ξ} {r : Set.Ioi (0 : ℝ)}
    {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {hData : Objects.CorrectedEvent.DataMatch C T}
    {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (hEvent : Objects.CorrectedEvent.correctedEvent C T hData F D D' g)
    (hL : (D g).IsLengthSpace) (hForget : Continuous (BiLipschitz.Barrier.forget (D g)))
    (hInner : Objects.CorrectedEvent.ambientAcross (D g) 0 C.r (1.5 * C.r) =
      Objects.CorrectedEvent.acr (D g) 0 C.r (1.5 * C.r))
    (hOuter : Objects.CorrectedEvent.ambientAcross (D g) 0 (2.5 * C.r) (3 * C.r) =
      Objects.CorrectedEvent.acr (D g) 0 (2.5 * C.r) (3 * C.r))
    (hXi : C.ξ = ξ) (hQ : C.Q = Q) (hR : C.r = r)
    (hAcross : par.Cacross = C.A_across)
    {V : Set ℂ} (hV : V ⊆ {x : ℂ | 1.5 * (r : ℝ) < dist x 0 ∧
      dist x 0 < 2.5 * (r : ℝ)})
    {c : ℝ} (hc : IsCircleAverage g r 0 c) :
    ENNReal.ofReal par.Cacross *
      ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)) ≤
      OptimalConstants.Ratios.setDist (D g) V (sphere 0 r ∪ sphere 0 (3 * (r : ℝ))) := by
  have hr : 0 < (r : ℝ) := r.2
  have hAvg := Objects.Producer.circleAvg_eq_of_isCircleAverage hc
  have hN : Objects.CorrectedEvent.normalizer C g C.r 0 =
      ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)) := by
    simp only [Objects.CorrectedEvent.normalizer, hXi, hQ, hR, hAvg]
  have hbar := Objects.CorrectedEvent.event_across_of_barrier_equalities hEvent hInner hOuter
  rw [hN, ← hAcross, hR] at hbar
  rw [hR] at hInner hOuter
  unfold OptimalConstants.Ratios.setDist
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  have hxmid := hV hx
  rcases hy with hy | hy
  · have hyR : dist y 0 = (r : ℝ) := mem_sphere.mp hy
    have hcost := acr_le_dist_of_endpoint_order (D g) hL hForget
      (x := y) (y := x) (z := 0) (a := (r : ℝ)) (b := 1.5 * (r : ℝ))
      (by linarith) hyR.le hxmid.1.le
    calc
      ENNReal.ofReal par.Cacross *
          ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c))
          ≤ Objects.CorrectedEvent.acr (D g) 0 r (1.5 * (r : ℝ)) := by rw [← hInner]; exact hbar.1
      _ ≤ (D g) (y, x) := hcost
      _ = (D g) (x, y) := (D g).isExtMetric.2.2.1 y x
  · have hyR : dist y 0 = 3 * (r : ℝ) := mem_sphere.mp hy
    have hcost := acr_le_dist_of_endpoint_order (D g) hL hForget
      (x := x) (y := y) (z := 0) (a := 2.5 * (r : ℝ)) (b := 3 * (r : ℝ))
      (by linarith) hxmid.2.le hyR.ge
    calc
      ENNReal.ofReal par.Cacross *
          ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c))
          ≤ Objects.CorrectedEvent.acr (D g) 0 (2.5 * (r : ℝ)) (3 * (r : ℝ)) := by rw [← hOuter]; exact hbar.2
      _ ≤ (D g) (x, y) := hcost

end SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero
