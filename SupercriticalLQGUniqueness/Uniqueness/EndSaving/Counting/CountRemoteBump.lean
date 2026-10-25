import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.EventGood




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC)

theorem bumpSum_zero_on_disjoint_ball
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (i : ℤ × ℤ)
    (hsep : ∀ j ∈ Z,
      Disjoint
        (Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) (4 * (r : ℝ)))
        (Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))))
    (x : ℂ)
    (hx : x ∈ Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
      (4 * (r : ℝ))) :
    LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z) x = 0 := by
  change (∑ j ∈ Z, (obj j).f) x = 0
  rw [_root_.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hnot : x ∉ Metric.ball
      (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) (4 * (r : ℝ)) := by
    intro hmem
    exact Set.disjoint_left.mp (hsep j hj) hmem hx
  exact image_eq_zero_of_notMem_tsupport
    (fun hmem => hnot (EndSaving.RadonNikodym.ObjectAtV2.tsupport_f_subset_ball4 (obj j) hmem))

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
