import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.ShiftedLocalEvent




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC TestC)

 

theorem isCircleAverage_addFun_iff_of_zero_sphere
    (g : DistC) (f : C(ℂ, ℝ)) (r : Set.Ioi (0 : ℝ))
    (z : ℂ) (a : ℝ)
    (hf : ∀ x ∈ Metric.sphere z (r : ℝ), f x = 0) :
    IsCircleAverage (LQGMetric.addFun g f) r z a ↔
      IsCircleAverage g r z a := by
  constructor
  · intro ha
    have hneg : ∀ x ∈ Metric.sphere z (r : ℝ), (-f) x = 0 := by
      intro x hx
      simp only [ContinuousMap.neg_apply, hf x hx, neg_zero]
    have h := EndSaving.Scaling.isCircleAverage_addFun_of_zero_sphere
      (LQGMetric.addFun g f) (-f) r z a ha hneg
    simpa only [EndSaving.Choices.addFun_addFun, add_neg_cancel, EndSaving.Choices.addFun_zero] using h
  · exact fun ha => EndSaving.Scaling.isCircleAverage_addFun_of_zero_sphere
      g f r z a ha hf

 
theorem bumpSum_zero_on_reference_sphere
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z)
    (x : ℂ) (hx : x ∈ Metric.sphere (0 : ℂ) b) :
    LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z) x = 0 := by
  change (∑ j ∈ Z, (obj j).f) x = 0
  rw [_root_.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hnot : x ∉ Metric.ball
      (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) (4 * (r : ℝ)) := by
    intro hmem
    exact Set.disjoint_left.mp (hconfig.2 j hj) hmem (Or.inr hx)
  exact image_eq_zero_of_notMem_tsupport
    (fun hmem => hnot (EndSaving.RadonNikodym.ObjectAtV2.tsupport_f_subset_ball4 (obj j) hmem))

 
theorem bumpSum_zero_on_site_sphere
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z)
    (i : ℤ × ℤ) (hi : i ∈ Z)
    (x : ℂ) (hx : x ∈ Metric.sphere
      (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) :
    LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z) x = 0 := by
  let z := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
  have hdist : dist x z = (r : ℝ) := by simpa only [z, Metric.mem_sphere] using hx
  have hx4 : x ∈ Metric.ball z (4 * (r : ℝ)) := by
    rw [Metric.mem_ball, hdist]
    have hr : (0 : ℝ) < (r : ℝ) := r.property
    linarith only [hr]
  change (∑ j ∈ Z, (obj j).f) x = 0
  rw [_root_.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  apply (obj j).f_off_V x
  intro hxV
  by_cases hji : j = i
  · subst j
    have hv := ((obj i).V_annular).1 hxV
    change (r : ℝ) < dist x z ∧ dist x z < 3 * (r : ℝ) at hv
    exact (lt_irrefl (r : ℝ)) (hdist ▸ hv.1)
  · have hxj4 : x ∈ Metric.ball
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) (4 * (r : ℝ)) := by
      rw [Metric.mem_ball]
      have hv := ((obj j).V_annular).1 hxV
      change (r : ℝ) < dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) ∧
        dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) < 3 * (r : ℝ) at hv
      have hr : (0 : ℝ) < (r : ℝ) := r.property
      linarith only [hv.2, hr]
    exact Set.disjoint_left.mp (hconfig.1 i hi j hj (Ne.symm hji)) hx4 hxj4

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
