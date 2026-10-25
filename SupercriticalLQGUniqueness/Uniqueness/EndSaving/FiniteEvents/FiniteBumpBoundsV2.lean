import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.InterfaceV2




 




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents

 

theorem finite_bump_values_bounds_v2
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (h : Ω → LQGMetric.DistC)
    (D D' : LQGMetric.DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ)) (S : Finset ι) (z : ι → ℂ)
    (obj : ∀ i : ι, EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar (z i) r)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint ((obj i).V : Set ℂ) ((obj j).V : Set ℂ))
    (x : ℂ) :
    0 ≤ ∑ i ∈ S, (obj i).f x ∧
      (∑ i ∈ S, (obj i).f x) ≤ par.Cmax := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (obj i).f_nonneg x)
  · by_cases hex : ∃ i ∈ S, x ∈ ((obj i).V : Set ℂ)
    · obtain ⟨i, hi, hxi⟩ := hex
      have hzero : ∀ j ∈ S, j ≠ i → (obj j).f x = 0 := by
        intro j hj hji
        apply (obj j).f_off_V x
        exact fun hxj => (Set.disjoint_left.mp (hdisj i hi j hj hji.symm)) hxi hxj
      have hsum : (∑ j ∈ S, (obj j).f x) = (obj i).f x := by
        apply Finset.sum_eq_single i
        · exact hzero
        · intro hnot
          exact False.elim (hnot hi)
      rw [hsum]
      exact (obj i).f_le x
    · have hzero : ∀ i ∈ S, (obj i).f x = 0 := by
        intro i hi
        exact (obj i).f_off_V x (fun hxi => hex ⟨i, hi, hxi⟩)
      have hsum : (∑ i ∈ S, (obj i).f x) = 0 :=
        Finset.sum_eq_zero hzero
      rw [hsum]
      exact par.max_pos.le

 
theorem configuration_V_disjoint_v2
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistC)
    (D D' : LQGMetric.DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (S : Finset (ℤ × ℤ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ S) :
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint ((obj i).V : Set ℂ) ((obj j).V : Set ℂ) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi4 : x ∈ Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
      (4 * (r : ℝ)) := by
    rw [Metric.mem_ball]
    have h3 := ((obj i).V_annular).1 hxi
    change (r : ℝ) < dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) ∧
      dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) < 3 * (r : ℝ) at h3
    have hr : (0 : ℝ) < (r : ℝ) := r.property
    linarith only [h3.2, hr]
  have hj4 : x ∈ Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) j)
      (4 * (r : ℝ)) := by
    rw [Metric.mem_ball]
    have h3 := ((obj j).V_annular).1 hxj
    change (r : ℝ) < dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) ∧
      dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) < 3 * (r : ℝ) at h3
    have hr : (0 : ℝ) < (r : ℝ) := r.property
    linarith only [h3.2, hr]
  exact Set.disjoint_left.mp (hconfig.1 i hi j hj hij) hi4 hj4

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents
