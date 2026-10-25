import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.ObjectRNBridgeV2




 





set_option autoImplicit false
noncomputable section
open Set Finset
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
open LQGMetric (TestC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces

 
theorem finiteBumpSum_eq_one_on_ball
    {ι : Type} [DecidableEq ι] (Z : Finset ι) (f : ι → TestC)
    (z : ι → ℂ) (r : ℝ)
    (hsupp : ∀ i ∈ Z,
      tsupport (⇑(f i) : ℂ → ℝ) ⊆ Metric.ball (z i) (4 * r))
    (hballs : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
      Disjoint (Metric.ball (z i) (4 * r))
        (Metric.ball (z j) (4 * r)))
    (i : ι) (hi : i ∈ Z) (x : ℂ)
    (hx : x ∈ Metric.ball (z i) (4 * r)) :
    (∑ j ∈ Z, f j : TestC) x = f i x := by
  have hzero : ∀ j ∈ Z, j ≠ i → f j x = 0 := by
    intro j hj hji
    have hnot : x ∉ Metric.ball (z j) (4 * r) :=
      fun hmem => Set.disjoint_left.mp (hballs i hi j hj hji.symm) hx hmem
    have hts : x ∉ tsupport (⇑(f j) : ℂ → ℝ) :=
      fun hmem => hnot (hsupp j hj hmem)
    exact image_eq_zero_of_notMem_tsupport hts
  rw [_root_.sum_apply]
  exact Finset.sum_eq_single i hzero (fun hnot => (hnot hi).elim)

 

theorem objectBumpSum_eq_one_on_ball
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : MeasureTheory.Measure Ω) (h : Ω → LQGMetric.DistC)
    (D D' : LQGMetric.DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (par : Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ)) (Z : Finset ι) (z : ι → ℂ)
    (obj : ∀ i : ι, i ∈ Z →
      ObjectAtV2 P h D D' ξ Q cMid par pbar (z i) r)
    (hballs : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
      Disjoint (Metric.ball (z i) (4 * (r : ℝ)))
        (Metric.ball (z j) (4 * (r : ℝ))))
    (i : ι) (hi : i ∈ Z) (x : ℂ)
    (hx : x ∈ Metric.ball (z i) (4 * (r : ℝ))) :
    let f : ι → TestC := fun j => if hj : j ∈ Z then (obj j hj).f else 0
    (∑ j ∈ Z, f j : TestC) x = (obj i hi).f x := by
  classical
  dsimp only
  let f : ι → TestC := fun j => if hj : j ∈ Z then (obj j hj).f else 0
  have hf : ∀ j : ι, ∀ hj : j ∈ Z, f j = (obj j hj).f := by
    intro j hj
    simp [f, hj]
  have hsup : ∀ j ∈ Z,
      tsupport (⇑(f j) : ℂ → ℝ) ⊆ Metric.ball (z j) (4 * (r : ℝ)) := by
    intro j hj
    rw [hf j hj]
    exact ObjectAtV2.tsupport_f_subset_ball4 (obj j hj)
  rw [← hf i hi]
  exact finiteBumpSum_eq_one_on_ball Z f z (r : ℝ) hsup hballs i hi x hx

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
