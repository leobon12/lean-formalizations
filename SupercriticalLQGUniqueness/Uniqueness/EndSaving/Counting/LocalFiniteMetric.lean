import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.TwoShiftInternal
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.RemoteBumpV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteBumpBoundsV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteEventsV2




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC)

private def euclidForget'' (D : LSCMetric) : D.Space → ℂ := id

 


theorem finite_shift_internal_eq_at_site
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z)
    (g : DistC)
    (hforget : Continuous (euclidForget'' (D g)))
    (hLength : (D g).IsLengthSpace)
    (hWeyl : ∀ f : C(ℂ, ℝ),
      weylScale (ξ : ℝ) f (D g) = (D (LQGMetric.addFun g f)).1)
    (i : ℤ × ℤ) (hi : i ∈ Z)
    (W : Set ℂ)
    (hW : W ⊆ Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
      (4 * (r : ℝ))) (p : W × W) :
    (D (LQGMetric.addFun g (LQGMetric.testCont
      (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)))).internal W p =
    (D (LQGMetric.addFun g (LQGMetric.testCont (obj i).f))).internal W p := by
  classical
  let fZ := LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)
  let fi := LQGMetric.testCont (obj i).f
  have hV := EndSaving.FiniteEvents.configuration_V_disjoint_v2 P h D D' ξ Q cMid par pbar
    r b K₁ K₂ Z obj hconfig
  have hfZ : ∀ x : ℂ, 0 ≤ fZ x ∧ fZ x ≤ par.Cmax := by
    intro x
    have hbound := EndSaving.FiniteEvents.finite_bump_values_bounds_v2 P h D D' ξ Q cMid
      par pbar r Z (fun j => LQGMetric.GM.gridPt ((r : ℝ) / 100) j) obj hV x
    change 0 ≤ (∑ j ∈ Z, (obj j).f) x ∧
      (∑ j ∈ Z, (obj j).f) x ≤ par.Cmax
    rw [_root_.sum_apply]
    exact hbound
  have hfi : ∀ x : ℂ, 0 ≤ fi x ∧ fi x ≤ par.Cmax := by
    intro x
    exact ⟨(obj i).f_nonneg x, (obj i).f_le x⟩
  have hfg : ∀ x ∈ W, fZ x = fi x := by
    intro x hx
    have hsup : ∀ j ∈ Z,
        tsupport (⇑((obj j).f) : ℂ → ℝ) ⊆
          Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) j)
            (4 * (r : ℝ)) := by
      intro j _
      exact EndSaving.RadonNikodym.ObjectAtV2.tsupport_f_subset_ball4 (obj j)
    have hlocal := EndSaving.RadonNikodym.finiteBumpSum_eq_one_on_ball Z
      (fun j => (obj j).f)
      (fun j => LQGMetric.GM.gridPt ((r : ℝ) / 100) j)
      (r : ℝ) hsup hconfig.1 i hi x (hW hx)
    exact hlocal
  have hEz : ∀ q : ℂ × ℂ,
      D (LQGMetric.addFun g fZ) q = weylScale (ξ : ℝ) fZ (D g) q := by
    intro q
    exact (congrFun (hWeyl fZ) q).symm
  have hEi : ∀ q : ℂ × ℂ,
      D (LQGMetric.addFun g fi) q = weylScale (ξ : ℝ) fi (D g) q := by
    intro q
    exact (congrFun (hWeyl fi) q).symm
  exact internal_eq_of_shifts_agree_on_carrier (D g)
    (D (LQGMetric.addFun g fZ)) (D (LQGMetric.addFun g fi))
    (ξ : ℝ) ξ.2.le fZ fi 0 par.Cmax 0 par.Cmax
    hforget hLength hEz hEi hfZ hfi W hfg p

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
