import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.CountRemoteBump




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC)

theorem remote_shift_internal_eq
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
    (i : ℤ × ℤ)
    (hsep : ∀ j ∈ Z,
      Disjoint
        (Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) j) (4 * (r : ℝ)))
        (Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))))
    (g : DistC) (hreg : EndSaving.Choices.RegularAt D' (ξ : ℝ) g)
    (W : Set ℂ)
    (hW : W ⊆ Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
      (4 * (r : ℝ))) (p : W × W) :
    (D' (LQGMetric.addFun g (LQGMetric.testCont
      (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)))).internal W p =
    (D' g).internal W p := by
  let fZ := LQGMetric.testCont
    (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)
  have hV := EndSaving.FiniteEvents.configuration_V_disjoint_v2 P h D D' ξ Q cMid par pbar
    r b K₁ K₂ Z obj hconfig
  have hbound : ∀ x : ℂ, 0 ≤ fZ x ∧ fZ x ≤ par.Cmax := by
    intro x
    have h := EndSaving.FiniteEvents.finite_bump_values_bounds_v2 P h D D' ξ Q cMid
      par pbar r Z (fun j => LQGMetric.GM.gridPt ((r : ℝ) / 100) j) obj hV x
    change 0 ≤ (∑ j ∈ Z, (obj j).f) x ∧
      (∑ j ∈ Z, (obj j).f) x ≤ par.Cmax
    rw [_root_.sum_apply]
    exact h
  have hzero : ∀ x ∈ W, fZ x = 0 := by
    intro x hx
    exact bumpSum_zero_on_disjoint_ball P h D D' ξ Q cMid par pbar r
      obj Z i hsep x (hW hx)
  have hWeyl : ∀ q : ℂ × ℂ,
      D' (LQGMetric.addFun g fZ) q = weylScale (ξ : ℝ) fZ (D' g) q := by
    intro q
    exact (congrFun (hreg.weyl fZ) q).symm
  exact internal_eq_of_zero_on_carrier (D' g)
    (D' (LQGMetric.addFun g fZ)) (ξ : ℝ) ξ.2.le fZ 0 par.Cmax
    hreg.forget hreg.length hWeyl hbound W hzero p

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
