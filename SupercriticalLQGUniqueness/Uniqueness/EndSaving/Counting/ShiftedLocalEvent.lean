import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.LocalFiniteMetric
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.CircleAverageShift




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC TestC)

 

theorem shifted_local_event_at_site_ae
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ Z)
    (i : ℤ × ℤ) (hi : i ∈ Z) :
    ∀ᵐ ω ∂P,
      LQGMetric.addFun (h ω) (LQGMetric.testCont
        (EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z)) ∈ (obj i).E ↔
      LQGMetric.addFun (h ω) (LQGMetric.testCont (obj i).f) ∈ (obj i).E := by
  classical
  let T := Z.erase i
  let z := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
  let K : Set ℂ := {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}
  let φ : TestC := ∑ j ∈ T, (obj j).f
  let ψ : TestC := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z
  have hremote : ∀ j ∈ T, ∃ ε > 0,
      Disjoint (tsupport (((obj j).f : TestC) : ℂ → ℝ))
        (Metric.thickening ε K) := by
    intro j hj
    have hji : j ≠ i ∧ j ∈ Z := Finset.mem_erase.mp hj
    exact EndSaving.FiniteEvents.configuration_remote_bump_v2 P h D D' ξ Q cMid par pbar
      r b K₁ K₂ Z obj hconfig i hi j hji.2 hji.1.symm
  have hG : ∀ u ∈ T.image (fun j => (obj j).f), ∃ ε > 0,
      Disjoint (tsupport (u : ℂ → ℝ)) (Metric.thickening ε K) := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    exact hremote j hj
  obtain ⟨ε, hε, hAll⟩ := LQGMetric.GM.exists_eps_disjoint_cm K
    (T.image (fun j => (obj j).f)) hG
  have hφ : ∃ ε > 0,
      Disjoint (tsupport (φ : ℂ → ℝ)) (Metric.thickening ε K) := by
    refine ⟨ε, hε, ?_⟩
    apply Set.disjoint_left.mpr
    intro x hx hxK
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp
      (EndSaving.RadonNikodym.tsupport_finset_sum_subset T (fun j => (obj j).f) hx)
    exact Set.disjoint_left.mp
      (hAll (obj j).f (Finset.mem_image.mpr ⟨j, hj, rfl⟩)) hxj hxK
  have hloc := EndSaving.Scaling.local_event_subTest_shifted_ae P h hh K φ ψ hφ
    (obj i).E (obj i).E_measurable (obj i).E_constant (obj i).E_local
  have hsum : ψ - φ = (obj i).f := by
    dsimp [ψ, φ, EndSaving.FiniteEvents.bumpSumV2, T]
    have heq : (∑ j ∈ Z, (obj j).f) =
        (obj i).f + ∑ j ∈ Z.erase i, (obj j).f :=
      (Finset.add_sum_erase Z _ hi).symm
    rw [heq]
    abel
  filter_upwards [hloc] with ω hω
  have heq := EndSaving.Choices.subTest_addFun (h ω) ψ φ
  rw [hsum] at heq
  rw [heq] at hω
  simpa only [ψ] using hω.symm

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
