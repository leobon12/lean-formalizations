import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.LocalShiftV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteBumpBoundsV2




 




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents
open LQGMetric (DistC TestC)

 


theorem finite_configuration_local_events_ae
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ)) (S : Finset ι)
    (z : ι → ℂ) (obj : ∀ i : ι,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar (z i) r)
    (f : ι → TestC)
    (hremote : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ∃ ε > 0, Disjoint (tsupport ((f j : TestC) : ℂ → ℝ))
        (Metric.thickening ε
          {x : ℂ | r ≤ dist x (z i) ∧ dist x (z i) ≤ 4 * (r : ℝ)})) :
    ∀ᵐ ω ∂P, ∀ i ∈ S, ∀ T ∈ (S.erase i).powerset,
      LQGMetric.GM.subTest (h ω) (∑ j ∈ T, f j) ∈ (obj i).E ↔
        h ω ∈ (obj i).E := by
  refine (Filter.eventually_all_finset S).2 ?_
  intro i hi
  refine (Filter.eventually_all_finset (S.erase i).powerset).2 ?_
  intro T hT
  apply (obj i).finiteBump_local_shift_ae_of_each hh T f
  intro j hj
  have hTS : T ⊆ S.erase i := Finset.mem_powerset.mp hT
  have hjs : j ≠ i ∧ j ∈ S := Finset.mem_erase.mp (hTS hj)
  exact hremote i hi j hjs.2 hjs.1.symm

 

theorem configuration_remote_bump_v2
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (S : Finset (ℤ × ℤ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ S) :
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ∃ ε > 0, Disjoint (tsupport (((obj j).f : TestC) : ℂ → ℝ))
        (Metric.thickening ε
          {x : ℂ | r ≤ dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) ∧
            dist x (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) ≤ 4 * (r : ℝ)}) := by
  intro i hi j hj hij
  let zi := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
  let zj := LQGMetric.GM.gridPt ((r : ℝ) / 100) j
  have hr : (0 : ℝ) < (r : ℝ) := r.property
  have h4 : 0 < 4 * (r : ℝ) := by linarith only [hr]
  have hcent : 8 * (r : ℝ) ≤ dist zi zj := by
    have hd := hconfig.1 i hi j hj hij
    have h := (disjoint_ball_ball_iff h4 h4).mp hd
    dsimp [zi, zj]
    linarith only [h]
  have hsupp : Function.support (fun x : ℂ => (obj j).f x) ⊆
      ((obj j).V : Set ℂ) := by
    intro x hx
    by_contra hnot
    have hzero := (obj j).f_off_V x hnot
    exact hx hzero
  have hts : tsupport (((obj j).f : TestC) : ℂ → ℝ) ⊆
      closure ((obj j).V : Set ℂ) := by
    exact closure_mono hsupp
  refine ⟨(r : ℝ) / 2, by positivity, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hthick
  have hxV := hts hx
  have hx3 := (obj j).closure_V_annulus hxV
  change (r : ℝ) < dist x zj ∧ dist x zj < 3 * (r : ℝ) at hx3
  obtain ⟨y, hyK, hxy⟩ := Metric.mem_thickening_iff.mp hthick
  change (r : ℝ) ≤ dist y zi ∧ dist y zi ≤ 4 * (r : ℝ) at hyK
  have htri : dist zi zj ≤ dist zi y + dist y x + dist x zj := by
    calc
      dist zi zj ≤ dist zi y + dist y zj := dist_triangle _ _ _
      _ ≤ dist zi y + (dist y x + dist x zj) := by gcongr; exact dist_triangle _ _ _
      _ = dist zi y + dist y x + dist x zj := by ring
  rw [dist_comm zi y] at htri
  rw [dist_comm y x] at htri
  linarith only [hcent, htri, hyK.2, hx3.2, hxy, hr]

 

theorem configuration_local_events_ae
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (S : Finset (ℤ × ℤ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (hconfig : EndSaving.Interfaces.Configuration r b K₁ K₂ S) :
    ∀ᵐ ω ∂P, ∀ i ∈ S, ∀ T ∈ (S.erase i).powerset,
      LQGMetric.GM.subTest (h ω) (∑ j ∈ T, (obj j).f) ∈ (obj i).E ↔
        h ω ∈ (obj i).E := by
  exact finite_configuration_local_events_ae P h hh D D' ξ Q cMid par pbar r S
    (fun i => LQGMetric.GM.gridPt ((r : ℝ) / 100) i) obj
    (fun i => (obj i).f)
    (configuration_remote_bump_v2 P h D D' ξ Q cMid par pbar r b K₁ K₂ S obj hconfig)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents
