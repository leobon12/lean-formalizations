import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.FiniteRNWindowV2




 





set_option autoImplicit false
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
open LQGMetric (DistC TestC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces

 

theorem ObjectAtV2.tsupport_f_subset_ball4
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {D D' : DistC → LSCMetric} {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ}
    {par : Parameters ξ} {pbar : Set.Ioo (0 : ℝ) 1}
    {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : ObjectAtV2 P h D D' ξ Q cMid par pbar z r) :
    tsupport (⇑obj.f : ℂ → ℝ) ⊆ Metric.ball z (4 * (r : ℝ)) := by
  have hsup : Function.support (⇑obj.f : ℂ → ℝ) ⊆ (obj.V : Set ℂ) := by
    intro x hx
    by_contra hnot
    exact hx (obj.f_off_V x hnot)
  have hts : tsupport (⇑obj.f : ℂ → ℝ) ⊆ closure (obj.V : Set ℂ) :=
    closure_minimal (hsup.trans subset_closure) isClosed_closure
  intro x hx
  have hA := obj.closure_V_annulus (hts hx)
  change (r : ℝ) < dist x z ∧ dist x z < 3 * (r : ℝ) at hA
  show dist x z < 4 * (r : ℝ)
  nlinarith [hA.2, r.property]

 



theorem finiteBump_probability_window_of_objects
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ))
    (Q cMid : ℝ) (par : Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ)) (Z : Finset ι) (z : ι → ℂ)
    (obj : ∀ i : ι, i ∈ Z →
      ObjectAtV2 P h D D' ξ Q cMid par pbar (z i) r)
    (hballs : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
      Disjoint (Metric.ball (z i) (4 * (r : ℝ)))
        (Metric.ball (z j) (4 * (r : ℝ))))
    (E : Set DistC) (hE : MeasurableSet E)
    (hconst : ∀ (g : DistC) (c : ℝ),
      g ∈ E ↔ LQGMetric.addConst g c ∈ E)
    (hgood : ∀ g ∈ E, ∀ i : ι, ∀ hi : i ∈ Z, g ∈ (obj i hi).E) :
    let f : ι → TestC := fun i => if hi : i ∈ Z then (obj i hi).f else 0
    ENNReal.ofReal ((par.Crn⁻¹) ^ Z.card) * P (sampleEvent h E) ≤
      P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont (∑ i ∈ Z, f i))) E) ∧
    P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont (∑ i ∈ Z, f i))) E) ≤
      ENNReal.ofReal (par.Crn ^ Z.card) * P (sampleEvent h E) := by
  classical
  dsimp only
  let f : ι → TestC := fun i => if hi : i ∈ Z then (obj i hi).f else 0
  have hf : ∀ i : ι, ∀ hi : i ∈ Z, f i = (obj i hi).f := by
    intro i hi
    simp [f, hi]
  have hsep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
      Disjoint (tsupport (⇑(f i) : ℂ → ℝ))
        (tsupport (⇑(f j) : ℂ → ℝ)) := by
    intro i hi j hj hij
    apply (hballs i hi j hj hij).mono
    · rw [hf i hi]
      exact ObjectAtV2.tsupport_f_subset_ball4 (obj i hi)
    · rw [hf j hj]
      exact ObjectAtV2.tsupport_f_subset_ball4 (obj j hj)
  apply finiteBump_probability_window P h hh Z f hsep E hE hconst
    par.Crn par.rn_pos
  intro g hg i hi
  rw [hf i hi]
  exact (obj i hi).E_rn g (hgood g hg i hi)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
