/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYFillMeas

/-! # Filled increasing unions of Gaussian local sets -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H)
open LQGMetric LocalSets

/-- Relative closure preserves the Euclidean closure of a subset of `ℍ`. -/
theorem closure_relClosureH_of_subset {A : Set ℂ} (hA : A ⊆ H) :
    closure (relClosureH A) = closure A := by
  have h₁ : A ⊆ relClosureH A := fun z hz => ⟨hA hz, subset_closure ⟨hz, hA hz⟩⟩
  have h₂ : relClosureH A ⊆ closure A := fun _ hz => closure_mono inter_subset_left hz.2
  exact Subset.antisymm ((closure_mono h₂).trans_eq closure_closure) (closure_mono h₁)

/-- The filling of an almost surely bounded increasing union of local sets is
local. This includes newly swallowed pockets and permits merely a.e. measurable
input sets, as in the frozen definition. -/
theorem isLocalSet_fillH_iUnion {S : Type u} [mS : MeasurableSpace S]
    {P : Measure S} [IsProbabilityMeasure P] {h : S → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A : ℕ → S → Set ℂ}
    (hmono : ∀ᵐ ω ∂P, Monotone fun n => A n ω)
    (hbound : ∀ᵐ ω ∂P, Bornology.IsBounded (⋃ n, A n ω))
    (hloc : ∀ n, IsLocalSet (A n) h P) :
    IsLocalSet (fun ω => fillH (⋃ n, A n ω)) h P := by
  choose A' hA'm hA'e hA'loc using fun n =>
    WholeField.IsLocalSet.exists_measurable_version (hloc n) hh.measurable
  have hEq : ∀ᵐ ω ∂P, ∀ n, A' n ω = A n ω := ae_all_iff.2 hA'e
  have hmono' : ∀ᵐ ω ∂P, Monotone fun n => A' n ω := by
    filter_upwards [hmono, hEq] with ω hm he
    simpa only [he] using hm
  let B : S → Set ℂ := fun ω => relClosureH (⋃ n, A' n ω)
  have hBm : Measurable[mS, hittingSigma] B :=
    measurable_relClosureH.comp (measurable_iUnion_hitting hA'm)
  have hBloc : IsLocalSet B h P := isLocalSet_relClosure_iUnion hh hA'm hmono' hA'loc
  have hBbound : ∀ᵐ ω ∂P, Bornology.IsBounded (B ω) := by
    filter_upwards [hbound, hEq] with ω hb he
    have hb' : Bornology.IsBounded (⋃ n, A' n ω) := by simpa only [he] using hb
    exact (hb'.subset inter_subset_left).closure.subset inter_subset_right
  have hclosed : ∀ᵐ ω ∂P, hullFillReader (B ω) ⊆ H ∧ IsOpen (H \ hullFillReader (B ω)) := by
    filter_upwards [hBbound] with ω hb
    rw [hullFillReader_eq_fillH (relClosureH_subset _) hb]
    exact ⟨fillH_subset_H _, isOpen_H_diff_fillH hb⟩
  have hfill := isLocalSet_enlarge hh hBm hBloc measurable_hullFillReader subset_hullFillReader hclosed
  apply Coupling.IsLocalSet.congr_set hfill
  filter_upwards [hEq, hBbound, ae_all_iff.2 (fun n => (hloc n).2.1)] with ω he hb hAH
  have hU : (⋃ n, A n ω) ⊆ H := iUnion_subset fun n => (hAH n).1
  rw [hullFillReader_eq_fillH (relClosureH_subset _) hb]
  change fillH (⋃ n, A n ω) = fillH (relClosureH (⋃ n, A' n ω))
  simp only [he]
  exact fillH_congr (by rw [closure_relClosureH_of_subset hU])

end InteractingSLE.Restart.FlowStopIdentCMI
