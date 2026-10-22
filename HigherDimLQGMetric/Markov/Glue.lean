import HigherDimLQGMetric.Markov.Kolm
import Mathlib.Topology.Compactness.Lindelof

/-! Gluing countably many local continuous modifications on an open set. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped Topology

namespace HigherDimLQGMetric

/-- Local continuous modifications of a real process on a Euclidean open set glue to a jointly
chosen continuous modification, measurable at every point. -/
theorem markov_glue_local_versions {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (O : Opens (HigherDimLFPP.Rd d))
    (Z : HigherDimLFPP.Rd d → Ω → ℝ)
    (hLoc : ∀ x : O, ∃ r : ℝ, 0 < r ∧ ball (x : HigherDimLFPP.Rd d) r ⊆ O ∧
      ∃ H : HigherDimLFPP.Rd d → Ω → ℝ,
        (∀ ω, ContinuousOn (fun y => H y ω) (ball (x : HigherDimLFPP.Rd d) r)) ∧
        (∀ y, Measurable (H y)) ∧
        (∀ y ∈ ball (x : HigherDimLFPP.Rd d) r,
          (fun ω => H y ω) =ᵐ[P] Z y)) :
    ∃ Y : Ω → HigherDimLFPP.Rd d → ℝ,
      (∀ ω, ContinuousOn (Y ω) O) ∧
      Measurable Y ∧
      ∀ y ∈ O, (fun ω => Y ω y) =ᵐ[P] Z y := by
  classical
  choose r hr hsub H hHc hHm hHZ using hLoc
  let U : O → Set (HigherDimLFPP.Rd d) := fun x => ball (x : HigherDimLFPP.Rd d) (r x)
  have hUo : ∀ x : O, IsOpen (U x) := fun _ => isOpen_ball
  have hCover : (O : Set (HigherDimLFPP.Rd d)) ⊆ ⋃ x : O, U x := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩, mem_ball_self (hr ⟨y,hy⟩)⟩
  have hL : IsLindelof (O : Set (HigherDimLFPP.Rd d)) :=
    HereditarilyLindelofSpace.isLindelof _
  obtain ⟨J, hJc, hJcover⟩ := hL.elim_countable_subcover U hUo hCover
  have hJmem (y : HigherDimLFPP.Rd d) (hy : y ∈ O) :
      ∃ j : J, y ∈ U j := by
    obtain ⟨j,hj,hjy⟩ := mem_iUnion₂.mp (hJcover hy)
    exact ⟨⟨j,hj⟩,hjy⟩
  let jOf (y : HigherDimLFPP.Rd d) (hy : y ∈ O) : J :=
    Classical.choose (hJmem y hy)
  have hjOf (y : HigherDimLFPP.Rd d) (hy : y ∈ O) :
      y ∈ U (jOf y hy) := Classical.choose_spec (hJmem y hy)
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense (HigherDimLFPP.Rd d)
  haveI : Countable J := hJc.to_subtype
  haveI : Countable D := hDc.to_subtype
  let Good : Set Ω := {ω | ∀ i j : J, ∀ y : D,
    y.1 ∈ U i → y.1 ∈ U j → H i y ω = H j y ω}
  have hGoodm : MeasurableSet Good := by
    have hm (i j : J) (y : D) : MeasurableSet
        {ω : Ω | y.1 ∈ U i → y.1 ∈ U j → H i y ω = H j y ω} := by
      by_cases hi : y.1 ∈ U i
      · by_cases hj : y.1 ∈ U j
        · simpa [hi, hj] using measurableSet_eq_fun (hHm i y) (hHm j y)
        · simp [hi, hj]
      · simp [hi]
    have hAll : MeasurableSet (⋂ i : J, ⋂ j : J, ⋂ y : D,
        {ω : Ω | y.1 ∈ U i → y.1 ∈ U j → H i y ω = H j y ω}) :=
      MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        MeasurableSet.iInter fun y => hm i j y
    have heq : Good = (⋂ i : J, ⋂ j : J, ⋂ y : D,
        {ω : Ω | y.1 ∈ U i → y.1 ∈ U j → H i y ω = H j y ω}) := by
      ext ω
      simp only [Good, mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact hAll
  have hGoodAe : ∀ᵐ ω ∂P, ω ∈ Good := by
    change ∀ᵐ ω ∂P, ∀ i j : J, ∀ y : D,
      y.1 ∈ U i → y.1 ∈ U j → H i y ω = H j y ω
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro y
    by_cases hi : y.1 ∈ U i
    · by_cases hj : y.1 ∈ U j
      · filter_upwards [hHZ i y hi, hHZ j y hj] with ω h1 h2
        exact fun _ _ => h1.trans h2.symm
      · exact Filter.Eventually.of_forall (fun ω _ h => False.elim (hj h))
    · exact Filter.Eventually.of_forall (fun ω h => False.elim (hi h))
  have hAgree (ω : Ω) (hω : ω ∈ Good) (i j : J) :
      EqOn (fun y => H i y ω) (fun y => H j y ω) (U i ∩ U j) := by
    let T : Set (HigherDimLFPP.Rd d) := U i ∩ U j
    have hTo : IsOpen T := (hUo i).inter (hUo j)
    have hDsubset : D ∩ T ⊆ T := inter_subset_right
    have hTclosure : T ⊆ closure (D ∩ T) := by
      simpa only [inter_comm D] using hDd.open_subset_closure_inter hTo
    have hEq : EqOn (fun y => H i y ω) (fun y => H j y ω) (D ∩ T) := by
      intro y hy
      exact hω i j ⟨y,hy.1⟩ hy.2.1 hy.2.2
    exact hEq.of_subset_closure
      ((hHc i ω).mono inter_subset_left)
      ((hHc j ω).mono inter_subset_right)
      hDsubset hTclosure
  let Y : Ω → HigherDimLFPP.Rd d → ℝ := fun ω y =>
    if hy : y ∈ O then
      if ω ∈ Good then H (jOf y hy) y ω else 0
    else 0
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ Good
    · intro y hy
      let j := jOf y hy
      have hyj : y ∈ U j := hjOf y hy
      have heq : EqOn (Y ω) (fun v => H j v ω) (U j) := by
        intro v hv
        have hvo : v ∈ O := hsub j hv
        simp only [Y, dite_eq_left hvo, ite_eq_left hω]
        exact hAgree ω hω (jOf v hvo) j ⟨hjOf v hvo,hv⟩
      have hcont : ContinuousAt (fun v => H j v ω) y :=
        (hHc j ω).continuousAt ((hUo j).mem_nhds hyj)
      exact (hcont.congr_of_eventuallyEq
        (heq.eventuallyEq_of_mem ((hUo j).mem_nhds hyj))).continuousWithinAt
    · have hzero : EqOn (Y ω) (fun _ => (0 : ℝ)) O := by
        intro y hy
        simp [Y, hω]
      exact ContinuousOn.congr continuousOn_const hzero
  · rw [measurable_pi_iff]
    intro y
    by_cases hy : y ∈ O
    · have hpm : Measurable
          (Good.piecewise (H (jOf y hy) y) (fun _ : Ω => (0 : ℝ))) :=
        (hHm (jOf y hy) y).piecewise hGoodm measurable_const
      have he : (fun ω : Ω => if ω ∈ Good then H (jOf y hy) y ω else 0) =
          Good.piecewise (H (jOf y hy) y) (fun _ => 0) := by
        funext ω
        rfl
      simpa only [Y, dite_eq_left hy, he] using hpm
    · simpa only [Y, dite_eq_right hy] using
        (measurable_const : Measurable fun _ : Ω => (0 : ℝ))
  · intro y hy
    let j := jOf y hy
    have hyj : y ∈ U j := hjOf y hy
    filter_upwards [hGoodAe, hHZ j y hyj] with ω hω heq
    simp only [Y, dite_eq_left hy, ite_eq_left hω]
    exact heq

end HigherDimLQGMetric
