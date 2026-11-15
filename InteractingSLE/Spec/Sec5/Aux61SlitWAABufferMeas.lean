/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstInverseMeas
import InteractingSLE.Spec.Sec5.Aux61GInstBoundaryMeas
import InteractingSLE.Spec.Sec5.Aux61GWordWindows

/-! # Initial-record measurability of finite physical buffers

Avoiding the inverse Cayley pole on a fixed compact buffer is measurable
from the chart record. The uncountable condition uses the existing
measurable distance-to-compact-range theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Aux61SlitWAA
open Aux61GInst Aux61FibData
variable {X : Type*} [MeasurableSpace X]

/-- The bounded inverse at any closed-half-plane point is measurable
on a measurable event where its canonical extension is continuous. -/
theorem measurable_boundedInverse_Hbar {E : Set X} (hE : MeasurableSet E) {c : X → Chart}
    (hm : IsMeasChart c) (hc : ∀ x ∈ E, (c x).IsConformal)
    (hF : ∀ x ∈ E, EqOn (boundedInverse (c x)) (cayley ∘ (c x).2.1) H ∧
      ContinuousOn (boundedInverse (c x)) Hbar) {z : ℂ} (hz : z ∈ Hbar) :
    Measurable (E.indicator fun x => boundedInverse (c x) z) := by
  classical
  change 0 ≤ z.im at hz
  rcases eq_or_lt_of_le hz with hz0 | hz0
  · have heq : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im, hz0.symm]
    rw [heq]
    exact measurable_boundedInverse_real hE hm hc hF z.re
  · have hi := measurable_chart_inverse (isConformal_chartOf hc) (hm.chartOf hE) hz0
    have hcm : Measurable cayley :=
      (measurable_id.sub measurable_const).div (measurable_id.add measurable_const)
    convert (hcm.comp hi).indicator hE using 1
    funext x
    by_cases hx : x ∈ E
    · simp only [indicator_of_mem hx, chartOf_of_mem hx, (hF x hx).1 hz0, Function.comp_apply]
    · simp only [indicator_of_notMem hx]

/-- For a continuous random function on a fixed compact plane set,
avoidance of one value on the whole set is a measurable event. -/
theorem measurableSet_avoids_on_compact {K : Set ℂ} (hK : IsCompact K) {F : X → ℂ → ℂ}
    (hc : ∀ x, ContinuousOn (F x) K) (hm : ∀ z ∈ K, Measurable (fun x => F x z)) (w : ℂ) :
    MeasurableSet {x | ∀ z ∈ K, F x z ≠ w} := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp only [mem_empty_iff_false, IsEmpty.forall_iff, implies_true, Set.ofPred_true]
    exact MeasurableSet.univ
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have : Nonempty K := hne.to_subtype
  let f : X → K → ℂ := fun x z => F x z
  have hfc : ∀ x, Continuous (f x) := fun x => (hc x).domRestrict
  have hfm : ∀ z, Measurable (fun x => f x z) := fun z => hm z z.2
  have hdist := measurable_infDist_compact_range hfc hfm w
  have heq : {x | ∀ z ∈ K, F x z ≠ w} = {x | 0 < infDist w (range (f x))} := by
    ext x
    simp only [mem_ofPred_eq]
    rw [← (isCompact_range (hfc x)).isClosed.notMem_iff_infDist_pos (range_nonempty _)]
    simp only [mem_range, not_exists, f, Subtype.forall, ne_eq, eq_comm]
  rw [heq]
  exact measurableSet_lt measurable_const hdist

/-- The physical-infinity avoidance condition on a fixed compact buffer
is a measurable selection criterion on the retained chart record. -/
theorem measurableSet_finite_buffer {E : Set X} (hE : MeasurableSet E) {c : X → Chart}
    (hm : IsMeasChart c) (hc : ∀ x ∈ E, (c x).IsConformal)
    (hF : ∀ x ∈ E, EqOn (boundedInverse (c x)) (cayley ∘ (c x).2.1) H ∧
      ContinuousOn (boundedInverse (c x)) Hbar) {B : Set ℂ} (hB : IsCompact B) :
    MeasurableSet {x | x ∈ E ∧ ∀ z ∈ B ∩ Hbar, boundedInverse (c x) z ≠ 1} := by
  have hK : IsCompact (B ∩ Hbar) := hB.inter_right QuantumZipper.isClosed_Hbar
  have hc' : ∀ x, ContinuousOn (fun z => E.indicator (fun x => boundedInverse (c x) z) x)
      (B ∩ Hbar) := by
    intro x
    by_cases hx : x ∈ E
    · simpa only [indicator_of_mem hx] using ((hF x hx).2.mono inter_subset_right)
    · simpa only [indicator_of_notMem hx] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) (B ∩ Hbar))
  have hm' := measurableSet_avoids_on_compact hK hc'
    (fun z hz => measurable_boundedInverse_Hbar hE hm hc hF hz.2) 1
  convert hE.inter hm' using 1
  ext x
  by_cases hx : x ∈ E <;> simp only [mem_ofPred_eq, mem_inter_iff, hx,
    indicator_of_mem, true_and, false_and]

/-- The finite-buffer tests for the fixed countable window family are
preimages of measurable retained-record events. Future capture is not
part of this selection criterion. -/
theorem exists_history_finite_buffer_pieces {Y β : Type*} [mβ : MeasurableSpace β] (Z : Y → β)
    {E : Set Y} (hE : MeasurableSet[mβ.comap Z] E) {c : Y → Chart}
    (hm : @IsMeasChart Y (mβ.comap Z) c) (hc : ∀ x ∈ E, (c x).IsConformal)
    (hF : ∀ x ∈ E, EqOn (boundedInverse (c x)) (cayley ∘ (c x).2.1) H ∧
      ContinuousOn (boundedInverse (c x)) Hbar) :
    ∃ B : Aux61GWord.SeedWindowIndex → Set β, (∀ j, MeasurableSet (B j)) ∧
      ∀ j, Z ⁻¹' B j = {x | x ∈ E ∧
        ∀ z ∈ closure (Aux61GWord.outerBuffer j) ∩ Hbar, boundedInverse (c x) z ≠ 1} := by
  have hmeas : ∀ j : Aux61GWord.SeedWindowIndex, MeasurableSet[mβ.comap Z]
      {x | x ∈ E ∧ ∀ z ∈ closure (Aux61GWord.outerBuffer j) ∩ Hbar,
        boundedInverse (c x) z ≠ 1} := fun j =>
    @measurableSet_finite_buffer Y (mβ.comap Z) E hE c hm hc hF _ j.property.2.2.2
  choose B hBm hpre using fun j => MeasurableSpace.measurableSet_comap.1 (hmeas j)
  exact ⟨B, hBm, hpre⟩

end InteractingSLE.Sec5.Aux61SlitWAA
