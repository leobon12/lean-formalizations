/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcFrz

/-!
# The random hull chart at random points

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B). PROVE-RESTART-CPL4's `Restart.measurableSet_mem_H_diff_fillH`
and `Restart.measurable_indicator_mapOut` read the mapping-out function of a dyadic-hit measurable random compact set
at a FIXED point. F2b′'s relative curve reads it at B's random points. Same proof (the level-`n` dyadic cover takes
countably many values, and the cover maps converge), with the point random:

* `measurableSet_mem_countable_pt`, `measurable_comp_countable_pt`: a countable-range variable with a measurable point;
* **`measurableSet_mem_H_diff_fillH_rand`**, **`measurable_indicator_mapOut_rand`**,
  **`measurable_indicator_hullChart_rand`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Nc

open Restart

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable point in a set depending on a countable-range variable with measurable fibres. -/
theorem measurableSet_mem_countable_pt {α : Type*} {f : Ω → α} (hc : (range f).Countable)
    (hf : ∀ a, MeasurableSet (f ⁻¹' {a})) {z : Ω → ℂ} (hz : Measurable z) {U : α → Set ℂ}
    (hU : ∀ a ∈ range f, MeasurableSet (U a)) : MeasurableSet {ω | z ω ∈ U (f ω)} := by
  have e : {ω | z ω ∈ U (f ω)} = ⋃ a ∈ range f, f ⁻¹' {a} ∩ z ⁻¹' U a := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff, exists_prop]
    constructor
    · intro h; exact ⟨f ω, mem_range_self ω, rfl, h⟩
    · rintro ⟨a, -, rfl, h⟩; exact h
  rw [e]
  exact MeasurableSet.biUnion hc fun a ha => (hf a).inter (hz (hU a ha))

/-- A function of a countable-range variable with measurable fibres and of a measurable point. -/
theorem measurable_comp_countable_pt {α β : Type*} [MeasurableSpace β] {f : Ω → α} (hc : (range f).Countable)
    (hf : ∀ a, MeasurableSet (f ⁻¹' {a})) {z : Ω → ℂ} (hz : Measurable z) {G : α → ℂ → β}
    (hG : ∀ a ∈ range f, Measurable (G a)) : Measurable fun ω => G (f ω) (z ω) := fun B hB =>
  measurableSet_mem_countable_pt hc hf hz (U := fun a => G a ⁻¹' B) fun a ha => hG a ha hB

variable {K : Ω → Set ℂ}

/-- **A random point in the random domain** is a measurable event. -/
theorem measurableSet_mem_H_diff_fillH_rand (hK : IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω))
    {z : Ω → ℂ} (hz : Measurable z) : MeasurableSet {ω | z ω ∈ H \ fillH (K ω)} := by
  have heq : {ω | z ω ∈ H \ fillH (K ω)} =
      ⋃ n : ℕ, {ω | z ω ∈ H \ fillH (coverOf n (dyadicIdx n (K ω)))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, ← dyadicCover_eq_coverOf]
    constructor
    · intro hz'
      have h := mem_iInter.not.1 (show z ω ∉ ⋂ n, fillH (dyadicCover n (K ω)) by
        rw [iInter_fillH_dyadicCover (hKc ω)]; exact hz'.2)
      obtain ⟨n, hn⟩ := not_forall.1 h
      exact ⟨n, hz'.1, hn⟩
    · rintro ⟨n, hz', hn⟩
      exact ⟨hz', fun h => hn (fillH_subset_fillH_dyadicCover n h)⟩
  rw [heq]
  refine MeasurableSet.iUnion fun n => measurableSet_mem_countable_pt (U := fun S => H \ fillH (coverOf n S))
    (countable_range_dyadicIdx (fun ω => (hKc ω).isBounded) n) (measurableSet_dyadicIdx_eq hK n) hz ?_
  rintro _ ⟨ω, rfl⟩
  rw [← dyadicCover_eq_coverOf]
  exact (isOpen_H_diff_fillH (isCompact_dyadicCover (hKc ω).isBounded n).isBounded).measurableSet

/-- **The mapping-out function of the random compact set at a random point of its domain is measurable.** -/
theorem measurable_indicator_mapOut_rand (hK : IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf)) {z : Ω → ℂ} (hz : Measurable z) :
    Measurable ({ω | z ω ∈ H \ fillH (K ω)}.indicator fun ω => ConformalImage.mapOut (fillH (K ω)) (z ω)) := by
  classical
  set E := {ω | z ω ∈ H \ fillH (K ω)} with hEdef
  have hEm : MeasurableSet E := measurableSet_mem_H_diff_fillH_rand hK hKc hz
  set G : ℕ → Set (ℤ × ℤ) → ℂ → ℂ := fun n S => (H \ fillH (coverOf n S)).indicator
    (ConformalImage.mapOut (fillH (coverOf n S))) with hGdef
  have hGm : ∀ n, ∀ S ∈ range (fun ω => dyadicIdx n (K ω)), Measurable (G n S) := by
    rintro n _ ⟨ω, rfl⟩
    have hA : IsHPHull (fillH (coverOf n (dyadicIdx n (K ω)))) := by
      rw [← dyadicCover_eq_coverOf]; exact isHPHull_fillH_dyadicCover (hKc ω).isBounded (hKp ω) n
    have hU : IsOpen (H \ fillH (coverOf n (dyadicIdx n (K ω)))) := by
      rw [← dyadicCover_eq_coverOf]
      exact isOpen_H_diff_fillH (isCompact_dyadicCover (hKc ω).isBounded n).isBounded
    have hcont : ContinuousOn (ConformalImage.mapOut (fillH (coverOf n (dyadicIdx n (K ω)))))
        (H \ fillH (coverOf n (dyadicIdx n (K ω)))) :=
      (ConformalImage.isMapOut_mapOut hA).1.1.continuousOn
    have := hcont.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const hU.measurableSet
    have e : ((H \ fillH (coverOf n (dyadicIdx n (K ω)))).piecewise
        (ConformalImage.mapOut (fillH (coverOf n (dyadicIdx n (K ω))))) fun _ => (0 : ℂ)) =
        G n (dyadicIdx n (K ω)) := by
      funext y
      by_cases hy : y ∈ H \ fillH (coverOf n (dyadicIdx n (K ω)))
      · rw [Set.piecewise_eq_of_mem _ _ _ hy, hGdef]; exact (indicator_of_mem hy _).symm
      · rw [Set.piecewise_eq_of_notMem _ _ _ hy, hGdef]; exact (indicator_of_notMem hy _).symm
    rwa [e] at this
  refine measurable_of_tendsto_metrizable
    (f := fun n => E.indicator fun ω => G n (dyadicIdx n (K ω)) (z ω)) (fun n => ?_) ?_
  · exact (measurable_comp_countable_pt (countable_range_dyadicIdx (fun ω => (hKc ω).isBounded) n)
      (measurableSet_dyadicIdx_eq hK n) hz (hGm n)).indicator hEm
  · rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω]
      have hlim := (tendstoLocallyUniformlyOn_mapOut_dyadicCover (hKc ω) (hKp ω)).tendsto_at hω
      have hev : ∀ᶠ n in atTop, z ω ∈ H \ fillH (dyadicCover n (K ω)) := by
        obtain ⟨n₀, hn₀⟩ : ∃ n₀, z ω ∉ fillH (dyadicCover n₀ (K ω)) := by
          by_contra hc
          push Not at hc
          exact hω.2 (by rw [← iInter_fillH_dyadicCover (hKc ω)]; exact mem_iInter.2 hc)
        filter_upwards [eventually_ge_atTop n₀] with n hn
        exact ⟨hω.1, fun h => hn₀ (fillH_dyadicCover_antitone hn h)⟩
      refine hlim.congr' ?_
      filter_upwards [hev] with n hn
      have hn' : z ω ∈ H \ fillH (coverOf n (dyadicIdx n (K ω))) := by rw [← dyadicCover_eq_coverOf]; exact hn
      simp only [hGdef, indicator_of_mem hn', dyadicCover_eq_coverOf]
    · simp only [indicator_of_notMem hω]
      exact tendsto_const_nhds

/-- **The random hull chart at a random point of its domain is measurable.** -/
theorem measurable_indicator_hullChart_rand (hK : IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf)) {x₀ : Ω → ℝ} (hx₀ : Measurable x₀) {z : Ω → ℂ}
    (hz : Measurable z) :
    Measurable ({ω | z ω ∈ H \ fillH (K ω)}.indicator
      fun ω => (Mo.hullChart (fillH (K ω)) (x₀ ω)).1 (z ω)) := by
  have hEm : MeasurableSet {ω | z ω ∈ H \ fillH (K ω)} := measurableSet_mem_H_diff_fillH_rand hK hKc hz
  have e : ({ω | z ω ∈ H \ fillH (K ω)}.indicator fun ω => (Mo.hullChart (fillH (K ω)) (x₀ ω)).1 (z ω)) =
      ({ω | z ω ∈ H \ fillH (K ω)}.indicator fun ω => ConformalImage.mapOut (fillH (K ω)) (z ω)) -
        ({ω | z ω ∈ H \ fillH (K ω)}.indicator fun ω => ((x₀ ω : ℝ) : ℂ)) := by
    funext ω
    by_cases hω : ω ∈ {ω | z ω ∈ H \ fillH (K ω)}
    · simp only [indicator_of_mem hω, Pi.sub_apply, Mo.hullChart_fwd]
    · simp only [indicator_of_notMem hω, Pi.sub_apply, sub_zero]
  rw [e]
  exact (measurable_indicator_mapOut_rand hK hKc hKp hz).sub ((Complex.measurable_ofReal.comp hx₀).indicator hEm)

end

end InteractingSLE.Theorem14.SB.Nc
