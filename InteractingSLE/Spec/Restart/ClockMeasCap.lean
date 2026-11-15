/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockData
import InteractingSLE.Spec.Coupling.WholeField2Cap

/-!
# Measurability of the relative capacity of a random continuous path

Packet PROVE-RESTART-CPL5. For the W8.1 clocks to be random variables, the capacity `hcap fill Γ([0, r])` of the
filling of a random continuous path must be measurable in `ω`. PROVE-WHOLEFIELD2's `hcapHit` (an infimum of the
capacities of grid covers) is measurable for the hitting σ-algebra and equals the capacity on compact hulls. Here:

* `hcapHit_image_eq`: for a continuous path from a point of `{Im ≤ 0}`, `hcapHit Γ([0, r]) = hcap fill Γ([0, r])`
  (a cover of the path in `ℍ` covers its filling's capacity, and the covers of the filling cover the path);
* `exists_mem_image_Icc_iff`: a continuous path meets an open set on `[0, r]` iff it does at `r` or at a rational time
  in `[0, r)`;
* `measurable_image_Icc`: a random path, continuous for every `ω` and measurable at each time, has `Γ([0, r])`
  measurable for the hitting σ-algebra;
* `measurable_hcapHit_image`: hence `ω ↦ hcapHit Γ_ω([0, r])` is measurable.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-- **The grid capacity of a path is the capacity of its filling.** -/
theorem hcapHit_image_eq {Γ : ℝ≥0 → ℂ} {r : ℝ≥0} (hc : ContinuousOn Γ (Icc 0 r)) (h0 : (Γ 0).im ≤ 0) :
    WholeField.hcapHit (Γ '' Icc 0 r) = ENNReal.ofReal (ConformalImage.hcapSet (fillH (Γ '' Icc 0 r))) := by
  classical
  set A := Γ '' Icc 0 r with hA
  have hF := isHPHull_fillH_image hc h0
  rw [ConformalImage.hcapSet_eq hF, ← WholeField.IsHPHull.hcapHit_eq hF]
  have hAF : ∀ z ∈ A, z ∈ H → z ∈ fillH A := fun z hz hzH => mem_fillH_of_mem_closure hzH (subset_closure hz)
  refine le_antisymm (iInf₂_mono fun n s => ?_) ?_
  · split_ifs with h1 h2 h2
    · exact le_rfl
    · exact le_top
    · exfalso
      exact h1 (Set.disjoint_left.2 fun z hz hz' => Set.disjoint_left.1 h2 (hAF z hz hz'.1) hz')
    · exact le_rfl
  rw [WholeField.IsHPHull.hcapHit_eq hF]
  refine le_iInf₂ fun n s => ?_
  split_ifs with hd
  · unfold WholeField.gridCap
    split_ifs with hcC
    · refine ENNReal.ofReal_le_ofReal ?_
      have hsub : fillH A ⊆ fillH (WholeField.gridUnion n s) := by
        have hAH : fillH A = fillH (A ∩ H) := by
          conv_lhs => rw [← inter_union_sdiff A H]
          exact fillH_union_of_forall_notMem_H fun z hz => hz.2
        rw [hAH]
        refine fillH_mono fun z hz => ?_
        by_contra hzC
        exact Set.disjoint_left.1 hd hz.1 ⟨hz.2, hzC⟩
      exact HPHull.hcap_mono (A := ⟨_, hF⟩)
        (B := ⟨_, isHPHull_fillH_of_isPreconnected (WholeField.isBounded_gridUnion n s) hcC⟩) hsub
    · exact le_top
  · exact le_top

/-- A continuous path meets an open set on `[0, r]` iff it does at `r` or at a rational time in `[0, r)`. -/
theorem exists_mem_image_Icc_iff {Γ : ℝ≥0 → ℂ} (hΓ : Continuous Γ) {U : Set ℂ} (hU : IsOpen U) (r : ℝ≥0) :
    (Γ '' Icc 0 r ∩ U).Nonempty ↔
      Γ r ∈ U ∨ ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < r ∧ Γ (q : ℝ).toNNReal ∈ U := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hxU⟩
    rcases hx.2.lt_or_eq with hxr | rfl
    · right
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hΓ) x hxU
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (x : ℝ) < min (x + ε) r from
        lt_min (by linarith) (NNReal.coe_lt_coe.2 hxr))
      have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg x).trans hq1.le
      refine ⟨q, hq0, lt_of_lt_of_le hq2 (min_le_right _ _), hball ?_⟩
      rw [mem_ball, NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_lt]
      constructor <;> linarith [min_le_left (x + ε) r]
    · exact Or.inl hxU
  · rintro (h | ⟨q, hq0, hqr, hq⟩)
    · exact ⟨_, ⟨r, ⟨zero_le, le_rfl⟩, rfl⟩, h⟩
    · refine ⟨_, ⟨(q : ℝ).toNNReal, ⟨zero_le, ?_⟩, rfl⟩, hq⟩
      exact (Real.toNNReal_le_iff_le_coe).2 hqr.le

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random path, continuous for every `ω` and measurable at each time, has `Γ([0, r])` measurable for the hitting
σ-algebra. -/
theorem measurable_image_Icc {Γ : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (Γ ω))
    (hm : ∀ t, Measurable fun ω => Γ ω t) (r : ℝ≥0) :
    Measurable[_, hittingSigma] fun ω => Γ ω '' Icc 0 r := by
  refine @measurable_generateFrom Ω (Set ℂ) _ _ _ fun S hS => ?_
  obtain ⟨U, hU, -, rfl⟩ := hS
  have : (fun ω => Γ ω '' Icc 0 r) ⁻¹' {A | (A ∩ U).Nonempty} =
      {ω | Γ ω r ∈ U} ∪ ⋃ q : ℚ, {ω | 0 ≤ (q : ℝ) ∧ (q : ℝ) < r ∧ Γ ω (q : ℝ).toNNReal ∈ U} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_iUnion]
    exact exists_mem_image_Icc_iff (hc ω) hU r
  rw [this]
  exact (hm r hU.measurableSet).union (MeasurableSet.iUnion fun q =>
    (MeasurableSet.const (0 ≤ (q : ℝ))).inter ((MeasurableSet.const ((q : ℝ) < r)).inter
      (hm _ hU.measurableSet)))

/-- The grid capacity of a random continuous path is measurable. -/
theorem measurable_hcapHit_image {Γ : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (Γ ω))
    (hm : ∀ t, Measurable fun ω => Γ ω t) (r : ℝ≥0) :
    Measurable fun ω => WholeField.hcapHit (Γ ω '' Icc 0 r) :=
  WholeField.measurable_hcapHit.comp (measurable_image_Icc hc hm r)

end Restart

end InteractingSLE
