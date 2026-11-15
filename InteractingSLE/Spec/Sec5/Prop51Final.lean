/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51

/-!
# Proposition 5.1's final step without closedness of the flow-line range

Packet PROVE-SEC5-J (specification p. 135, proof of Proposition 5.1, and p. 120, the last sentence of the proof of
Proposition 4.9: "taking a countable dense collection of stopping times `τ′` … and invoking the almost sure continuity
of `η′`").

The landed final step `ae_liesRightOf_liesLeftOf_of_countable` (`Prop51.lean`, PROVE-SEC5-D) asks that the flow-line
range `A ω` be closed. For `A = pathRange η ζ = η([0, ζ))` this fails whenever the lifetime `ζ` is finite (the endpoint
`η(ζ)` is missing), which is the normal case for the §5 flow lines that stop on `∂_U𝒮`
(`planning/handoffs/PROVE-SEC5-I.md`, "What remains" 2(b)). The density argument only needs the strict sides to be
**open**, and they are open as soon as `ℍ \ A` is open. This file:

* `stripLeftSide_anti`, `stripRightSide_anti`: the strict sides are antitone in the obstacle; in particular
  `stripLeftSide (closure A) ⊆ stripLeftSide A`; `LiesRightOf.of_subset`;
* `isOpen_stripLeftSide_of_isOpen`, `isOpen_stripRightSide_of_isOpen`: the sides are open when `ℍ \ A` is;
* **`ae_liesRightOf_liesLeftOf_of_countable_of_isOpen`**: the final step with `IsOpen (ℍ \ A ω)` in place of
  `IsClosed (A ω)`;
* **`ae_liesRightOf_liesLeftOf_closure_of_countable`**: the final step with no regularity of `A` at all, concluding
  for the closure `closure (A ω)` from the per-time statements for `A ω` itself;
* `pathRange_inter_H_eq_of_ne_top`, `isOpen_H_diff_pathRange_of_ne_top` (finite lifetime, real endpoint),
  `isClosed_pathRange_top` (infinite lifetime, transient trace), `isOpen_H_diff_pathRange`: the flow-line range has
  an open complement in `ℍ` in both cases, and `closure_pathRange_inter_H`: its closure adds no point of `ℍ`;
* **`ae_liesRightOf_liesLeftOf_pathRange_of_countable`**: the corrected final step of Proposition 5.1 for
  `A = pathRange η ζ`, with the regularity of `η` (continuity on `[0, ζ]`; a real endpoint when `ζ < ∞`; transience when
  `ζ = ∞`) in place of closedness.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Sec5

open Sec4 (stripCounterflowChart)

/-! ### The strict sides: antitone in the obstacle, open with an open complement -/

/-- A larger obstacle has smaller strict left side. -/
theorem stripLeftSide_anti {A B : Set ℂ} (hAB : A ⊆ B) : stripLeftSide B ⊆ stripLeftSide A := by
  rintro z ⟨⟨hzH, hzB⟩, x, hx, hxB, hcl⟩
  exact ⟨⟨hzH, fun h => hzB (hAB h)⟩, x, hx, fun h => hxB (hAB h),
    closure_mono (connectedComponentIn_mono z (sdiff_subset_sdiff_right hAB)) hcl⟩

/-- A larger obstacle has smaller strict right side. -/
theorem stripRightSide_anti {A B : Set ℂ} (hAB : A ⊆ B) : stripRightSide B ⊆ stripRightSide A := by
  rintro z ⟨⟨hzH, hzB⟩, x, hx, hxB, hcl⟩
  exact ⟨⟨hzH, fun h => hzB (hAB h)⟩, x, hx, fun h => hxB (hAB h),
    closure_mono (connectedComponentIn_mono z (sdiff_subset_sdiff_right hAB)) hcl⟩

theorem stripLeftSide_closure_subset (A : Set ℂ) : stripLeftSide (closure A) ⊆ stripLeftSide A :=
  stripLeftSide_anti subset_closure

theorem stripRightSide_closure_subset (A : Set ℂ) : stripRightSide (closure A) ⊆ stripRightSide A :=
  stripRightSide_anti subset_closure

/-- Lying to the right of an obstacle passes to every larger obstacle. -/
theorem LiesRightOf.of_subset {K A B : Set ℂ} (h : LiesRightOf K A) (hAB : A ⊆ B) : LiesRightOf K B :=
  h.mono_right (stripLeftSide_anti hAB)

theorem LiesLeftOf.of_subset {K A B : Set ℂ} (h : LiesLeftOf K A) (hAB : A ⊆ B) : LiesLeftOf K B :=
  h.mono_right (stripRightSide_anti hAB)

theorem isOpen_stripLeftSide_of_isOpen {A : Set ℂ} (hU : IsOpen (H \ A)) : IsOpen (stripLeftSide A) :=
  isOpen_iff_forall_mem_open.2 fun _ hz => ⟨_, connectedComponentIn_subset_stripLeftSide hz,
    hU.connectedComponentIn, mem_connectedComponentIn hz.1⟩

theorem isOpen_stripRightSide_of_isOpen {A : Set ℂ} (hU : IsOpen (H \ A)) : IsOpen (stripRightSide A) :=
  isOpen_iff_forall_mem_open.2 fun _ hz => ⟨_, connectedComponentIn_subset_stripRightSide hz,
    hU.connectedComponentIn, mem_connectedComponentIn hz.1⟩

/-! ### The final step with an open complement, and with the closure -/

/-- **The final step of Proposition 5.1, with an open complement** (`IsOpen (ℍ \ A ω)` in place of `IsClosed (A ω)`).
If almost surely `ℍ \ A ω` is open and the counterflow trace is continuous and avoids `−1` before its lifetime, then
the per-time statements at the times of a countable dense set give `LiesRightOf` (resp. `LiesLeftOf`) for the whole
counterflow. -/
theorem ae_liesRightOf_liesLeftOf_of_countable_of_isOpen {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} {γ : Ω → ℝ≥0 → ℂ} {ζ' : Ω → ℝ≥0∞} {A : Ω → Set ℂ} {D : Set ℝ≥0} (hDc : D.Countable)
    (hD : Dense D)
    (hreg : ∀ᵐ ω ∂P, IsOpen (H \ A ω) ∧ ContinuousOn (γ ω) {t | (t : ℝ≥0∞) < ζ' ω} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω → γ ω t ≠ -1) :
    ((∀ r ∈ D, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ' ω → (stripCounterflowChart q).2.1 (γ ω r) ∉ stripLeftSide (A ω)) →
        ∀ᵐ ω ∂P, LiesRightOf (stripCounterflowRange q (γ ω) (ζ' ω)) (A ω)) ∧
      ((∀ r ∈ D, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ' ω →
          (stripCounterflowChart q).2.1 (γ ω r) ∉ stripRightSide (A ω)) →
        ∀ᵐ ω ∂P, LiesLeftOf (stripCounterflowRange q (γ ω) (ζ' ω)) (A ω)) := by
  refine ⟨fun hpt => ?_, fun hpt => ?_⟩
  · refine ae_disjoint_stripCounterflowRange_of_countable hDc hD ?_ hpt
    filter_upwards [hreg] with ω ⟨hA, hγ, hne⟩ using ⟨isOpen_stripLeftSide_of_isOpen hA, hγ, hne⟩
  · refine ae_disjoint_stripCounterflowRange_of_countable hDc hD ?_ hpt
    filter_upwards [hreg] with ω ⟨hA, hγ, hne⟩ using ⟨isOpen_stripRightSide_of_isOpen hA, hγ, hne⟩

/-- **The final step of Proposition 5.1, with the closure** (no regularity of the obstacle). The per-time
statements for `A ω` itself give `LiesRightOf` (resp. `LiesLeftOf`) of the whole counterflow with respect to the
closure `closure (A ω)` (whose strict sides are open and contained in those of `A ω`). -/
theorem ae_liesRightOf_liesLeftOf_closure_of_countable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} {γ : Ω → ℝ≥0 → ℂ} {ζ' : Ω → ℝ≥0∞} {A : Ω → Set ℂ} {D : Set ℝ≥0} (hDc : D.Countable)
    (hD : Dense D)
    (hreg : ∀ᵐ ω ∂P, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) < ζ' ω} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω → γ ω t ≠ -1) :
    ((∀ r ∈ D, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ' ω → (stripCounterflowChart q).2.1 (γ ω r) ∉ stripLeftSide (A ω)) →
        ∀ᵐ ω ∂P, LiesRightOf (stripCounterflowRange q (γ ω) (ζ' ω)) (closure (A ω))) ∧
      ((∀ r ∈ D, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ' ω →
          (stripCounterflowChart q).2.1 (γ ω r) ∉ stripRightSide (A ω)) →
        ∀ᵐ ω ∂P, LiesLeftOf (stripCounterflowRange q (γ ω) (ζ' ω)) (closure (A ω))) := by
  have hreg' : ∀ᵐ ω ∂P, IsClosed (closure (A ω)) ∧ ContinuousOn (γ ω) {t | (t : ℝ≥0∞) < ζ' ω} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω → γ ω t ≠ -1 := by
    filter_upwards [hreg] with ω hω using ⟨isClosed_closure, hω⟩
  have hfin := ae_liesRightOf_liesLeftOf_of_countable (P := P) (q := q) (γ := γ) (ζ' := ζ')
    (A := fun ω => closure (A ω)) hDc hD hreg'
  refine ⟨fun hpt => hfin.1 fun r hr => ?_, fun hpt => hfin.2 fun r hr => ?_⟩
  · filter_upwards [hpt r hr] with ω hω hlt hmem using hω hlt (stripLeftSide_closure_subset _ hmem)
  · filter_upwards [hpt r hr] with ω hω hlt hmem using hω hlt (stripRightSide_closure_subset _ hmem)

/-! ### Regularity of the flow-line range -/

theorem setOf_coe_lt_eq_Iio {ζ : ℝ≥0∞} (hζ : ζ ≠ ⊤) :
    {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} = Iio ζ.toNNReal := by
  ext t
  simp only [mem_ofPred_eq, mem_Iio]
  conv_lhs => rw [← ENNReal.coe_toNNReal hζ]
  exact ENNReal.coe_lt_coe

theorem setOf_coe_le_eq_Iic {ζ : ℝ≥0∞} (hζ : ζ ≠ ⊤) :
    {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} = Iic ζ.toNNReal := by
  ext t
  simp only [mem_ofPred_eq, mem_Iic]
  conv_lhs => rw [← ENNReal.coe_toNNReal hζ]
  exact ENNReal.coe_le_coe

/-- With a finite lifetime and an endpoint off `ℍ`, the range before the lifetime and the closed range agree on `ℍ`. -/
theorem pathRange_inter_H_eq_of_ne_top {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hζ : ζ ≠ ⊤) (hend : η ζ.toNNReal ∉ H) :
    pathRange η ζ ∩ H = η '' Iic ζ.toNNReal ∩ H := by
  rw [pathRange, setOf_coe_lt_eq_Iio hζ, ← Iio_insert, image_insert_eq, insert_inter_of_notMem hend]

/-- **The flow-line range has an open complement in `ℍ` when the lifetime is finite** and the endpoint is off `ℍ`
(the trace is continuous on the closed lifetime interval). -/
theorem isOpen_H_diff_pathRange_of_ne_top {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hζ : ζ ≠ ⊤)
    (hη : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ}) (hend : η ζ.toNNReal ∉ H) : IsOpen (H \ pathRange η ζ) := by
  have hc : IsClosed (η '' Iic ζ.toNNReal) := by
    rw [setOf_coe_le_eq_Iic hζ] at hη
    have hK : IsCompact (Iic ζ.toNNReal) := by
      rw [← Icc_bot]; exact isCompact_Icc
    exact (hK.image_of_continuousOn hη).isClosed
  have heq : H \ pathRange η ζ = H \ η '' Iic ζ.toNNReal := by
    ext z
    constructor
    · rintro ⟨hz, hzA⟩
      refine ⟨hz, fun h => hzA ?_⟩
      have : z ∈ η '' Iic ζ.toNNReal ∩ H := ⟨h, hz⟩
      rw [← pathRange_inter_H_eq_of_ne_top hζ hend] at this
      exact this.1
    · rintro ⟨hz, hzA⟩
      refine ⟨hz, fun h => hzA ?_⟩
      have : z ∈ pathRange η ζ ∩ H := ⟨h, hz⟩
      rw [pathRange_inter_H_eq_of_ne_top hζ hend] at this
      exact this.1
  rw [heq]
  exact (isOpen_lt continuous_const Complex.continuous_im).sdiff hc

theorem pathRange_top (η : ℝ≥0 → ℂ) : pathRange η ⊤ = range η := by
  rw [pathRange]
  have : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun t => ENNReal.coe_lt_top
  rw [this, image_univ]

/-- **A transient continuous trace on `[0, ∞)` has a closed range.** -/
theorem isClosed_pathRange_top {η : ℝ≥0 → ℂ} (hη : Continuous η)
    (htend : Tendsto (fun t => ‖η t‖) atTop atTop) : IsClosed (pathRange η ⊤) := by
  rw [pathRange_top, ← closure_subset_iff_isClosed]
  intro z hz
  obtain ⟨R, hR⟩ := (htend.eventually_ge_atTop (‖z‖ + 1)).exists_forall_of_atTop
  have hsplit : range η = η '' Iic R ∪ η '' Ici R := by
    rw [← image_union, Iic_union_Ici, image_univ]
  rw [hsplit, closure_union] at hz
  rcases hz with hz | hz
  · have hK : IsCompact (Iic R) := by rw [← Icc_bot]; exact isCompact_Icc
    have hc : IsClosed (η '' Iic R) := (hK.image hη).isClosed
    rw [hc.closure_eq] at hz
    exact image_subset_range _ _ hz
  · exfalso
    obtain ⟨w, ⟨t, ht, rfl⟩, hw⟩ := Metric.mem_closure_iff.1 hz 1 one_pos
    have h1 := hR t ht
    have h2 : ‖η t‖ ≤ ‖z‖ + dist z (η t) := by
      rw [dist_eq_norm]
      calc ‖η t‖ = ‖z - (z - η t)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖z‖ + ‖z - η t‖ := norm_sub_le _ _
    linarith

/-- **The flow-line range has an open complement in `ℍ`**: for a finite lifetime with an endpoint off `ℍ`, or for
an infinite lifetime with a transient trace (the trace being continuous on `[0, ζ]` in both cases). -/
theorem isOpen_H_diff_pathRange {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hη : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hend : ζ ≠ ⊤ → η ζ.toNNReal ∉ H) (htend : ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :
    IsOpen (H \ pathRange η ζ) := by
  by_cases hζ : ζ = ⊤
  · subst hζ
    have hc : Continuous η := continuousOn_univ.1 (hη.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    exact (isOpen_lt continuous_const Complex.continuous_im).sdiff (isClosed_pathRange_top hc (htend rfl))
  · exact isOpen_H_diff_pathRange_of_ne_top hζ hη (hend hζ)

/-- Under the same regularity, the closure of the flow-line range adds no point of `ℍ`. -/
theorem closure_pathRange_inter_H {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hη : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hend : ζ ≠ ⊤ → η ζ.toNNReal ∉ H) (htend : ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :
    closure (pathRange η ζ) ∩ H = pathRange η ζ ∩ H := by
  refine Subset.antisymm (fun z ⟨hzc, hzH⟩ => ⟨?_, hzH⟩) (inter_subset_inter_left _ subset_closure)
  by_contra hz
  have hU := isOpen_H_diff_pathRange hη hend htend
  have hmem : z ∈ H \ pathRange η ζ := ⟨hzH, hz⟩
  obtain ⟨w, hw, hwA⟩ := mem_closure_iff.1 hzc _ hU hmem
  exact hw.2 hwA

/-! ### The corrected final step for the flow-line range -/

/-- **The final step of Proposition 5.1, corrected** (`A = pathRange η ζ`, no closedness). Assume almost surely: the
flow-line trace `η` is continuous on `[0, ζ]`, its endpoint `η(ζ)` is off `ℍ` when `ζ < ∞`, and `‖η‖ → ∞` when
`ζ = ∞`; and the counterflow trace `γ` (chart `M_q`) is continuous and avoids `−1` before its lifetime. Then the
per-time statements at the times of a countable dense set `D` give `LiesRightOf` (resp. `LiesLeftOf`) of the whole
counterflow with respect to the flow-line range. -/
theorem ae_liesRightOf_liesLeftOf_pathRange_of_countable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ℝ} {η γ : Ω → ℝ≥0 → ℂ} {ζ ζ' : Ω → ℝ≥0∞} {D : Set ℝ≥0} (hDc : D.Countable) (hD : Dense D)
    (hreg : ∀ᵐ ω ∂P, ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} ∧ (ζ ω ≠ ⊤ → η ω (ζ ω).toNNReal ∉ H) ∧
      (ζ ω = ⊤ → Tendsto (fun t => ‖η ω t‖) atTop atTop) ∧
      ContinuousOn (γ ω) {t | (t : ℝ≥0∞) < ζ' ω} ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω → γ ω t ≠ -1) :
    ((∀ r ∈ D, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ' ω →
          (stripCounterflowChart q).2.1 (γ ω r) ∉ stripLeftSide (pathRange (η ω) (ζ ω))) →
        ∀ᵐ ω ∂P, LiesRightOf (stripCounterflowRange q (γ ω) (ζ' ω)) (pathRange (η ω) (ζ ω))) ∧
      ((∀ r ∈ D, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ' ω →
          (stripCounterflowChart q).2.1 (γ ω r) ∉ stripRightSide (pathRange (η ω) (ζ ω))) →
        ∀ᵐ ω ∂P, LiesLeftOf (stripCounterflowRange q (γ ω) (ζ' ω)) (pathRange (η ω) (ζ ω))) := by
  refine ae_liesRightOf_liesLeftOf_of_countable_of_isOpen hDc hD ?_
  filter_upwards [hreg] with ω ⟨hη, hend, htend, hγ, hne⟩
  exact ⟨isOpen_H_diff_pathRange hη hend htend, hγ, hne⟩

end Sec5

end InteractingSLE
