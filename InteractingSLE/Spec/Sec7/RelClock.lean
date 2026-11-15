/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Process.Stopping

/-!
# The right inverse of a nondecreasing relative clock: (ER2)

Packet PROVE-STRIPSYS7. Specification §7.4, proof of Aux. lemma 125 (`source/spec/p385-432.md` L213–L222, p. 396),
"The relative stopping filtration": "Let `q(t)` be the relative half-plane capacity accumulated by the erased prefix,
divided by two. The established erasure makes `q` adapted, continuous, and nondecreasing on `[τ, σ)`, and constant on
the collapsed gaps. Freeze `q` at its terminal value `ζ` after `σ`, allowing the value infinity. Its right inverse

  `T(s) = inf {t ≥ τ : q(t) > s}`   (ER2)

is an ambient stopping time whenever `s` is below the relative capacity lifetime `ζ`. […] For a stopping time `S` in
the relative history filtration, the usual right-inverse time-change argument makes `T(S)` an ambient stopping time in
the exterior-enlarged filtration. Explicitly, the right continuity of `T(·)` expresses `{T(S) < t}` as the countable
union of `{S < r} ∩ {T(r) < t}` over positive rational `r`. Use a cemetery state once `s ≥ ζ`; then `T(s) = ∞` there.
In the usual right-inverse filtration this makes `ζ` a stopping lifetime, since `{ζ ≤ s} = {T(s) = ∞}`."

The clock `q` is an arbitrary real function of time here (it is only used at times `t ≥ τ`), and the relative time
`S` is an element of `WithTop ℝ≥0`; the cemetery convention is built in: `T(∞) = ∞`.

## Main definitions

* `rightInv q τ S = inf {t ≥ τ : S < q(t)}` (in `WithTop ℝ≥0`; `⊤` if there is no such `t`);
* `relLife q τ = sup {q(t) : t ≥ τ}` (in `WithTop ℝ≥0`), the relative lifetime `ζ`;
* `relFilt`: the time-changed filtration `s ↦ 𝓕_{T(s)}` ("the usual right-inverse filtration").

## Main results

* `rightInv_lt_iff`, `rightInv_eq_top_iff_relLife_le`, `rightInv_lt_top_iff`: `T(S) < ∞ ↔ S < ζ`;
* `rightInv_lt_coe_iff_exists_rat`: the right continuity of `T(·)` in the form used for `{T(S) < t}`;
* `apply_rightInv`: for a continuous clock, `q(T(s)) = s` when `q(τ) ≤ s` and `T(s)` is finite;
* **`isStoppingTime_rightInv_const`**: `T(s)` is a stopping time of a right-continuous filtration;
* **`isStoppingTime_rightInv`**: `T(S)` is a stopping time for every stopping time `S` of `relFilt`;
* **`isStoppingTime_relLife`**: `ζ` is a stopping time of `relFilt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace RelClock

/-! ### The deterministic right inverse -/

section Deterministic

/-- The right inverse `T(S) = inf {t ≥ τ : S < q(t)}` of the clock `q` started at `τ` (ER2), with `T(∞) = ∞`. -/
def rightInv (q : ℝ≥0 → ℝ) (τ S : WithTop ℝ≥0) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : τ ≤ t ∧ S < ((q t).toNNReal : WithTop ℝ≥0)), (t : WithTop ℝ≥0)

/-- The relative lifetime `ζ = sup {q(t) : t ≥ τ}` (the terminal value of the frozen clock, possibly `∞`). -/
def relLife (q : ℝ≥0 → ℝ) (τ : WithTop ℝ≥0) : WithTop ℝ≥0 :=
  ⨆ (t : ℝ≥0) (_ : τ ≤ t), ((q t).toNNReal : WithTop ℝ≥0)

variable {q : ℝ≥0 → ℝ} {τ S S' : WithTop ℝ≥0}

theorem coe_lt_toNNReal_iff {s : ℝ≥0} {x : ℝ} : (s : WithTop ℝ≥0) < (x.toNNReal : WithTop ℝ≥0) ↔ (s : ℝ) < x := by
  rw [WithTop.coe_lt_coe]
  exact Real.lt_toNNReal_iff_coe_lt

theorem rightInv_le {t : ℝ≥0} (hτ : τ ≤ t) (hS : S < ((q t).toNNReal : WithTop ℝ≥0)) :
    rightInv q τ S ≤ t :=
  iInf₂_le t ⟨hτ, hS⟩

theorem le_rightInv_iff {c : WithTop ℝ≥0} :
    c ≤ rightInv q τ S ↔ ∀ t : ℝ≥0, τ ≤ t → S < ((q t).toNNReal : WithTop ℝ≥0) → c ≤ t := by
  simp only [rightInv, le_iInf_iff, and_imp]

theorem le_rightInv : τ ≤ rightInv q τ S :=
  le_rightInv_iff.2 fun _ ht _ => ht

theorem rightInv_lt_iff {c : WithTop ℝ≥0} :
    rightInv q τ S < c ↔ ∃ t : ℝ≥0, τ ≤ t ∧ S < ((q t).toNNReal : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) < c := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact absurd h (not_lt.2 (le_rightInv_iff.2 fun t ht hS => hne t ht hS))
  · rintro ⟨t, ht, hS, htc⟩
    exact (rightInv_le ht hS).trans_lt htc

@[simp]
theorem rightInv_top : rightInv q τ ⊤ = ⊤ :=
  top_le_iff.1 (le_rightInv_iff.2 fun _ _ h => absurd h (not_lt.2 le_top))

theorem rightInv_mono (h : S ≤ S') : rightInv q τ S ≤ rightInv q τ S' :=
  le_rightInv_iff.2 fun _ ht hS => rightInv_le ht (h.trans_lt hS)

theorem monotone_rightInv : Monotone (rightInv q τ) := fun _ _ h => rightInv_mono h

theorem rightInv_eq_top_iff :
    rightInv q τ S = ⊤ ↔ ∀ t : ℝ≥0, τ ≤ t → ((q t).toNNReal : WithTop ℝ≥0) ≤ S := by
  rw [← top_le_iff, le_rightInv_iff]
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    exact absurd (h hlt) (not_le.2 (WithTop.coe_lt_top t))
  · intro h hS
    exact absurd h (not_le.2 hS)

theorem relLife_le_iff {c : WithTop ℝ≥0} :
    relLife q τ ≤ c ↔ ∀ t : ℝ≥0, τ ≤ t → ((q t).toNNReal : WithTop ℝ≥0) ≤ c := by
  simp only [relLife, iSup_le_iff]

/-- `T(S) = ∞` if and only if `ζ ≤ S` ("`{ζ ≤ s} = {T(s) = ∞}`"). -/
theorem rightInv_eq_top_iff_relLife_le : rightInv q τ S = ⊤ ↔ relLife q τ ≤ S := by
  rw [rightInv_eq_top_iff, relLife_le_iff]

/-- `T(S) < ∞` if and only if `S < ζ`. -/
theorem rightInv_lt_top_iff : rightInv q τ S < ⊤ ↔ S < relLife q τ := by
  rw [lt_top_iff_ne_top, ne_eq, rightInv_eq_top_iff_relLife_le, not_le]

/-- A rational strictly between two nonnegative reals, as a nonnegative real. -/
theorem exists_rat_btwn_nnreal {a b : ℝ≥0} (h : a < b) :
    ∃ r : ℚ, a < (r : ℝ).toNNReal ∧ (r : ℝ).toNNReal < b := by
  obtain ⟨r, har, hrb⟩ := exists_rat_btwn (show (a : ℝ) < b from h)
  have hr0 : (0 : ℝ) ≤ r := a.2.trans har.le
  refine ⟨r, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
    exact har
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
    exact hrb

/-- **Right continuity of `T(·)`, in rational form** (proof of Aux. lemma 125: "the right continuity of `T(·)`
expresses `{T(S) < t}` as the countable union of `{S < r} ∩ {T(r) < t}` over positive rational `r`"). -/
theorem rightInv_lt_iff_exists_rat {c : WithTop ℝ≥0} :
    rightInv q τ S < c ↔
      ∃ r : ℚ, S < (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ∧
        rightInv q τ (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < c := by
  constructor
  · intro h
    obtain ⟨t, ht, hS, htc⟩ := rightInv_lt_iff.1 h
    obtain ⟨s, rfl⟩ : ∃ s : ℝ≥0, S = s := by
      rcases S with _ | s
      · exact absurd hS (not_lt.2 le_top)
      · exact ⟨s, rfl⟩
    obtain ⟨r, hsr, hrq⟩ := exists_rat_btwn_nnreal (WithTop.coe_lt_coe.1 hS)
    refine ⟨r, WithTop.coe_lt_coe.2 hsr, (rightInv_le ht (WithTop.coe_lt_coe.2 hrq)).trans_lt htc⟩
  · rintro ⟨r, hSr, hr⟩
    exact (rightInv_mono hSr.le).trans_lt hr

/-- Before `T(s)`, the clock has not exceeded `s`. -/
theorem apply_le_of_lt_rightInv {s : ℝ≥0} {t : ℝ≥0} (hτ : τ ≤ t) (ht : (t : WithTop ℝ≥0) < rightInv q τ s) :
    q t ≤ s := by
  by_contra hlt
  push Not at hlt
  exact absurd (rightInv_le hτ (coe_lt_toNNReal_iff.2 hlt)) (not_le.2 ht)

/-- **The clock at its right inverse** (ER2): for a clock continuous on `[τ, ∞)` with `q(τ) ≤ s`, a finite `T(s)`
has `q(T(s)) = s`. -/
theorem apply_rightInv {s t₀ : ℝ≥0} (hτt : τ ≤ t₀)
    (hcont : ∀ t : ℝ≥0, τ ≤ t → ContinuousWithinAt q {u | τ ≤ (u : WithTop ℝ≥0)} t)
    (hτs : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) = τ → q t ≤ s) (hT : rightInv q τ s = t₀) : q t₀ = s := by
  have hcw := hcont t₀ hτt
  refine le_antisymm ?_ ?_
  · -- left limit, or the initial value
    by_cases hτeq : (t₀ : WithTop ℝ≥0) = τ
    · exact hτs t₀ hτeq
    · have hlt : τ < t₀ := lt_of_le_of_ne hτt (Ne.symm hτeq)
      obtain ⟨τ₀, rfl⟩ : ∃ τ₀ : ℝ≥0, τ = τ₀ := by
        rcases τ with _ | τ₀
        · exact absurd hlt (not_lt.2 le_top)
        · exact ⟨τ₀, rfl⟩
      have hlt' : τ₀ < t₀ := WithTop.coe_lt_coe.1 hlt
      have hev : ∀ᶠ u in 𝓝[Ico τ₀ t₀] t₀, q u ≤ s := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact apply_le_of_lt_rightInv (WithTop.coe_le_coe.2 hu.1)
          (hT ▸ WithTop.coe_lt_coe.2 hu.2)
      have hsub : Ico τ₀ t₀ ⊆ {u : ℝ≥0 | ((τ₀ : ℝ≥0) : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} :=
        fun u hu => WithTop.coe_le_coe.2 hu.1
      have hcl : t₀ ∈ closure (Ico τ₀ t₀) := by
        rw [closure_Ico hlt'.ne]
        exact right_mem_Icc.2 hlt'.le
      have : (𝓝[Ico τ₀ t₀] t₀).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
      exact le_of_tendsto (hcw.mono hsub).tendsto hev
  · -- right limit: points with `q > s` accumulate at `T(s)` from the right
    by_contra hlt
    push Not at hlt
    have hev : ∀ᶠ u : ℝ≥0 in 𝓝 t₀, τ ≤ (u : WithTop ℝ≥0) → q u < s :=
      eventually_nhdsWithin_iff.1 (hcw.eventually (gt_mem_nhds hlt))
    obtain ⟨u, htu, hsub⟩ := exists_Ico_subset_of_mem_nhds hev ⟨t₀ + 1, lt_add_one t₀⟩
    have hu' : rightInv q τ s < (u : WithTop ℝ≥0) := hT ▸ WithTop.coe_lt_coe.2 htu
    obtain ⟨t, hτ', hS, htu'⟩ := rightInv_lt_iff.1 hu'
    have ht₀t : t₀ ≤ t := WithTop.coe_le_coe.1 (hT ▸ rightInv_le hτ' hS)
    have hq := hsub ⟨ht₀t, WithTop.coe_lt_coe.1 htu'⟩ hτ'
    exact absurd (coe_lt_toNNReal_iff.1 hS) (not_lt.2 hq.le)

end Deterministic

/-! ### Stopping times -/

section Stopping

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- A set measurable at a stopping time `τ`, cut by `{τ < i}`, is measurable at time `i`. -/
theorem measurableSet_inter_lt {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (i : ℝ≥0) :
    MeasurableSet[𝓕 i] (A ∩ {ω | τ ω < i}) := by
  have e : A ∩ {ω | τ ω < i} = ⋃ (r : ℚ) (_ : (r : ℝ).toNNReal < i),
      A ∩ {ω | τ ω ≤ (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hω, hlt⟩
      have hne : τ ω ≠ ⊤ := ne_top_of_lt hlt
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
      rw [← ht] at hlt
      obtain ⟨r, htr, hri⟩ := exists_rat_btwn_nnreal (WithTop.coe_lt_coe.1 hlt)
      refine ⟨r, hri, hω, ?_⟩
      rw [← ht]
      exact WithTop.coe_le_coe.2 htr.le
    · rintro ⟨r, hri, hω, hr⟩
      exact ⟨hω, lt_of_le_of_lt hr (WithTop.coe_lt_coe.2 hri)⟩
  rw [e]
  exact MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun hri => 𝓕.mono hri.le _ (hA.2 _)

variable {q : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- **`T(s)` is an ambient stopping time** (proof of Aux. lemma 125, (ER2): "Its right inverse `T(s)` is an ambient
stopping time"): for a right-continuous filtration, an adapted clock that is nondecreasing after the stopping time `τ`,
and a fixed relative time `S`. -/
theorem isStoppingTime_rightInv_const [𝓕.IsRightContinuous] (hq : ∀ t, Measurable[𝓕 t] (q t))
    (hτ : IsStoppingTime 𝓕 τ) (hmono : ∀ ω (t t' : ℝ≥0), τ ω ≤ t → t ≤ t' → q t ω ≤ q t' ω)
    (S : WithTop ℝ≥0) : IsStoppingTime 𝓕 fun ω => rightInv (fun t => q t ω) (τ ω) S := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i => ?_
  have e : {ω | rightInv (fun t => q t ω) (τ ω) S < i} = ⋃ (r : ℚ) (_ : (r : ℝ).toNNReal < i),
      {ω | τ ω ≤ (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} ∩
        {ω | S < ((q (r : ℝ).toNNReal ω).toNNReal : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      obtain ⟨t, hτt, hS, hti⟩ := rightInv_lt_iff.1 h
      obtain ⟨r, htr, hri⟩ := exists_rat_btwn_nnreal (WithTop.coe_lt_coe.1 hti)
      refine ⟨r, hri, hτt.trans (WithTop.coe_le_coe.2 htr.le), hS.trans_le ?_⟩
      exact WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal (hmono ω t _ hτt htr.le))
    · rintro ⟨r, hri, hτr, hS⟩
      exact (rightInv_le hτr hS).trans_lt (WithTop.coe_lt_coe.2 hri)
  rw [e]
  refine MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun hri => 𝓕.mono hri.le _ ((hτ _).inter ?_)
  by_cases hS : S = ⊤
  · subst hS
    have : {ω | (⊤ : WithTop ℝ≥0) < ((q (r : ℝ).toNNReal ω).toNNReal : WithTop ℝ≥0)} = ∅ :=
      eq_empty_of_forall_notMem fun ω hω => (not_lt.2 le_top) (show (⊤ : WithTop ℝ≥0) < _ from hω)
    rw [this]
    exact @MeasurableSet.empty _ (𝓕 _)
  · obtain ⟨s, rfl⟩ := WithTop.ne_top_iff_exists.1 hS
    have : {ω | ((s : ℝ≥0) : WithTop ℝ≥0) < ((q (r : ℝ).toNNReal ω).toNNReal : WithTop ℝ≥0)} =
        {ω | (s : ℝ) < q (r : ℝ).toNNReal ω} := by
      ext ω
      exact coe_lt_toNNReal_iff
    rw [this]
    exact measurableSet_lt measurable_const (hq _)

/-- **The relative (time-changed) filtration** `s ↦ 𝓕_{T(s)}` ("the usual right-inverse filtration"). -/
def relFilt (hT : ∀ s : ℝ≥0, IsStoppingTime 𝓕 fun ω => rightInv (fun t => q t ω) (τ ω) s) :
    Filtration ℝ≥0 mΩ where
  seq s := (hT s).measurableSpace
  mono' _ _ hss' := IsStoppingTime.measurableSpace_mono _ _ fun _ =>
    rightInv_mono (WithTop.coe_le_coe.2 hss')
  le' s := (hT s).measurableSpace_le

theorem relFilt_apply (hT : ∀ s : ℝ≥0, IsStoppingTime 𝓕 fun ω => rightInv (fun t => q t ω) (τ ω) s)
    (s : ℝ≥0) : relFilt hT s = (hT s).measurableSpace := rfl

/-- **`T(S)` is an ambient stopping time for every relative stopping time `S`** (proof of Aux. lemma 125: "For a
stopping time `S` in the relative history filtration, the usual right-inverse time-change argument makes `T(S)` an
ambient stopping time […] `{T(S) < t}` [is] the countable union of `{S < r} ∩ {T(r) < t}` over positive rational
`r`"). -/
theorem isStoppingTime_rightInv [𝓕.IsRightContinuous]
    (hT : ∀ s : ℝ≥0, IsStoppingTime 𝓕 fun ω => rightInv (fun t => q t ω) (τ ω) s) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (relFilt hT) S) : IsStoppingTime 𝓕 fun ω => rightInv (fun t => q t ω) (τ ω) (S ω) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i => ?_
  have e : {ω | rightInv (fun t => q t ω) (τ ω) (S ω) < i} = ⋃ r : ℚ,
      {ω | S ω < (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} ∩
        {ω | rightInv (fun t => q t ω) (τ ω) (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < i} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    exact rightInv_lt_iff_exists_rat
  rw [e]
  exact MeasurableSet.iUnion fun r => measurableSet_inter_lt (hT _) (hS.measurableSet_lt _) i

/-- **The relative lifetime is a stopping time of the relative filtration** (proof of Aux. lemma 125: "In the usual
right-inverse filtration this makes `ζ` a stopping lifetime, since `{ζ ≤ s} = {T(s) = ∞}`"). -/
theorem isStoppingTime_relLife
    (hT : ∀ s : ℝ≥0, IsStoppingTime 𝓕 fun ω => rightInv (fun t => q t ω) (τ ω) s) :
    IsStoppingTime (relFilt hT) fun ω => relLife (fun t => q t ω) (τ ω) := by
  intro s
  have e : {ω | relLife (fun t => q t ω) (τ ω) ≤ s} =
      {ω | rightInv (fun t => q t ω) (τ ω) s = ⊤} := by
    ext ω
    exact rightInv_eq_top_iff_relLife_le.symm
  rw [e, relFilt_apply]
  have e2 : {ω | rightInv (fun t => q t ω) (τ ω) s = ⊤} =
      ⋂ n : ℕ, {ω | rightInv (fun t => q t ω) (τ ω) s ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, not_le]
    constructor
    · intro h n
      rw [h]
      exact WithTop.coe_lt_top _
    · intro h
      by_contra hne
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
      obtain ⟨n, hn⟩ := exists_nat_gt t
      have := h n
      rw [← ht] at this
      exact absurd (WithTop.coe_lt_coe.1 this) (not_lt.2 hn.le)
  rw [e2]
  exact MeasurableSet.iInter fun n => ((hT s).measurableSet_le' _).compl

end Stopping

end RelClock

end Sec7

end InteractingSLE
