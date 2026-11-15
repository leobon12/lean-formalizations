/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageExp

/-!
# Proposition 5.9's switching rule is measurable

Packet PROVE-PROP59T4. Specification §5.2, proof of Proposition 5.9 (p. 146): "Regular conditional distributions, or
the measurable SDE transition kernels, make this choice measurable with respect to the past. […] All decisions to
continue or abort are made at stopping times."

For one stage of the alternating construction (PROVE-PROP59T2's `StageData`, switching rule `succSet`/`swT`,
next start `nextStart`) whose piece is **regular** (`IsRegStage`: jointly measurable driver and marks, measurable
lifetime, a continuous strictly increasing original clock measurable in the sample, and a far gap continuous before
the lifetime), the switching events and the switching time are measurable:

* `clkHit`, `clkInv`: the event that the original clock reaches the grid point `g`, and the (unique) piece time at
  which it does; `measurableSet_clkHit`, `measurable_clkInv`;
* `swSet`: the switching condition at that time; `measurableSet_swSet`;
* **`measurableSet_succSet`**, **`measurable_swT`**, **`measurable_swIdx`** (the grid index of the switch),
  **`measurable_nextStart`**, **`measurableSet_succ_one`**.

The proof reads "for all `u ≤ s`, the far gap is positive" through rational times and a positive margin (compactness
of `[0, s]` and continuity before the lifetime).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59System

open Prop59Stage

/-! ### Positivity on `[0, s]` through rational times -/

/-- **Positivity on `[0, τ]` through rational times**: for `f` continuous on `{u < ζ}` and `τ < ζ`, `f > 0` on `[0, τ]`
iff for some `m`, `f ≥ 1/(m + 1)` at every rational time `≤ τ` and at `τ`. -/
theorem forall_le_pos_iff {f : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hf : ContinuousOn f {u | (u : ℝ≥0∞) < ζ}) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < ζ) :
    (∀ u ≤ τ, 0 < f u) ↔ ∃ m : ℕ, (∀ q : ℚ≥0, (q : ℝ≥0) ≤ τ → 1 / ((m : ℝ) + 1) ≤ f q) ∧
      1 / ((m : ℝ) + 1) ≤ f τ := by
  have hsub : Icc (0 : ℝ≥0) τ ⊆ {u | (u : ℝ≥0∞) < ζ} := fun u hu =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu.2) hτ
  have hopen : IsOpen {u : ℝ≥0 | (u : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  constructor
  · intro hpos
    obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le : (0 : ℝ≥0) ≤ τ)) (hf.mono hsub)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (hpos u₀ hu₀.2)
    refine ⟨m, fun q hq => ?_, ?_⟩
    · exact hm.le.trans (hmin ⟨zero_le, hq⟩)
    · exact hm.le.trans (hmin ⟨zero_le, le_rfl⟩)
  · rintro ⟨m, hq, hτm⟩ u hu
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    rcases hu.lt_or_eq with hlt | rfl
    · refine lt_of_lt_of_le hm ?_
      by_contra hcon
      push Not at hcon
      have hcu : ContinuousAt f u := hf.continuousAt (hopen.mem_nhds (hsub ⟨zero_le, hu⟩))
      have hev : ∀ᶠ v in 𝓝 u, f v < 1 / ((m : ℝ) + 1) := hcu.eventually (gt_mem_nhds hcon)
      obtain ⟨b, hb, hbsub⟩ := exists_Ico_subset_of_mem_nhds hev ⟨τ, hlt⟩
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn₀ (lt_min hb hlt)
      have h1 : f q < 1 / ((m : ℝ) + 1) := hbsub ⟨hq1.le, hq2.trans_le (min_le_left _ _)⟩
      have h2 := hq q (hq2.trans_le (min_le_right _ _)).le
      linarith
    · exact lt_of_lt_of_le hm hτm

/-! ### Regular stages -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ}

/-- **A regular stage**: measurable start, jointly measurable driver and marks, measurable lifetime, an original clock
that is continuous and strictly increasing at every sample and measurable at every time, and a far gap continuous
before the lifetime at every sample. -/
structure IsRegStage (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j)) : Prop where
  y : Measurable d.y
  W : Measurable (Function.uncurry d.W)
  VL : ∀ i, Measurable (Function.uncurry (d.VL i))
  VR : ∀ k, Measurable (Function.uncurry (d.VR k))
  ζ : Measurable d.ζ
  clk : ∀ s, Measurable fun ω => d.clk ω s
  clk_cont : ∀ ω, Continuous (d.clk ω)
  clk_mono : ∀ ω, StrictMono (d.clk ω)
  gap : ∀ ω, ContinuousOn (farGap hnL hnR j d ω) {u | (u : ℝ≥0∞) < d.ζ ω}

section Clock

variable {j : ℕ} (d : StageData Ω (nL₀ + j) (nR₀ + j))

/-- The event that the original clock reaches `g`. -/
def clkHit (g : ℝ≥0) : Set Ω := {ω | ∃ s, d.clk ω s = g}

open Classical in
/-- The piece time at which the original clock reaches `g` (`0` if it does not). -/
def clkInv (g : ℝ≥0) (ω : Ω) : ℝ≥0 := if h : ω ∈ clkHit d g then Classical.choose h else 0

variable {d}

omit mΩ in
theorem clk_clkInv {g : ℝ≥0} {ω : Ω} (h : ω ∈ clkHit d g) : d.clk ω (clkInv d g ω) = g := by
  classical
  have e : clkInv d g ω = Classical.choose h := by simp only [clkInv, h, ↓reduceDIte]
  rw [e]
  exact Classical.choose_spec h

omit mΩ in
theorem eq_clkInv {g : ℝ≥0} {ω : Ω} (hm : StrictMono (d.clk ω)) {s : ℝ≥0} (hs : d.clk ω s = g) :
    s = clkInv d g ω :=
  hm.injective (hs.trans (clk_clkInv ⟨s, hs⟩).symm)

omit mΩ in
theorem clkInv_le_iff {g : ℝ≥0} {ω : Ω} (hm : StrictMono (d.clk ω)) (h : ω ∈ clkHit d g) (a : ℝ≥0) :
    clkInv d g ω ≤ a ↔ g ≤ d.clk ω a := by
  rw [← hm.le_iff_le, clk_clkInv h]

omit mΩ in
theorem mem_clkHit_iff {g : ℝ≥0} {ω : Ω} (hc : Continuous (d.clk ω)) (hm : StrictMono (d.clk ω)) :
    ω ∈ clkHit d g ↔ d.clk ω 0 ≤ g ∧ ∃ m : ℕ, g ≤ d.clk ω m := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨hm.monotone zero_le, ⌈(s : ℝ)⌉₊, hm.monotone (by
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact Nat.le_ceil _)⟩
  · rintro ⟨h0, m, hm'⟩
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ m) hc.continuousOn ⟨h0, hm'⟩
    exact ⟨s, hs⟩

variable (hd : ∀ ω, Continuous (d.clk ω) ∧ StrictMono (d.clk ω)) (hcm : ∀ s, Measurable fun ω => d.clk ω s)
include hd hcm

theorem measurableSet_clkHit (g : ℝ≥0) : MeasurableSet (clkHit d g) := by
  have e : clkHit d g = {ω | d.clk ω 0 ≤ g} ∩ ⋃ m : ℕ, {ω | g ≤ d.clk ω m} := by
    ext ω
    rw [mem_clkHit_iff (hd ω).1 (hd ω).2]
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
  rw [e]
  exact (measurableSet_le (hcm 0) measurable_const).inter
    (MeasurableSet.iUnion fun m => measurableSet_le measurable_const (hcm _))

theorem measurable_clkInv (g : ℝ≥0) : Measurable (clkInv d g) := by
  refine measurable_of_Iic fun a => ?_
  have e : clkInv d g ⁻¹' Iic a = (clkHit d g ∩ {ω | g ≤ d.clk ω a}) ∪ (clkHit d g)ᶜ := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
    by_cases h : ω ∈ clkHit d g
    · rw [clkInv_le_iff (hd ω).2 h]
      simp [h]
    · have : clkInv d g ω = 0 := by simp only [clkInv, h, ↓reduceDIte]
      simp [h, this]
  rw [e]
  exact ((measurableSet_clkHit hd hcm g).inter (measurableSet_le measurable_const (hcm a))).union
    (measurableSet_clkHit hd hcm g).compl

end Clock

/-! ### The switching events -/

section Switch

variable {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀} {j : ℕ} {d : StageData Ω (nL₀ + j) (nR₀ + j)}

/-- The switching condition at the grid point `g`: the clock reaches `g` and the switching condition holds there. -/
def swSet (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j)) (g : ℝ≥0) : Set Ω :=
  {ω | ω ∈ clkHit d g ∧ SwCond hnL hnR j d ω (clkInv d g ω)}

theorem measurable_farGap_apply (hW : Measurable (Function.uncurry d.W))
    (hVL : ∀ i, Measurable (Function.uncurry (d.VL i))) (hVR : ∀ k, Measurable (Function.uncurry (d.VR k)))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) : Measurable fun ω => farGap hnL hnR j d ω (τ ω) := by
  have hpair : Measurable fun ω => (τ ω, ω) := hτ.prodMk measurable_id
  unfold farGap
  by_cases hj : Even j
  · simp only [hj, ↓reduceIte]
    exact (hW.comp hpair).sub ((hVL _).comp hpair)
  · simp only [hj, ↓reduceIte]
    exact ((hVR _).comp hpair).sub (hW.comp hpair)

theorem measurableSet_swSet (hr : IsRegStage hnL hnR j d) (g : ℝ≥0) : MeasurableSet (swSet hnL hnR j d g) := by
  have hd : ∀ ω, Continuous (d.clk ω) ∧ StrictMono (d.clk ω) := fun ω => ⟨hr.clk_cont ω, hr.clk_mono ω⟩
  have hH := measurableSet_clkHit hd hr.clk g
  have hI := measurable_clkInv hd hr.clk g
  have hpair : Measurable fun ω => (clkInv d g ω, ω) := hI.prodMk measurable_id
  have hlt : MeasurableSet {ω | (clkInv d g ω : ℝ≥0∞) < d.ζ ω} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp hI) hr.ζ
  have hband : MeasurableSet {ω | (d.y ω).1 + d.W (clkInv d g ω) ω ∈ band j} :=
    ((measurable_fst.comp hr.y).add (hr.W.comp hpair)) measurableSet_Ioo
  have hgapq : ∀ q : ℚ≥0, Measurable fun ω => farGap hnL hnR j d ω (q : ℝ≥0) := fun q =>
    measurable_farGap_apply hr.W hr.VL hr.VR measurable_const
  have hgapτ : Measurable fun ω => farGap hnL hnR j d ω (clkInv d g ω) :=
    measurable_farGap_apply hr.W hr.VL hr.VR hI
  have e : swSet hnL hnR j d g = clkHit d g ∩ {ω | (clkInv d g ω : ℝ≥0∞) < d.ζ ω} ∩
      {ω | (d.y ω).1 + d.W (clkInv d g ω) ω ∈ band j} ∩
      ⋃ m : ℕ, (⋂ q : ℚ≥0, ({ω | (q : ℝ≥0) ≤ clkInv d g ω}ᶜ ∪
        {ω | 1 / ((m : ℝ) + 1) ≤ farGap hnL hnR j d ω (q : ℝ≥0)})) ∩
        {ω | 1 / ((m : ℝ) + 1) ≤ farGap hnL hnR j d ω (clkInv d g ω)} := by
    ext ω
    simp only [swSet, SwCond, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, mem_union, mem_compl_iff,
      not_le]
    constructor
    · rintro ⟨hω, hζ, hb, hgap⟩
      obtain ⟨m, h1, h2⟩ := (forall_le_pos_iff (hr.gap ω) hζ).1 hgap
      refine ⟨⟨⟨hω, hζ⟩, hb⟩, m, fun q => ?_, h2⟩
      by_cases hq : (q : ℝ≥0) ≤ clkInv d g ω
      · exact Or.inr (h1 q hq)
      · exact Or.inl (not_le.1 hq)
    · rintro ⟨⟨⟨hω, hζ⟩, hb⟩, m, h1, h2⟩
      refine ⟨hω, hζ, hb, (forall_le_pos_iff (hr.gap ω) hζ).2 ⟨m, fun q hq => ?_, h2⟩⟩
      rcases h1 q with h | h
      · exact absurd hq (not_le.2 h)
      · exact h
  rw [e]
  refine ((hH.inter hlt).inter hband).inter (MeasurableSet.iUnion fun m => ?_)
  refine (MeasurableSet.iInter fun q => ?_).inter (measurableSet_le measurable_const hgapτ)
  exact (measurableSet_le measurable_const hI).compl.union (measurableSet_le measurable_const (hgapq q))

theorem succSet_eq_iUnion (hr : IsRegStage hnL hnR j d) (n : ℕ) :
    succSet G hnL hnR j d n = ⋃ k, swSet hnL hnR j d (G n k) := by
  ext ω
  simp only [succSet, swSet, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨k, s, hs, hc⟩
    refine ⟨k, ⟨s, hs⟩, ?_⟩
    rwa [← eq_clkInv (hr.clk_mono ω) hs]
  · rintro ⟨k, hω, hc⟩
    exact ⟨k, _, clk_clkInv hω, hc⟩

theorem measurableSet_succSet (hr : IsRegStage hnL hnR j d) (n : ℕ) :
    MeasurableSet (succSet G hnL hnR j d n) := by
  rw [succSet_eq_iUnion hr]
  exact MeasurableSet.iUnion fun k => measurableSet_swSet hr _

/-- **The grid index of the switch** (the least successful grid index; `0` if the stage fails). -/
def swIdx (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (j : ℕ) (d : StageData Ω (nL₀ + j) (nR₀ + j))
    (n : ℕ) (ω : Ω) : ℕ :=
  sInf {k | ω ∈ swSet hnL hnR j d (G n k)}

theorem swIdx_spec (hr : IsRegStage hnL hnR j d) {n : ℕ} {ω : Ω} (h : ω ∈ succSet G hnL hnR j d n) :
    ω ∈ swSet hnL hnR j d (G n (swIdx G hnL hnR j d n ω)) ∧
      ∀ k < swIdx G hnL hnR j d n ω, ω ∉ swSet hnL hnR j d (G n k) := by
  have hne : {k | ω ∈ swSet hnL hnR j d (G n k)}.Nonempty := by
    rw [succSet_eq_iUnion hr, mem_iUnion] at h
    exact h
  exact ⟨Nat.sInf_mem hne, fun k hk => Nat.notMem_of_lt_sInf hk⟩

theorem swIdx_of_not_mem (hr : IsRegStage hnL hnR j d) {n : ℕ} {ω : Ω} (h : ω ∉ succSet G hnL hnR j d n) :
    swIdx G hnL hnR j d n ω = 0 := by
  have he : {k | ω ∈ swSet hnL hnR j d (G n k)} = ∅ := by
    rw [succSet_eq_iUnion hr, mem_iUnion] at h
    push Not at h
    exact eq_empty_iff_forall_notMem.2 h
  simp only [swIdx, he, Nat.sInf_empty]

theorem measurable_swIdx (hr : IsRegStage hnL hnR j d) (n : ℕ) : Measurable (swIdx G hnL hnR j d n) := by
  refine measurable_to_countable' fun k => ?_
  have e : swIdx G hnL hnR j d n ⁻¹' {k} =
      (succSet G hnL hnR j d n ∩ (swSet hnL hnR j d (G n k) ∩ ⋂ i ∈ Finset.range k,
        (swSet hnL hnR j d (G n i))ᶜ)) ∪ ((succSet G hnL hnR j d n)ᶜ ∩ {_ω | k = 0}) := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_iInter, Finset.mem_range,
      mem_compl_iff, mem_ofPred_eq]
    by_cases h : ω ∈ succSet G hnL hnR j d n
    · obtain ⟨h1, h2⟩ := swIdx_spec hr h
      simp only [h, true_and, not_true_eq_false, false_and, or_false]
      constructor
      · rintro rfl
        exact ⟨h1, h2⟩
      · rintro ⟨hk, hmin⟩
        refine le_antisymm ?_ ?_
        · by_contra hlt
          exact h2 k (not_le.1 hlt) hk
        · by_contra hlt
          exact hmin _ (not_le.1 hlt) h1
    · simp only [h, false_and, not_false_eq_true, true_and, false_or, swIdx_of_not_mem hr h]
      exact eq_comm
  rw [e]
  refine ((measurableSet_succSet hr n).inter ((measurableSet_swSet hr _).inter
    (MeasurableSet.biInter (Finset.range k).countable_toSet fun i _ => (measurableSet_swSet hr _).compl))).union
    ((measurableSet_succSet hr n).compl.inter (MeasurableSet.const _))

/-- **The switching time is the clock inverse at the least successful grid point.** -/
theorem swT_eq (hr : IsRegStage hnL hnR j d) {n : ℕ} {ω : Ω} (h : ω ∈ succSet G hnL hnR j d n) :
    swT G hnL hnR j d n ω = clkInv d (G n (swIdx G hnL hnR j d n ω)) ω := by
  classical
  have e : swT G hnL hnR j d n ω = Classical.choose (Nat.find_spec h) := by
    simp only [swT, h, ↓reduceDIte]
  have hs := Classical.choose_spec (Nat.find_spec h)
  obtain ⟨h1, h2⟩ := swIdx_spec hr h
  have hk : Nat.find h = swIdx G hnL hnR j d n ω := by
    refine le_antisymm (Nat.find_min' h ⟨_, clk_clkInv h1.1, h1.2⟩) ?_
    by_contra hlt
    refine h2 _ (not_le.1 hlt) ⟨⟨_, hs.1⟩, ?_⟩
    rw [← eq_clkInv (hr.clk_mono ω) hs.1]
    exact hs.2
  rw [e]
  exact eq_clkInv (hr.clk_mono ω) (hs.1.trans (by rw [hk]))

theorem measurable_swT (hr : IsRegStage hnL hnR j d) (n : ℕ) : Measurable (swT G hnL hnR j d n) := by
  classical
  have hd : ∀ ω, Continuous (d.clk ω) ∧ StrictMono (d.clk ω) := fun ω => ⟨hr.clk_cont ω, hr.clk_mono ω⟩
  have hjoint : Measurable fun p : Ω × ℕ => clkInv d (G n p.2) p.1 :=
    measurable_from_prod_countable_left fun k => measurable_clkInv hd hr.clk (G n k)
  have hidx : Measurable fun ω => clkInv d (G n (swIdx G hnL hnR j d n ω)) ω :=
    hjoint.comp (measurable_id.prodMk (measurable_swIdx hr n))
  have e : swT G hnL hnR j d n = (succSet G hnL hnR j d n).piecewise
      (fun ω => clkInv d (G n (swIdx G hnL hnR j d n ω)) ω) fun _ => 0 := by
    funext ω
    by_cases h : ω ∈ succSet G hnL hnR j d n
    · rw [piecewise_eq_of_mem _ _ _ h, swT_eq hr h]
    · rw [piecewise_eq_of_notMem _ _ _ h]
      simp only [swT, h, ↓reduceDIte]
  rw [e]
  exact hidx.piecewise (measurableSet_succSet hr n) measurable_const

theorem measurableSet_succ_one (hr : IsRegStage hnL hnR j d) (n : ℕ) :
    MeasurableSet {ω | ω ∈ succSet G hnL hnR j d n ∧ (1 : ℝ≥0) ≤ swT G hnL hnR j d n ω} :=
  (measurableSet_succSet hr n).inter (show MeasurableSet {ω | (1 : ℝ≥0) ≤ swT G hnL hnR j d n ω} from
    measurableSet_le measurable_const (measurable_swT hr n))

/-- **The next start is measurable.** -/
theorem measurable_nextStart (hr : IsRegStage hnL hnR j d) (n : ℕ) :
    Measurable (nextStart G hnL hnR j d n) := by
  have hT := measurable_swT (G := G) hr n
  have hpair : Measurable fun ω => (swT G hnL hnR j d n ω, ω) := hT.prodMk measurable_id
  have hW : Measurable fun ω => d.W (swT G hnL hnR j d n ω) ω := hr.W.comp hpair
  refine ((measurable_fst.comp hr.y).add hW).prodMk ((measurable_pi_iff.2 fun i => ?_).prodMk
    (measurable_pi_iff.2 fun k => ?_))
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact measurable_const
    · exact ((hr.VL i).comp hpair).sub hW
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact measurable_const
    · exact ((hr.VR k).comp hpair).sub hW

end Switch

end InteractingSLE.Sec5.Prop59System
