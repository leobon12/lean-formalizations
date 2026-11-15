/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GZoneM
import InteractingSLE.Spec.Sec7.Lemma78MeanWordMeas
import InteractingSLE.Spec.Supplement.G7RestartMeas

/-!
# Measurability of the boundary word of a disjoint pair

Packet PROVE-LEMMA76G (the word of Lemma 7.6 must be measurable for the retained σ-algebra). For retained data `d`
with `IsMeasGood` (for any σ-algebra):

* `measurable_indicator_chartPt`: the chart point of a measurable point, on a measurable event on which the chart has
  a limit there, is measurable (limits of the measurable forward chart along the random domain);
* the events on which a real point, resp. the first tip, is a regular point of the closure of the domain
  (`ptEv`, `tipEv`) are measurable, and there the chart has a limit;
* the bases of the two prefixes are measurable (`measurable_indicator_baseL`, `…_baseR`);
* the **word builder** `zbuild` (the word of `ZW.word`, truncated, as a function of the counts, the chart points of the
  original jumps and the five chart points of the zones) is measurable in its real inputs;
* **`wordM`**: the word with every input read on its measurable event, measurable (`IsMeasGood.measurable_wordM`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

open Restart Supp7

/-! ### The word builder -/

/-- **The word builder**: the truncated word of `ZW.word` with counts `k₁ ≤ k₂ ≤ k₃ ≤ k₄`, chart points `Tp i` of
the original jumps and chart points `L₂, R₂, L₁, M₁, R₁` (and `M₂ = 0`). -/
def zbuild (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) (k₁ k₂ k₃ k₄ : ℕ) (Tp : ℕ → ℝ) (L₂ R₂ L₁ M₁ R₁ : ℝ) :
    BoundaryWord :=
  (k₁ + 3 + (k₃ - k₂) + 3 + (c₀.1 - k₄),
    fun i => if i < k₁ + 3 + (k₃ - k₂) + 3 + (c₀.1 - k₄) then
      (if i < k₁ then Tp i else if i = k₁ then L₂ else if i = k₁ + 1 then 0
      else if i = k₁ + 2 then R₂ else if i < k₁ + 3 + (k₃ - k₂) then Tp (i - (k₁ + 3) + k₂)
      else if i = k₁ + 3 + (k₃ - k₂) then L₁ else if i = k₁ + 3 + (k₃ - k₂) + 1 then M₁
      else if i = k₁ + 3 + (k₃ - k₂) + 2 then R₁ else Tp (i - (k₁ + 3 + (k₃ - k₂) + 3) + k₄)) else 0,
    fun j => if j ≤ k₁ then c₀.2.2 j else if j = k₁ + 1 then g₁ else if j = k₁ + 2 then g₂
      else if j ≤ k₁ + 3 + (k₃ - k₂) then c₀.2.2 (j - (k₁ + 3) + k₂) else if j = k₁ + 3 + (k₃ - k₂) + 1 then g₃
      else if j = k₁ + 3 + (k₃ - k₂) + 2 then g₄ else c₀.2.2 (j - (k₁ + 3 + (k₃ - k₂) + 3) + k₄))

/-- The truncated zone word is the builder. -/
theorem trunc_word_eq_zbuild (z : ZW) (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) (hM₂ : z.M₂ = 0) :
    (z.word c₀ g₁ g₂ g₃ g₄).trunc = zbuild c₀ g₁ g₂ g₃ g₄ (z.k₁ c₀) (z.k₂ c₀) (z.k₃ c₀) (z.k₄ c₀)
      (fun i => z.T (c₀.2.1 i)) z.L₂ z.R₂ z.L₁ z.M₁ z.R₁ := by
  unfold BoundaryWord.trunc ZW.word ZW.m zbuild
  rw [hM₂]

/-- The builder only reads the chart points of the original jumps of the three zones. -/
theorem zbuild_congr {c₀ : BoundaryWord} {g₁ g₂ g₃ g₄ : ℝ} {k₁ k₂ k₃ k₄ : ℕ} {Tp Tp' : ℕ → ℝ}
    {L₂ R₂ L₁ M₁ R₁ : ℝ} (h4 : k₄ ≤ c₀.1)
    (hT : ∀ i, (i < k₁ ∨ (k₂ ≤ i ∧ i < k₃) ∨ (k₄ ≤ i ∧ i < c₀.1)) → Tp i = Tp' i) :
    zbuild c₀ g₁ g₂ g₃ g₄ k₁ k₂ k₃ k₄ Tp L₂ R₂ L₁ M₁ R₁ = zbuild c₀ g₁ g₂ g₃ g₄ k₁ k₂ k₃ k₄ Tp' L₂ R₂ L₁ M₁ R₁ := by
  simp only [zbuild, Prod.mk.injEq, true_and, and_true]
  funext i
  split_ifs <;> first | rfl | (apply hT; omega)

theorem measurable_zbuild_pos {Ω : Type*} [MeasurableSpace Ω] (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ)
    (k₁ k₂ k₃ k₄ : ℕ) {Tp : ℕ → Ω → ℝ} (hTp : ∀ i, Measurable (Tp i)) {L₂ R₂ L₁ M₁ R₁ : Ω → ℝ}
    (hL₂ : Measurable L₂) (hR₂ : Measurable R₂) (hL₁ : Measurable L₁) (hM₁ : Measurable M₁) (hR₁ : Measurable R₁)
    (i : ℕ) :
    Measurable fun ω => (zbuild c₀ g₁ g₂ g₃ g₄ k₁ k₂ k₃ k₄ (fun j => Tp j ω) (L₂ ω) (R₂ ω) (L₁ ω) (M₁ ω)
      (R₁ ω)).2.1 i := by
  simp only [zbuild]
  split_ifs
  all_goals first | exact hTp _ | exact hL₂ | exact hR₂ | exact hL₁ | exact hM₁ | exact hR₁ | exact measurable_const

/-! ### Chart points of measurable points -/

section ChartPt

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

/-- **The chart point of a measurable point on a measurable event where the chart has a limit is measurable.** -/
theorem measurable_indicator_chartPt (hd : d.IsMeasGood) {C : Set Ω} (hC : MeasurableSet C) {q : Ω → ℂ}
    (hq : Measurable q)
    (hspec : ∀ ω ∈ C, q ω ∈ closure (d.D ω) ∧ ∃ y, Tendsto (d.fwd ω) (𝓝[d.D ω] (q ω)) (𝓝 y)) :
    Measurable (C.indicator fun ω => chartPt (d.fwd ω) (d.D ω) (q ω)) := by
  classical
  set q' : Ω → ℂ := fun ω => if ω ∈ C then q ω else d.p ω with hq'def
  have hq' : Measurable q' := Measurable.ite hC hq hd.measurable_p
  have hq'D : ∀ ω, q' ω ∈ closure (d.D ω) := fun ω => by
    by_cases hω : ω ∈ C
    · simp only [hq'def, hω, ↓reduceIte]; exact (hspec ω hω).1
    · simp only [hq'def, hω, ↓reduceIte]; exact hd.p_mem_closure ω
  have hfg : ∀ ω, d.g ω = fun z => d.fwd ω z + d.shift ω := fun ω => by
    funext z; simp [RetData.fwd]
  have hex : ∀ ω, ∃ y, Tendsto (d.g ω) (𝓝[d.D ω] (q' ω)) (𝓝 y) := fun ω => by
    by_cases hω : ω ∈ C
    · simp only [hq'def, hω, ↓reduceIte]
      obtain ⟨y, hy⟩ := (hspec ω hω).2
      rw [hfg ω]
      exact ⟨_, hy.add_const _⟩
    · simp only [hq'def, hω, ↓reduceIte]
      exact ⟨_, hd.tendsto_shift ω⟩
  set w : Ω → ℂ := fun ω => limUnder (𝓝[d.D ω] (q' ω)) (d.g ω) with hwdef
  have hw : Measurable w := measurable_of_tendsto_nhdsWithin hd.isOpen_D hd.measurableSet_mem_D
    hd.measurable_indicator_g hq' hq'D fun ω => tendsto_nhds_limUnder (hex ω)
  have heq : C.indicator (fun ω => chartPt (d.fwd ω) (d.D ω) (q ω)) =
      C.indicator fun ω => (w ω - d.shift ω).re := by
    refine Set.indicator_congr fun ω hω => ?_
    obtain ⟨hcl, y, hy⟩ := hspec ω hω
    have hNe : (𝓝[d.D ω] (q ω)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have hqω : q' ω = q ω := by simp only [hq'def, hω, ↓reduceIte]
    have hT' : Tendsto (d.g ω) (𝓝[d.D ω] (q ω)) (𝓝 (w ω)) := by
      show Tendsto (d.g ω) (𝓝[d.D ω] (q ω)) (𝓝 (limUnder (𝓝[d.D ω] (q' ω)) (d.g ω)))
      rw [hqω]
      exact tendsto_nhds_limUnder ⟨_, by rw [hfg ω]; exact hy.add_const _⟩
    rw [hfg ω] at hT'
    have h1 := tendsto_nhds_unique (hy.add_const (d.shift ω)) hT'
    have h2 : limUnder (𝓝[d.D ω] (q ω)) (d.fwd ω) = y := hy.limUnder_eq
    simp only [chartPt, h2, ← h1, add_sub_cancel_right]
  rw [heq]
  exact (Complex.measurable_re.comp (hw.sub hd.measurable_shift)).indicator hC

/-- On the chart event the chart has a limit at every regular point of the closure of the domain. -/
theorem exists_tendsto_fwd_of_regular (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {q : ℂ}
    (hq : q ∈ closure (d.D ω)) (hreg : IsChartRegularPoint (d.η₁ ω) d.u (d.η₂ ω) d.r q) :
    ∃ y, Tendsto (d.fwd ω) (𝓝[d.D ω] q) (𝓝 y) := by
  have h0₂ : (d.η₂ ω 0).im = 0 := (hd.good ω (RetData.E_subset_G hE)).2.2.2.2.2.1
  rw [hd.D_of_mem hE] at hq ⊢
  obtain ⟨y, -, hy, -⟩ := (hd.isRetChart hE).2.exists_tendsto_of_regular h0₂ hq hreg
  exact ⟨y, hy⟩

/-- The first tip is regular as soon as it is off the second prefix and not visited earlier. -/
theorem isChartRegularPoint_tip₁' {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} (hc₁ : ContinuousOn α (Icc 0 a))
    (hc₂ : ContinuousOn β (Icc 0 b)) (h0₁ : (α 0).im = 0) (h0₂ : (β 0).im = 0) (hq : α a ∉ β '' Icc 0 b)
    (hi : ∀ s < a, α s ≠ α a) : IsChartRegularPoint α a β b (α a) := by
  refine Or.inr (isUnboundedLinked_of_forall fun z hz hzq => ?_)
  rcases hz with ⟨s, hs, rfl⟩ | hz
  · have hsa : s < a := lt_of_le_of_ne hs.2 fun h => hzq (by rw [h])
    refine ⟨α '' Icc 0 s, fun x hx => Or.inl (image_mono (Icc_subset_Icc_right hsa.le) hx),
      isPreconnected_Icc.image _ (hc₁.mono (Icc_subset_Icc_right hsa.le)), ⟨s, right_mem_Icc.2 zero_le, rfl⟩,
      ?_, α 0, ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₁⟩
    rintro ⟨s', hs', he⟩
    exact hi s' (lt_of_le_of_lt hs'.2 hsa) he
  · exact ⟨β '' Icc 0 b, subset_union_right, isPreconnected_Icc.image _ hc₂, hz, hq, β 0,
      ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₂⟩

/-- The event on which a real point is off the retained union and adherent to the domain. -/
def ptEv (d : RetData Ω) (x : Ω → ℝ) : Set Ω :=
  d.E ∩ {ω | ((x ω : ℝ) : ℂ) ∈ closure (d.D ω)} ∩
    ({ω | ((x ω : ℝ) : ℂ) ∉ d.η₁ ω '' Icc 0 d.u} ∩ {ω | ((x ω : ℝ) : ℂ) ∉ d.η₂ ω '' Icc 0 d.r})

/-- The event on which the first tip is a regular point of the closure of the domain. -/
def tipEv (d : RetData Ω) : Set Ω :=
  d.E ∩ {ω | d.η₁ ω d.u ∈ closure (d.D ω)} ∩
    ({ω | d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r} ∩ {ω | ∀ s < d.u, d.η₁ ω s ≠ d.η₁ ω d.u})

theorem measurableSet_notMem_image (hd : d.IsMeasGood) {f : Ω → ℝ≥0 → ℂ} (hf : ∀ t, Measurable fun ω => f ω t)
    {c : ℝ≥0} (hcont : ∀ ω ∈ d.E, ContinuousOn (f ω) (Icc 0 c)) {q : Ω → ℂ} (hq : Measurable q) :
    MeasurableSet (d.E ∩ {ω | q ω ∉ f ω '' Icc 0 c}) := by
  have h := measurableSet_inter_exists_eq hd.measurableSet_E hf (f₂ := fun ω (_ : ℝ≥0) => q ω) (fun _ => hq)
    (c₁ := fun _ => c) (c₂ := fun _ => 0) measurable_const measurable_const
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact hcont ω hω) (fun _ _ => continuousOn_const)
  have heq : d.E ∩ {ω | q ω ∉ f ω '' Icc 0 c} =
      d.E \ (d.E ∩ {ω | ∃ s ≤ c, ∃ t ≤ (0 : ℝ≥0), f ω s = q ω}) := by
    ext ω
    constructor
    · rintro ⟨hω, hn⟩
      exact ⟨hω, fun ⟨_, s, hs, _, _, he⟩ => hn ⟨s, ⟨zero_le, hs⟩, he⟩⟩
    · rintro ⟨hω, hn⟩
      exact ⟨hω, fun ⟨s, hs, he⟩ => hn ⟨hω, s, hs.2, 0, le_rfl, he⟩⟩
  rw [heq]
  exact hd.measurableSet_E.diff h

theorem cont₁ (hd : d.IsMeasGood) : ∀ ω ∈ d.E, ContinuousOn (d.η₁ ω) (Icc 0 d.u) := fun ω hω =>
  (hd.good ω (RetData.E_subset_G hω)).1

theorem cont₂ (hd : d.IsMeasGood) : ∀ ω ∈ d.E, ContinuousOn (d.η₂ ω) (Icc 0 d.r) := fun ω hω =>
  (hd.good ω (RetData.E_subset_G hω)).2.1

theorem measurableSet_ptEv (hd : d.IsMeasGood) {x : Ω → ℝ} (hx : Measurable x) : MeasurableSet (ptEv d x) := by
  have hq : Measurable fun ω => ((x ω : ℝ) : ℂ) := Complex.measurable_ofReal.comp hx
  have h1 := measurableSet_notMem_image hd hd.meas₁ (cont₁ hd) hq
  have h2 := measurableSet_notMem_image hd hd.meas₂ (cont₂ hd) hq
  have hcl := measurableSet_mem_closure hd.isOpen_D hd.measurableSet_mem_D hq
  have heq : ptEv d x = (d.E ∩ {ω | ((x ω : ℝ) : ℂ) ∉ d.η₁ ω '' Icc 0 d.u}) ∩
      (d.E ∩ {ω | ((x ω : ℝ) : ℂ) ∉ d.η₂ ω '' Icc 0 d.r}) ∩ {ω | ((x ω : ℝ) : ℂ) ∈ closure (d.D ω)} := by
    ext ω
    simp only [ptEv, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [heq]
  exact (h1.inter h2).inter hcl

theorem measurableSet_tipEv (hd : d.IsMeasGood) : MeasurableSet (tipEv d) := by
  have hq : Measurable fun ω => d.η₁ ω d.u := hd.meas₁ d.u
  have h1 := measurableSet_notMem_image hd hd.meas₂ (cont₂ hd) hq
  have hcl := measurableSet_mem_closure hd.isOpen_D hd.measurableSet_mem_D hq
  -- not visited before `u`: a countable union over rational times
  have hvis : MeasurableSet (d.E ∩ {ω | ∃ s < d.u, d.η₁ ω s = d.η₁ ω d.u}) := by
    have heq : d.E ∩ {ω | ∃ s < d.u, d.η₁ ω s = d.η₁ ω d.u} = ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < d.u),
        d.E ∩ {ω | ∃ s ≤ (q : ℝ).toNNReal, ∃ t ≤ (0 : ℝ≥0), d.η₁ ω s = d.η₁ ω d.u} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hω, s, hs, he⟩
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (s : ℝ) < d.u from hs)
        have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg s).trans hq1.le
        exact ⟨q, ⟨hq0, hq2⟩, hω, s, (Real.le_toNNReal_iff_coe_le hq0).2 hq1.le, 0, le_rfl, he⟩
      · rintro ⟨q, ⟨hq0, hq⟩, hω, s, hs, -, -, he⟩
        refine ⟨hω, s, ?_, he⟩
        have : (s : ℝ) ≤ q := (Real.le_toNNReal_iff_coe_le hq0).1 hs
        exact_mod_cast lt_of_le_of_lt this hq
    rw [heq]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
    have hqu : (q : ℝ).toNNReal ≤ d.u := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq.1]; exact hq.2.le
    exact measurableSet_inter_exists_eq hd.measurableSet_E hd.meas₁ (f₂ := fun ω (_ : ℝ≥0) => d.η₁ ω d.u)
      (fun _ => hd.meas₁ d.u) (c₁ := fun _ => (q : ℝ).toNNReal) (c₂ := fun _ => 0) measurable_const
      measurable_const (fun ω hω => by
        rw [← Icc_zero_eq_Iic]
        exact (cont₁ hd ω hω).mono (Icc_subset_Icc_right hqu))
      (fun _ _ => continuousOn_const)
  have heq : tipEv d = (d.E ∩ {ω | d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r}) ∩
      (d.E \ (d.E ∩ {ω | ∃ s < d.u, d.η₁ ω s = d.η₁ ω d.u})) ∩ {ω | d.η₁ ω d.u ∈ closure (d.D ω)} := by
    ext ω
    simp only [tipEv, mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, not_and, not_exists]
    constructor
    · rintro ⟨⟨hω, hcl⟩, hβ, hne⟩
      exact ⟨⟨⟨hω, hβ⟩, hω, fun _ s hs he => hne s hs he⟩, hcl⟩
    · rintro ⟨⟨⟨hω, hβ⟩, -, hne⟩, hcl⟩
      exact ⟨⟨hω, hcl⟩, hβ, fun s hs he => hne hω s hs he⟩
  rw [heq]
  exact (h1.inter (hd.measurableSet_E.diff hvis)).inter hcl

theorem h0₁E (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) : (d.η₁ ω 0).im = 0 :=
  (hd.good ω (RetData.E_subset_G hω)).2.2.2.2.1

theorem h0₂E (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) : (d.η₂ ω 0).im = 0 :=
  (hd.good ω (RetData.E_subset_G hω)).2.2.2.2.2.1

theorem ptEv_spec (hd : d.IsMeasGood) {x : Ω → ℝ} {ω : Ω} (hω : ω ∈ ptEv d x) :
    ((x ω : ℝ) : ℂ) ∈ closure (d.D ω) ∧ ∃ y, Tendsto (d.fwd ω) (𝓝[d.D ω] ((x ω : ℝ) : ℂ)) (𝓝 y) := by
  obtain ⟨⟨hE, hcl⟩, h1, h2⟩ := hω
  refine ⟨hcl, exists_tendsto_fwd_of_regular hd hE hcl ?_⟩
  exact isChartRegularPoint_of_notMem (cont₁ hd ω hE) (cont₂ hd ω hE) (h0₁E hd hE) (h0₂E hd hE)
    (fun h => h.elim h1 h2)

theorem tipEv_spec (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ tipEv d) :
    d.η₁ ω d.u ∈ closure (d.D ω) ∧ ∃ y, Tendsto (d.fwd ω) (𝓝[d.D ω] (d.η₁ ω d.u)) (𝓝 y) := by
  obtain ⟨⟨hE, hcl⟩, h1, h2⟩ := hω
  exact ⟨hcl, exists_tendsto_fwd_of_regular hd hE hcl (isChartRegularPoint_tip₁' (cont₁ hd ω hE) (cont₂ hd ω hE)
    (h0₁E hd hE) (h0₂E hd hE) h1 h2)⟩

/-! ### The bases -/

theorem isCompact_realSet' {γ : ℝ≥0 → ℂ} {c : ℝ≥0} (hγ : ContinuousOn γ (Icc 0 c)) : IsCompact (realSet γ c) :=
  Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage (isCompact_Icc.image_of_continuousOn hγ)

theorem re_zero_mem_realSet {γ : ℝ≥0 → ℂ} {c : ℝ≥0} (h0 : (γ 0).im = 0) : (γ 0).re ∈ realSet γ c :=
  ⟨0, ⟨le_rfl, zero_le⟩, (Restart.ofReal_re_eq h0).symm⟩

theorem baseL_le_iff {γ : ℝ≥0 → ℂ} {c : ℝ≥0} (hγ : ContinuousOn γ (Icc 0 c)) (h0 : (γ 0).im = 0) (t : ℝ) :
    baseL γ c ≤ t ↔ ∃ s ≤ c, γ s ∈ {z : ℂ | z.im = 0 ∧ z.re ≤ t} := by
  have hK := isCompact_realSet' hγ
  have hne : (realSet γ c).Nonempty := ⟨_, re_zero_mem_realSet h0⟩
  constructor
  · intro h
    obtain ⟨s, hs, he⟩ := hK.sInf_mem hne
    refine ⟨s, hs.2, ?_⟩
    rw [he]
    refine ⟨by simp, ?_⟩
    simp only [ofReal_re]
    exact h
  · rintro ⟨s, hs, him, hre⟩
    have hm : (γ s).re ∈ realSet γ c := ⟨s, ⟨zero_le, hs⟩, (Restart.ofReal_re_eq him).symm⟩
    exact (csInf_le hK.isBounded.bddBelow hm).trans hre

theorem le_baseR_iff {γ : ℝ≥0 → ℂ} {c : ℝ≥0} (hγ : ContinuousOn γ (Icc 0 c)) (h0 : (γ 0).im = 0) (t : ℝ) :
    t ≤ baseR γ c ↔ ∃ s ≤ c, γ s ∈ {z : ℂ | z.im = 0 ∧ t ≤ z.re} := by
  have hK := isCompact_realSet' hγ
  have hne : (realSet γ c).Nonempty := ⟨_, re_zero_mem_realSet h0⟩
  constructor
  · intro h
    obtain ⟨s, hs, he⟩ := hK.sSup_mem hne
    refine ⟨s, hs.2, ?_⟩
    rw [he]
    refine ⟨by simp, ?_⟩
    simp only [ofReal_re]
    exact h
  · rintro ⟨s, hs, him, hre⟩
    have hm : (γ s).re ∈ realSet γ c := ⟨s, ⟨zero_le, hs⟩, (Restart.ofReal_re_eq him).symm⟩
    exact hre.trans (le_csSup hK.isBounded.bddAbove hm)

theorem measurable_indicator_baseL (hd : d.IsMeasGood) {f : Ω → ℝ≥0 → ℂ} (hf : ∀ t, Measurable fun ω => f ω t)
    {c : ℝ≥0} (hcont : ∀ ω ∈ d.E, ContinuousOn (f ω) (Icc 0 c)) (h0 : ∀ ω ∈ d.E, (f ω 0).im = 0) :
    Measurable (d.E.indicator fun ω => baseL (f ω) c) := by
  refine measurable_of_Iic fun t => ?_
  have hQ : IsClosed {z : ℂ | z.im = 0 ∧ z.re ≤ t} :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_re continuous_const)
  have hQne : ({z : ℂ | z.im = 0 ∧ z.re ≤ t} : Set ℂ).Nonempty := ⟨(t : ℂ), by simp⟩
  have h := measurableSet_inter_exists_mem hd.measurableSet_E hf (c := fun _ => c) measurable_const
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact hcont ω hω) hQ hQne
  have heq : d.E.indicator (fun ω => baseL (f ω) c) ⁻¹' Iic t =
      (d.E ∩ {ω | ∃ s ≤ c, f ω s ∈ {z : ℂ | z.im = 0 ∧ z.re ≤ t}}) ∪ (d.Eᶜ ∩ {_ω | (0 : ℝ) ≤ t}) := by
    ext ω
    by_cases hω : ω ∈ d.E
    · simp only [mem_preimage, mem_Iic, indicator_of_mem hω, mem_union, mem_inter_iff, mem_ofPred_eq, hω,
        true_and, mem_compl_iff, not_true_eq_false, false_and, or_false]
      exact baseL_le_iff (hcont ω hω) (h0 ω hω) t
    · simp only [mem_preimage, mem_Iic, indicator_of_notMem hω, mem_union, mem_inter_iff, mem_ofPred_eq, hω,
        false_and, mem_compl_iff, not_false_eq_true, true_and, false_or]
  rw [heq]
  exact h.union (hd.measurableSet_E.compl.inter (MeasurableSet.const _))

theorem measurable_indicator_baseR (hd : d.IsMeasGood) {f : Ω → ℝ≥0 → ℂ} (hf : ∀ t, Measurable fun ω => f ω t)
    {c : ℝ≥0} (hcont : ∀ ω ∈ d.E, ContinuousOn (f ω) (Icc 0 c)) (h0 : ∀ ω ∈ d.E, (f ω 0).im = 0) :
    Measurable (d.E.indicator fun ω => baseR (f ω) c) := by
  refine measurable_of_Ici fun t => ?_
  have hQ : IsClosed {z : ℂ | z.im = 0 ∧ t ≤ z.re} :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_const continuous_re)
  have hQne : ({z : ℂ | z.im = 0 ∧ t ≤ z.re} : Set ℂ).Nonempty := ⟨(t : ℂ), by simp⟩
  have h := measurableSet_inter_exists_mem hd.measurableSet_E hf (c := fun _ => c) measurable_const
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact hcont ω hω) hQ hQne
  have heq : d.E.indicator (fun ω => baseR (f ω) c) ⁻¹' Ici t =
      (d.E ∩ {ω | ∃ s ≤ c, f ω s ∈ {z : ℂ | z.im = 0 ∧ t ≤ z.re}}) ∪ (d.Eᶜ ∩ {_ω | t ≤ (0 : ℝ)}) := by
    ext ω
    by_cases hω : ω ∈ d.E
    · simp only [mem_preimage, mem_Ici, indicator_of_mem hω, mem_union, mem_inter_iff, mem_ofPred_eq, hω,
        true_and, mem_compl_iff, not_true_eq_false, false_and, or_false]
      exact le_baseR_iff (hcont ω hω) (h0 ω hω) t
    · simp only [mem_preimage, mem_Ici, indicator_of_notMem hω, mem_union, mem_inter_iff, mem_ofPred_eq, hω,
        false_and, mem_compl_iff, not_false_eq_true, true_and, false_or]
  rw [heq]
  exact h.union (hd.measurableSet_E.compl.inter (MeasurableSet.const _))

end ChartPt

/-! ### The measurable word -/

section Word

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

/-- The left end of the second base (on the chart event). -/
def A₂ (d : RetData Ω) (ω : Ω) : ℝ := d.E.indicator (fun ω => baseL (d.η₂ ω) d.r) ω

/-- The right end of the second base (on the chart event). -/
def B₂ (d : RetData Ω) (ω : Ω) : ℝ := d.E.indicator (fun ω => baseR (d.η₂ ω) d.r) ω

/-- The left end of the first base (on the chart event). -/
def A₁ (d : RetData Ω) (ω : Ω) : ℝ := d.E.indicator (fun ω => baseL (d.η₁ ω) d.u) ω

/-- The right end of the first base (on the chart event). -/
def B₁ (d : RetData Ω) (ω : Ω) : ℝ := d.E.indicator (fun ω => baseR (d.η₁ ω) d.u) ω

/-- The chart point of a real point, on the event where it is a regular point of the closure of the domain. -/
def Tpt (d : RetData Ω) (x : Ω → ℝ) (ω : Ω) : ℝ :=
  (ptEv d x).indicator (fun ω => chartPt (d.fwd ω) (d.D ω) ((x ω : ℝ) : ℂ)) ω

/-- **The measurable boundary word of a disjoint pair**: the word builder with every input read on its event. -/
def wordM (d : RetData Ω) (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) (ω : Ω) : BoundaryWord :=
  zbuild c₀ g₁ g₂ g₃ g₄ (cntLt c₀ (A₂ d ω)) (cntLe c₀ (B₂ d ω)) (cntLt c₀ (A₁ d ω)) (cntLe c₀ (B₁ d ω))
    (fun i => Tpt d (fun _ => c₀.2.1 i) ω)
    (⨆ n : ℕ, Tpt d (fun ω => A₂ d ω - 1 / ((n : ℝ) + 1)) ω)
    (⨅ n : ℕ, Tpt d (fun ω => B₂ d ω + (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) ω)
    (⨆ n : ℕ, Tpt d (fun ω => A₁ d ω - (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) ω)
    ((tipEv d).indicator (fun ω => chartPt (d.fwd ω) (d.D ω) (d.η₁ ω d.u)) ω)
    (⨅ n : ℕ, Tpt d (fun ω => B₁ d ω + 1 / ((n : ℝ) + 1)) ω)

theorem measurable_cntLt (c₀ : BoundaryWord) : Measurable (cntLt c₀) := by
  classical
  have e : cntLt c₀ = fun A => ∑ i ∈ Finset.range c₀.1, if c₀.2.1 i < A then 1 else 0 := by
    funext A; unfold cntLt; rw [Finset.card_filter]
  rw [e]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const

theorem measurable_cntLe (c₀ : BoundaryWord) : Measurable (cntLe c₀) := by
  classical
  have e : cntLe c₀ = fun A => ∑ i ∈ Finset.range c₀.1, if c₀.2.1 i ≤ A then 1 else 0 := by
    funext A; unfold cntLe; rw [Finset.card_filter]
  rw [e]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

variable (hd : d.IsMeasGood)
include hd

theorem measurable_A₂ : Measurable (A₂ d) := measurable_indicator_baseL hd hd.meas₂ (cont₂ hd) fun _ h => h0₂E hd h

theorem measurable_B₂ : Measurable (B₂ d) := measurable_indicator_baseR hd hd.meas₂ (cont₂ hd) fun _ h => h0₂E hd h

theorem measurable_A₁ : Measurable (A₁ d) := measurable_indicator_baseL hd hd.meas₁ (cont₁ hd) fun _ h => h0₁E hd h

theorem measurable_B₁ : Measurable (B₁ d) := measurable_indicator_baseR hd hd.meas₁ (cont₁ hd) fun _ h => h0₁E hd h

theorem measurable_Tpt {x : Ω → ℝ} (hx : Measurable x) : Measurable (Tpt d x) :=
  measurable_indicator_chartPt hd (measurableSet_ptEv hd hx) (Complex.measurable_ofReal.comp hx)
    fun _ hω => ptEv_spec hd hω

/-- **The measurable word is measurable.** -/
theorem measurable_wordM (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) : Measurable (wordM d c₀ g₁ g₂ g₃ g₄) := by
  have hK : Measurable fun ω => (cntLt c₀ (A₂ d ω), cntLe c₀ (B₂ d ω), cntLt c₀ (A₁ d ω), cntLe c₀ (B₁ d ω)) :=
    ((measurable_cntLt c₀).comp (measurable_A₂ hd)).prodMk (((measurable_cntLe c₀).comp (measurable_B₂ hd)).prodMk
      (((measurable_cntLt c₀).comp (measurable_A₁ hd)).prodMk ((measurable_cntLe c₀).comp (measurable_B₁ hd))))
  have hTp : ∀ i, Measurable (Tpt d (fun _ => c₀.2.1 i)) := fun i => measurable_Tpt hd measurable_const
  have hL₂ : Measurable fun ω => ⨆ n : ℕ, Tpt d (fun ω => A₂ d ω - 1 / ((n : ℝ) + 1)) ω :=
    Measurable.iSup fun n => measurable_Tpt hd ((measurable_A₂ hd).sub_const _)
  have hR₂ : Measurable fun ω => ⨅ n : ℕ, Tpt d (fun ω => B₂ d ω + (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) ω :=
    Measurable.iInf fun n => measurable_Tpt hd ((measurable_B₂ hd).add
      (((measurable_A₁ hd).sub (measurable_B₂ hd)).div_const _))
  have hL₁ : Measurable fun ω => ⨆ n : ℕ, Tpt d (fun ω => A₁ d ω - (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) ω :=
    Measurable.iSup fun n => measurable_Tpt hd ((measurable_A₁ hd).sub
      (((measurable_A₁ hd).sub (measurable_B₂ hd)).div_const _))
  have hM₁ : Measurable ((tipEv d).indicator fun ω => chartPt (d.fwd ω) (d.D ω) (d.η₁ ω d.u)) :=
    measurable_indicator_chartPt hd (measurableSet_tipEv hd) (hd.meas₁ d.u) fun _ hω => tipEv_spec hd hω
  have hR₁ : Measurable fun ω => ⨅ n : ℕ, Tpt d (fun ω => B₁ d ω + 1 / ((n : ℝ) + 1)) ω :=
    Measurable.iInf fun n => measurable_Tpt hd ((measurable_B₁ hd).add_const _)
  -- the three components
  have h1 : Measurable fun ω => (wordM d c₀ g₁ g₂ g₃ g₄ ω).1 :=
    (measurable_of_countable fun k : ℕ × ℕ × ℕ × ℕ => k.1 + 3 + (k.2.2.1 - k.2.1) + 3 + (c₀.1 - k.2.2.2)).comp hK
  have h2 : Measurable fun ω => (wordM d c₀ g₁ g₂ g₃ g₄ ω).2.1 := by
    refine measurable_pi_iff.2 fun i => ?_
    have hF : Measurable fun p : Ω × (ℕ × ℕ × ℕ × ℕ) =>
        (zbuild c₀ g₁ g₂ g₃ g₄ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 (fun j => Tpt d (fun _ => c₀.2.1 j) p.1)
          (⨆ n : ℕ, Tpt d (fun ω => A₂ d ω - 1 / ((n : ℝ) + 1)) p.1)
          (⨅ n : ℕ, Tpt d (fun ω => B₂ d ω + (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) p.1)
          (⨆ n : ℕ, Tpt d (fun ω => A₁ d ω - (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) p.1)
          ((tipEv d).indicator (fun ω => chartPt (d.fwd ω) (d.D ω) (d.η₁ ω d.u)) p.1)
          (⨅ n : ℕ, Tpt d (fun ω => B₁ d ω + 1 / ((n : ℝ) + 1)) p.1)).2.1 i :=
      measurable_from_prod_countable_left fun k =>
        measurable_zbuild_pos c₀ g₁ g₂ g₃ g₄ k.1 k.2.1 k.2.2.1 k.2.2.2 hTp hL₂ hR₂ hL₁ hM₁ hR₁ i
    exact hF.comp (measurable_id.prodMk hK)
  have h3 : Measurable fun ω => (wordM d c₀ g₁ g₂ g₃ g₄ ω).2.2 := by
    refine measurable_pi_iff.2 fun j => ?_
    exact (measurable_of_countable fun k : ℕ × ℕ × ℕ × ℕ =>
      (zbuild c₀ g₁ g₂ g₃ g₄ k.1 k.2.1 k.2.2.1 k.2.2.2 (fun _ => 0) 0 0 0 0 0).2.2 j).comp hK
  exact h1.prodMk (h2.prodMk h3)

end Word

end Lemma76G

end Sec7

end InteractingSLE
