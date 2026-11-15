/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7RetainedChart

/-!
# Lemma G7: the measurable retained chart and chart field at deterministic cutoffs

Packet PROVE-G7. The retained-pair analogue of CPL4's measurable first-contact chart (`Restart.PairData`,
`Spec/Restart/ChartMeas.lean`). Data (`RetData`): two random paths `η₁, η₂`, deterministic own cutoffs `u, r` and a
measurable event `G` on which the paths are continuous on `[0, u]`, `[0, r]`, lie in `ℍ̄`, start on `ℝ`, and `η₂` does
not visit its tip `η₂(r)` before `r`. On the measurable **chart event**

  `E = G ∩ {η₂(r) ∈ ℍ} ∩ {η₂(r) ∉ η₁([0, u])} ∩ {η₂(r) ∈ closure D}`,  `D = activeDomain η₁ u η₂ r`,

the retained union `K = η₁([0, u]) ∪ η₂([0, r])` (`∅` off the first three events), the domain `D = ℍ \ fill K`, the
mapping-out function `g`, the forward limit `x₀` of `g` at the tip, the canonical lift `Im log g′` and a pathwise choice
of the inverse give the retained chart (`RetData.chart`, `Chart.id` off `E`), which is an `IsRetChart` on `E`
(`exists_retChart`), and the chart field `Hc = chartTransport chart 1 0 χ h` is measurable
(`RetData.IsMeasGood.measurable_chartField`) with `IsChartTransport` at every `ω`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp7

open Restart

/-- The pathwise hypotheses of the retained chart at deterministic cutoffs `(u, r)`. -/
def IsRetGood (η₁ : ℝ≥0 → ℂ) (u : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (r : ℝ≥0) : Prop :=
  ContinuousOn η₁ (Icc 0 u) ∧ ContinuousOn η₂ (Icc 0 r) ∧ MapsTo η₁ (Icc 0 u) Hbar ∧ MapsTo η₂ (Icc 0 r) Hbar ∧
    (η₁ 0).im = 0 ∧ (η₂ 0).im = 0 ∧ ∀ t < r, η₂ t ≠ η₂ r

/-- Two random paths with deterministic own cutoffs and a good event. -/
structure RetData (Ω : Type*) where
  /-- The good event. -/
  G : Set Ω
  /-- The first path. -/
  η₁ : Ω → ℝ≥0 → ℂ
  /-- The second path. -/
  η₂ : Ω → ℝ≥0 → ℂ
  /-- The first cutoff. -/
  u : ℝ≥0
  /-- The second cutoff. -/
  r : ℝ≥0

namespace RetData

variable {Ω : Type*} [MeasurableSpace Ω] (d : RetData Ω)

/-- The measurability hypotheses, and the pathwise ones on `G`. -/
structure IsMeasGood : Prop where
  measurableSet_G : MeasurableSet d.G
  meas₁ : ∀ t, Measurable fun ω => d.η₁ ω t
  meas₂ : ∀ t, Measurable fun ω => d.η₂ ω t
  good : ∀ ω ∈ d.G, IsRetGood (d.η₁ ω) d.u (d.η₂ ω) d.r

/-- The event on which the retained union is recorded: `G`, the second tip interior and off the first prefix. -/
def E₀ : Set Ω := d.G ∩ {ω | d.η₂ ω d.r ∈ H} ∩ {ω | d.η₂ ω d.r ∉ d.η₁ ω '' Icc 0 d.u}

open scoped Classical in
/-- The random compact set `η₁[0, u] ∪ η₂[0, r]` on an event `F` (`∅` off `F`). -/
def KOf (F : Set Ω) (ω : Ω) : Set ℂ := if ω ∈ F then prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r else ∅

/-- The random domain `ℍ \ fill(K)` on an event `F` (`ℍ` off `F`). -/
def DOf (F : Set Ω) (ω : Ω) : Set ℂ := H \ fillH (d.KOf F ω)

/-- **The chart event**: `E₀` and the second tip adherent to the active domain (joint activity of the tip). -/
def E : Set Ω := d.E₀ ∩ {ω | d.η₂ ω d.r ∈ closure (d.DOf d.E₀ ω)}

/-- The random compact set `η₁[0, u] ∪ η₂[0, r]` (`∅` off `E`). -/
def K (ω : Ω) : Set ℂ := d.KOf d.E ω

/-- The random domain `ℍ \ fill(K)` (`ℍ` off `E`). -/
def D (ω : Ω) : Set ℂ := d.DOf d.E ω

/-- The canonical mapping-out function of the filled union. -/
def g (ω : Ω) : ℂ → ℂ := ConformalImage.mapOut (fillH (d.K ω))

open scoped Classical in
/-- The tip `η₂(r)` (`i` off `E`). -/
def p (ω : Ω) : ℂ := if ω ∈ d.E then d.η₂ ω d.r else I

/-- The forward limit of `g` at the tip along the domain. -/
def shift (ω : Ω) : ℂ := limUnder (𝓝[d.D ω] (d.p ω)) (d.g ω)

/-- The canonical lift: the imaginary part of the canonical logarithm of `g′`. -/
def lift (ω : Ω) : ℂ → ℝ := fun z => (canonDerivLog (fillH (d.K ω)) z).im

/-- The forward chart map `φ = g − x₀`. -/
def fwd (ω : Ω) : ℂ → ℂ := fun z => d.g ω z - d.shift ω

open scoped Classical in
/-- A pathwise choice of the chart inverse (`id` if there is none). -/
def inv (ω : Ω) : ℂ → ℂ :=
  if h : ∃ ψ, IsRetChart (d.η₁ ω) d.u (d.η₂ ω) d.r (d.fwd ω) ψ (d.lift ω) then h.choose else id

open scoped Classical in
/-- **The retained chart** (`Chart.id` off `E`). -/
def chart (ω : Ω) : Chart := if ω ∈ d.E then (d.fwd ω, d.inv ω, d.lift ω) else Chart.id

variable {d}

omit [MeasurableSpace Ω] in
theorem KOf_of_mem {F : Set Ω} {ω : Ω} (hω : ω ∈ F) : d.KOf F ω = prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := by
  simp [KOf, hω]

omit [MeasurableSpace Ω] in
theorem KOf_of_notMem {F : Set Ω} {ω : Ω} (hω : ω ∉ F) : d.KOf F ω = ∅ := by
  simp [KOf, hω]

omit [MeasurableSpace Ω] in
theorem K_of_mem {ω : Ω} (hω : ω ∈ d.E) : d.K ω = prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := KOf_of_mem hω

omit [MeasurableSpace Ω] in
theorem K_of_notMem {ω : Ω} (hω : ω ∉ d.E) : d.K ω = ∅ := KOf_of_notMem hω

omit [MeasurableSpace Ω] in
theorem E₀_subset_G : d.E₀ ⊆ d.G := fun _ h => h.1.1

omit [MeasurableSpace Ω] in
theorem E_subset_E₀ : d.E ⊆ d.E₀ := inter_subset_left

/-! ### Measurability of the recorded union -/

theorem IsMeasGood.measurableSet_E₀ (hd : d.IsMeasGood) : MeasurableSet d.E₀ := by
  have h1 : MeasurableSet (d.G ∩ {ω | d.η₂ ω d.r ∈ H}) :=
    hd.measurableSet_G.inter (measurableSet_lt measurable_const (Complex.measurable_im.comp (hd.meas₂ d.r)))
  have h2 := measurableSet_inter_exists_eq h1 hd.meas₁ (f₂ := fun ω (_ : ℝ≥0) => d.η₂ ω d.r)
    (fun _ => hd.meas₂ d.r) (c₁ := fun _ => d.u) (c₂ := fun _ => 0) measurable_const measurable_const
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hd.good ω hω.1).1) (fun _ _ => continuousOn_const)
  have heq : d.E₀ = (d.G ∩ {ω | d.η₂ ω d.r ∈ H}) \
      ((d.G ∩ {ω | d.η₂ ω d.r ∈ H}) ∩ {ω | ∃ s ≤ d.u, ∃ t ≤ (0 : ℝ≥0), d.η₁ ω s = d.η₂ ω d.r}) := by
    ext ω
    constructor
    · rintro ⟨⟨hG, hH⟩, hn⟩
      refine ⟨⟨hG, hH⟩, fun hc => ?_⟩
      obtain ⟨s, hs, t, -, he⟩ := hc.2
      exact hn ⟨s, ⟨zero_le, hs⟩, he⟩
    · rintro ⟨⟨hG, hH⟩, hn⟩
      refine ⟨⟨hG, hH⟩, fun ⟨s, hs, he⟩ => hn ⟨⟨hG, hH⟩, s, hs.2, 0, le_rfl, he⟩⟩
  rw [heq]
  exact h1.diff h2

theorem IsMeasGood.isCompact_KOf (hd : d.IsMeasGood) {F : Set Ω} (hFG : F ⊆ d.G) (ω : Ω) :
    IsCompact (d.KOf F ω) := by
  by_cases hω : ω ∈ F
  · rw [KOf_of_mem hω, prefixSet]
    have hg := hd.good ω (hFG hω)
    exact (isCompact_Icc.image_of_continuousOn hg.1).union (isCompact_Icc.image_of_continuousOn hg.2.1)
  · rw [KOf_of_notMem hω]; exact isCompact_empty

theorem IsMeasGood.isPreconnected_KOf (hd : d.IsMeasGood) {F : Set Ω} (hFG : F ⊆ d.G) (ω : Ω) :
    IsPreconnected (d.KOf F ω ∪ lowerHalf) := by
  by_cases hω : ω ∈ F
  · rw [KOf_of_mem hω, prefixSet]
    have hg := hd.good ω (hFG hω)
    have h1 : IsPreconnected (d.η₁ ω '' Icc 0 d.u) := isPreconnected_Icc.image _ hg.1
    have h2 : IsPreconnected (d.η₂ ω '' Icc 0 d.r) := isPreconnected_Icc.image _ hg.2.1
    have hL : IsPreconnected lowerHalf :=
      (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
    have m1 : d.η₁ ω 0 ∈ lowerHalf := show (d.η₁ ω 0).im ≤ 0 by rw [hg.2.2.2.2.1]
    have m2 : d.η₂ ω 0 ∈ lowerHalf := show (d.η₂ ω 0).im ≤ 0 by rw [hg.2.2.2.2.2.1]
    have h3 : IsPreconnected (d.η₁ ω '' Icc 0 d.u ∪ lowerHalf) :=
      h1.union (d.η₁ ω 0) (mem_image_of_mem (d.η₁ ω) (left_mem_Icc.2 zero_le)) m1 hL
    have h4 := h3.union (d.η₂ ω 0) (Or.inr m2) (mem_image_of_mem (d.η₂ ω) (left_mem_Icc.2 zero_le)) h2
    rwa [show d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r ∪ lowerHalf =
      d.η₁ ω '' Icc 0 d.u ∪ lowerHalf ∪ d.η₂ ω '' Icc 0 d.r from union_right_comm _ _ _]
  · rw [KOf_of_notMem hω, empty_union]
    exact (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected

theorem IsMeasGood.isDyadicHitMeasurable_KOf (hd : d.IsMeasGood) {F : Set Ω} (hF : MeasurableSet F)
    (hFG : F ⊆ d.G) : IsDyadicHitMeasurable (d.KOf F) := by
  intro n k
  set Q := dyadicSquare n k
  have hQ : IsClosed Q := isClosed_dyadicSquare n k
  have hQne : Q.Nonempty := PairData.dyadicSquare_nonempty n k
  have heq : {ω | (Q ∩ d.KOf F ω).Nonempty} =
      (F ∩ {ω | ∃ s ≤ d.u, d.η₁ ω s ∈ Q}) ∪ (F ∩ {ω | ∃ t ≤ d.r, d.η₂ ω t ∈ Q}) := by
    ext ω
    by_cases hω : ω ∈ F
    · simp only [mem_ofPred_eq, mem_union, mem_inter_iff, hω, true_and, KOf_of_mem hω, prefixSet]
      constructor
      · rintro ⟨z, hzQ, ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩⟩
        · exact Or.inl ⟨s, hs.2, hzQ⟩
        · exact Or.inr ⟨t, ht.2, hzQ⟩
      · rintro (⟨s, hs, hsQ⟩ | ⟨t, ht, htQ⟩)
        · exact ⟨_, hsQ, Or.inl ⟨s, ⟨zero_le, hs⟩, rfl⟩⟩
        · exact ⟨_, htQ, Or.inr ⟨t, ⟨zero_le, ht⟩, rfl⟩⟩
    · simp [KOf_of_notMem hω, hω]
  rw [heq]
  exact (measurableSet_inter_exists_mem hF hd.meas₁ (c := fun _ => d.u) measurable_const
      (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hd.good ω (hFG hω)).1) hQ hQne).union
    (measurableSet_inter_exists_mem hF hd.meas₂ (c := fun _ => d.r) measurable_const
      (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hd.good ω (hFG hω)).2.1) hQ hQne)

theorem IsMeasGood.isOpen_DOf (hd : d.IsMeasGood) {F : Set Ω} (hFG : F ⊆ d.G) (ω : Ω) : IsOpen (d.DOf F ω) :=
  (isHPHull_fillH_of_compact (hd.isCompact_KOf hFG ω) (hd.isPreconnected_KOf hFG ω)).isOpen

theorem IsMeasGood.measurableSet_mem_DOf (hd : d.IsMeasGood) {F : Set Ω} (hF : MeasurableSet F)
    (hFG : F ⊆ d.G) (z : ℂ) : MeasurableSet {ω | z ∈ d.DOf F ω} :=
  measurableSet_mem_H_diff_fillH (hd.isDyadicHitMeasurable_KOf hF hFG) (hd.isCompact_KOf hFG) z

theorem IsMeasGood.DOf_of_mem (hd : d.IsMeasGood) {F : Set Ω} (hFG : F ⊆ d.G) {ω : Ω} (hω : ω ∈ F) :
    d.DOf F ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := by
  have hc := hd.isCompact_KOf hFG ω
  rw [KOf_of_mem hω] at hc
  rw [DOf, KOf_of_mem hω, activeDomain_eq hc.isClosed]

omit [MeasurableSpace Ω] in
theorem DOf_of_notMem {F : Set Ω} {ω : Ω} (hω : ω ∉ F) : d.DOf F ω = H := by
  rw [DOf, KOf_of_notMem hω, YuanCharacterisation.fillH_eq_empty_of_subset (empty_subset _), sdiff_empty]

/-- **The chart event is measurable**: adherence of the tip to the random open domain is a countable condition. -/
theorem IsMeasGood.measurableSet_E (hd : d.IsMeasGood) : MeasurableSet d.E := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hiff : ∀ ω, d.η₂ ω d.r ∈ closure (d.DOf d.E₀ ω) ↔
      ∀ m : ℕ, ∃ j : ℕ, e j ∈ d.DOf d.E₀ ω ∧ dist (e j) (d.η₂ ω d.r) < 1 / ((m : ℝ) + 1) := by
    intro ω
    constructor
    · intro hc m
      have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      obtain ⟨y, hyD, hyq⟩ := Metric.mem_closure_iff.1 hc _ hr
      obtain ⟨j, hj⟩ := he.exists_mem_open ((hd.isOpen_DOf E₀_subset_G ω).inter isOpen_ball)
        ⟨y, hyD, mem_ball.2 (by rw [dist_comm]; exact hyq)⟩
      exact ⟨j, hj.1, mem_ball.1 hj.2⟩
    · intro h
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨j, hjD, hjd⟩ := h m
      exact ⟨e j, hjD, by rw [dist_comm]; exact hjd.trans hm⟩
  have heq : {ω | d.η₂ ω d.r ∈ closure (d.DOf d.E₀ ω)} =
      ⋂ m : ℕ, ⋃ j : ℕ, ({ω | e j ∈ d.DOf d.E₀ ω} ∩ {ω | dist (e j) (d.η₂ ω d.r) < 1 / ((m : ℝ) + 1)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
    exact hiff ω
  refine hd.measurableSet_E₀.inter ?_
  rw [heq]
  exact MeasurableSet.iInter fun m => MeasurableSet.iUnion fun j =>
    (hd.measurableSet_mem_DOf hd.measurableSet_E₀ E₀_subset_G (e j)).inter
      (measurableSet_lt (measurable_const.dist (hd.meas₂ d.r)) measurable_const)

omit [MeasurableSpace Ω] in
theorem E_subset_G : d.E ⊆ d.G := fun _ h => h.1.1.1

theorem IsMeasGood.isCompact_K (hd : d.IsMeasGood) (ω : Ω) : IsCompact (d.K ω) := hd.isCompact_KOf E_subset_G ω

theorem IsMeasGood.isPreconnected_K (hd : d.IsMeasGood) (ω : Ω) : IsPreconnected (d.K ω ∪ lowerHalf) :=
  hd.isPreconnected_KOf E_subset_G ω

theorem IsMeasGood.isDyadicHitMeasurable (hd : d.IsMeasGood) : IsDyadicHitMeasurable d.K :=
  hd.isDyadicHitMeasurable_KOf hd.measurableSet_E E_subset_G

theorem IsMeasGood.isHPHull (hd : d.IsMeasGood) (ω : Ω) : IsHPHull (fillH (d.K ω)) :=
  isHPHull_fillH_of_compact (hd.isCompact_K ω) (hd.isPreconnected_K ω)

theorem IsMeasGood.isOpen_D (hd : d.IsMeasGood) (ω : Ω) : IsOpen (d.D ω) := hd.isOpen_DOf E_subset_G ω

theorem IsMeasGood.measurableSet_mem_D (hd : d.IsMeasGood) (z : ℂ) : MeasurableSet {ω | z ∈ d.D ω} :=
  hd.measurableSet_mem_DOf hd.measurableSet_E E_subset_G z

theorem IsMeasGood.measurable_indicator_g (hd : d.IsMeasGood) (z : ℂ) :
    Measurable ({ω | z ∈ d.D ω}.indicator fun ω => d.g ω z) :=
  measurable_indicator_mapOut hd.isDyadicHitMeasurable hd.isCompact_K hd.isPreconnected_K z

theorem IsMeasGood.D_of_mem (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    d.D ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := hd.DOf_of_mem E_subset_G hω

omit [MeasurableSpace Ω] in
theorem D_of_notMem {ω : Ω} (hω : ω ∉ d.E) : d.D ω = H := DOf_of_notMem hω

/-! ### The tip and the forward limit -/

theorem IsMeasGood.measurable_p (hd : d.IsMeasGood) : Measurable d.p := by
  classical
  have h := @Measurable.piecewise _ _ _ _ _ _ _ (Classical.decPred _) hd.measurableSet_E (hd.meas₂ d.r)
    (measurable_const (a := I))
  convert h using 1
  funext ω
  by_cases hω : ω ∈ d.E <;> simp [RetData.p, Set.piecewise, hω]

omit [MeasurableSpace Ω] in
theorem p_of_mem {ω : Ω} (hω : ω ∈ d.E) : d.p ω = d.η₂ ω d.r := by simp [p, hω]

omit [MeasurableSpace Ω] in
theorem p_of_notMem {ω : Ω} (hω : ω ∉ d.E) : d.p ω = I := by simp [p, hω]

/-- The retained chart data of `exists_retChart` at a point of `E`. -/
theorem IsMeasGood.exists_chart (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    ∃ x₀ : ℝ, Tendsto (d.g ω) (𝓝[d.D ω] (d.p ω)) (𝓝 (x₀ : ℂ)) ∧
    ∀ lift : ℂ → ℝ, ContinuousOn lift (d.D ω) →
      (∀ z ∈ d.D ω, deriv (fun z => d.g ω z - x₀) z = (‖deriv (fun z => d.g ω z - x₀) z‖ : ℂ) *
        exp (I * (lift z : ℂ))) →
      ∃ ψ : ℂ → ℂ, IsRetChart (d.η₁ ω) d.u (d.η₂ ω) d.r (fun z => d.g ω z - x₀) ψ lift := by
  have hω₀ := E_subset_E₀ hω
  have hg := hd.good ω hω₀.1.1
  have hcl : d.η₂ ω d.r ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r) := by
    rw [← hd.DOf_of_mem E₀_subset_G hω₀]; exact hω.2
  obtain ⟨x₀, hx₀, hψ⟩ := exists_retChart hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1
    hω₀.1.2 hω₀.2 hg.2.2.2.2.2.2 hcl
  have hgK : d.g ω = ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) := by
    rw [RetData.g, K_of_mem hω]
  refine ⟨x₀, ?_, fun lift hlc hlift => ?_⟩
  · rw [hgK, hd.D_of_mem hω, p_of_mem hω]; exact hx₀
  · rw [hd.D_of_mem hω] at hlc hlift
    rw [hgK] at hlift ⊢
    exact hψ lift hlc hlift

theorem I_mem_H : (I : ℂ) ∈ H := show (0 : ℝ) < I.im by simp

theorem IsMeasGood.exists_tendsto (hd : d.IsMeasGood) (ω : Ω) :
    ∃ y, Tendsto (d.g ω) (𝓝[d.D ω] (d.p ω)) (𝓝 y) := by
  by_cases hω : ω ∈ d.E
  · obtain ⟨x₀, hx₀, -⟩ := hd.exists_chart hω
    exact ⟨_, hx₀⟩
  · rw [p_of_notMem hω]
    have hcont : ContinuousOn (d.g ω) (d.D ω) :=
      (ConformalImage.isMapOut_mapOut (hd.isHPHull ω)).1.1.continuousOn
    have hI : I ∈ d.D ω := by rw [D_of_notMem hω]; exact I_mem_H
    exact ⟨_, hcont I hI⟩

theorem IsMeasGood.tendsto_shift (hd : d.IsMeasGood) (ω : Ω) :
    Tendsto (d.g ω) (𝓝[d.D ω] (d.p ω)) (𝓝 (d.shift ω)) :=
  tendsto_nhds_limUnder (hd.exists_tendsto ω)

theorem IsMeasGood.p_mem_closure (hd : d.IsMeasGood) (ω : Ω) : d.p ω ∈ closure (d.D ω) := by
  by_cases hω : ω ∈ d.E
  · rw [p_of_mem hω, hd.D_of_mem hω, ← hd.DOf_of_mem E₀_subset_G (E_subset_E₀ hω)]; exact hω.2
  · rw [D_of_notMem hω, p_of_notMem hω]; exact subset_closure I_mem_H

/-- **The forward limit at the tip is measurable.** -/
theorem IsMeasGood.measurable_shift (hd : d.IsMeasGood) : Measurable d.shift :=
  measurable_of_tendsto_nhdsWithin hd.isOpen_D hd.measurableSet_mem_D hd.measurable_indicator_g hd.measurable_p
    hd.p_mem_closure hd.tendsto_shift

/-- On `E` the forward limit is real and the chart with the canonical lift is a retained chart. -/
theorem IsMeasGood.isRetChart (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    (∃ x₀ : ℝ, d.shift ω = x₀) ∧ IsRetChart (d.η₁ ω) d.u (d.η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) := by
  classical
  obtain ⟨x₀, hx₀, hψ⟩ := hd.exists_chart hω
  have hNe : (𝓝[d.D ω] (d.p ω)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hd.p_mem_closure ω)
  have hsh : d.shift ω = x₀ := tendsto_nhds_unique (hd.tendsto_shift ω) hx₀
  refine ⟨⟨x₀, hsh⟩, ?_⟩
  have hA := hd.isHPHull ω
  have hL := isCanonicalDerivLog_canonDerivLog hA
  have hlc : ContinuousOn (d.lift ω) (d.D ω) :=
    Complex.continuous_im.comp_continuousOn hL.1.1.continuousOn
  have hlift : ∀ z ∈ d.D ω, deriv (fun z => d.g ω z - x₀) z =
      (‖deriv (fun z => d.g ω z - x₀) z‖ : ℂ) * exp (I * (d.lift ω z : ℂ)) := by
    intro z hz
    rw [deriv_sub_const]
    show deriv (ConformalImage.mapOut (fillH (d.K ω))) z =
      (‖deriv (ConformalImage.mapOut (fillH (d.K ω))) z‖ : ℂ) *
        exp (I * ((canonDerivLog (fillH (d.K ω)) z).im : ℂ))
    rw [← hL.1.2 z hz]
    exact exp_eq_norm_mul_exp_im _
  obtain ⟨ψ, hψ'⟩ := hψ (d.lift ω) hlc hlift
  have hfwd : d.fwd ω = fun z => d.g ω z - x₀ := by
    funext z; rw [RetData.fwd, hsh]
  have hex : ∃ ψ, IsRetChart (d.η₁ ω) d.u (d.η₂ ω) d.r (d.fwd ω) ψ (d.lift ω) := ⟨ψ, hfwd ▸ hψ'⟩
  have hinv : d.inv ω = hex.choose := by
    unfold RetData.inv
    rw [dite_eq_left_of_eq_true (eq_true hex)]
  rw [hinv]
  exact hex.choose_spec

/-! ### The chart and the chart field -/

omit [MeasurableSpace Ω] in
theorem chart_of_mem {ω : Ω} (hω : ω ∈ d.E) : d.chart ω = (d.fwd ω, d.inv ω, d.lift ω) := by
  simp [chart, hω]

omit [MeasurableSpace Ω] in
theorem chart_of_notMem {ω : Ω} (hω : ω ∉ d.E) : d.chart ω = Chart.id := by
  simp [chart, hω]

theorem IsMeasGood.isConformal_chart (hd : d.IsMeasGood) (ω : Ω) : (d.chart ω).IsConformal := by
  by_cases hω : ω ∈ d.E
  · rw [chart_of_mem hω]
    obtain ⟨-, hC⟩ := hd.isRetChart hω
    have h0₂ := (hd.good ω (E_subset_G hω)).2.2.2.2.2.1
    exact ⟨hC.differentiableOn_inv, fun w hw => ((hC.bijOn h0₂).mapsTo hw).1.1, hC.fwd_inv⟩
  · rw [chart_of_notMem hω]; exact Chart.isConformal_id

theorem IsMeasGood.coe_dom_chart (hd : d.IsMeasGood) (ω : Ω) : ((d.chart ω).dom : Set ℂ) = d.D ω := by
  rw [(hd.isConformal_chart ω).coe_dom]
  by_cases hω : ω ∈ d.E
  · rw [chart_of_mem hω]
    obtain ⟨-, hC⟩ := hd.isRetChart hω
    have h0₂ := (hd.good ω (E_subset_G hω)).2.2.2.2.2.1
    rw [hd.D_of_mem hω]
    exact (hC.bijOn h0₂).image_eq
  · rw [chart_of_notMem hω, D_of_notMem hω]
    exact image_id H

theorem IsMeasGood.continuousOn_lift_chart (hd : d.IsMeasGood) (ω : Ω) :
    ContinuousOn (d.chart ω).2.2 (d.chart ω).dom := by
  rw [hd.coe_dom_chart ω]
  by_cases hω : ω ∈ d.E
  · rw [chart_of_mem hω]
    exact Complex.continuous_im.comp_continuousOn
      (isCanonicalDerivLog_canonDerivLog (hd.isHPHull ω)).1.1.continuousOn
  · rw [chart_of_notMem hω]; exact continuousOn_const

/-- **The retained chart field** `Hc = chartTransport chart 1 0 χ(κ) h` (Lemma G7: the conditional field in the
inherited hydrodynamic chart, `h ∘ φ⁻¹ − χ arg (φ⁻¹)′`). -/
def IsMeasGood.chartField (hd : d.IsMeasGood) (κ : ℝ) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (ω : Ω) : LQGMetric.DistOn upperHalfPlaneOpens :=
  Chart.chartTransport (hd.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ) (h ω)

theorem IsMeasGood.isChartTransport_chartField (hd : d.IsMeasGood) (κ : ℝ)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (ω : Ω) :
    IsChartTransport (d.chart ω) 1 0 (QuantumZipper.chiC κ) (h ω) (hd.chartField κ h ω) :=
  Chart.isChartTransport_chartTransport (hd.isConformal_chart ω)
    (Chart.locallyIntegrableOn_of_continuousOn
      ((hd.isConformal_chart ω).continuousOn_lift_inv (hd.continuousOn_lift_chart ω))) _ _ _ _

/-- **The chart is measurable** in the form of PROVE-PUSHFWD's random-chart results. -/
theorem IsMeasGood.chart_measurability (hd : d.IsMeasGood) :
    (∀ z, MeasurableSet {ω | z ∈ (d.chart ω).dom}) ∧
    (∀ z, Measurable ({ω | z ∈ (d.chart ω).dom}.indicator fun ω => (d.chart ω).1 z)) ∧
    (∀ z, Measurable ({ω | z ∈ (d.chart ω).dom}.indicator fun ω => (d.chart ω).2.2 z)) := by
  classical
  have hdomEq : ∀ z, {ω | z ∈ (d.chart ω).dom} = {ω | z ∈ d.D ω} := fun z => by
    ext ω
    simp only [mem_ofPred_eq]
    rw [← SetLike.mem_coe, hd.coe_dom_chart ω]
  have hdom : ∀ z, MeasurableSet {ω | z ∈ (d.chart ω).dom} := fun z => by
    rw [hdomEq z]; exact hd.measurableSet_mem_D z
  have hfwd : ∀ z, Measurable ({ω | z ∈ (d.chart ω).dom}.indicator fun ω => (d.chart ω).1 z) := by
    intro z
    rw [hdomEq z]
    have hm := @Measurable.piecewise _ _ _ _ _ _ _ (Classical.decPred _) hd.measurableSet_E
      ((hd.measurable_indicator_g z).sub
        (hd.measurable_shift.indicator (hd.measurableSet_mem_D z)))
        ((measurable_const (a := z)).indicator (hd.measurableSet_mem_D z))
    convert hm using 1
    funext ω
    simp only [Set.piecewise]
    by_cases hz : z ∈ d.D ω
    · have hz' : ω ∈ {ω | z ∈ d.D ω} := hz
      by_cases hω : ω ∈ d.E
      · simp only [Pi.sub_apply, indicator_of_mem hz', hω, ↓reduceIte, chart_of_mem hω, RetData.fwd]
      · simp only [indicator_of_mem hz', hω, ↓reduceIte, chart_of_notMem hω, Chart.id]
    · have hz' : ω ∉ {ω | z ∈ d.D ω} := hz
      simp only [Pi.sub_apply, indicator_of_notMem hz', sub_zero]
      split_ifs <;> rfl
  have hliftm : ∀ z, Measurable ({ω | z ∈ (d.chart ω).dom}.indicator fun ω => (d.chart ω).2.2 z) := by
    intro z
    rw [hdomEq z]
    have hc := measurable_indicator_canonDerivLog hd.isDyadicHitMeasurable hd.isCompact_K hd.isPreconnected_K z
    have hm := @Measurable.piecewise _ _ _ _ _ _ _ (Classical.decPred _) hd.measurableSet_E
      (Complex.measurable_im.comp hc)
      (measurable_const (a := (0 : ℝ)))
    convert hm using 1
    funext ω
    simp only [Set.piecewise, Function.comp_apply]
    by_cases hz : z ∈ d.D ω
    · have hz' : ω ∈ {ω | z ∈ d.D ω} := hz
      have hz'' : ω ∈ {ω | z ∈ H \ fillH (d.K ω)} := hz
      by_cases hω : ω ∈ d.E
      · simp only [indicator_of_mem hz', indicator_of_mem hz'', hω, ↓reduceIte, chart_of_mem hω, RetData.lift]
      · simp only [indicator_of_mem hz', hω, ↓reduceIte, chart_of_notMem hω, Chart.id]
    · have hz' : ω ∉ {ω | z ∈ d.D ω} := hz
      have hz'' : ω ∉ {ω | z ∈ H \ fillH (d.K ω)} := hz
      simp only [indicator_of_notMem hz', indicator_of_notMem hz'', zero_im]
      split_ifs <;> rfl
  exact ⟨hdom, hfwd, hliftm⟩

/-- **The retained chart field is measurable.** -/
theorem IsMeasGood.measurable_chartField (hd : d.IsMeasGood) (κ : ℝ)
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : Measurable h) : Measurable (hd.chartField κ h) := by
  obtain ⟨hdom, hfwd, hliftm⟩ := hd.chart_measurability
  exact Chart.measurable_chartTransport_random' hd.isConformal_chart hdom hfwd hliftm hd.continuousOn_lift_chart
    hh 1 0 (QuantumZipper.chiC κ)

end RetData

end Supp7

end InteractingSLE
