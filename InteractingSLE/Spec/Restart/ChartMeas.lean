/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeasChart
import InteractingSLE.GFF.PushforwardMeas

/-!
# The measurable first-contact chart and chart field

Packet PROVE-RESTART-CPL4, item 1 of `FirstContactChartDataFCStatement` (CPL3 handoff, "What remains" 1): a
**measurable choice of the first-contact chart** and of the chart field `Hc`.

Data (`PairData`): two random paths `η₁, η₂` with lifetimes `ζ₁, ζ₂`, and an event `G`. Hypotheses
(`PairData.IsMeasGood`): `G` is measurable, the paths are measurable at each fixed time, the lifetimes are measurable,
and on `G` (`IsChartGood`) the paths are continuous on their closed available intervals, lie in `ℍ̄`, start on `ℝ`,
and whenever they meet they have a first contact whose point lies in the closure of the active domain (Lemma 7.7's
confinement, `Supp10.Lemma77Statement`).

Construction, on the contact event `E = G ∩ {the paths meet}` (`PairData.E`):
* the first-contact times `s₀, t₀` (`fcPair`), measurable (`ChartMeasPath.lean`);
* the random compact set `K = η₁[0, s₀] ∪ η₂[0, t₀]` (`∅` off `E`), dyadic-hit measurable, so that the domain events
  `{z ∈ D}`, `D = ℍ \ fill(K)` (the active domain on `E`, `ℍ` off `E`), the canonical mapping-out function `g` on `D`
  and the canonical logarithm of `g′` are measurable (`ChartMeasRandom.lean`, `ChartMeasLift.lean`);
* the contact point `p = η₁(s₀)` and the forward limit `x₀ = lim_{z → p, z ∈ D} g(z)` (`PairData.shift`), measurable
  (`measurable_of_tendsto_nhdsWithin`);
* the chart `(φ, ψ, lift) = (g − x₀, ψ, Im log g′)` (`PairData.chart`; `Chart.id` off `E`), with the inverse `ψ` chosen
  pathwise; it is a first-contact chart on `E` (`PairData.isFirstContactChart`, through
  `exists_isFirstContactChart_mapOut`),
  with the derivative argument normalized to vanish at `i∞` (Lemma 7.8);
* the chart field `Hc = chartTransport chart 1 0 χ h` (`PairData.chartField`), **measurable**
  (`PairData.measurable_chartField`, through PROVE-PUSHFWD's `Chart.measurable_chartTransport_random'`), with
  `IsChartTransport` at every `ω`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-! ### The pathwise hypotheses -/

/-- The pathwise hypotheses of the chart construction: continuity on the closed available intervals, values in `ℍ̄`,
real seeds, and a first contact in the closure of the active domain whenever the paths meet. -/
def IsChartGood (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ContinuousOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁} ∧ ContinuousOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂} ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ Hbar) ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂ t ∈ Hbar) ∧
    (η₁ 0).im = 0 ∧ (η₂ 0).im = 0 ∧
    (HasContact η₁ ζ₁ η₂ ζ₂ → ∃ s₀ t₀ : ℝ≥0, IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀ ∧
      η₁ s₀ ∈ closure (activeDomain η₁ s₀ η₂ t₀))

theorem Icc_zero_eq_Iic (a : ℝ≥0) : Icc (0 : ℝ≥0) a = Iic a := by
  ext x; simp

/-! ### Random path pairs -/

/-- Two random available paths together with an event on which they are well behaved. -/
structure PairData (Ω : Type*) where
  /-- The good event. -/
  G : Set Ω
  /-- The first path. -/
  η₁ : Ω → ℝ≥0 → ℂ
  /-- Its lifetime. -/
  ζ₁ : Ω → ℝ≥0∞
  /-- The second path. -/
  η₂ : Ω → ℝ≥0 → ℂ
  /-- Its lifetime. -/
  ζ₂ : Ω → ℝ≥0∞

namespace PairData

variable {Ω : Type*} [MeasurableSpace Ω] (d : PairData Ω)

/-- The measurability hypotheses, and the pathwise ones on `G`. -/
structure IsMeasGood : Prop where
  measurableSet_G : MeasurableSet d.G
  meas₁ : ∀ t, Measurable fun ω => d.η₁ ω t
  meas₂ : ∀ t, Measurable fun ω => d.η₂ ω t
  measζ₁ : Measurable d.ζ₁
  measζ₂ : Measurable d.ζ₂
  good : ∀ ω ∈ d.G, IsChartGood (d.η₁ ω) (d.ζ₁ ω) (d.η₂ ω) (d.ζ₂ ω)

/-- The contact event: `G` and the paths meet. -/
def E : Set Ω := d.G ∩ {ω | HasContact (d.η₁ ω) (d.ζ₁ ω) (d.η₂ ω) (d.ζ₂ ω)}

open scoped Classical in
/-- The first-contact time of the first path (`0` off `E`). -/
def s₀ (ω : Ω) : ℝ≥0 := if ω ∈ d.E then (fcPair (d.η₁ ω) (d.ζ₁ ω) (d.η₂ ω) (d.ζ₂ ω)).1 else 0

open scoped Classical in
/-- The first-contact time of the second path (`0` off `E`). -/
def t₀ (ω : Ω) : ℝ≥0 := if ω ∈ d.E then (fcPair (d.η₁ ω) (d.ζ₁ ω) (d.η₂ ω) (d.ζ₂ ω)).2 else 0

open scoped Classical in
/-- The random compact set `η₁[0, s₀] ∪ η₂[0, t₀]` (`∅` off `E`). -/
def K (ω : Ω) : Set ℂ := if ω ∈ d.E then prefixSet (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) else ∅

/-- The random domain `ℍ \ fill(K)`: the active domain on `E`, `ℍ` off `E`. -/
def D (ω : Ω) : Set ℂ := H \ fillH (d.K ω)

/-- The canonical mapping-out function of the filled compact set. -/
def g (ω : Ω) : ℂ → ℂ := ConformalImage.mapOut (fillH (d.K ω))

open scoped Classical in
/-- The contact point `η₁(s₀)` (`i` off `E`). -/
def p (ω : Ω) : ℂ := if ω ∈ d.E then d.η₁ ω (d.s₀ ω) else I

/-- The forward limit of `g` at the contact point along the domain. -/
def shift (ω : Ω) : ℂ := limUnder (𝓝[d.D ω] (d.p ω)) (d.g ω)

/-- The canonical lift: the imaginary part of the canonical logarithm of `g′`. -/
def lift (ω : Ω) : ℂ → ℝ := fun z => (canonDerivLog (fillH (d.K ω)) z).im

/-- The forward chart map `φ = g − x₀`. -/
def fwd (ω : Ω) : ℂ → ℂ := fun z => d.g ω z - d.shift ω

open scoped Classical in
/-- A pathwise choice of the chart inverse (`id` if there is none). -/
def inv (ω : Ω) : ℂ → ℂ :=
  if h : ∃ ψ, IsFirstContactChart (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) (d.fwd ω) ψ (d.lift ω) then h.choose else id

open scoped Classical in
/-- **The first-contact chart** (`Chart.id` off `E`). -/
def chart (ω : Ω) : Chart := if ω ∈ d.E then (d.fwd ω, d.inv ω, d.lift ω) else Chart.id

variable {d}

/-! ### The contact event and the first-contact times -/

theorem IsMeasGood.measurableSet_E (hd : d.IsMeasGood) : MeasurableSet d.E :=
  measurableSet_inter_hasContact hd.measurableSet_G hd.meas₁ hd.meas₂ hd.measζ₁ hd.measζ₂
    (fun ω hω => (hd.good ω hω).1) (fun ω hω => (hd.good ω hω).2.1)

theorem IsMeasGood.measurable_s₀ (hd : d.IsMeasGood) : Measurable d.s₀ := by
  convert (measurable_piecewise_fcTime hd.measurableSet_G hd.meas₁ hd.meas₂ hd.measζ₁ hd.measζ₂
    (fun ω hω => (hd.good ω hω).1) (fun ω hω => (hd.good ω hω).2.1)
    (fun ω hω hc => by obtain ⟨s₀, t₀, h, -⟩ := (hd.good ω hω).2.2.2.2.2.2 hc; exact ⟨s₀, t₀, h⟩)).1 using 1
  funext ω
  simp only [PairData.s₀, PairData.E]
  split_ifs with h <;> simp only [h, ↓reduceIte]

theorem IsMeasGood.measurable_t₀ (hd : d.IsMeasGood) : Measurable d.t₀ := by
  convert (measurable_piecewise_fcTime hd.measurableSet_G hd.meas₁ hd.meas₂ hd.measζ₁ hd.measζ₂
    (fun ω hω => (hd.good ω hω).1) (fun ω hω => (hd.good ω hω).2.1)
    (fun ω hω hc => by obtain ⟨s₀, t₀, h, -⟩ := (hd.good ω hω).2.2.2.2.2.2 hc; exact ⟨s₀, t₀, h⟩)).2 using 1
  funext ω
  simp only [PairData.t₀, PairData.E]
  split_ifs with h <;> simp only [h, ↓reduceIte]

omit [MeasurableSpace Ω] in
theorem s₀_of_mem {ω : Ω} (hω : ω ∈ d.E) : d.s₀ ω = (fcPair (d.η₁ ω) (d.ζ₁ ω) (d.η₂ ω) (d.ζ₂ ω)).1 := by
  simp [s₀, hω]

omit [MeasurableSpace Ω] in
theorem t₀_of_mem {ω : Ω} (hω : ω ∈ d.E) : d.t₀ ω = (fcPair (d.η₁ ω) (d.ζ₁ ω) (d.η₂ ω) (d.ζ₂ ω)).2 := by
  simp [t₀, hω]

theorem IsMeasGood.isFirstContact (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    IsFirstContact (d.η₁ ω) (d.ζ₁ ω) (d.η₂ ω) (d.ζ₂ ω) (d.s₀ ω) (d.t₀ ω) := by
  obtain ⟨s₀, t₀, h, -⟩ := (hd.good ω hω.1).2.2.2.2.2.2 hω.2
  rw [s₀_of_mem hω, t₀_of_mem hω]
  exact isFirstContact_fcPair h

theorem IsMeasGood.mem_closure (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    d.η₁ ω (d.s₀ ω) ∈ closure (activeDomain (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω)) := by
  obtain ⟨s₀, t₀, h, hcl⟩ := (hd.good ω hω.1).2.2.2.2.2.2 hω.2
  have he := fcPair_eq h
  rw [s₀_of_mem hω, t₀_of_mem hω, he]
  exact hcl

omit [MeasurableSpace Ω] in
/-- A first contact of the paths at `ω ∈ G` is `(s₀ ω, t₀ ω)`, and `ω ∈ E`. -/
theorem eq_of_isFirstContact {ω : Ω} (hω : ω ∈ d.G) {s t : ℝ≥0}
    (h : IsFirstContact (d.η₁ ω) (d.ζ₁ ω) (d.η₂ ω) (d.ζ₂ ω) s t) : ω ∈ d.E ∧ d.s₀ ω = s ∧ d.t₀ ω = t := by
  have hE : ω ∈ d.E := ⟨hω, s, t, h.1, h.2.1, h.2.2.1⟩
  refine ⟨hE, ?_, ?_⟩
  · rw [s₀_of_mem hE, fcPair_eq h]
  · rw [t₀_of_mem hE, fcPair_eq h]

/-! ### The random compact set -/

omit [MeasurableSpace Ω] in
theorem K_of_mem {ω : Ω} (hω : ω ∈ d.E) : d.K ω = prefixSet (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) := by
  simp [K, hω]

omit [MeasurableSpace Ω] in
theorem K_of_notMem {ω : Ω} (hω : ω ∉ d.E) : d.K ω = ∅ := by
  simp [K, hω]

theorem IsMeasGood.continuousOn₁ (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    ContinuousOn (d.η₁ ω) (Iic (d.s₀ ω)) :=
  (hd.good ω hω.1).1.mono fun _ hs => (ENNReal.coe_le_coe.2 hs).trans (hd.isFirstContact hω).1

theorem IsMeasGood.continuousOn₂ (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    ContinuousOn (d.η₂ ω) (Iic (d.t₀ ω)) :=
  (hd.good ω hω.1).2.1.mono fun _ hs => (ENNReal.coe_le_coe.2 hs).trans (hd.isFirstContact hω).2.1

theorem IsMeasGood.isCompact_K (hd : d.IsMeasGood) (ω : Ω) : IsCompact (d.K ω) := by
  by_cases hω : ω ∈ d.E
  · rw [K_of_mem hω, prefixSet, Icc_zero_eq_Iic, Icc_zero_eq_Iic]
    exact ((isCompact_Iic_nnreal _).image_of_continuousOn (hd.continuousOn₁ hω)).union
      ((isCompact_Iic_nnreal _).image_of_continuousOn (hd.continuousOn₂ hω))
  · rw [K_of_notMem hω]; exact isCompact_empty

theorem IsMeasGood.isPreconnected_K (hd : d.IsMeasGood) (ω : Ω) : IsPreconnected (d.K ω ∪ lowerHalf) := by
  by_cases hω : ω ∈ d.E
  · rw [K_of_mem hω, prefixSet, Icc_zero_eq_Iic, Icc_zero_eq_Iic]
    have hg := hd.good ω hω.1
    have h1 : IsPreconnected (d.η₁ ω '' Iic (d.s₀ ω)) := by
      rw [← Icc_zero_eq_Iic]; exact isPreconnected_Icc.image _ ((hd.continuousOn₁ hω).mono (by
        rw [Icc_zero_eq_Iic]))
    have h2 : IsPreconnected (d.η₂ ω '' Iic (d.t₀ ω)) := by
      rw [← Icc_zero_eq_Iic]; exact isPreconnected_Icc.image _ ((hd.continuousOn₂ hω).mono (by
        rw [Icc_zero_eq_Iic]))
    have hL : IsPreconnected lowerHalf :=
      (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
    have m1 : d.η₁ ω 0 ∈ lowerHalf := show (d.η₁ ω 0).im ≤ 0 by rw [hg.2.2.2.2.1]
    have m2 : d.η₂ ω 0 ∈ lowerHalf := show (d.η₂ ω 0).im ≤ 0 by rw [hg.2.2.2.2.2.1]
    have h3 : IsPreconnected (d.η₁ ω '' Iic (d.s₀ ω) ∪ lowerHalf) :=
      h1.union (d.η₁ ω 0) (mem_image_of_mem _ (mem_Iic.2 zero_le)) m1 hL
    have h4 := h3.union (d.η₂ ω 0) (Or.inr m2) (mem_image_of_mem _ (mem_Iic.2 zero_le)) h2
    rwa [show d.η₁ ω '' Iic (d.s₀ ω) ∪ d.η₂ ω '' Iic (d.t₀ ω) ∪ lowerHalf =
      d.η₁ ω '' Iic (d.s₀ ω) ∪ lowerHalf ∪ d.η₂ ω '' Iic (d.t₀ ω) from union_right_comm _ _ _]
  · rw [K_of_notMem hω, empty_union]
    exact (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected

theorem dyadicSquare_nonempty (n : ℕ) (k : ℤ × ℤ) : (dyadicSquare n k).Nonempty := by
  refine ⟨((k.1 : ℝ) / 2 ^ n : ℝ) + ((k.2 : ℝ) / 2 ^ n : ℝ) * I, ?_⟩
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  simp only [dyadicSquare, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, mul_im, zero_add]
  field_simp
  refine ⟨le_refl _, ?_, le_refl _, ?_⟩ <;> linarith

theorem IsMeasGood.isDyadicHitMeasurable (hd : d.IsMeasGood) : IsDyadicHitMeasurable d.K := by
  intro n k
  set Q := dyadicSquare n k
  have hQ : IsClosed Q := isClosed_dyadicSquare n k
  have hQne : Q.Nonempty := dyadicSquare_nonempty n k
  have heq : {ω | (Q ∩ d.K ω).Nonempty} =
      (d.E ∩ {ω | ∃ s ≤ d.s₀ ω, d.η₁ ω s ∈ Q}) ∪ (d.E ∩ {ω | ∃ t ≤ d.t₀ ω, d.η₂ ω t ∈ Q}) := by
    ext ω
    by_cases hω : ω ∈ d.E
    · simp only [mem_ofPred_eq, mem_union, mem_inter_iff, hω, true_and, K_of_mem hω, prefixSet]
      constructor
      · rintro ⟨z, hzQ, ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩⟩
        · exact Or.inl ⟨s, hs.2, hzQ⟩
        · exact Or.inr ⟨t, ht.2, hzQ⟩
      · rintro (⟨s, hs, hsQ⟩ | ⟨t, ht, htQ⟩)
        · exact ⟨_, hsQ, Or.inl ⟨s, ⟨zero_le, hs⟩, rfl⟩⟩
        · exact ⟨_, htQ, Or.inr ⟨t, ⟨zero_le, ht⟩, rfl⟩⟩
    · simp [K_of_notMem hω, hω]
  rw [heq]
  exact (measurableSet_inter_exists_mem hd.measurableSet_E hd.meas₁ hd.measurable_s₀
      (fun ω hω => hd.continuousOn₁ hω) hQ hQne).union
    (measurableSet_inter_exists_mem hd.measurableSet_E hd.meas₂ hd.measurable_t₀
      (fun ω hω => hd.continuousOn₂ hω) hQ hQne)

/-! ### The domain, the contact point and the forward limit -/

theorem IsMeasGood.D_of_mem (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    d.D ω = activeDomain (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) := by
  have hc := hd.isCompact_K ω
  rw [K_of_mem hω] at hc
  rw [D, K_of_mem hω, activeDomain_eq hc.isClosed]

omit [MeasurableSpace Ω] in
theorem D_of_notMem {ω : Ω} (hω : ω ∉ d.E) : d.D ω = H := by
  rw [D, K_of_notMem hω, YuanCharacterisation.fillH_eq_empty_of_subset (empty_subset _), sdiff_empty]

theorem IsMeasGood.isHPHull (hd : d.IsMeasGood) (ω : Ω) : IsHPHull (fillH (d.K ω)) :=
  isHPHull_fillH_of_compact (hd.isCompact_K ω) (hd.isPreconnected_K ω)

theorem IsMeasGood.isOpen_D (hd : d.IsMeasGood) (ω : Ω) : IsOpen (d.D ω) := (hd.isHPHull ω).isOpen

theorem IsMeasGood.measurableSet_mem_D (hd : d.IsMeasGood) (z : ℂ) : MeasurableSet {ω | z ∈ d.D ω} :=
  measurableSet_mem_H_diff_fillH hd.isDyadicHitMeasurable hd.isCompact_K z

theorem IsMeasGood.measurable_indicator_g (hd : d.IsMeasGood) (z : ℂ) :
    Measurable ({ω | z ∈ d.D ω}.indicator fun ω => d.g ω z) :=
  measurable_indicator_mapOut hd.isDyadicHitMeasurable hd.isCompact_K hd.isPreconnected_K z

theorem IsMeasGood.measurable_p (hd : d.IsMeasGood) : Measurable d.p := by
  classical
  have hF := measurable_piecewise_eval hd.measurableSet_E hd.meas₁ hd.measurable_s₀
    (fun ω hω => hd.continuousOn₁ hω)
  have h := @Measurable.piecewise _ _ _ _ _ _ _ (Classical.decPred _) hd.measurableSet_E hF
    (measurable_const (a := I))
  convert h using 1
  funext ω
  by_cases hω : ω ∈ d.E <;> simp [PairData.p, Set.piecewise, hω]

omit [MeasurableSpace Ω] in
theorem p_of_mem {ω : Ω} (hω : ω ∈ d.E) : d.p ω = d.η₁ ω (d.s₀ ω) := by simp [p, hω]

omit [MeasurableSpace Ω] in
theorem p_of_notMem {ω : Ω} (hω : ω ∉ d.E) : d.p ω = I := by simp [p, hω]

theorem I_mem_H : (I : ℂ) ∈ H := show (0 : ℝ) < I.im by simp

/-- The chart data of `exists_isFirstContactChart_mapOut` at a point of `E`. -/
theorem IsMeasGood.exists_chart (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    ∃ x₀ : ℝ, Tendsto (d.g ω) (𝓝[d.D ω] (d.p ω)) (𝓝 (x₀ : ℂ)) ∧
    ∀ lift : ℂ → ℝ, ContinuousOn lift (d.D ω) →
      (∀ z ∈ d.D ω, deriv (fun z => d.g ω z - x₀) z = (‖deriv (fun z => d.g ω z - x₀) z‖ : ℂ) *
        exp (I * (lift z : ℂ))) →
      ∃ ψ : ℂ → ℂ, IsFirstContactChart (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) (fun z => d.g ω z - x₀) ψ lift := by
  have hg := hd.good ω hω.1
  have hfc := hd.isFirstContact hω
  have hI₁ : Icc 0 (d.s₀ ω) ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ d.ζ₁ ω} := fun s hs =>
    (ENNReal.coe_le_coe.2 hs.2).trans hfc.1
  have hI₂ : Icc 0 (d.t₀ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.ζ₂ ω} := fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2).trans hfc.2.1
  have hne₁ : ∀ s < d.s₀ ω, d.η₁ ω s ≠ d.η₁ ω (d.s₀ ω) := fun s hs he => by
    have := hfc.2.2.2 s (d.t₀ ω) ((ENNReal.coe_le_coe.2 hs.le).trans hfc.1) hfc.2.1 (he.trans hfc.2.2.1)
    exact absurd this.1 (not_le.2 hs)
  have hne₂ : ∀ t < d.t₀ ω, d.η₂ ω t ≠ d.η₁ ω (d.s₀ ω) := fun t ht he => by
    have := hfc.2.2.2 (d.s₀ ω) t hfc.1 ((ENNReal.coe_le_coe.2 ht.le).trans hfc.2.1) he.symm
    exact absurd this.2 (not_le.2 ht)
  obtain ⟨x₀, hx₀, hψ⟩ := exists_isFirstContactChart_mapOut (hg.1.mono hI₁) (hg.2.1.mono hI₂)
    (fun s hs => hg.2.2.1 s (hI₁ hs)) (fun t ht => hg.2.2.2.1 t (hI₂ ht)) hg.2.2.2.2.1 hg.2.2.2.2.2.1
    hfc.2.2.1 hne₁ hne₂ (hd.mem_closure hω)
  have hgK : d.g ω = ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω))) := by
    rw [PairData.g, K_of_mem hω]
  refine ⟨x₀, ?_, fun lift hlc hlift => ?_⟩
  · rw [hgK, hd.D_of_mem hω, p_of_mem hω]; exact hx₀
  · rw [hd.D_of_mem hω] at hlc hlift
    rw [hgK] at hlift ⊢
    exact hψ lift hlc hlift

theorem IsMeasGood.exists_tendsto (hd : d.IsMeasGood) (ω : Ω) :
    ∃ y, Tendsto (d.g ω) (𝓝[d.D ω] (d.p ω)) (𝓝 y) := by
  by_cases hω : ω ∈ d.E
  · obtain ⟨x₀, hx₀, -⟩ := hd.exists_chart hω
    exact ⟨_, hx₀⟩
  · rw [D_of_notMem hω, p_of_notMem hω]
    have hcont : ContinuousOn (d.g ω) H := by
      have := (ConformalImage.isMapOut_mapOut (hd.isHPHull ω)).1.1.continuousOn
      rwa [show H \ fillH (d.K ω) = H by rw [← PairData.D, D_of_notMem hω]] at this
    exact ⟨_, hcont I I_mem_H⟩

theorem IsMeasGood.tendsto_shift (hd : d.IsMeasGood) (ω : Ω) :
    Tendsto (d.g ω) (𝓝[d.D ω] (d.p ω)) (𝓝 (d.shift ω)) :=
  tendsto_nhds_limUnder (hd.exists_tendsto ω)

theorem IsMeasGood.p_mem_closure (hd : d.IsMeasGood) (ω : Ω) : d.p ω ∈ closure (d.D ω) := by
  by_cases hω : ω ∈ d.E
  · rw [hd.D_of_mem hω, p_of_mem hω]; exact hd.mem_closure hω
  · rw [D_of_notMem hω, p_of_notMem hω]; exact subset_closure I_mem_H

/-- **The forward limit at the contact point is measurable.** -/
theorem IsMeasGood.measurable_shift (hd : d.IsMeasGood) : Measurable d.shift :=
  measurable_of_tendsto_nhdsWithin hd.isOpen_D hd.measurableSet_mem_D hd.measurable_indicator_g hd.measurable_p
    hd.p_mem_closure hd.tendsto_shift

/-- On `E` the forward limit is real and the chart with the canonical lift is a first-contact chart. -/
theorem IsMeasGood.isFirstContactChart (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) :
    (∃ x₀ : ℝ, d.shift ω = x₀) ∧
      IsFirstContactChart (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) (d.fwd ω) (d.inv ω) (d.lift ω) := by
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
    funext z; rw [PairData.fwd, hsh]
  have hex : ∃ ψ, IsFirstContactChart (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) (d.fwd ω) ψ (d.lift ω) :=
    ⟨ψ, hfwd ▸ hψ'⟩
  have hinv : d.inv ω = hex.choose := by
    unfold PairData.inv
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
    obtain ⟨-, hC⟩ := hd.isFirstContactChart hω
    exact ⟨hC.2.2.2.2.2.2.1, fun w hw => (hC.2.1.mapsTo hw).1.1, hC.2.2.1⟩
  · rw [chart_of_notMem hω]; exact Chart.isConformal_id

theorem IsMeasGood.coe_dom_chart (hd : d.IsMeasGood) (ω : Ω) : ((d.chart ω).dom : Set ℂ) = d.D ω := by
  rw [(hd.isConformal_chart ω).coe_dom]
  by_cases hω : ω ∈ d.E
  · rw [chart_of_mem hω]
    obtain ⟨-, hC⟩ := hd.isFirstContactChart hω
    rw [hd.D_of_mem hω]
    exact hC.2.1.image_eq
  · rw [chart_of_notMem hω, D_of_notMem hω]
    exact image_id H

theorem IsMeasGood.continuousOn_lift_chart (hd : d.IsMeasGood) (ω : Ω) :
    ContinuousOn (d.chart ω).2.2 (d.chart ω).dom := by
  rw [hd.coe_dom_chart ω]
  by_cases hω : ω ∈ d.E
  · rw [chart_of_mem hω]
    exact Complex.continuous_im.comp_continuousOn (isCanonicalDerivLog_canonDerivLog (hd.isHPHull ω)).1.1.continuousOn
  · rw [chart_of_notMem hω]; exact continuousOn_const

/-- **The chart field** `Hc = chartTransport chart 1 0 χ(κ) h` (Lemma 7.8: `h ∘ φ⁻¹ − χ arg (φ⁻¹)′` in the chart). -/
def IsMeasGood.chartField (hd : d.IsMeasGood) (κ : ℝ) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (ω : Ω) : LQGMetric.DistOn upperHalfPlaneOpens :=
  Chart.chartTransport (hd.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ) (h ω)

theorem IsMeasGood.isChartTransport_chartField (hd : d.IsMeasGood) (κ : ℝ)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (ω : Ω) :
    IsChartTransport (d.chart ω) 1 0 (QuantumZipper.chiC κ) (h ω) (hd.chartField κ h ω) :=
  Chart.isChartTransport_chartTransport (hd.isConformal_chart ω)
    (Chart.locallyIntegrableOn_of_continuousOn
      ((hd.isConformal_chart ω).continuousOn_lift_inv (hd.continuousOn_lift_chart ω))) _ _ _ _

/-- **The chart is measurable** in the form PROVE-PUSHFWD's random-chart results ask for: the domain events, and the
forward maps and lifts on the domain (indicator form). -/
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
      · simp only [Pi.sub_apply, indicator_of_mem hz', hω, ↓reduceIte, chart_of_mem hω, PairData.fwd]
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
      · simp only [indicator_of_mem hz', indicator_of_mem hz'', hω, ↓reduceIte, chart_of_mem hω, PairData.lift]
      · simp only [indicator_of_mem hz', hω, ↓reduceIte, chart_of_notMem hω, Chart.id]
    · have hz' : ω ∉ {ω | z ∈ d.D ω} := hz
      have hz'' : ω ∉ {ω | z ∈ H \ fillH (d.K ω)} := hz
      simp only [indicator_of_notMem hz', indicator_of_notMem hz'', zero_im]
      split_ifs <;> rfl
  exact ⟨hdom, hfwd, hliftm⟩

/-- **The chart field is measurable.** -/
theorem IsMeasGood.measurable_chartField (hd : d.IsMeasGood) (κ : ℝ)
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : Measurable h) : Measurable (hd.chartField κ h) := by
  obtain ⟨hdom, hfwd, hliftm⟩ := hd.chart_measurability
  exact Chart.measurable_chartTransport_random' hd.isConformal_chart hdom hfwd hliftm hd.continuousOn_lift_chart
    hh 1 0 (QuantumZipper.chiC κ)

end PairData

end Restart

end InteractingSLE
