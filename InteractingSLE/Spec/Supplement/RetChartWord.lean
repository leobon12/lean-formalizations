/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetTouchLimit
import InteractingSLE.Spec.Sec7.Lemma72BChart

/-!
# The zone data of a touching retained pair and its measurable word

Packet PROVE-T15-RET5 (Theorem 1.5's leaf `RLC.RetTouchChartBoundaryStatement`; Aux. lemmas 85–86, supplement
pp. 299–301). PROVE-T15-RET4 proved the word layer of a touching retained pair for any zone data `z` with the outer
boundary (OF2) in the retained chart (`RetTouch.IsTouchZones`). This file fixes the zone data and makes the word
measurable for the retained σ-algebra:

* **`junction`**: the junction chart point, the supremum of the rational chart points in `(0, M₁)` whose image is on
  the second prefix (`0` if there is none);
* **`zoneDataT`**: the touching zone data — the two outer zones `(−∞, a₂)` (left of the second base) and `(b₁, ∞)`
  (right of the first base) with chart points `T(x)`, `L₂ = sup T(a₂⁻)`, `R₁ = inf T(b₁⁺)`, the second tip at `0`,
  the first tip `M₁`, and the junction `R₂ = L₁ = J`; the middle block is empty (`a₁ = a₂`, `b₂ = b₁`);
* **`wordT`**: the measurable word, every input read on its measurable event (`measurable_wordT`); at a chart event on
  which the first tip is regular and the outer real points are untouched, it is the truncated touching word
  (`wordT_eq`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace RetChart

open Restart Supp7 Sec7 Sec7.Lemma76G RetTouch

/-! ### The deterministic zone data -/

open scoped Classical in
/-- **The junction chart point**: the supremum of the rational chart points in `(0, M₁)` whose image under `ψ` lies
on the second prefix `β([0, b])` (`0` if there is none). -/
def junction (ψ : ℂ → ℂ) (β : ℝ≥0 → ℂ) (b : ℝ≥0) (M₁ : ℝ) : ℝ :=
  ⨆ q : ℚ, if 0 < (q : ℝ) ∧ (q : ℝ) < M₁ ∧ ψ ((q : ℝ) : ℂ) ∈ β '' Icc 0 b then (q : ℝ) else 0

/-- **The zone data of a touching retained pair** (Aux. lemma 85 in the retained chart, second tip at `0`): chart points
`T(x)` of real points, the outer zones `(−∞, a₂)` and `(b₁, ∞)` with `a₂ = baseL β`, `b₁ = baseR α`, the empty middle
block (`a₁ = a₂`, `b₂ = b₁`), `L₂ = sup T(a₂⁻)`, `M₂ = 0`, the junction `R₂ = L₁`, the first tip `M₁` and
`R₁ = inf T(b₁⁺)`. -/
def zoneDataT (φ : ℂ → ℂ) (D : Set ℂ) (ψ : ℂ → ℂ) (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (b : ℝ≥0) : ZW where
  T := fun x : ℝ => chartPt φ D (x : ℂ)
  a₂ := baseL β b
  b₂ := baseR α a
  a₁ := baseL β b
  b₁ := baseR α a
  L₂ := ⨆ n : ℕ, chartPt φ D ((baseL β b - 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  M₂ := 0
  R₂ := junction ψ β b (chartPt φ D (α a))
  L₁ := junction ψ β b (chartPt φ D (α a))
  M₁ := chartPt φ D (α a)
  R₁ := ⨅ n : ℕ, chartPt φ D ((baseR α a + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)

/-! ### The measurable inputs -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

/-- The chart inverse at a real point, on the chart event (`0` off it). -/
def invR (d : RetData Ω) (x : ℝ) (ω : Ω) : ℂ := d.E.indicator (fun ω => d.inv ω (x : ℂ)) ω

/-- The chart point of the first tip, on the tip event (`0` off it). -/
def M₁M (d : RetData Ω) (ω : Ω) : ℝ := (tipEv d).indicator (fun ω => chartPt (d.fwd ω) (d.D ω) (d.η₁ ω d.u)) ω

/-- The event on which the rational `q` is a chart point in `(0, M₁)` with image on the second prefix. -/
def jEv (d : RetData Ω) (q : ℚ) : Set Ω :=
  d.E ∩ {ω | 0 < (q : ℝ) ∧ (q : ℝ) < M₁M d ω} ∩ {ω | invR d q ω ∈ d.η₂ ω '' Icc 0 d.r}

/-- The measurable junction. -/
def JM (d : RetData Ω) (ω : Ω) : ℝ := ⨆ q : ℚ, (jEv d q).indicator (fun _ => (q : ℝ)) ω

/-- **The measurable word of a touching pair**: the word builder with every input read on its event. -/
def wordT (d : RetData Ω) (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) (ω : Ω) : BoundaryWord :=
  zbuild c₀ g₁ g₂ g₃ g₄ (cntLt c₀ (A₂ d ω)) (cntLe c₀ (B₁ d ω)) (cntLt c₀ (A₂ d ω)) (cntLe c₀ (B₁ d ω))
    (fun i => Tpt d (fun _ => c₀.2.1 i) ω)
    (⨆ n : ℕ, Tpt d (fun ω => A₂ d ω - 1 / ((n : ℝ) + 1)) ω)
    (JM d ω) (JM d ω) (M₁M d ω)
    (⨅ n : ℕ, Tpt d (fun ω => B₁ d ω + 1 / ((n : ℝ) + 1)) ω)

variable (hd : d.IsMeasGood)
include hd

/-- **The chart inverse at a real point is measurable** on the chart event: it is the limit of the inverse at the
interior points `x + i/(n + 1)` (continuity of `ψ` on `ℍ̄`), each measurable (`Lemma72B.measurable_inv_apply`). -/
theorem measurable_invR (x : ℝ) : Measurable (invR d x) := by
  obtain ⟨hdom, hfwd, -⟩ := hd.chart_measurability
  set w : ℕ → ℂ := fun n => (x : ℂ) + I / ((n : ℂ) + 1) with hw
  have hwH : ∀ n, w n ∈ H := fun n => by
    show (0 : ℝ) < ((x : ℂ) + I / ((n : ℂ) + 1)).im
    have e : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e, add_im, ofReal_im, zero_add, div_ofReal_im, I_im]
    positivity
  have hn : ∀ n : ℕ, Measurable (d.E.indicator fun ω => d.inv ω (w n)) := by
    intro n
    have hm := Sec7.Lemma72B.measurable_inv_apply hd.isConformal_chart hdom hfwd (hwH n)
    have e : (d.E.indicator fun ω => d.inv ω (w n)) = d.E.indicator fun ω => (d.chart ω).2.1 (w n) :=
      indicator_congr fun ω hω => by rw [RetData.chart_of_mem hω]
    rw [e]
    exact hm.indicator hd.measurableSet_E
  have hseq : Tendsto w atTop (𝓝[Hbar] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => show (0 : ℝ) ≤ (w n).im from (hwH n).le⟩
    have h1 : Tendsto (fun n : ℕ => I / ((n : ℂ) + 1)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
      have h3 := h2.const_mul I
      rw [mul_zero] at h3
      exact h3.congr fun n => by ring
    have h4 := (tendsto_const_nhds (x := (x : ℂ))).add h1
    rw [add_zero] at h4
    exact h4
  refine measurable_of_tendsto_metrizable hn (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ d.E
  · simp only [invR, indicator_of_mem hω]
    have hψc := (hd.isRetChart hω).2.continuousOn_inv
    have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
    exact ((hψc _ hxH).tendsto).comp hseq
  · simp only [invR, indicator_of_notMem hω]
    exact tendsto_const_nhds

theorem measurable_M₁M : Measurable (M₁M d) :=
  measurable_indicator_chartPt hd (measurableSet_tipEv hd) (hd.meas₁ d.u) fun _ hω => tipEv_spec hd hω

theorem measurableSet_jEv (q : ℚ) : MeasurableSet (jEv d q) := by
  have h1 : MeasurableSet {ω | 0 < (q : ℝ) ∧ (q : ℝ) < M₁M d ω} :=
    (MeasurableSet.const _).inter (measurableSet_lt measurable_const (measurable_M₁M hd))
  have h2 := measurableSet_inter_exists_eq hd.measurableSet_E hd.meas₂ (f₂ := fun ω (_ : ℝ≥0) => invR d q ω)
    (fun _ => measurable_invR hd q) (c₁ := fun _ => d.r) (c₂ := fun _ => 0) measurable_const measurable_const
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact cont₂ hd ω hω) (fun _ _ => continuousOn_const)
  have heq : jEv d q = (d.E ∩ {ω | ∃ s ≤ d.r, ∃ t ≤ (0 : ℝ≥0), d.η₂ ω s = invR d q ω}) ∩
      {ω | 0 < (q : ℝ) ∧ (q : ℝ) < M₁M d ω} := by
    ext ω
    simp only [jEv, mem_inter_iff, mem_ofPred_eq, mem_image, mem_Icc]
    constructor
    · rintro ⟨⟨hω, hq⟩, s, hs, he⟩
      exact ⟨⟨hω, s, hs.2, 0, le_rfl, he⟩, hq⟩
    · rintro ⟨⟨hω, s, hs, -, -, he⟩, hq⟩
      exact ⟨⟨hω, hq⟩, s, ⟨zero_le, hs⟩, he⟩
  rw [heq]
  exact h2.inter h1

theorem measurable_JM : Measurable (JM d) :=
  Measurable.iSup fun q => measurable_const.indicator (measurableSet_jEv hd q)

/-- **The measurable word of a touching pair is measurable.** -/
theorem measurable_wordT (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) : Measurable (wordT d c₀ g₁ g₂ g₃ g₄) := by
  have hK : Measurable fun ω => (cntLt c₀ (A₂ d ω), cntLe c₀ (B₁ d ω), cntLt c₀ (A₂ d ω), cntLe c₀ (B₁ d ω)) :=
    ((measurable_cntLt c₀).comp (measurable_A₂ hd)).prodMk (((measurable_cntLe c₀).comp (measurable_B₁ hd)).prodMk
      (((measurable_cntLt c₀).comp (measurable_A₂ hd)).prodMk ((measurable_cntLe c₀).comp (measurable_B₁ hd))))
  have hTp : ∀ i, Measurable (Tpt d (fun _ => c₀.2.1 i)) := fun i => measurable_Tpt hd measurable_const
  have hL₂ : Measurable fun ω => ⨆ n : ℕ, Tpt d (fun ω => A₂ d ω - 1 / ((n : ℝ) + 1)) ω :=
    Measurable.iSup fun n => measurable_Tpt hd ((measurable_A₂ hd).sub_const _)
  have hJ := measurable_JM hd
  have hM₁ := measurable_M₁M hd
  have hR₁ : Measurable fun ω => ⨅ n : ℕ, Tpt d (fun ω => B₁ d ω + 1 / ((n : ℝ) + 1)) ω :=
    Measurable.iInf fun n => measurable_Tpt hd ((measurable_B₁ hd).add_const _)
  have h1 : Measurable fun ω => (wordT d c₀ g₁ g₂ g₃ g₄ ω).1 :=
    (measurable_of_countable fun k : ℕ × ℕ × ℕ × ℕ => k.1 + 3 + (k.2.2.1 - k.2.1) + 3 + (c₀.1 - k.2.2.2)).comp hK
  have h2 : Measurable fun ω => (wordT d c₀ g₁ g₂ g₃ g₄ ω).2.1 := by
    refine measurable_pi_iff.2 fun i => ?_
    have hF : Measurable fun p : Ω × (ℕ × ℕ × ℕ × ℕ) =>
        (zbuild c₀ g₁ g₂ g₃ g₄ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 (fun j => Tpt d (fun _ => c₀.2.1 j) p.1)
          (⨆ n : ℕ, Tpt d (fun ω => A₂ d ω - 1 / ((n : ℝ) + 1)) p.1) (JM d p.1) (JM d p.1) (M₁M d p.1)
          (⨅ n : ℕ, Tpt d (fun ω => B₁ d ω + 1 / ((n : ℝ) + 1)) p.1)).2.1 i :=
      measurable_from_prod_countable_left fun k =>
        measurable_zbuild_pos c₀ g₁ g₂ g₃ g₄ k.1 k.2.1 k.2.2.1 k.2.2.2 hTp hL₂ hJ hJ hM₁ hR₁ i
    exact hF.comp (measurable_id.prodMk hK)
  have h3 : Measurable fun ω => (wordT d c₀ g₁ g₂ g₃ g₄ ω).2.2 := by
    refine measurable_pi_iff.2 fun j => ?_
    exact (measurable_of_countable fun k : ℕ × ℕ × ℕ × ℕ =>
      (zbuild c₀ g₁ g₂ g₃ g₄ k.1 k.2.1 k.2.2.1 k.2.2.2 (fun _ => 0) 0 0 0 0 0).2.2 j).comp hK
  exact h1.prodMk (h2.prodMk h3)

end Meas

/-! ### The measurable word at a touching pair -/

section Eq

variable {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} {z : ZW}

/-- **Outer-zone real points are adherent to the active domain**: `x = ψ(T x)` with `T x` real, and `ψ` maps `ℍ` onto
the domain and is continuous on `ℍ̄`. -/
theorem mem_closure_of_touchZone (ht : IsTouchZones α a β b ψ z) (hC : IsRetChart α a β b φ ψ lift)
    (h0₂ : (β 0).im = 0) {x : ℝ} (hx : x < z.a₂ ∨ z.b₁ < x) :
    ((x : ℝ) : ℂ) ∈ closure (activeDomain α a β b) := by
  rw [← ht.T_spec x hx, ← (hC.bijOn h0₂).image_eq]
  have hTbar : ((z.T x : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((z.T x : ℝ) : ℂ).im by simp
  have hT : ((z.T x : ℝ) : ℂ) ∈ closure H := by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hTbar
  have hcw : ContinuousWithinAt ψ H ((z.T x : ℝ) : ℂ) :=
    (hC.continuousOn_inv _ hTbar).mono fun w (hw : w ∈ H) => show (0 : ℝ) ≤ w.im from le_of_lt hw
  exact hcw.mem_closure_image hT

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

/-- **The measurable word is the truncated touching word** at a chart event `ω` on which the zone data of paths
`α`, `β` (agreeing with the retained paths on the prefixes) have the outer boundary (OF2) and the first tip is
regular. -/
theorem wordT_eq (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) (h₁ : ∀ s ≤ d.u, d.η₁ ω s = α s)
    (h₂ : ∀ t ≤ d.r, d.η₂ ω t = β t)
    (ht : IsTouchZones α d.u β d.r (d.inv ω)
      (zoneDataT (d.fwd ω) (activeDomain α d.u β d.r) (d.inv ω) α d.u β d.r))
    (htip₁ : α d.u ∈ closure (activeDomain α d.u β d.r)) (htip₂ : α d.u ∉ β '' Icc 0 d.r)
    (htip₃ : ∀ s < d.u, α s ≠ α d.u) {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (g₁ g₂ g₃ g₄ : ℝ) :
    wordT d c₀ g₁ g₂ g₃ g₄ ω =
      ((zoneDataT (d.fwd ω) (activeDomain α d.u β d.r) (d.inv ω) α d.u β d.r).word c₀ g₁ g₂ g₃ g₄).trunc := by
  set z := zoneDataT (d.fwd ω) (activeDomain α d.u β d.r) (d.inv ω) α d.u β d.r with hzdef
  have hz := ht.good
  have hDeq : d.D ω = activeDomain α d.u β d.r := by
    rw [hd.D_of_mem hE]
    exact activeDomain_congr_Icc (fun s hs => h₁ s hs.2) (fun t ht => h₂ t ht.2)
  have hi₁ : d.η₁ ω '' Icc 0 d.u = α '' Icc 0 d.u := image_congr fun s hs => h₁ s hs.2
  have hi₂ : d.η₂ ω '' Icc 0 d.r = β '' Icc 0 d.r := image_congr fun t ht => h₂ t ht.2
  have hC : IsRetChart α d.u β d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
    (Lemma76F.isRetChart_congr h₁ h₂).1 (hd.isRetChart hE).2
  have h0₂ : (β 0).im = 0 := by rw [← h₂ 0 zero_le]; exact h0₂E hd hE
  have hA₂ : A₂ d ω = z.a₂ := by
    simp only [A₂, indicator_of_mem hE, baseL, realSet_congr h₂, hzdef, zoneDataT]
  have hB₁ : B₁ d ω = z.b₁ := by
    simp only [B₁, indicator_of_mem hE, baseR, realSet_congr h₁, hzdef, zoneDataT]
  -- chart points of outer-zone points
  have hTpt : ∀ (xf : Ω → ℝ) (x : ℝ), xf ω = x → (x < z.a₂ ∨ z.b₁ < x) → Tpt d xf ω = z.T x := by
    intro xf x hxf hx
    have hn := ht.notMem_zone x hx
    have hmem : ω ∈ ptEv d xf := by
      refine ⟨⟨hE, ?_⟩, ?_, ?_⟩
      · show ((xf ω : ℝ) : ℂ) ∈ closure (d.D ω)
        rw [hxf, hDeq]; exact mem_closure_of_touchZone ht hC h0₂ hx
      · show ((xf ω : ℝ) : ℂ) ∉ d.η₁ ω '' Icc 0 d.u
        rw [hxf, hi₁]; exact fun h => hn (Or.inl h)
      · show ((xf ω : ℝ) : ℂ) ∉ d.η₂ ω '' Icc 0 d.r
        rw [hxf, hi₂]; exact fun h => hn (Or.inr h)
    simp only [Tpt, indicator_of_mem hmem, hxf, hDeq, hzdef, zoneDataT]
  have hL₂ : (⨆ n : ℕ, Tpt d (fun ω => A₂ d ω - 1 / ((n : ℝ) + 1)) ω) = z.L₂ := by
    simp only [hzdef, zoneDataT]
    refine iSup_congr fun n => hTpt _ _ (by rw [hA₂]; rfl) (Or.inl ?_)
    exact sub_lt_self _ (one_div_succ_pos n)
  have hR₁ : (⨅ n : ℕ, Tpt d (fun ω => B₁ d ω + 1 / ((n : ℝ) + 1)) ω) = z.R₁ := by
    simp only [hzdef, zoneDataT]
    refine iInf_congr fun n => hTpt _ _ (by rw [hB₁]; rfl) (Or.inr ?_)
    exact lt_add_of_pos_right _ (one_div_succ_pos n)
  have hM₁ : M₁M d ω = z.M₁ := by
    have hαa : d.η₁ ω d.u = α d.u := h₁ d.u le_rfl
    have hmem : ω ∈ tipEv d := by
      refine ⟨⟨hE, ?_⟩, ?_, ?_⟩
      · show d.η₁ ω d.u ∈ closure (d.D ω)
        rw [hαa, hDeq]; exact htip₁
      · show d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r
        rw [hαa, hi₂]; exact htip₂
      · intro s hs' he
        rw [h₁ s hs'.le, hαa] at he
        exact htip₃ s hs' he
    simp only [M₁M, indicator_of_mem hmem, hαa, hDeq, hzdef, zoneDataT]
  have hJ : JM d ω = z.R₂ := by
    simp only [JM, hzdef, zoneDataT, junction]
    refine iSup_congr fun q => ?_
    have hinv : invR d q ω = d.inv ω ((q : ℝ) : ℂ) := by simp only [invR, indicator_of_mem hE]
    have hM : M₁M d ω = chartPt (d.fwd ω) (activeDomain α d.u β d.r) (α d.u) := hM₁
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) < chartPt (d.fwd ω) (activeDomain α d.u β d.r) (α d.u) ∧
        d.inv ω ((q : ℝ) : ℂ) ∈ β '' Icc 0 d.r
    · have hmem : ω ∈ jEv d q := by
        refine ⟨⟨hE, hq.1, hM ▸ hq.2.1⟩, ?_⟩
        show invR d q ω ∈ d.η₂ ω '' Icc 0 d.r
        rw [hinv, hi₂]; exact hq.2.2
      rw [indicator_of_mem hmem]
      split_ifs
      rfl
    · have hmem : ω ∉ jEv d q := by
        rintro ⟨⟨-, h1, h2⟩, h3⟩
        have h3' : invR d q ω ∈ d.η₂ ω '' Icc 0 d.r := h3
        rw [hinv, hi₂] at h3'
        exact hq ⟨h1, hM ▸ h2, h3'⟩
      rw [indicator_of_notMem hmem]
      split_ifs
      rfl
  have hJ' : JM d ω = z.L₁ := hJ.trans ht.junction
  -- assemble
  rw [trunc_word_eq_zbuild z c₀ g₁ g₂ g₃ g₄ ht.M₂_eq]
  simp only [wordT, hA₂, hB₁, hL₂, hR₁, hM₁]
  rw [← hJ, ← hJ']
  have hk₂ : z.k₂ c₀ = cntLe c₀ z.b₁ := rfl
  have hk₃ : z.k₃ c₀ = cntLt c₀ z.a₂ := rfl
  rw [hk₂, hk₃]
  refine zbuild_congr (ZW.k₄_le (z := z) (c₀ := c₀)) fun i hi => ?_
  have hiN : i < c₀.1 := by
    rcases hi with hi | ⟨-, hi⟩ | ⟨-, hi⟩
    · exact lt_of_lt_of_le hi (card_filter_le_range _)
    · exact lt_of_lt_of_le hi (card_filter_le_range _)
    · exact hi
  refine hTpt _ _ rfl ?_
  rcases hi with hi | ⟨hi2, hi3⟩ | ⟨hi4, -⟩
  · exact Or.inl ((ZW.lt_k₁_iff (z := z) hc₀ hiN).1 hi)
  · exfalso
    have h3 : c₀.2.1 i < z.a₂ := (ZW.lt_k₁_iff (z := z) hc₀ hiN).1 hi3
    have h2 : i < z.k₂ c₀ := (ZW.lt_k₂_iff (z := z) hc₀ hiN).2 (h3.le.trans hz.a₂_le_b₁)
    rw [hk₂] at h2
    omega
  · refine Or.inr (not_le.1 fun h => ?_)
    have := (ZW.lt_k₄_iff (z := z) hc₀ hiN).2 h
    have e4 : z.k₄ c₀ = cntLe c₀ z.b₁ := rfl
    omega

end Eq

end RetChart

end RLC

end InteractingSLE
