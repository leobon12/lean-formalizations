/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopProcEnds

/-!
# The end points of the retained union in the chart of retained data

Packet PROVE-T15-ASTOP-PROC (item 3 of `AStopSourceInputs`). For retained data `d`:

* `touchEv d` (the prefixes meet, on the chart event) and `retEnds d ω : OrdModel.Ends`, the four chart end points
  `(L₂, R₂, L₁, R₁)` read by countable suprema/infima of chart points of real points (the measurable zone functionals
  of Lemma 7.6, `Sec7.Lemma76G.Tpt`; at a touching pair `R₂ = L₁` is the measurable junction `RetChart.JM`);
* **`measurable_retEnds`**: `retEnds d` is measurable for every measurable space in which `d` is measurable good data;
* **`retEnds_eq_of_setting`** / **`retEnds_eq_of_touch`**: at a disjoint (Lemma 7.6's `IsSetting`) or touching
  (Aux. 85's `IsTouchZones`) chart sample, `retEnds d ω` are the zone end points (the proofs of
  `Lemma76G.wordM_eq_of_setting` and `RetChart.wordT_eq`, restricted to the end points).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Supp7 Sec7 Sec7.Lemma76G RetChart RetTouch OrdModel

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The touching event**: the chart event on which the two prefixes meet. -/
def touchEv (d : RetData Ω) : Set Ω := d.E ∩ {ω | ∃ s ≤ d.u, ∃ t ≤ d.r, d.η₁ ω s = d.η₂ ω t}

/-- The left end of the second prefix's chart interval (`sup T(a₂⁻)`). -/
def endL₂ (d : RetData Ω) (ω : Ω) : ℝ := ⨆ n : ℕ, Tpt d (fun ω => A₂ d ω - 1 / ((n : ℝ) + 1)) ω

/-- The right end of the second prefix's chart interval at a disjoint pair (`inf T(b₂⁺)`). -/
def endR₂ (d : RetData Ω) (ω : Ω) : ℝ :=
  ⨅ n : ℕ, Tpt d (fun ω => B₂ d ω + (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) ω

/-- The left end of the first prefix's chart interval at a disjoint pair (`sup T(a₁⁻)`). -/
def endL₁ (d : RetData Ω) (ω : Ω) : ℝ :=
  ⨆ n : ℕ, Tpt d (fun ω => A₁ d ω - (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) ω

/-- The right end of the first prefix's chart interval (`inf T(b₁⁺)`). -/
def endR₁ (d : RetData Ω) (ω : Ω) : ℝ := ⨅ n : ℕ, Tpt d (fun ω => B₁ d ω + 1 / ((n : ℝ) + 1)) ω

open scoped Classical in
/-- **The chart end points of the retained union** `(L₂, R₂, L₁, R₁)`; at a touching pair `R₂ = L₁` is the junction. -/
def retEnds (d : RetData Ω) (ω : Ω) : Ends :=
  if ω ∈ touchEv d then (endL₂ d ω, JM d ω, JM d ω, endR₁ d ω)
  else (endL₂ d ω, endR₂ d ω, endL₁ d ω, endR₁ d ω)

variable {d : RetData Ω}

theorem measurableSet_touchEv (hd : d.IsMeasGood) : MeasurableSet (touchEv d) :=
  measurableSet_inter_exists_eq hd.measurableSet_E hd.meas₁ hd.meas₂ (c₁ := fun _ => d.u) (c₂ := fun _ => d.r)
    measurable_const measurable_const (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact cont₁ hd ω hω)
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact cont₂ hd ω hω)

/-- **The chart end points are measurable.** -/
theorem measurable_retEnds (hd : d.IsMeasGood) : Measurable (retEnds d) := by
  classical
  have hL₂ : Measurable (endL₂ d) :=
    Measurable.iSup fun n => measurable_Tpt hd ((measurable_A₂ hd).sub_const _)
  have hR₂ : Measurable (endR₂ d) := Measurable.iInf fun n => measurable_Tpt hd
    ((measurable_B₂ hd).add (((measurable_A₁ hd).sub (measurable_B₂ hd)).div_const _))
  have hL₁ : Measurable (endL₁ d) := Measurable.iSup fun n => measurable_Tpt hd
    ((measurable_A₁ hd).sub (((measurable_A₁ hd).sub (measurable_B₂ hd)).div_const _))
  have hR₁ : Measurable (endR₁ d) :=
    Measurable.iInf fun n => measurable_Tpt hd ((measurable_B₁ hd).add_const _)
  have hJ := measurable_JM hd
  exact Measurable.ite (measurableSet_touchEv hd) (hL₂.prodMk (hJ.prodMk (hJ.prodMk hR₁)))
    (hL₂.prodMk (hR₂.prodMk (hL₁.prodMk hR₁)))

/-- **At a disjoint chart sample the end points are Lemma 7.6's zone end points.** -/
theorem retEnds_eq_of_setting (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    {x₁ x₂ : ℝ} {ψ' : ℂ → ℂ} {lift' : ℂ → ℝ} (hs : IsSetting α ζ₁ x₁ d.u β ζ₂ x₂ d.r (d.fwd ω) ψ' lift')
    (h₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (h₂ : ∀ t ≤ d.r, d.η₂ ω t = β t) :
    retEnds d ω = ((zoneData (d.fwd ω) α d.u β d.r).L₂, (zoneData (d.fwd ω) α d.u β d.r).R₂,
      (zoneData (d.fwd ω) α d.u β d.r).L₁, (zoneData (d.fwd ω) α d.u β d.r).R₁) := by
  classical
  set z := zoneData (d.fwd ω) α d.u β d.r with hzdef
  have hz := hs.zoneData_good
  have hDeq : d.D ω = activeDomain α d.u β d.r := by
    rw [hd.D_of_mem hE]
    exact activeDomain_congr_Icc (fun s hs => h₁ s hs.2) (fun t ht => h₂ t ht.2)
  have hi₁ : d.η₁ ω '' Icc 0 d.u = α '' Icc 0 d.u := image_congr fun s hs => h₁ s hs.2
  have hi₂ : d.η₂ ω '' Icc 0 d.r = β '' Icc 0 d.r := image_congr fun t ht => h₂ t ht.2
  have hnt : ω ∉ touchEv d := by
    rintro ⟨-, s, hs', t, ht', he⟩
    refine Set.disjoint_left.1 hs.disj ⟨s, ⟨zero_le, hs'⟩, rfl⟩ ?_
    rw [← h₁ s hs', he, h₂ t ht']
    exact ⟨t, ⟨zero_le, ht'⟩, rfl⟩
  have hA₂ : A₂ d ω = z.a₂ := by
    simp only [A₂, indicator_of_mem hE, baseL, realSet_congr h₂, hzdef, zoneData]
  have hB₂ : B₂ d ω = z.b₂ := by
    simp only [B₂, indicator_of_mem hE, baseR, realSet_congr h₂, hzdef, zoneData]
  have hA₁ : A₁ d ω = z.a₁ := by
    simp only [A₁, indicator_of_mem hE, baseL, realSet_congr h₁, hzdef, zoneData]
  have hB₁ : B₁ d ω = z.b₁ := by
    simp only [B₁, indicator_of_mem hE, baseR, realSet_congr h₁, hzdef, zoneData]
  have hTpt : ∀ (xf : Ω → ℝ) (x : ℝ), xf ω = x → IsUntouched α d.u β d.r x → Tpt d xf ω = z.T x := by
    intro xf x hxf hx
    have hmem : ω ∈ ptEv d xf := by
      refine ⟨⟨hE, ?_⟩, ?_, ?_⟩
      · show ((xf ω : ℝ) : ℂ) ∈ closure (d.D ω)
        rw [hxf, hDeq]; exact hx.2
      · show ((xf ω : ℝ) : ℂ) ∉ d.η₁ ω '' Icc 0 d.u
        rw [hxf, hi₁]; exact fun h => hx.1 (Or.inl h)
      · show ((xf ω : ℝ) : ℂ) ∉ d.η₂ ω '' Icc 0 d.r
        rw [hxf, hi₂]; exact fun h => hx.1 (Or.inr h)
    simp only [Tpt, indicator_of_mem hmem, hxf, hDeq, hzdef, zoneData]
  have hzone := fun x hx => hs.untouched_of_zone (φ := d.fwd ω) (x := x) hx
  have hL₂ : endL₂ d ω = z.L₂ := by
    have := congrArg ZW.L₂ hs.zoneDataM_eq
    simp only [zoneDataM] at this
    rw [hzdef, ← this]
    refine iSup_congr fun n => hTpt _ _ (by rw [hA₂]; rfl) (hzone _ (Or.inl ?_))
    exact sub_lt_self _ (one_div_succ_pos n)
  have hc : 0 < z.a₁ - z.b₂ := sub_pos.2 hz.b₂_lt_a₁
  have hR₂ : endR₂ d ω = z.R₂ := by
    have := congrArg ZW.R₂ hs.zoneDataM_eq
    simp only [zoneDataM] at this
    rw [hzdef, ← this]
    refine iInf_congr fun n => hTpt _ _ (by rw [hA₁, hB₂]; rfl) (hzone _ (Or.inr (Or.inl ?_)))
    exact ⟨lt_add_of_pos_right _ (div_succ_succ_pos hc n), lt_sub_iff_add_lt'.1 (div_succ_succ_lt hc n)⟩
  have hL₁ : endL₁ d ω = z.L₁ := by
    have := congrArg ZW.L₁ hs.zoneDataM_eq
    simp only [zoneDataM] at this
    rw [hzdef, ← this]
    refine iSup_congr fun n => hTpt _ _ (by rw [hA₁, hB₂]; rfl) (hzone _ (Or.inr (Or.inl ?_)))
    exact ⟨lt_sub_comm.2 (div_succ_succ_lt hc n), sub_lt_self _ (div_succ_succ_pos hc n)⟩
  have hR₁ : endR₁ d ω = z.R₁ := by
    have := congrArg ZW.R₁ hs.zoneDataM_eq
    simp only [zoneDataM] at this
    rw [hzdef, ← this]
    refine iInf_congr fun n => hTpt _ _ (by rw [hB₁]; rfl) (hzone _ (Or.inr (Or.inr ?_)))
    exact lt_add_of_pos_right _ (one_div_succ_pos n)
  simp only [retEnds, hnt, ↓reduceIte, hL₂, hR₂, hL₁, hR₁]

/-- **At a touching chart sample the end points are Aux. 85's zone end points** (`R₂ = L₁` the junction). -/
theorem retEnds_eq_of_touch (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {α β : ℝ≥0 → ℂ}
    (h₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (h₂ : ∀ t ≤ d.r, d.η₂ ω t = β t)
    (ht : IsTouchZones α d.u β d.r (d.inv ω)
      (zoneDataT (d.fwd ω) (activeDomain α d.u β d.r) (d.inv ω) α d.u β d.r))
    (htip₁ : α d.u ∈ closure (activeDomain α d.u β d.r)) (htip₂ : α d.u ∉ β '' Icc 0 d.r)
    (htip₃ : ∀ s < d.u, α s ≠ α d.u) (htouch : ¬ Disjoint (α '' Icc 0 d.u) (β '' Icc 0 d.r)) :
    retEnds d ω = ((zoneDataT (d.fwd ω) (activeDomain α d.u β d.r) (d.inv ω) α d.u β d.r).L₂,
      (zoneDataT (d.fwd ω) (activeDomain α d.u β d.r) (d.inv ω) α d.u β d.r).R₂,
      (zoneDataT (d.fwd ω) (activeDomain α d.u β d.r) (d.inv ω) α d.u β d.r).L₁,
      (zoneDataT (d.fwd ω) (activeDomain α d.u β d.r) (d.inv ω) α d.u β d.r).R₁) := by
  classical
  set z := zoneDataT (d.fwd ω) (activeDomain α d.u β d.r) (d.inv ω) α d.u β d.r with hzdef
  have hDeq : d.D ω = activeDomain α d.u β d.r := by
    rw [hd.D_of_mem hE]
    exact activeDomain_congr_Icc (fun s hs => h₁ s hs.2) (fun t ht => h₂ t ht.2)
  have hi₁ : d.η₁ ω '' Icc 0 d.u = α '' Icc 0 d.u := image_congr fun s hs => h₁ s hs.2
  have hi₂ : d.η₂ ω '' Icc 0 d.r = β '' Icc 0 d.r := image_congr fun t ht => h₂ t ht.2
  have hC : IsRetChart α d.u β d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
    (Lemma76F.isRetChart_congr h₁ h₂).1 (hd.isRetChart hE).2
  have h0₂ : (β 0).im = 0 := by rw [← h₂ 0 zero_le]; exact h0₂E hd hE
  have htev : ω ∈ touchEv d := by
    refine ⟨hE, ?_⟩
    obtain ⟨p, ⟨s, hs, hps⟩, ⟨t, ht', hpt⟩⟩ := Set.not_disjoint_iff.1 htouch
    exact ⟨s, hs.2, t, ht'.2, by rw [h₁ s hs.2, h₂ t ht'.2, hps, hpt]⟩
  have hA₂ : A₂ d ω = z.a₂ := by
    simp only [A₂, indicator_of_mem hE, baseL, realSet_congr h₂, hzdef, zoneDataT]
  have hB₁ : B₁ d ω = z.b₁ := by
    simp only [B₁, indicator_of_mem hE, baseR, realSet_congr h₁, hzdef, zoneDataT]
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
  have hL₂ : endL₂ d ω = z.L₂ := by
    simp only [endL₂, hzdef, zoneDataT]
    refine iSup_congr fun n => hTpt _ _ (by rw [hA₂]; rfl) (Or.inl ?_)
    exact sub_lt_self _ (one_div_succ_pos n)
  have hR₁ : endR₁ d ω = z.R₁ := by
    simp only [endR₁, hzdef, zoneDataT]
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
  simp only [retEnds, htev, ↓reduceIte, hL₂, hR₁]
  rw [← hJ, ← hJ']

end InteractingSLE.RLC.AStopProc
