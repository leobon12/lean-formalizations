/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCLRestartCond
import InteractingSLE.Spec.Sec7.Lemma76GMeas
import InteractingSLE.Spec.Sec7.Lemma76GOrder
import InteractingSLE.Spec.Sec7.Lemma76FChart
import InteractingSLE.Spec.Supplement.S9DCuts

/-!
# Lemma G8's positivity: the good frame from a small chart gap, measurably in the retained histories

Packet PROVE-RLC-L, second statement: `RLC.G8PositivityStatement` (PROVE-RLC-K, `RLCKDisint.lean`), item (d) of
`planning/handoffs/PROVE-RLC-G.md`. Source: proof of Lemma G8, "Small-gap frames and disintegration" (supplement
pp. 500–501): "For any prescribed `ε > 0`, continuity before the contact and a countable union give fixed rational own
times `s, t` at which the history-measurable good-frame event `0 < v_R − w_α < ε(w_α − w_β)` has positive probability,
with both tips interior and active."

The good frame `IsGoodFrame ε α u β r ψ` is a statement about the chart inverse `ψ` on the whole real line. This file
reduces it to one inequality between two chart points of the canonical forward chart (`retFwd`): the chart point
`T(1)` of the untouched real point `1` (every real point of the retained union lies left of `1`) and the chart point
`w₁ > 0` of the first tip, `T(1) < (1 + ε) w₁` (`IsFrameGap`). That inequality is read from the retained histories by
the measurable chart points of PROVE-LEMMA76G (`Sec7.Lemma76G.Tpt`, the chart point of the first tip), so the
countable union over dyadic cutoffs and the passage to an event of `histSigma d` are proved here:

* **`isGoodFrame_of_gap`** (deterministic): the gap inequality gives the good frame for every chart inverse `ψ`
  (Aux. lemma 60 generalized, `Sec7.Lemma76G.lt_of_inv_mem`: a chart real point beyond `T(1)` cannot lie over the
  retained prefixes or over a real point `≤ 1`, by the order of chart points and the single fibres of regular points);
* `retFwd`, `IsFrameGap`; `G8PathFrameStatement` (**named input**, the pathwise core of G8's positivity: with positive
  probability some dyadic cutoffs give an ordinary retained pair with a small gap — the swallow, the final interior
  approach, GB1 on the relative chain after a late cut, and the joint activity);
* `stopRetData`, `frameEv` (the measurable proxy event of a retained datum), `measurableSet_frameEv`;
* **`g8PositivityStatement_of_pathFrame`**: `G8PositivityStatement` from `G8PathFrameStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart

/-! ### The good frame from a small gap at an untouched real point -/

section Frame

variable {α β : ℝ≥0 → ℂ} {u r : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- **The good frame from the chart points of `1` and of the first tip.** At a retained chart `(φ, ψ)` of
`ℍ \ fill(α[0, u] ∪ β[0, r])`, suppose every real point of the retained union is left of `1`, that `1` is adherent
to the domain, and that the first tip is a regular boundary point (adherent, off the second prefix, not visited
earlier). If the chart point `w₁` of the first tip is positive and the chart point `T(1)` of `1` satisfies
`T(1) < (1 + ε) w₁`, the frame is good: every chart real point beyond `w₁ + ε w₁` lies over a real point `> 1`, which
is off the retained union. -/
theorem isGoodFrame_of_gap {ε : ℝ} (hC : IsRetChart α u β r φ ψ lift) (hc₁ : ContinuousOn α (Icc 0 u))
    (hc₂ : ContinuousOn β (Icc 0 r)) (hH₁ : MapsTo α (Icc 0 u) Hbar) (hH₂ : MapsTo β (Icc 0 r) Hbar)
    (h0₁ : (α 0).im = 0) (h0₂ : (β 0).im = 0)
    (hR : ∀ z ∈ prefixSet α u β r, z.im = 0 → z.re < 1) (h1 : (1 : ℂ) ∈ closure (activeDomain α u β r))
    (htcl : α u ∈ closure (activeDomain α u β r)) (htip : α u ∉ β '' Icc 0 r) (hi : ∀ s < u, α s ≠ α u)
    (hgap : 0 < Sec7.Lemma76G.chartPt φ (activeDomain α u β r) (α u) ∧
      Sec7.Lemma76G.chartPt φ (activeDomain α u β r) 1 <
        (1 + ε) * Sec7.Lemma76G.chartPt φ (activeDomain α u β r) (α u)) :
    IsGoodFrame ε α u β r ψ := by
  have hK := isCompact_prefixSet' hc₁ hc₂
  have hDeq : activeDomain α u β r = H \ fillH (prefixSet α u β r) := activeDomain_eq hK.isClosed
  have hDH : activeDomain α u β r ⊆ H := by rw [hDeq]; exact sdiff_subset
  have h1K : (1 : ℂ) ∉ prefixSet α u β r := fun h => by
    have := hR 1 h (by simp)
    simp at this
  have hoff : ∀ z ∈ prefixSet α u β r, z ∉ H \ fillH (prefixSet α u β r) :=
    fun z hz h => h.2 ⟨h.1, Or.inl (subset_closure hz)⟩
  -- the chart points of `1` and of the first tip
  obtain ⟨w₁, hw₁H, hT₁, hψ₁, hu₁⟩ := hC.exists_tendsto_of_regular h0₂ h1
    (isChartRegularPoint_of_notMem hc₁ hc₂ h0₁ h0₂ h1K)
  obtain ⟨w₀, hw₀H, hT₀, hψ₀, hu₀⟩ := hC.exists_tendsto_of_regular h0₂ htcl
    (Sec7.Lemma76G.isChartRegularPoint_tip₁' hc₁ hc₂ h0₁ h0₂ htip hi)
  have hreal_of : ∀ {w z : ℂ}, w ∈ Hbar → ψ w = z → z ∉ activeDomain α u β r → w = (w.re : ℂ) := by
    intro w z hw hwz hzD
    have him : w.im = 0 := by
      by_contra hne
      have hwH : w ∈ H := lt_of_le_of_ne hw (Ne.symm hne)
      exact hzD (hwz ▸ (hC.bijOn h0₂).mapsTo hwH)
    exact Complex.ext (by simp) (by simp [him])
  have h1D : (1 : ℂ) ∉ activeDomain α u β r := fun h => by
    have := hDH h
    simp [H] at this
  have htD : α u ∉ activeDomain α u β r := by
    rw [hDeq]
    exact hoff _ (Or.inl ⟨u, ⟨zero_le, le_rfl⟩, rfl⟩)
  have hw₁r := hreal_of hw₁H hψ₁ h1D
  have hw₀r := hreal_of hw₀H hψ₀ htD
  have hcp₁ : Sec7.Lemma76G.chartPt φ (activeDomain α u β r) 1 = w₁.re := by
    have : (𝓝[activeDomain α u β r] (1 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 h1
    simp only [Sec7.Lemma76G.chartPt, hT₁.limUnder_eq]
  have hcp₀ : Sec7.Lemma76G.chartPt φ (activeDomain α u β r) (α u) = w₀.re := by
    have : (𝓝[activeDomain α u β r] (α u)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 htcl
    simp only [Sec7.Lemma76G.chartPt, hT₀.limUnder_eq]
  rw [hcp₁, hcp₀] at hgap
  obtain ⟨hw₀pos, hlt⟩ := hgap
  -- the order of chart points against the chart point of `1`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M := hC.2.2.2.2.2.2.2.2.2.1
  have hbij : BijOn ψ H (H \ fillH (prefixSet α u β r)) := hDeq ▸ hC.bijOn h0₂
  have hrealψ : ∀ w ∉ H, ψ w ∉ H \ fillH (prefixSet α u β r) := hDeq ▸ hC.inv_notMem h0₂
  have hψ1 : ψ ((w₁.re : ℝ) : ℂ) ∈ ({(1 : ℂ)} : Set ℂ) := by
    rw [mem_singleton_iff, ← hw₁r]
    exact hψ₁
  have hord : ∀ {Cs : Set ℂ}, IsCompact Cs → IsPreconnected Cs → (∀ z ∈ Cs, 0 ≤ z.im) →
      (∀ z ∈ Cs, z ∉ H \ fillH (prefixSet α u β r)) → (∀ z ∈ Cs, z.im = 0 → z.re < 1) →
      ∀ {x₀ : ℝ}, ((x₀ : ℝ) : ℂ) ∈ Cs → ∀ {y : ℝ}, ψ y ∈ Cs → y < w₁.re := by
    intro Cs hCc hCpc hCim hCD hCx x₀ hx₀ y hy
    have hdisj : Disjoint ({(1 : ℂ)} : Set ℂ) Cs := by
      rw [disjoint_singleton_left]
      intro h
      have := hCx 1 h (by simp)
      simp at this
    exact Sec7.Lemma76G.lt_of_inv_mem hK hC.continuousOn_inv hbij hrealψ hM isCompact_singleton
      isPreconnected_singleton (fun z hz => by rw [mem_singleton_iff.1 hz]; simp)
      (fun z hz h => by rw [mem_singleton_iff.1 hz] at h; exact absurd h.1 (by simp [H]))
      hCc hCpc hCim hCD hdisj (x := 1) (by simp) hCx hx₀ hψ1 hy
  intro w hw y hy
  have hww : (w : ℂ) = w₀ := hu₀ w (ofReal_mem_Hbar w) hw
  have hw_eq : w = w₀.re := by rw [← hww]; simp
  have hy₁ : w₁.re < y := by
    rw [hw_eq] at hy
    nlinarith
  have hψyH : ψ y ∈ Hbar :=
    Sec7.Lemma76E.im_nonneg_of_mapsTo hC.continuousOn_inv
      (fun v hv => hDH ((hC.bijOn h0₂).mapsTo hv)) (ofReal_mem_Hbar y)
  by_cases hyK : ψ y ∈ prefixSet α u β r
  · exfalso
    rcases hyK with hα | hβ
    · have := hord (isCompact_Icc.image_of_continuousOn hc₁) (isPreconnected_Icc.image _ hc₁)
        (fun z ⟨s, hs, hz⟩ => hz ▸ hH₁ hs) (fun z hz => hoff z (Or.inl hz)) (fun z hz => hR z (Or.inl hz))
        (x₀ := (α 0).re) ⟨0, ⟨le_rfl, zero_le⟩, (ofReal_re_eq h0₁).symm⟩ hα
      linarith
    · have := hord (isCompact_Icc.image_of_continuousOn hc₂) (isPreconnected_Icc.image _ hc₂)
        (fun z ⟨s, hs, hz⟩ => hz ▸ hH₂ hs) (fun z hz => hoff z (Or.inr hz)) (fun z hz => hR z (Or.inr hz))
        (x₀ := (β 0).re) ⟨0, ⟨le_rfl, zero_le⟩, (ofReal_re_eq h0₂).symm⟩ hβ
      linarith
  · have hyim : (ψ y).im = 0 := by
      by_contra hne
      exact hyK (inv_mem_prefixSet_of_real hC h0₂ hc₁ hc₂ (lt_of_le_of_ne hψyH (Ne.symm hne)))
    rcases lt_trichotomy (ψ y).re 1 with hlt1 | heq1 | hgt1
    · exfalso
      have := hord (Cs := {ψ y}) isCompact_singleton isPreconnected_singleton
        (fun z hz => by rw [mem_singleton_iff.1 hz]; exact hψyH)
        (fun z hz h => by rw [mem_singleton_iff.1 hz] at h; exact absurd h.1 (by simp [H, hyim]))
        (fun z hz _ => by rw [mem_singleton_iff.1 hz]; exact hlt1)
        (x₀ := (ψ y).re) (by rw [mem_singleton_iff]; exact ofReal_re_eq hyim) (mem_singleton _)
      linarith
    · exfalso
      have h1' : ψ y = 1 := Complex.ext (by simp [heq1]) (by simp [hyim])
      have hyw := hu₁ y (ofReal_mem_Hbar y) h1'
      have : y = w₁.re := by rw [← hyw]; simp
      linarith
    · exact ⟨hyim, by linarith, hyK⟩

end Frame

/-! ### The small gap, and the pathwise core of the positivity -/

/-- **The canonical forward chart of a retained pair**: the mapping-out function of the filled union, shifted by its
limit at the second tip (`RetData.fwd` on the chart event, `fwd_eq_retFwd`). -/
def retFwd (α : ℝ≥0 → ℂ) (u : ℝ≥0) (β : ℝ≥0 → ℂ) (r : ℝ≥0) (z : ℂ) : ℂ :=
  ConformalImage.mapOut (fillH (prefixSet α u β r)) z -
    limUnder (𝓝[activeDomain α u β r] (β r)) (ConformalImage.mapOut (fillH (prefixSet α u β r)))

/-- **A small gap at the untouched point `1`** (the good-frame event of G8's proof, `0 < v_R − w_α < ε(w_α − w_β)`,
read at the untouched real point `1` beyond the junction `v_R`): every real point of the retained union lies left of
`1`, the point `1` is adherent to the domain, and in the canonical chart (second tip at `0`) the chart point `w₁` of the
first tip is positive and the chart point of `1` is less than `(1 + ε) w₁`. -/
def IsFrameGap (ε : ℝ) (α : ℝ≥0 → ℂ) (u : ℝ≥0) (β : ℝ≥0 → ℂ) (r : ℝ≥0) : Prop :=
  (∀ z ∈ prefixSet α u β r, z.im = 0 → z.re < 1) ∧ (1 : ℂ) ∈ closure (activeDomain α u β r) ∧
    0 < Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) (α u) ∧
    Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) 1 <
      (1 + ε) * Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) (α u)

theorem retFwd_congr {α α' β β' : ℝ≥0 → ℂ} {u r : ℝ≥0} (h₁ : EqOn α α' (Icc 0 u)) (h₂ : EqOn β β' (Icc 0 r)) :
    retFwd α u β r = retFwd α' u β' r := by
  unfold retFwd
  rw [prefixSet_congr_Icc h₁ h₂, activeDomain_congr_Icc h₁ h₂, h₂ ⟨zero_le, le_rfl⟩]

theorem isFrameGap_congr {ε : ℝ} {α α' β β' : ℝ≥0 → ℂ} {u r : ℝ≥0} (h₁ : EqOn α α' (Icc 0 u))
    (h₂ : EqOn β β' (Icc 0 r)) : IsFrameGap ε α u β r ↔ IsFrameGap ε α' u β' r := by
  unfold IsFrameGap
  rw [retFwd_congr h₁ h₂, prefixSet_congr_Icc h₁ h₂, activeDomain_congr_Icc h₁ h₂, h₁ ⟨zero_le, le_rfl⟩]

/-- **Named input: the pathwise core of Lemma G8's positivity** (supplement pp. 500–501: "a reference and a
positive-probability swallow", "small-gap frames"). For Proposition 7.4's reference (data `−a` on `ℝ₋`, `C` on `ℝ₊`,
`a = 2λ + θ₂χ`, with its complete ordered pair) and every `ε > 0`: with positive probability there are dyadic own
cutoffs `(u, r)` at which the pair is an ordinary retained pair with a small gap at `1` (`IsFrameGap`). Source route:
the point `1` is swallowed almost surely with a real landing point `q > 1` (`RLCJ.ae_flowLine_swallow_landing`); a
dyadic interior `β`-cut near the seed, off the whole `α` range up to the swallow; the final interior approach of `α`
to `q`; GB1 (`GB1.tendsto_ratio`) on the relative Loewner chain of `α` after a late cut, whose passive
characteristics are the chart points of the `β` tip, of the junction and of `1`; joint activity (Aux. lemma 90,
`Supp9D.aux90`). **Not proved in Lean.** -/
def G8PathFrameStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ C : ℝ, θ₁ < θ₂ →
    -2 < Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) →
    Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) < κ / 2 - 2 →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h (Sec7.prop74Data (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C)
        ((({0} : Finset ℝ)) : Set ℝ) →
    ∀ (α β : Ω → ℝ≥0 → ℂ) (ζα ζβ : Ω → ℝ≥0∞),
      IsFlowLine κ (Sec7.prop74Data (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C) {0} 0 θ₁ P h α ζα →
      IsFlowLine κ (Sec7.prop74Data (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C) {0} 0 θ₂ P h β ζβ →
      (∀ᵐ ω ∂P, ζα ω = ⊤ ∧ ζβ ω = ⊤ ∧ Sec7.Prop74Order.IsCompleteOrderedPair (α ω) (β ω)) →
    ∀ ε : ℝ, 0 < ε → ∃ᵐ ω ∂P, ∃ u ∈ dyadSet, ∃ r ∈ dyadSet,
      IsOrdinaryRetainedPair (α ω) (ζα ω) u (β ω) (ζβ ω) r ∧ IsFrameGap ε (α ω) u (β ω) r

/-! ### The stopped datum and the measurable proxy event -/

section Proxy

variable {Ω : Type*}

/-- The retained datum with both paths stopped at their cutoffs (its paths are the retained histories). -/
def stopRetData (d : RetData Ω) : RetData Ω where
  G := d.G
  η₁ := fun ω t => d.η₁ ω (min t d.u)
  η₂ := fun ω t => d.η₂ ω (min t d.r)
  u := d.u
  r := d.r

theorem stopRetData_eqOn₁ (d : RetData Ω) (ω : Ω) : EqOn ((stopRetData d).η₁ ω) (d.η₁ ω) (Icc 0 d.u) :=
  fun s hs => by simp only [stopRetData, min_eq_left hs.2]

theorem stopRetData_eqOn₂ (d : RetData Ω) (ω : Ω) : EqOn ((stopRetData d).η₂ ω) (d.η₂ ω) (Icc 0 d.r) :=
  fun s hs => by simp only [stopRetData, min_eq_left hs.2]

theorem isRetGood_stopRetData {d : RetData Ω} {ω : Ω} (h : IsRetGood (d.η₁ ω) d.u (d.η₂ ω) d.r) :
    IsRetGood ((stopRetData d).η₁ ω) d.u ((stopRetData d).η₂ ω) d.r := by
  obtain ⟨c₁, c₂, m₁, m₂, z₁, z₂, hne⟩ := h
  have e₁ := stopRetData_eqOn₁ d ω
  have e₂ := stopRetData_eqOn₂ d ω
  refine ⟨c₁.congr e₁, c₂.congr e₂, fun s hs => e₁ hs ▸ m₁ hs, fun s hs => e₂ hs ▸ m₂ hs, ?_, ?_, ?_⟩
  · rw [e₁ ⟨le_rfl, zero_le⟩]; exact z₁
  · rw [e₂ ⟨le_rfl, zero_le⟩]; exact z₂
  · intro t ht
    rw [e₂ ⟨zero_le, ht.le⟩, e₂ ⟨zero_le, le_rfl⟩]
    exact hne t ht

variable [mΩ : MeasurableSpace Ω]

/-- **The stopped datum is measurable for the retained histories.** -/
theorem isMeasGood_stopRetData {d : RetData Ω} (hd : d.IsMeasGood) :
    @RetData.IsMeasGood Ω (histSigma d) (stopRetData d) := by
  have hcm : Measurable[histSigma d] (retHistStop d) :=
    (comap_measurable (retHistStop d)).mono le_sup_left le_rfl
  exact @RetData.IsMeasGood.mk Ω (histSigma d) (stopRetData d)
    ((le_sup_right : MeasurableSpace.generateFrom {d.G} ≤ histSigma d) _
      (MeasurableSpace.measurableSet_generateFrom (mem_singleton _)))
    (fun t => ((measurable_pi_apply t).comp measurable_fst).comp hcm)
    (fun t => ((measurable_pi_apply t).comp measurable_snd).comp hcm)
    (fun ω hω => isRetGood_stopRetData (hd.good ω hω))

/-- The chart point of the first tip, on its regularity event. -/
def tipPt (d : RetData Ω) (ω : Ω) : ℝ :=
  (Sec7.Lemma76G.tipEv d).indicator (fun ω => Sec7.Lemma76G.chartPt (d.fwd ω) (d.D ω) (d.η₁ ω d.u)) ω

/-- **The measurable proxy event of a small gap**: the first tip regular and interior, `1` adherent and off both
prefixes, both prefixes' real bases left of `1`, and the chart-point inequality. -/
def frameEv (d : RetData Ω) (ε : ℝ) : Set Ω :=
  Sec7.Lemma76G.tipEv d ∩ Sec7.Lemma76G.ptEv d (fun _ => 1) ∩ {ω | d.η₁ ω d.u ∈ H} ∩
    {ω | Sec7.Lemma76G.B₁ d ω < 1 ∧ Sec7.Lemma76G.B₂ d ω < 1} ∩
    {ω | 0 < tipPt d ω ∧ Sec7.Lemma76G.Tpt d (fun _ => 1) ω < (1 + ε) * tipPt d ω}

theorem measurable_tipPt {d : RetData Ω} (hd : d.IsMeasGood) : Measurable (tipPt d) :=
  Sec7.Lemma76G.measurable_indicator_chartPt hd (Sec7.Lemma76G.measurableSet_tipEv hd) (hd.meas₁ d.u)
    fun _ hω => Sec7.Lemma76G.tipEv_spec hd hω

theorem measurableSet_frameEv {d : RetData Ω} (hd : d.IsMeasGood) (ε : ℝ) : MeasurableSet (frameEv d ε) := by
  have hT := measurable_tipPt hd
  have h1 := Sec7.Lemma76G.measurable_Tpt hd (x := fun _ => (1 : ℝ)) measurable_const
  refine (((Sec7.Lemma76G.measurableSet_tipEv hd).inter (Sec7.Lemma76G.measurableSet_ptEv hd measurable_const)).inter
    (measurableSet_lt measurable_const (Complex.measurable_im.comp (hd.meas₁ d.u)))).inter
    ((measurableSet_lt (Sec7.Lemma76G.measurable_B₁ hd) measurable_const).inter
      (measurableSet_lt (Sec7.Lemma76G.measurable_B₂ hd) measurable_const)) |>.inter ?_
  exact (measurableSet_lt measurable_const hT).inter (measurableSet_lt h1 (measurable_const.mul hT))

/-- On the chart event the forward chart is the canonical one. -/
theorem fwd_eq_retFwd {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    d.fwd ω = retFwd (d.η₁ ω) d.u (d.η₂ ω) d.r := by
  funext z
  have hp : d.p ω = d.η₂ ω d.r := by simp only [RetData.p, hE, ↓reduceIte]
  simp only [RetData.fwd, RetData.shift, RetData.g, retFwd]
  rw [hp, hd.D_of_mem hE, RetData.K_of_mem hE]

end Proxy


/-! ### The proxy event and the small gap, pathwise -/

section Pathwise

variable {Ω : Type*} [MeasurableSpace Ω]

theorem baseR_lt_one {γ : ℝ≥0 → ℂ} {c : ℝ≥0} (hc : ContinuousOn γ (Icc 0 c)) (h0 : (γ 0).im = 0)
    (h : ∀ x ∈ Sec7.Lemma76G.realSet γ c, x < 1) : Sec7.Lemma76G.baseR γ c < 1 :=
  h _ ((Sec7.Lemma76G.isCompact_realSet' hc).sSup_mem ⟨_, Sec7.Lemma76G.re_zero_mem_realSet h0⟩)

theorem re_lt_one_of_baseR {γ : ℝ≥0 → ℂ} {c : ℝ≥0} (hc : ContinuousOn γ (Icc 0 c))
    (h : Sec7.Lemma76G.baseR γ c < 1) {z : ℂ} (hz : z ∈ γ '' Icc 0 c) (hzi : z.im = 0) : z.re < 1 := by
  have hmem : z.re ∈ Sec7.Lemma76G.realSet γ c := by
    show ((z.re : ℝ) : ℂ) ∈ γ '' Icc 0 c
    rw [ofReal_re_eq hzi]
    exact hz
  exact lt_of_le_of_lt (le_csSup (Sec7.Lemma76G.isCompact_realSet' hc).bddAbove hmem) h

/-- **An ordinary retained pair with a small gap lies in the proxy event** of every retained datum agreeing with it
on the prefixes. -/
theorem mem_frameEv_of_gap {d : RetData Ω} (hd : d.IsMeasGood) {ε : ℝ} {ω : Ω} {α β : ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : ℝ≥0∞} (hG : ω ∈ d.G) (a₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (a₂ : ∀ t ≤ d.r, d.η₂ ω t = β t)
    (hi : Function.Injective α) (hord : IsOrdinaryRetainedPair α ζ₁ d.u β ζ₂ d.r)
    (hgap : IsFrameGap ε α d.u β d.r) : ω ∈ frameEv d ε := by
  have hE := hd.mem_E_of_ordinary hG a₁ a₂ hord
  have e₁ : EqOn (d.η₁ ω) α (Icc 0 d.u) := fun s hs => a₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) β (Icc 0 d.r) := fun t ht => a₂ t ht.2
  have hDD : d.D ω = activeDomain α d.u β d.r := (hd.D_of_mem hE).trans (activeDomain_congr_Icc e₁ e₂)
  have hfwd : d.fwd ω = retFwd α d.u β d.r := (fwd_eq_retFwd hd hE).trans (retFwd_congr e₁ e₂)
  have hαu : d.η₁ ω d.u = α d.u := a₁ _ le_rfl
  have hg := hd.good ω hG
  have h1K : (1 : ℂ) ∉ prefixSet α d.u β d.r := fun h => by
    have := hgap.1 1 h (by simp)
    simp at this
  have htip : ω ∈ Sec7.Lemma76G.tipEv d := by
    refine ⟨⟨hE, ?_⟩, ?_, fun s hs => ?_⟩
    · show d.η₁ ω d.u ∈ closure (d.D ω)
      rw [hαu, hDD]; exact hord.2.2.2.2.2.2.1
    · show d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r
      rw [hαu, e₂.image_eq]; exact hord.2.2.2.2.2.1
    · rw [a₁ s hs.le, hαu]; exact hi.ne hs.ne
  have hpt : ω ∈ Sec7.Lemma76G.ptEv d (fun _ => 1) := by
    refine ⟨⟨hE, ?_⟩, ?_, ?_⟩
    · show ((1 : ℝ) : ℂ) ∈ closure (d.D ω)
      rw [ofReal_one, hDD]; exact hgap.2.1
    · show ((1 : ℝ) : ℂ) ∉ d.η₁ ω '' Icc 0 d.u
      rw [ofReal_one, e₁.image_eq]; exact fun h => h1K (Or.inl h)
    · show ((1 : ℝ) : ℂ) ∉ d.η₂ ω '' Icc 0 d.r
      rw [ofReal_one, e₂.image_eq]; exact fun h => h1K (Or.inr h)
  have hTip : tipPt d ω = Sec7.Lemma76G.chartPt (retFwd α d.u β d.r) (activeDomain α d.u β d.r) (α d.u) := by
    simp only [tipPt, indicator_of_mem htip]
    rw [hfwd, hDD, hαu]
  have hT1 : Sec7.Lemma76G.Tpt d (fun _ => 1) ω =
      Sec7.Lemma76G.chartPt (retFwd α d.u β d.r) (activeDomain α d.u β d.r) 1 := by
    simp only [Sec7.Lemma76G.Tpt, indicator_of_mem hpt]
    rw [hfwd, hDD, ofReal_one]
  refine ⟨⟨⟨⟨htip, hpt⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · show d.η₁ ω d.u ∈ H
    rw [hαu]; exact hord.2.2.1
  · simp only [Sec7.Lemma76G.B₁, indicator_of_mem hE]
    exact baseR_lt_one hg.1 hg.2.2.2.2.1 fun x hx => by
      have hx' : ((x : ℝ) : ℂ) ∈ α '' Icc 0 d.u := by rw [← e₁.image_eq]; exact hx
      simpa using hgap.1 _ (Or.inl hx') (by simp)
  · simp only [Sec7.Lemma76G.B₂, indicator_of_mem hE]
    exact baseR_lt_one hg.2.1 hg.2.2.2.2.2.1 fun x hx => by
      have hx' : ((x : ℝ) : ℂ) ∈ β '' Icc 0 d.r := by rw [← e₂.image_eq]; exact hx
      simpa using hgap.1 _ (Or.inr hx') (by simp)
  · show 0 < tipPt d ω ∧ Sec7.Lemma76G.Tpt d (fun _ => 1) ω < (1 + ε) * tipPt d ω
    rw [hTip, hT1]
    exact hgap.2.2

/-- **The proxy event of the stopped datum gives an ordinary retained pair with a good frame** for the chart inverse
of the original datum, at a sample where the datum agrees with a complete ordered pair on the prefixes. -/
theorem ord_goodFrame_of_mem_frameEv {d : RetData Ω} (hd : d.IsMeasGood) {ε : ℝ} {ω : Ω} {α β : ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : ℝ≥0∞} (hG : ω ∈ d.G) (a₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (a₂ : ∀ t ≤ d.r, d.η₂ ω t = β t)
    (hζ₁ : (d.u : ℝ≥0∞) < ζ₁) (hζ₂ : (d.r : ℝ≥0∞) < ζ₂) (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β)
    (hmem : ω ∈ frameEv (stopRetData d) ε) :
    IsOrdinaryRetainedPair α ζ₁ d.u β ζ₂ d.r ∧ IsGoodFrame ε α d.u β d.r (d.inv ω) := by
  set d' := stopRetData d with hd'def
  have hd'm : d'.IsMeasGood := Sec7.Lemma76F.RetData.IsMeasGood.mono_sigma (isMeasGood_stopRetData hd) (histSigma_le hd)
  obtain ⟨⟨⟨⟨htip, hpt⟩, hH⟩, hB₁, hB₂⟩, hpos, hineq⟩ := hmem
  have hE' : ω ∈ d'.E := htip.1.1
  have e₁ : EqOn (d'.η₁ ω) α (Icc 0 d.u) := fun s hs => (stopRetData_eqOn₁ d ω hs).trans (a₁ s hs.2)
  have e₂ : EqOn (d'.η₂ ω) β (Icc 0 d.r) := fun t ht => (stopRetData_eqOn₂ d ω ht).trans (a₂ t ht.2)
  have hDD : d'.D ω = activeDomain α d.u β d.r := (hd'm.D_of_mem hE').trans (activeDomain_congr_Icc e₁ e₂)
  have hfwd' : d'.fwd ω = retFwd α d.u β d.r := (fwd_eq_retFwd hd'm hE').trans (retFwd_congr e₁ e₂)
  have hαu : d'.η₁ ω d.u = α d.u := e₁ ⟨zero_le, le_rfl⟩
  have hβr : d'.η₂ ω d.r = β d.r := e₂ ⟨zero_le, le_rfl⟩
  have hg := hd'm.good ω hG
  -- the ordinary pair
  have hβH : β d.r ∈ H := by rw [← hβr]; exact hE'.1.1.2
  have hβα : β d.r ∉ α '' Icc 0 d.u := by rw [← hβr, ← e₁.image_eq]; exact hE'.1.2
  have hβcl : β d.r ∈ closure (activeDomain α d.u β d.r) := by
    have h := hd'm.p_mem_closure ω
    have hp : d'.p ω = d'.η₂ ω d'.r := by simp only [RetData.p, hE', ↓reduceIte]
    rw [hp, hDD] at h
    rw [← hβr]; exact h
  have hαH : α d.u ∈ H := by rw [← hαu]; exact hH
  have hαβ : α d.u ∉ β '' Icc 0 d.r := by rw [← hαu, ← e₂.image_eq]; exact htip.2.1
  have hαcl : α d.u ∈ closure (activeDomain α d.u β d.r) := by
    rw [← hαu, ← hDD]; exact htip.1.2
  have hord : IsOrdinaryRetainedPair α ζ₁ d.u β ζ₂ d.r :=
    ⟨hζ₁, hζ₂, hαH, hβH, hβα, hαβ, hαcl, hβcl, hcop.hasOrderedProperCompletions _ _⟩
  refine ⟨hord, ?_⟩
  -- the good frame, for the chart of the original datum
  have hE := hd.mem_E_of_ordinary hG a₁ a₂ hord
  have hC : IsRetChart α d.u β d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
    (Sec7.Lemma76F.isRetChart_congr a₁ a₂).1 (hd.isRetChart hE).2
  have hfwd : d.fwd ω = retFwd α d.u β d.r :=
    (fwd_eq_retFwd hd hE).trans (retFwd_congr (fun s hs => a₁ s hs.2) (fun t ht => a₂ t ht.2))
  have h0₁ : (α 0).im = 0 := by rw [← e₁ ⟨le_rfl, zero_le⟩]; exact hg.2.2.2.2.1
  have h0₂ : (β 0).im = 0 := by rw [← e₂ ⟨le_rfl, zero_le⟩]; exact hg.2.2.2.2.2.1
  have hc₁ : ContinuousOn α (Icc 0 d.u) := hcop.1.continuousOn
  have hc₂ : ContinuousOn β (Icc 0 d.r) := hcop.2.2.2.2.1.continuousOn
  have hR : ∀ z ∈ prefixSet α d.u β d.r, z.im = 0 → z.re < 1 := by
    have hB₁' : Sec7.Lemma76G.baseR α d.u < 1 := by
      have h := hB₁
      simp only [Sec7.Lemma76G.B₁, indicator_of_mem hE'] at h
      rwa [show Sec7.Lemma76G.baseR (d'.η₁ ω) d'.u = Sec7.Lemma76G.baseR α d.u by
        simp only [Sec7.Lemma76G.baseR, Sec7.Lemma76G.realSet]
        rw [show d'.u = d.u from rfl, e₁.image_eq]] at h
    have hB₂' : Sec7.Lemma76G.baseR β d.r < 1 := by
      have h := hB₂
      simp only [Sec7.Lemma76G.B₂, indicator_of_mem hE'] at h
      rwa [show Sec7.Lemma76G.baseR (d'.η₂ ω) d'.r = Sec7.Lemma76G.baseR β d.r by
        simp only [Sec7.Lemma76G.baseR, Sec7.Lemma76G.realSet]
        rw [show d'.r = d.r from rfl, e₂.image_eq]] at h
    rintro z (hz | hz) hzi
    · exact re_lt_one_of_baseR hc₁ hB₁' hz hzi
    · exact re_lt_one_of_baseR hc₂ hB₂' hz hzi
  have h1cl : (1 : ℂ) ∈ closure (activeDomain α d.u β d.r) := by
    have h := hpt.1.2
    simp only [mem_ofPred_eq] at h
    rwa [ofReal_one, hDD] at h
  have hTip : tipPt d' ω = Sec7.Lemma76G.chartPt (retFwd α d.u β d.r) (activeDomain α d.u β d.r) (α d.u) := by
    have hαu' : d'.η₁ ω d'.u = α d.u := hαu
    simp only [tipPt, indicator_of_mem htip]
    rw [hfwd', hDD, hαu']
  have hT1 : Sec7.Lemma76G.Tpt d' (fun _ => 1) ω =
      Sec7.Lemma76G.chartPt (retFwd α d.u β d.r) (activeDomain α d.u β d.r) 1 := by
    simp only [Sec7.Lemma76G.Tpt, indicator_of_mem hpt]
    rw [hfwd', hDD, ofReal_one]
  rw [hTip] at hpos hineq
  rw [hT1] at hineq
  refine isGoodFrame_of_gap hC hc₁ hc₂ (fun s _ => hcop.2.2.1 s) (fun s _ => hcop.2.2.2.2.2.2.1 s) h0₁ h0₂ hR
    h1cl hαcl hαβ (fun s hs => hcop.2.1.ne hs.ne) ?_
  rw [hfwd]
  exact ⟨hpos, hineq⟩

end Pathwise

/-! ### The positivity -/

/-- **Lemma G8's positivity from its pathwise core** (supplement pp. 500–501: "continuity before the contact and a
countable union give fixed rational own times `s, t` at which the history-measurable good-frame event […] has positive
probability"). The countable union over dyadic cutoffs gives one pair `(u, r)` at which an ordinary retained pair with
a small gap has positive probability; for every retained datum `d` at `(u, r)`, the proxy event of its stopped datum
(`frameEv (stopRetData d) ε`) is an event of the retained histories, contains that event almost surely, and on it the
pair is ordinary with a good frame for the chart of `d` (`isGoodFrame_of_gap`). -/
theorem g8PositivityStatement_of_pathFrame (hF : G8PathFrameStatement.{u}) : G8PositivityStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ C hθ hr₁ hr₂ Ω mΩ P hP h hh α β ζα ζβ hα hβ hord ε hε
  have hfr := hF κ hκ hκ4 θ₁ θ₂ C hθ hr₁ hr₂ P h hh α β ζα ζβ hα hβ hord ε hε
  -- one pair of dyadic cutoffs (countable union)
  obtain ⟨u, r, hS⟩ : ∃ u r : ℝ≥0, ∃ᵐ ω ∂P,
      IsOrdinaryRetainedPair (α ω) (ζα ω) u (β ω) (ζβ ω) r ∧ IsFrameGap ε (α ω) u (β ω) r := by
    by_contra hcon
    have h1 : ∀ p q : ℕ × ℕ, ∀ᵐ ω ∂P, ¬ (IsOrdinaryRetainedPair (α ω) (ζα ω) (Sec2.Assembly.dyad p.1 p.2) (β ω) (ζβ ω)
        (Sec2.Assembly.dyad q.1 q.2) ∧
          IsFrameGap ε (α ω) (Sec2.Assembly.dyad p.1 p.2) (β ω) (Sec2.Assembly.dyad q.1 q.2)) :=
      fun p q => Filter.not_frequently.1 fun hf => hcon ⟨_, _, hf⟩
    have h2 := ae_all_iff.2 fun p => ae_all_iff.2 fun q => h1 p q
    refine Filter.not_frequently.2 ?_ hfr
    filter_upwards [h2] with ω hω
    rintro ⟨u, ⟨p, rfl⟩, r, ⟨q, rfl⟩, hS⟩
    exact hω p q hS
  refine ⟨u, r, fun d hd hu hr hag => ?_⟩
  subst hu hr
  have hd' := isMeasGood_stopRetData hd
  have hd'm : (stopRetData d).IsMeasGood := Sec7.Lemma76F.RetData.IsMeasGood.mono_sigma hd' (histSigma_le hd)
  -- the samples where the datum agrees with the complete ordered pair
  have hgood : ∀ᵐ ω ∂P, ζα ω = ⊤ ∧ ζβ ω = ⊤ ∧ Sec7.Prop74Order.IsCompleteOrderedPair (α ω) (β ω) ∧
      ω ∈ d.G ∧ (∀ s ≤ d.u, d.η₁ ω s = α ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = β ω t := by
    filter_upwards [hord, hag] with ω ⟨h1, h2, h3⟩ hω
    obtain ⟨hG, a₁, a₂⟩ := hω (by rw [h1]; exact ENNReal.coe_lt_top) (by rw [h2]; exact ENNReal.coe_lt_top)
    exact ⟨h1, h2, h3, hG, a₁, a₂⟩
  refine ⟨frameEv (stopRetData d) ε, @measurableSet_frameEv Ω (histSigma d) (stopRetData d) hd' ε, ?_, ?_⟩
  · intro h0
    have hnot : ∀ᵐ ω ∂P, ω ∉ frameEv (stopRetData d) ε := measure_eq_zero_iff_ae_notMem.1 h0
    refine Filter.not_frequently.2 ?_ hS
    filter_upwards [hnot, hgood] with ω hω ⟨_, _, hcop, hG, a₁, a₂⟩ hSω
    refine hω (mem_frameEv_of_gap hd'm hG (fun s hs => ?_) (fun t ht => ?_) hcop.2.1 hSω.1 hSω.2)
    · exact (stopRetData_eqOn₁ d ω ⟨zero_le, hs⟩).trans (a₁ s hs)
    · exact (stopRetData_eqOn₂ d ω ⟨zero_le, ht⟩).trans (a₂ t ht)
  · filter_upwards [hgood] with ω ⟨h1, h2, hcop, hG, a₁, a₂⟩ hmem
    exact ord_goodFrame_of_mem_frameEv hd hG a₁ a₂ (by rw [h1]; exact ENNReal.coe_lt_top)
      (by rw [h2]; exact ENNReal.coe_lt_top) hcop hmem

end RLC

end InteractingSLE
