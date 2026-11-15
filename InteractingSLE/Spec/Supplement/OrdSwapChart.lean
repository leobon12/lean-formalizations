/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdFstShift

/-!
# Theorem 1.5's leaf 3: retained data with the two paths exchanged

Packet PROVE-T15-ORDDET6. The retained chart `RetData.chart` of data `d` sits at the SECOND tip `η₂(r)`; the first
continuation is read in it after recentring at the first tip's chart point `tipPos d η₁` (PROVE-T15-ORDDET3). When the
first continuation encloses the second tip, the later chart of `d` does not exist (the second tip is inactive), and the
later line must be read in the chart of the **exchanged** data `e` (`IsSwap d e`: paths and cutoffs exchanged, chart
at the first tip). This file identifies the two readings at a sample of both chart events:

* the recorded union, domain, mapping-out function and canonical lift agree (`IsSwap.K_eq`, `D_eq`, `g_eq`, `lift_eq`);
* the forward limit of the exchanged data is the old one plus `tipPos` (`IsSwap.shift_eq`), so the exchanged forward
  map is the recentred one (`IsSwap.fwd_eq`) and the exchanged inverse is `w ↦ inv (w + tipPos)` on `ℍ̄`
  (`IsSwap.inv_eq`, uniqueness of the inverse on `ℍ` and continuity up to `ℝ`);
* hence the exchanged chart transports like the recentred chart (`IsSwap.chartTransport_eq`), and
* **`isRetMeanIdentOn_swap`** (the swap lemma for the mean identification): a mean identification of `d` by a word
  `β` gives the mean identification of `e`, for the exchanged flow lines, by `shiftW tipPos β` (the capped union and
  its cap are symmetric in the two paths; `OrdDet.chartTransport_recenter_eq_integral`).

`IsSwap.mem_E` is the exchanged chart event at an active, interior first tip off the second prefix;
`isRetMeanIdentOn_apply_swap` reads an exchanged mean identification with capped versions in the original order;
**`exists_isSwap`** constructs exchanged data on the same path versions for two flow lines.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.RLC.OrdSwap

open Supp7 Restart Sec7.Lemma76F

/-- **Exchanged retained data**: `e` is `d` with the two paths and their cutoffs exchanged (its chart sits at the
first tip `η₁(u)` of `d`). The good events are unrelated. -/
structure IsSwap {Ω : Type*} (d e : RetData Ω) : Prop where
  η₁_eq : e.η₁ = d.η₂
  η₂_eq : e.η₂ = d.η₁
  u_eq : e.u = d.r
  r_eq : e.r = d.u

section Chart

variable {Ω : Type*} [MeasurableSpace Ω] {d e : RetData Ω}

omit [MeasurableSpace Ω] in
theorem IsSwap.prefixSet_eq (hs : IsSwap d e) (ω : Ω) :
    Restart.prefixSet (e.η₁ ω) e.u (e.η₂ ω) e.r = Restart.prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := by
  rw [Restart.prefixSet, Restart.prefixSet, hs.η₁_eq, hs.η₂_eq, hs.u_eq, hs.r_eq, union_comm]

omit [MeasurableSpace Ω] in
theorem IsSwap.K_eq (hs : IsSwap d e) {ω : Ω} (hω : ω ∈ d.E) (hω' : ω ∈ e.E) : e.K ω = d.K ω := by
  rw [RetData.K_of_mem hω', RetData.K_of_mem hω, hs.prefixSet_eq]

omit [MeasurableSpace Ω] in
theorem IsSwap.D_eq (hs : IsSwap d e) {ω : Ω} (hω : ω ∈ d.E) (hω' : ω ∈ e.E) : e.D ω = d.D ω := by
  show H \ fillH (e.K ω) = H \ fillH (d.K ω)
  rw [hs.K_eq hω hω']

omit [MeasurableSpace Ω] in
theorem IsSwap.g_eq (hs : IsSwap d e) {ω : Ω} (hω : ω ∈ d.E) (hω' : ω ∈ e.E) : e.g ω = d.g ω := by
  show ConformalImage.mapOut (fillH (e.K ω)) = ConformalImage.mapOut (fillH (d.K ω))
  rw [hs.K_eq hω hω']

omit [MeasurableSpace Ω] in
theorem IsSwap.lift_eq (hs : IsSwap d e) {ω : Ω} (hω : ω ∈ d.E) (hω' : ω ∈ e.E) : e.lift ω = d.lift ω := by
  show (fun z => (canonDerivLog (fillH (e.K ω)) z).im) = fun z => (canonDerivLog (fillH (d.K ω)) z).im
  rw [hs.K_eq hω hω']

/-- **The exchanged forward limit**: the forward limit of the mapping-out function at the first tip is the old one
plus the first tip's chart point. -/
theorem IsSwap.shift_eq (hd : d.IsMeasGood) (he : e.IsMeasGood) (hs : IsSwap d e) {ω : Ω} (hω : ω ∈ d.E)
    (hω' : ω ∈ e.E) : e.shift ω = d.shift ω + tipPos d d.η₁ ω := by
  have hp : e.p ω = d.η₁ ω d.u := by rw [RetData.p_of_mem hω', hs.η₂_eq, hs.r_eq]
  have ht := he.tendsto_shift ω
  have hcl := he.p_mem_closure ω
  rw [hs.g_eq hω hω', hs.D_eq hω hω', hp] at ht
  rw [hs.D_eq hω hω', hp] at hcl
  have : (𝓝[d.D ω] (d.η₁ ω d.u)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hf : Tendsto (d.fwd ω) (𝓝[d.D ω] (d.η₁ ω d.u)) (𝓝 (e.shift ω - d.shift ω)) := ht.sub_const _
  obtain ⟨x, hx⟩ := (hd.isRetChart hω).1
  obtain ⟨y, hy⟩ := (he.isRetChart hω').1
  have htp : tipPos d d.η₁ ω = y - x := by
    rw [tipPos, hf.limUnder_eq, hx, hy, ← ofReal_sub, ofReal_re]
  rw [htp, hx, hy]
  push_cast
  ring

/-- The exchanged forward map is the recentred forward map. -/
theorem IsSwap.fwd_eq (hd : d.IsMeasGood) (he : e.IsMeasGood) (hs : IsSwap d e) {ω : Ω} (hω : ω ∈ d.E)
    (hω' : ω ∈ e.E) : e.fwd ω = fun z => d.fwd ω z - tipPos d d.η₁ ω := by
  funext z
  simp only [RetData.fwd, hs.g_eq hω hω', hs.shift_eq hd he hω hω']
  ring

/-- **The exchanged inverse is the recentred inverse on `ℍ̄`**: on `ℍ` both invert the forward map of the common
domain (`IsRetChart.bijOn`, `fwd_inv`); both are continuous on `ℍ̄ = closure ℍ`. -/
theorem IsSwap.inv_eq (hd : d.IsMeasGood) (he : e.IsMeasGood) (hs : IsSwap d e) {ω : Ω} (hω : ω ∈ d.E)
    (hω' : ω ∈ e.E) : ∀ w ∈ Hbar, e.inv ω w = d.inv ω (w + tipPos d d.η₁ ω) := by
  set τ := tipPos d d.η₁ ω with hτ
  have hCd := (hd.isRetChart hω).2
  have hCe := (he.isRetChart hω').2
  have h0d : (d.η₂ ω 0).im = 0 := (hd.good ω (RetData.E_subset_G hω)).2.2.2.2.2.1
  have h0e : (e.η₂ ω 0).im = 0 := (he.good ω (RetData.E_subset_G hω')).2.2.2.2.2.1
  have hAD : activeDomain (e.η₁ ω) e.u (e.η₂ ω) e.r = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := by
    rw [hs.η₁_eq, hs.η₂_eq, hs.u_eq, hs.r_eq, activeDomain_comm]
  have hH : EqOn (e.inv ω) (fun w => d.inv ω (w + τ)) H := by
    intro w hw
    have h1 : e.inv ω w ∈ activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := hAD ▸ (hCe.bijOn h0e).mapsTo hw
    obtain ⟨v, hv, hve⟩ := (hCd.bijOn h0d).surjOn h1
    have h2 : d.fwd ω (e.inv ω w) = w + τ := by
      have h := hCe.fwd_inv w hw
      rw [hs.fwd_eq hd he hω hω'] at h
      linear_combination h
    have h3 : d.fwd ω (e.inv ω w) = v := by rw [← hve, hCd.fwd_inv v hv]
    show e.inv ω w = d.inv ω (w + τ)
    rw [← hve, ← h3.symm.trans h2]
  have hc : ContinuousOn (fun w => d.inv ω (w + τ)) Hbar :=
    hCd.continuousOn_inv.comp (continuous_id.add continuous_const).continuousOn fun w hw => by
      show (0 : ℝ) ≤ (w + τ).im
      simpa using (show (0 : ℝ) ≤ w.im from hw)
  exact hH.of_subset_closure hCe.continuousOn_inv hc QuantumZipper.H_subset_Hbar
    QuantumZipper.CA.Car.closure_H_eq_Hbar.symm.subset

theorem IsSwap.chart_inv (hd : d.IsMeasGood) (he : e.IsMeasGood) (hs : IsSwap d e) {ω : Ω} (hω : ω ∈ d.E)
    (hω' : ω ∈ e.E) {w : ℂ} (hw : w ∈ Hbar) :
    (e.chart ω).2.1 w = ((d.chart ω).recenter (tipPos d d.η₁ ω)).2.1 w := by
  rw [OrdDet.chart_inv_eq hω', hs.inv_eq hd he hω hω' w hw]
  show _ = (d.chart ω).2.1 (w + _)
  rw [OrdDet.chart_inv_eq hω]

omit [MeasurableSpace Ω] in
theorem IsSwap.chart_lift (hs : IsSwap d e) {ω : Ω} (hω : ω ∈ d.E) (hω' : ω ∈ e.E) (τ : ℝ) :
    (e.chart ω).2.2 = ((d.chart ω).recenter τ).2.2 := by
  rw [OrdDet.chart_lift_eq hω', hs.lift_eq hω hω']
  show _ = (d.chart ω).2.2
  rw [OrdDet.chart_lift_eq hω]

/-- **The exchanged chart transports like the recentred chart.** -/
theorem IsSwap.chartTransport_eq (hd : d.IsMeasGood) (he : e.IsMeasGood) (hs : IsSwap d e) {ω : Ω}
    (hω : ω ∈ d.E) (hω' : ω ∈ e.E) (σ a k : ℝ) (M : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport (he.isConformal_chart ω) σ a k M =
      Chart.chartTransport ((hd.isConformal_chart ω).recenter (tipPos d d.η₁ ω)) σ a k M := by
  set τ := tipPos d d.η₁ ω
  have hc := (hd.isConformal_chart ω).recenter τ
  have hℓ : ContinuousOn ((d.chart ω).recenter τ).2.2 ((d.chart ω).recenter τ).dom := by
    rw [Chart.dom_recenter]
    exact hd.continuousOn_lift_chart ω
  have hinv : ∀ w ∈ H, (e.chart ω).2.1 w = ((d.chart ω).recenter τ).2.1 w := fun w hw =>
    hs.chart_inv hd he hω hω' (QuantumZipper.H_subset_Hbar hw)
  ext φ
  rw [Chart.chartTransport_apply', Chart.chartTransport_apply',
    Chart.liftDist_eq_integral_pushTest (he.isConformal_chart ω) (he.continuousOn_lift_chart ω),
    Chart.liftDist_eq_integral_pushTest hc hℓ, Chart.pushTest_congr hc (he.isConformal_chart ω) hinv φ,
    hs.chart_lift hω hω' τ]

/-- **The exchanged chart event**: at a sample of the exchanged good event where the first tip of `d` is interior,
off the second prefix and adherent to the active domain. -/
theorem IsSwap.mem_E (he : e.IsMeasGood) (hs : IsSwap d e) {ω : Ω} (hG : ω ∈ e.G) (hH : d.η₁ ω d.u ∈ H)
    (hoff : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r)
    (hcl : d.η₁ ω d.u ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r)) : ω ∈ e.E := by
  have hH' : e.η₂ ω e.r ∈ H := by rw [hs.η₂_eq, hs.r_eq]; exact hH
  have hoff' : e.η₂ ω e.r ∉ e.η₁ ω '' Icc 0 e.u := by rw [hs.η₂_eq, hs.r_eq, hs.η₁_eq, hs.u_eq]; exact hoff
  have hE₀ : ω ∈ e.E₀ := ⟨⟨hG, hH'⟩, hoff'⟩
  refine ⟨hE₀, ?_⟩
  have hKc : IsClosed (Restart.prefixSet (e.η₁ ω) e.u (e.η₂ ω) e.r) := by
    have h := (he.isCompact_KOf (fun _ h => h.1.1) ω (F := e.E₀)).isClosed
    rwa [RetData.KOf_of_mem hE₀] at h
  show e.η₂ ω e.r ∈ closure (H \ fillH (e.KOf e.E₀ ω))
  rw [RetData.KOf_of_mem hE₀, ← activeDomain_eq hKc, hs.η₁_eq, hs.η₂_eq, hs.u_eq, hs.r_eq, activeDomain_comm]
  exact hcl

/-- The exchanged chart event at an ordinary pair (for paths agreeing with `d`'s on the prefixes). -/
theorem IsSwap.mem_E_of_ordinary (he : e.IsMeasGood) (hs : IsSwap d e) {ω : Ω} (hG : ω ∈ e.G)
    {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} (ha₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (ha₂ : ∀ t ≤ d.r, d.η₂ ω t = β t)
    (hord : IsOrdinaryRetainedPair α ζ₁ d.u β ζ₂ d.r) : ω ∈ e.E := by
  have e₁ : EqOn (d.η₁ ω) α (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) β (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  refine hs.mem_E he hG ?_ ?_ ?_
  · rw [ha₁ d.u le_rfl]; exact hord.2.2.1
  · rw [ha₁ d.u le_rfl, e₂.image_eq]; exact hord.2.2.2.2.2.1
  · rw [ha₁ d.u le_rfl, activeDomain_congr_Icc e₁ e₂]; exact hord.2.2.2.2.2.2.1

end Chart

/-! ### The swap lemma for the mean identification -/

section Mean

variable {Ω : Type*} [MeasurableSpace Ω] {d e : RetData Ω}

/-- **The swap lemma for the mean identification.** If the word `β` identifies the conditional mean in the chart of
`d` on `O`, then `shiftW τ β` identifies it in the chart of the exchanged data `e`, for the exchanged flow lines, on
`O`, where almost surely on `O` both chart events hold and `τ` is the first tip's chart point. -/
theorem isRetMeanIdentOn_swap {κ : ℝ} {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u₀ : ℂ → ℝ} (hd : d.IsMeasGood) (he : e.IsMeasGood)
    (hs : IsSwap d e) {O : Set Ω} {β : Ω → BoundaryWord} (hm : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O β)
    (τ : Ω → ℝ) (hO : ∀ᵐ ω ∂P, ω ∈ O → ω ∈ d.E ∧ ω ∈ e.E ∧ τ ω = tipPos d d.η₁ ω) :
    IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ he O fun ω => Exist.StagedLaw.BoundaryWord.shiftW (τ ω) (β ω) := by
  intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hg
  have hcap : capR e.u e.r = capR d.u d.r := by
    rw [hs.u_eq, hs.r_eq]
    show d.r + d.u + 1 = d.u + d.r + 1
    rw [add_comm d.r]
  have hU : cstUnion ηc₁ ηc₂ e.u e.r = cstUnion ηc₂ ηc₁ d.u d.r := by
    funext ω
    rw [cstUnion_eq, cstUnion_eq, hs.u_eq, hs.r_eq, union_comm]
  rw [hcap] at ha₁ ha₂
  rw [hU] at hg
  filter_upwards [hm ηc₂ ηc₁ g hc₂ hc₁ hm₂ hm₁ ha₂ ha₁ hg, hO] with ω hω hOω hωO φ
  obtain ⟨hE, hE', hτ⟩ := hOω hωO
  rw [hs.chartTransport_eq hd he hE hE', hτ]
  exact OrdDet.chartTransport_recenter_eq_integral (hd.isConformal_chart ω)
    ((hd.isConformal_chart ω).continuousOn_lift_inv (hd.continuousOn_lift_chart ω)) _ _ (hω hωO) φ

/-- **Reading an exchanged mean identification with the paths in the original order**: a mean identification of
exchanged data `e` (for the exchanged flow lines) applies to capped versions `ηc₁`, `ηc₂` of `η₁`, `η₂` with the cap and
the stopped union of the original data `d` (both are symmetric in the two paths). -/
theorem isRetMeanIdentOn_apply_swap {κ : ℝ} {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u₀ : ℂ → ℝ} {he : e.IsMeasGood} (hs : IsSwap d e) {O : Set Ω}
    {β : Ω → BoundaryWord} (hm : IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ he O β) (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ)
    (g : Ω → DistOn upperHalfPlaneOpens) (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t) (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (Restart.capTime (capR d.u d.r) (ζ₁ ω) t))
    (ha₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (Restart.capTime (capR d.u d.r) (ζ₂ ω) t))
    (hg : LocalSets.IsLocalSetMean (cstUnion ηc₁ ηc₂ d.u d.r) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ O → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (he.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ)
        (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, (β ω).mean z * φ z := by
  have hcap : capR e.u e.r = capR d.u d.r := by
    rw [hs.u_eq, hs.r_eq]
    show d.r + d.u + 1 = d.u + d.r + 1
    rw [add_comm d.r]
  have hU : cstUnion ηc₂ ηc₁ e.u e.r = cstUnion ηc₁ ηc₂ d.u d.r := by
    funext ω
    rw [cstUnion_eq, cstUnion_eq, hs.u_eq, hs.r_eq, union_comm]
  rw [← hcap] at ha₁ ha₂
  rw [← hU] at hg
  exact hm ηc₂ ηc₁ g hc₂ hc₁ hm₂ hm₁ ha₂ ha₁ hg

/-- The mean identification on a smaller event. -/
theorem isRetMeanIdentOn_mono {κ : ℝ} {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u₀ : ℂ → ℝ} {hd : d.IsMeasGood} {O O' : Set Ω}
    {β : Ω → BoundaryWord} (hm : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O β) (hO : O' ⊆ O) :
    IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O' β := by
  intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hg
  filter_upwards [hm ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hg] with ω hω hωO using hω (hO hωO)

end Mean

/-! ### Exchanged data exist -/

section Exist

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Exchanged retained data on the same paths**: for measurable retained data `d` of two flow lines there are
measurable data `e` with `IsSwap d e` (the same path versions, exchanged) and the agreement with the exchanged flow
lines. Its good event is a measurable full-measure part of `d.G` on which `d.η₁` does not visit its tip before `u`
(injectivity of the flow line, Aux. 25). -/
theorem exists_isSwap (hκ : 0 < κ) (hκ4 : κ < 4) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) :
    ∃ e : RetData Ω, e.IsMeasGood ∧ IsSwap d e ∧
      ∀ᵐ ω ∂P, (e.u : ℝ≥0∞) < ζ₂ ω → (e.r : ℝ≥0∞) < ζ₁ ω → ω ∈ e.G ∧
        (∀ s ≤ e.u, e.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ e.r, e.η₂ ω t = η₁ ω t := by
  set Good : Set Ω := {ω | (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω →
    ω ∈ d.G ∧ ∀ t < d.u, d.η₁ ω t ≠ d.η₁ ω d.u} with hGood
  have hae : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hag, Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁]
      with ω hagω hi hu hr
    obtain ⟨hG, a₁, -⟩ := hagω hu hr
    refine ⟨hG, fun t ht he => ?_⟩
    rw [a₁ t ht.le, a₁ d.u le_rfl] at he
    have hle : ∀ s ≤ d.u, (s : ℝ≥0∞) ≤ ζ₁ ω := fun s hs => (ENNReal.coe_le_coe.2 hs).trans hu.le
    exact (ne_of_lt ht) (hi (hle t ht.le) (hle d.u le_rfl) he)
  set G₀ : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hG₀
  have hG₀sub : G₀ ⊆ Good := fun ω hω => by
    by_contra h'
    exact hω (subset_toMeasurable P _ h')
  have hG₀ae : ∀ᵐ ω ∂P, ω ∈ G₀ := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G₀} = toMeasurable P Goodᶜ := by ext ω; simp [hG₀]
    rw [this, measure_toMeasurable]
    exact ae_iff.1 hae
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  refine ⟨⟨G₀ ∩ {ω | (d.u : ℝ≥0∞) < ζ₁ ω} ∩ {ω | (d.r : ℝ≥0∞) < ζ₂ ω}, d.η₂, d.η₁, d.r, d.u⟩,
    ⟨?_, hd.meas₂, hd.meas₁, fun ω hω => ?_⟩, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · exact ((measurableSet_toMeasurable P _).compl.inter (measurableSet_lt measurable_const hζ₁)).inter
      (measurableSet_lt measurable_const hζ₂)
  · obtain ⟨hG, hne⟩ := hG₀sub hω.1.1 hω.1.2 hω.2
    obtain ⟨c₁, c₂, m₁, m₂, z₁, z₂, -⟩ := hd.good ω hG
    exact ⟨c₂, c₁, m₂, m₁, z₂, z₁, hne⟩
  · filter_upwards [hG₀ae, hag] with ω hω hagω hr hu
    obtain ⟨-, a₁, a₂⟩ := hagω hu hr
    exact ⟨⟨⟨hω, hu⟩, hr⟩, a₂, a₁⟩

end Exist

end InteractingSLE.RLC.OrdSwap
