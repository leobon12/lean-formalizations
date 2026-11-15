/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdSlitFst
import InteractingSLE.Spec.Exist.StagedLawData

/-!
# Leaf 3, the first continuation: the charts shifted to the first tip, and Aux. lemma 79 there

Packet PROVE-T15-ORDDET3 (Theorem 1.5's leaf 3, `RLC.RetOrdDetFstStatement`; supplement p. 497, Lemma G7 for the first
current tip; specification Aux. lemma 79, pp. 289–290).

The retained charts of `Supp7.RetData` are centred at the SECOND tip. The first continuation runs from the chart point
`τ` of the first tip, so its K2 is read in the recentred chart `(d.chart ω).recenter τ` (`fwd − τ`, `inv (· + τ)`, same
lift), with the recentred word `shiftW τ β` (`y ↦ β.fn (y + τ)`). This file proves:

* `mean_shiftW`: the word mean of the recentred word is the translate of the word mean;
* **`chartTransport_recenter_apply`**: the transport in a recentred chart is the transport in the original chart tested
  against the translated test function;
* `chartTransport_recenter_eq_flowField`: the transported field in a recentred chart is `Exist.flowField τ 0` of the
  transported field (the translation in which `Supp9.IsFlowLine.recenter` reads a flow line from the seed `τ`);
* **`chartTransport_recenter_eq_integral`**: a mean identification in a chart gives the mean identification of the
  recentred word in the recentred chart (the shifted-chart mean identification);
* **`ae_fn_eq_of_trans_shift`**: Aux. lemma 79 at a later line in charts recentred at arbitrary real points `τ₀`, `τ₁`
  (the shifted form of `OrdDet.ae_fn_eq_of_trans`): if `ψ₁(w + τ₁) = ψ₀(f_Q⁻¹ w + τ₀)` on `ℍ` with the lift chain rule
  (the form `OrdDet.retChart_trans_fst` produces for the first continuation), then at every real point `x` alive at
  `Q`, `β₁((v Q) + τ₁) = β₀(x + τ₀)` off the jumps.

For Theorem 1.5; uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

namespace OrdDet

open Restart Chart

/-! ### Recentred words and recentred charts -/

/-- **The word mean of the recentred word** is the translate of the word mean. -/
theorem mean_shiftW (τ : ℝ) (c : BoundaryWord) (z : ℂ) :
    (Exist.StagedLaw.BoundaryWord.shiftW τ c).mean z = c.mean (z + τ) := by
  simp only [BoundaryWord.mean, Exist.StagedLaw.BoundaryWord.shiftW]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 3
  push_cast
  ring

theorem notMem_jumps_shiftW {τ x : ℝ} {c : BoundaryWord} (hx : x + τ ∉ c.jumps) :
    x ∉ (Exist.StagedLaw.BoundaryWord.shiftW τ c).jumps := by
  rw [Exist.StagedLaw.BoundaryWord.jumps_shiftW]
  intro h
  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 h
  exact hx (by rw [← hjx, sub_add_cancel]; exact hj)

/-- The inverse of the translation chart is the translation. -/
theorem shiftChart_inv (τ : ℝ) (w : ℂ) : (Exist.shiftChart τ).2.1 w = w + τ := rfl

/-- **The transport in a recentred chart** is the transport in the original chart tested against the translated test
function `φ(· − τ)` (`pushTest` of the translation chart). -/
theorem chartTransport_recenter_apply {c : Chart} (hc : c.IsConformal)
    (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H) (τ σ a k : ℝ) (M : DistOn upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) :
    chartTransport (hc.recenter τ) σ a k M φ =
      chartTransport hc σ a k M (pushTest (Exist.isConformal_shiftChart τ) φ) := by
  have hℓ' := continuousOn_recenter_lift (a := τ) hℓ
  rw [chartTransport_apply (hc.recenter τ) (hℓ'.locallyIntegrableOn QuantumZipper.isOpen_H.measurableSet),
    chartTransport_apply hc (hℓ.locallyIntegrableOn QuantumZipper.isOpen_H.measurableSet)]
  have hpush : pushTest (hc.recenter τ) φ = pushTest hc (pushTest (Exist.isConformal_shiftChart τ) φ) := by
    ext z
    rw [coe_pushTest, coe_pushTest, dom_recenter]
    by_cases hz : z ∈ (c.dom : Set ℂ)
    · rw [indicator_of_mem hz, indicator_of_mem hz, Exist.pushTest_shiftChart_apply]
      change ‖deriv (fun z => c.1 z - (τ : ℂ)) z‖ ^ 2 * φ (c.1 z - τ) = _
      rw [deriv_sub_const]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz]
  have hone : ∫ w, pushTest (Exist.isConformal_shiftChart τ) φ w = ∫ w, φ w := by
    have h := integral_mul_pushTest (Exist.isConformal_shiftChart τ) φ (fun _ => (1 : ℝ))
    simp only [one_mul] at h
    exact h
  have hlift : ∫ w, c.2.2 (c.2.1 w) * pushTest (Exist.isConformal_shiftChart τ) φ w =
      ∫ w, (c.recenter τ).2.2 ((c.recenter τ).2.1 w) * φ w :=
    integral_mul_pushTest (Exist.isConformal_shiftChart τ) φ (fun z => c.2.2 (c.2.1 z))
  rw [hpush, hone, hlift]

/-- **The field in a recentred chart is the translated field**: the transport in the chart recentred at `τ` is
`Exist.flowField τ 0` (the field `· (· + τ)`) of the transport in the original chart, the form in which
`Supp9.IsFlowLine.recenter` reads a flow line from the seed `τ`. -/
theorem chartTransport_recenter_eq_flowField {c : Chart} (hc : c.IsConformal)
    (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H) (τ σ a k : ℝ) (M : DistOn upperHalfPlaneOpens) :
    chartTransport (hc.recenter τ) σ a k M = Exist.flowField τ 0 (chartTransport hc σ a k M) := by
  ext φ
  rw [chartTransport_recenter_apply hc hℓ, Exist.flowField_apply, zero_mul, add_zero]

/-- **The shifted-chart mean identification**: if the transport of `M` in the chart `c` is the word mean of `β`, then
its transport in the chart recentred at `τ` is the word mean of the recentred word `shiftW τ β`. -/
theorem chartTransport_recenter_eq_integral {c : Chart} (hc : c.IsConformal)
    (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H) (τ k : ℝ) {M : DistOn upperHalfPlaneOpens} {β : BoundaryWord}
    (hid : ∀ φ : TestOn upperHalfPlaneOpens, chartTransport hc 1 0 k M φ = ∫ w, β.mean w * φ w)
    (φ : TestOn upperHalfPlaneOpens) :
    chartTransport (hc.recenter τ) 1 0 k M φ =
      ∫ w, (Exist.StagedLaw.BoundaryWord.shiftW τ β).mean w * φ w := by
  rw [chartTransport_recenter_apply hc hℓ, hid,
    integral_mul_pushTest (Exist.isConformal_shiftChart τ) φ β.mean]
  simp only [shiftChart_inv, mean_shiftW]

/-! ### Aux. lemma 79 in recentred charts -/

section Trans

open Sec7 Sec7.Lemma76F Supp7 LocalSets RetZone

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

omit mΩ in
theorem chart_lift_eq {e : RetData Ω} {ω : Ω} (he : ω ∈ e.E) : (e.chart ω).2.2 = e.lift ω := by
  rw [RetData.chart_of_mem he]

/-- **Aux. lemma 79 at a later line, in recentred charts** (see the module docstring): `OrdDet.ae_fn_eq_of_trans` with
the two retained charts recentred at arbitrary real points `τ₀`, `τ₁` and the transition `ψ₁(w + τ₁) = ψ₀(f_Q⁻¹ w + τ₀)`
with the lift chain rule. -/
theorem ae_fn_eq_of_trans_shift (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (huu : d.u ≤ d'.u) (hrr : d.r ≤ d'.r) {O₀ O₁ : Set Ω} {β₀ β₁ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' O₁ β₁) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → ω ∈ O₁ → (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.E → ω ∈ d'.E →
      (β₀ ω).IsSorted → (β₁ ω).IsSorted →
      ∀ (τ₀ τ₁ : ℝ) (W : ℝ → ℝ) (Q : ℝ), Continuous W → W 0 = 0 → 0 ≤ Q →
        (∀ w ∈ H, d'.inv ω (w + τ₁) = d.inv ω (fwdMapInv W Q w + τ₀)) →
        (∀ w ∈ H, d'.lift ω (d'.inv ω (w + τ₁)) =
          (logDerivFwd W Q (fwdMapInv W Q w)).im + d.lift ω (d.inv ω (fwdMapInv W Q w + τ₀))) →
        ∀ (x : ℝ) (v : ℝ → ℂ), QuantumZipper.IsForwardSol W x Q v → x + τ₀ ∉ (β₀ ω).jumps →
          (v Q).re + τ₁ ∉ (β₁ ω).jumps → (β₁ ω).fn ((v Q).re + τ₁) = (β₀ ω).fn (x + τ₀) := by
  obtain ⟨ηa₁, ηa₂, hca₁, hca₂, hma₁, hma₂, -, -, haga₁, haga₂, g₀, hg₀, -⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hη₂ hu₀
      (capR d.u d.r) d.u d.r
  obtain ⟨ηb₁, ηb₂, hcb₁, hcb₂, hmb₁, hmb₂, -, -, hagb₁, hagb₂, g₁, hg₁, -⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hη₂ hu₀
      (capR d'.u d'.r) d'.u d'.r
  have hid₀ := hm₀ ηa₁ ηa₂ g₀ hca₁ hca₂ hma₁ hma₂ haga₁ haga₂ hg₀
  have hid₁ := hm₁ ηb₁ ηb₂ g₁ hcb₁ hcb₂ hmb₁ hmb₂ hagb₁ hagb₂ hg₁
  have hnest := ae_tendsto_sub_nested hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ huu hrr (lt_capR_left d.u d.r)
    (lt_capR_right d.u d.r) (lt_capR_left d'.u d'.r) (lt_capR_right d'.u d'.r) hca₁ hca₂ hcb₁ hcb₂ hma₁ hma₂
    hmb₁ hmb₂ haga₁ haga₂ hagb₁ hagb₂ hg₀ hg₁
  filter_upwards [hid₀, hid₁, hnest, hag, hag', hagb₁, hagb₂] with ω hi₀ hi₁ hn hagω hagω' hbω₁ hbω₂
  intro hO₀ hO₁ hu₁ hr₁ hE hE' hs₀ hs₁ τ₀ τ₁ W Q hW hW0 hQ hinvd hliftd x v hv hx hy
  have hu₀' : (d.u : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_le_coe.2 huu).trans_lt hu₁
  have hr₀' : (d.r : ℝ≥0∞) < ζ₂ ω := (ENNReal.coe_le_coe.2 hrr).trans_lt hr₁
  obtain ⟨-, hd₁, hd₂⟩ := hagω hu₀' hr₀'
  obtain ⟨-, hd₁', hd₂'⟩ := hagω' hu₁ hr₁
  obtain ⟨vh, hvh, hvr, hdec⟩ := hn hu₁ hr₁
  have h₀' := hd.isConformal_chart ω
  have h₁' := hd'.isConformal_chart ω
  set c₀ : Chart := (d.chart ω).recenter τ₀ with hc₀
  set c₁ : Chart := (d'.chart ω).recenter τ₁ with hc₁
  have h₀ : c₀.IsConformal := h₀'.recenter τ₀
  have h₁ : c₁.IsConformal := h₁'.recenter τ₁
  have hc₀inv : ∀ w, c₀.2.1 w = d.inv ω (w + τ₀) := fun w => by
    show (d.chart ω).2.1 (w + τ₀) = _
    rw [chart_inv_eq hE]
  have hc₁inv : ∀ w, c₁.2.1 w = d'.inv ω (w + τ₁) := fun w => by
    show (d'.chart ω).2.1 (w + τ₁) = _
    rw [chart_inv_eq hE']
  have hc₀lift : c₀.2.2 = d.lift ω := chart_lift_eq hE
  have hc₁lift : c₁.2.2 = d'.lift ω := chart_lift_eq hE'
  have hinv : ∀ w ∈ H, c₁.2.1 w = c₀.2.1 (fwdMapInv W Q w) := fun w hw => by
    rw [hc₁inv, hc₀inv]; exact hinvd w hw
  have hlift : ∀ w ∈ H, c₁.2.2 (c₁.2.1 w) =
      (logDerivFwd W Q (fwdMapInv W Q w)).im + c₀.2.2 (c₀.2.1 (fwdMapInv W Q w)) := fun w hw => by
    rw [hc₁lift, hc₀lift, hc₁inv, hc₀inv]; exact hliftd w hw
  -- the prefix sets of the data are those of the flow lines
  have hK₀ : prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r = prefixSet (η₁ ω) d.u (η₂ ω) d.r := by
    rw [prefixSet, prefixSet, image_congr fun s hs => hd₁ s hs.2, image_congr fun t ht => hd₂ t ht.2]
  have hK₁ : prefixSet (d'.η₁ ω) d'.u (d'.η₂ ω) d'.r = prefixSet (η₁ ω) d'.u (η₂ ω) d'.r := by
    rw [prefixSet, prefixSet, image_congr fun s hs => hd₁' s hs.2, image_congr fun t ht => hd₂' t ht.2]
  have hg₀G := hd.good ω (RetData.E_subset_G hE)
  have hg₁G := hd'.good ω (RetData.E_subset_G hE')
  have hdom₀ : (c₀.dom : Set ℂ) = H \ fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r) := by
    rw [hc₀, dom_recenter, hd.coe_dom_chart ω, hd.D_of_mem hE,
      activeDomain_eq (isCompact_prefixSet' hg₀G.1 hg₀G.2.1).isClosed, hK₀]
  have hdom₁ : (c₁.dom : Set ℂ) = H \ fillH (prefixSet (η₁ ω) d'.u (η₂ ω) d'.r) := by
    rw [hc₁, dom_recenter, hd'.coe_dom_chart ω, hd'.D_of_mem hE',
      activeDomain_eq (isCompact_prefixSet' hg₁G.1 hg₁G.2.1).isClosed, hK₁]
  -- the later union, read in the capped versions
  have hb₁ : ∀ t ≤ d'.u, ηb₁ ω t = η₁ ω t := eqOn_of_capped hbω₁ hu₁ (lt_capR_left d'.u d'.r)
  have hb₂ : ∀ t ≤ d'.r, ηb₂ ω t = η₂ ω t := eqOn_of_capped hbω₂ hr₁ (lt_capR_right d'.u d'.r)
  have hAω : cstUnion ηb₁ ηb₂ d'.u d'.r ω = prefixSet (η₁ ω) d'.u (η₂ ω) d'.r ∩ H := by
    rw [cstUnion_eq, prefixSet, image_congr fun t ht => hb₁ t ht.2, image_congr fun t ht => hb₂ t ht.2]
  have hoff : ∀ z ∈ (c₁.dom : Set ℂ), z ∈ H \ cstUnion ηb₁ ηb₂ d'.u d'.r ω := by
    intro z hz
    rw [hdom₁] at hz
    refine ⟨hz.1, fun hzA => hz.2 ?_⟩
    rw [hAω] at hzA
    exact mem_fillH_of_mem_closure hzA.2 (subset_closure hzA.1)
  have hback : ∀ w ∈ H \ fwdHull W Q, c₀.2.1 w ∈ (c₁.dom : Set ℂ) := by
    intro w hw
    have hfw : fwdMap W Q w ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hQ hw
    have e := hinv _ hfw
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hQ hw] at e
    rw [← e]
    exact h₁.inv_mem_dom hfw
  have hAt : MapsTo c₀.2.1 (H \ fwdHull W Q) (H \ cstUnion ηb₁ ηb₂ d'.u d'.r ω) :=
    fun w hw => hoff _ (hback w hw)
  have hℓ₀' : ContinuousOn (fun w => (d.chart ω).2.2 ((d.chart ω).2.1 w)) H :=
    (hd.continuousOn_lift_chart ω).comp h₀'.1.continuousOn fun w hw => h₀'.inv_mem_dom hw
  have hℓ₁' : ContinuousOn (fun w => (d'.chart ω).2.2 ((d'.chart ω).2.1 w)) H :=
    (hd'.continuousOn_lift_chart ω).comp h₁'.1.continuousOn fun w hw => h₁'.inv_mem_dom hw
  have hℓ₀ : ContinuousOn (fun w => c₀.2.2 (c₀.2.1 w)) H := continuousOn_recenter_lift hℓ₀'
  have hvr' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cstUnion ηb₁ ηb₂ d'.u d'.r ω →
      (g₁ ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ -
        (g₀ ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, vh z * φ z := by
    intro φ hφ
    rw [← hvr φ hφ, add_apply, add_apply]
    ring
  have hs₀' := Exist.StagedLaw.BoundaryWord.isSorted_shiftW hs₀ τ₀
  have hs₁' := Exist.StagedLaw.BoundaryWord.isSorted_shiftW hs₁ τ₁
  have heq := eqOn_couplingMean_sub_mean (κ := κ) h₀ h₁ hℓ₀ hW hW0 hQ hinv hlift hs₀' hs₁'
    (chartTransport_recenter_eq_integral h₀' hℓ₀' τ₀ _ (hi₀ hO₀))
    (chartTransport_recenter_eq_integral h₁' hℓ₁' τ₁ _ (hi₁ hO₁))
    (cstUnion_relClosed hcb₁ hcb₂ d'.u d'.r ω).2 hAt hvh hvr'
  -- the decay at `x`
  obtain ⟨⟨x₀, hx₀⟩, -⟩ := hd.isRetChart hE
  have hfwd : ∀ z, c₀.1 z =
      ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) z - ((x₀ + τ₀ : ℝ) : ℂ) := by
    intro z
    show (d.chart ω).1 z - τ₀ = _
    rw [RetData.chart_of_mem hE]
    show d.g ω z - d.shift ω - τ₀ = _
    rw [hx₀, RetData.g, RetData.K_of_mem hE, hK₀]
    push_cast
    ring
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hQ hv
  set ρ : ℝ := δ / Real.exp (2 / δ ^ 2 * Q) with hρdef
  have hρ : 0 < ρ := div_pos hδ (Real.exp_pos _)
  have hclr : ∀ z ∈ H \ fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r),
      ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) z ∈ ball ((x + (x₀ + τ₀) : ℝ) : ℂ) ρ →
        z ∉ prefixSet (η₁ ω) d'.u (η₂ ω) d'.r := by
    intro z hz hzb hzK
    rw [← hdom₀] at hz
    set w := c₀.1 z with hw
    have hwH : w ∈ H := h₀.fwd_mem hz
    have hwx : ‖w - x‖ * Real.exp (2 / δ ^ 2 * Q) < δ := by
      rw [mem_ball, dist_eq_norm] at hzb
      have e : w - x = ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) z -
          ((x + (x₀ + τ₀) : ℝ) : ℂ) := by
        rw [hw, hfwd z]; push_cast; ring
      rw [e]
      have := (lt_div_iff₀ (Real.exp_pos (2 / δ ^ 2 * Q))).1 hzb
      linarith
    have hwK : w ∈ H \ fwdHull W Q := ⟨hwH, not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hwH hwx⟩
    have hzw : c₀.2.1 w = z := h₀.inv_fwd hz
    have h1 := hback w hwK
    rw [hzw, hdom₁] at h1
    exact h1.2 (mem_fillH_of_mem_closure h1.1 (subset_closure hzK))
  have hF : Filter.map c₀.2.1 (𝓝[H] (x : ℂ)) ≤ 𝓟 (H \ fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) := by
    rw [← hdom₀, le_principal_iff, mem_map]
    exact Filter.eventually_of_mem self_mem_nhdsWithin fun w hw => h₀.inv_mem_dom hw
  have hT : Tendsto (ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)))
      (Filter.map c₀.2.1 (𝓝[H] (x : ℂ))) (𝓝 ((x + (x₀ + τ₀) : ℝ) : ℂ)) := by
    rw [tendsto_map'_iff]
    have h1 : Tendsto (fun w : ℂ => w + ((x₀ + τ₀ : ℝ) : ℂ)) (𝓝[H] (x : ℂ)) (𝓝 ((x + (x₀ + τ₀) : ℝ) : ℂ)) := by
      have h2 : Tendsto (fun w : ℂ => w + ((x₀ + τ₀ : ℝ) : ℂ)) (𝓝 (x : ℂ)) (𝓝 ((x : ℂ) + ((x₀ + τ₀ : ℝ) : ℂ))) :=
        (continuous_id.add continuous_const).tendsto (x : ℂ)
      rw [ofReal_add x (x₀ + τ₀)]
      exact h2.mono_left (nhdsWithin_le_nhds (s := H))
    refine h1.congr' (Filter.eventually_of_mem self_mem_nhdsWithin fun w hw => ?_)
    show w + ((x₀ + τ₀ : ℝ) : ℂ) =
      ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) (c₀.2.1 w)
    have e := hfwd (c₀.2.1 w)
    rw [h₀.2.2 w hw] at e
    linear_combination e
  have hdec' := hdec (x + (x₀ + τ₀)) ρ hρ hclr _ hF hT
  rw [tendsto_map'_iff] at hdec'
  have hfin := fn_eq_of_tendsto hW hW0 hQ hs₀' hs₁' heq hv (notMem_jumps_shiftW hx) (notMem_jumps_shiftW hy)
    hdec'
  rwa [Exist.StagedLaw.BoundaryWord.fn_shiftW, Exist.StagedLaw.BoundaryWord.fn_shiftW] at hfin

end Trans

end OrdDet

end RLC

end InteractingSLE
