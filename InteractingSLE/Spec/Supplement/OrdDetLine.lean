/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdDetNest
import InteractingSLE.Spec.Supplement.OrdDetTransport
import InteractingSLE.Spec.Supplement.RLCCondDetHistR1

/-!
# Aux. lemma 79 at a later line of a retained pair: the transported word at alive real points

Packet PROVE-T15-ORDDET (Theorem 1.5's leaf 3, `RLC.RetOrdDetStatement`; specification Aux. lemma 79, pp. 289–290). Two
retained data `d` (cutoffs `(u, r)`, the stop line) and `d'` (cutoffs `(u', r') ≥ (u, r)`, a later line) for the same
two flow lines, with words `β₀`, `β₁` identifying the conditional means in the two retained charts
(`IsRetMeanIdentOn`, e.g. from `RetOrdMeanWordStatement` at both pairs). **`ae_fn_eq_of_trans`**: almost surely, at
every sample where both identifications apply and both cutoffs are alive, for every continuous driver `W` and capacity
`Q` for which the later chart is the stop-line chart followed by the centred Loewner map `f_Q` ((III-a)), and every
real point `x` alive at `Q`,

  `β₁(f_Q x) = β₀(x)`   (when `x`, `f_Q x` are not jumps).

This is the word identity (III-b) of the later-line safe law on the old part of the boundary, for every retained pair
(touching or not) and through real contacts of the continuation; it applies to both continuations (`(u, r') ≥ (u, r)`
for the second path, `(u', r) ≥ (u, r)` for the first).

**Proof.** Local-set means `g₀`, `g₁` of the two stopped unions (`exists_cstUnion_marked_of_isFlowLine`); Proposition
3.8 in the stop-line chart for the nested unions (`OrdDet.ae_tendsto_sub_nested`) represents `g₁ − g₀` by a harmonic `v`
decaying at prime ends cleared of the later union; the pathwise conversion `OrdDet.eqOn_couplingMean_sub_mean` and
`OrdDet.fn_eq_of_tendsto`. The cleared ball at an alive `x` is the ball off the hull `K_Q` given by the forward solution
(`not_mem_fwdHull_of_isForwardSol`): its stop-line chart preimages lie in the later active domain by (III-a), hence off
the later union.

For Theorem 1.5; uses Lemma 7.5 (field determination) only (R43/R48).
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

open Sec7 Sec7.Lemma76F Restart Supp7 LocalSets RetZone Chart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Aux. lemma 79 at a later line, for retained data** (see the module docstring). -/
theorem ae_fn_eq_of_trans (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
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
      ∀ (W : ℝ → ℝ) (Q : ℝ), Continuous W → W 0 = 0 → 0 ≤ Q →
        (∀ w ∈ H, (d'.chart ω).2.1 w = (d.chart ω).2.1 (fwdMapInv W Q w)) →
        (∀ w ∈ H, (d'.chart ω).2.2 ((d'.chart ω).2.1 w) =
          (logDerivFwd W Q (fwdMapInv W Q w)).im + (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv W Q w))) →
        ∀ (x : ℝ) (v : ℝ → ℂ), QuantumZipper.IsForwardSol W x Q v → x ∉ (β₀ ω).jumps →
          (v Q).re ∉ (β₁ ω).jumps → (β₁ ω).fn (v Q).re = (β₀ ω).fn x := by
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
  intro hO₀ hO₁ hu₁ hr₁ hE hE' hs₀ hs₁ W Q hW hW0 hQ hinv hlift x v hv hx hy
  have hu₀' : (d.u : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_le_coe.2 huu).trans_lt hu₁
  have hr₀' : (d.r : ℝ≥0∞) < ζ₂ ω := (ENNReal.coe_le_coe.2 hrr).trans_lt hr₁
  obtain ⟨-, hd₁, hd₂⟩ := hagω hu₀' hr₀'
  obtain ⟨-, hd₁', hd₂'⟩ := hagω' hu₁ hr₁
  obtain ⟨vh, hvh, hvr, hdec⟩ := hn hu₁ hr₁
  have h₀ := hd.isConformal_chart ω
  have h₁ := hd'.isConformal_chart ω
  -- the prefix sets of the data are those of the flow lines
  have hK₀ : prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r = prefixSet (η₁ ω) d.u (η₂ ω) d.r := by
    rw [prefixSet, prefixSet, image_congr fun s hs => hd₁ s hs.2, image_congr fun t ht => hd₂ t ht.2]
  have hK₁ : prefixSet (d'.η₁ ω) d'.u (d'.η₂ ω) d'.r = prefixSet (η₁ ω) d'.u (η₂ ω) d'.r := by
    rw [prefixSet, prefixSet, image_congr fun s hs => hd₁' s hs.2, image_congr fun t ht => hd₂' t ht.2]
  have hg₀G := hd.good ω (RetData.E_subset_G hE)
  have hg₁G := hd'.good ω (RetData.E_subset_G hE')
  have hdom₀ : ((d.chart ω).dom : Set ℂ) = H \ fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r) := by
    rw [hd.coe_dom_chart ω, hd.D_of_mem hE, activeDomain_eq (isCompact_prefixSet' hg₀G.1 hg₀G.2.1).isClosed, hK₀]
  have hdom₁ : ((d'.chart ω).dom : Set ℂ) = H \ fillH (prefixSet (η₁ ω) d'.u (η₂ ω) d'.r) := by
    rw [hd'.coe_dom_chart ω, hd'.D_of_mem hE', activeDomain_eq (isCompact_prefixSet' hg₁G.1 hg₁G.2.1).isClosed,
      hK₁]
  -- the later union, read in the capped versions
  have hb₁ : ∀ t ≤ d'.u, ηb₁ ω t = η₁ ω t := eqOn_of_capped hbω₁ hu₁ (lt_capR_left d'.u d'.r)
  have hb₂ : ∀ t ≤ d'.r, ηb₂ ω t = η₂ ω t := eqOn_of_capped hbω₂ hr₁ (lt_capR_right d'.u d'.r)
  have hAω : cstUnion ηb₁ ηb₂ d'.u d'.r ω = prefixSet (η₁ ω) d'.u (η₂ ω) d'.r ∩ H := by
    rw [cstUnion_eq, prefixSet, image_congr fun t ht => hb₁ t ht.2, image_congr fun t ht => hb₂ t ht.2]
  -- the later active domain avoids the later union
  have hoff : ∀ z ∈ ((d'.chart ω).dom : Set ℂ), z ∈ H \ cstUnion ηb₁ ηb₂ d'.u d'.r ω := by
    intro z hz
    rw [hdom₁] at hz
    refine ⟨hz.1, fun hzA => hz.2 ?_⟩
    rw [hAω] at hzA
    exact mem_fillH_of_mem_closure hzA.2 (subset_closure hzA.1)
  -- (III-a) sends the complement of the hull into the later active domain
  have hback : ∀ w ∈ H \ fwdHull W Q, (d.chart ω).2.1 w ∈ ((d'.chart ω).dom : Set ℂ) := by
    intro w hw
    have hfw : fwdMap W Q w ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hQ hw
    have e := hinv _ hfw
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hQ hw] at e
    rw [← e]
    exact h₁.inv_mem_dom hfw
  have hAt : MapsTo (d.chart ω).2.1 (H \ fwdHull W Q) (H \ cstUnion ηb₁ ηb₂ d'.u d'.r ω) :=
    fun w hw => hoff _ (hback w hw)
  have hℓ₀ : ContinuousOn (fun w => (d.chart ω).2.2 ((d.chart ω).2.1 w)) H :=
    (hd.continuousOn_lift_chart ω).comp h₀.1.continuousOn fun w hw => h₀.inv_mem_dom hw
  have hvr' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cstUnion ηb₁ ηb₂ d'.u d'.r ω →
      (g₁ ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ -
        (g₀ ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, vh z * φ z := by
    intro φ hφ
    rw [← hvr φ hφ, add_apply, add_apply]
    ring
  have heq := eqOn_couplingMean_sub_mean (κ := κ) h₀ h₁ hℓ₀ hW hW0 hQ hinv hlift hs₀ hs₁ (hi₀ hO₀) (hi₁ hO₁)
    (cstUnion_relClosed hcb₁ hcb₂ d'.u d'.r ω).2 hAt hvh hvr'
  -- the decay at `x`
  obtain ⟨⟨x₀, hx₀⟩, -⟩ := hd.isRetChart hE
  have hfwd : ∀ z, (d.chart ω).1 z = ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) z - x₀ := by
    intro z
    rw [RetData.chart_of_mem hE]
    show d.g ω z - d.shift ω = _
    rw [hx₀, RetData.g, RetData.K_of_mem hE, hK₀]
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hQ hv
  set ρ : ℝ := δ / Real.exp (2 / δ ^ 2 * Q) with hρdef
  have hρ : 0 < ρ := div_pos hδ (Real.exp_pos _)
  have hclr : ∀ z ∈ H \ fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r),
      ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) z ∈ ball ((x + x₀ : ℝ) : ℂ) ρ →
        z ∉ prefixSet (η₁ ω) d'.u (η₂ ω) d'.r := by
    intro z hz hzb hzK
    rw [← hdom₀] at hz
    set w := (d.chart ω).1 z with hw
    have hwH : w ∈ H := h₀.fwd_mem hz
    have hwx : ‖w - x‖ * Real.exp (2 / δ ^ 2 * Q) < δ := by
      rw [mem_ball, dist_eq_norm] at hzb
      have e : w - x = ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) z - ((x + x₀ : ℝ) : ℂ) := by
        rw [hw, hfwd z]; push_cast; ring
      rw [e]
      have := (lt_div_iff₀ (Real.exp_pos (2 / δ ^ 2 * Q))).1 hzb
      linarith
    have hwK : w ∈ H \ fwdHull W Q := ⟨hwH, not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hwH hwx⟩
    have hzw : (d.chart ω).2.1 w = z := h₀.inv_fwd hz
    have h1 := hback w hwK
    rw [hzw, hdom₁] at h1
    exact h1.2 (mem_fillH_of_mem_closure h1.1 (subset_closure hzK))
  have hF : Filter.map (d.chart ω).2.1 (𝓝[H] (x : ℂ)) ≤ 𝓟 (H \ fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) := by
    rw [← hdom₀, le_principal_iff, mem_map]
    exact Filter.eventually_of_mem self_mem_nhdsWithin fun w hw => h₀.inv_mem_dom hw
  have hT : Tendsto (ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)))
      (Filter.map (d.chart ω).2.1 (𝓝[H] (x : ℂ))) (𝓝 ((x + x₀ : ℝ) : ℂ)) := by
    rw [tendsto_map'_iff]
    have h1 : Tendsto (fun w : ℂ => w + (x₀ : ℂ)) (𝓝[H] (x : ℂ)) (𝓝 ((x + x₀ : ℝ) : ℂ)) := by
      have h2 : Tendsto (fun w : ℂ => w + (x₀ : ℂ)) (𝓝 (x : ℂ)) (𝓝 ((x : ℂ) + x₀)) :=
        (continuous_id.add continuous_const).tendsto (x : ℂ)
      rw [ofReal_add]
      exact h2.mono_left (nhdsWithin_le_nhds (s := H))
    refine h1.congr' (Filter.eventually_of_mem self_mem_nhdsWithin fun w hw => ?_)
    show w + x₀ = ConformalImage.mapOut (fillH (prefixSet (η₁ ω) d.u (η₂ ω) d.r)) ((d.chart ω).2.1 w)
    have e := hfwd ((d.chart ω).2.1 w)
    rw [h₀.2.2 w hw] at e
    linear_combination e
  have hdec' := hdec (x + x₀) ρ hρ hclr _ hF hT
  rw [tendsto_map'_iff] at hdec'
  exact fn_eq_of_tendsto hW hW0 hQ hs₀ hs₁ heq hv hx hy hdec'

end OrdDet

end RLC

end InteractingSLE
