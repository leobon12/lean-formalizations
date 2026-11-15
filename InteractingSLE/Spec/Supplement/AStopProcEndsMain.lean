/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopProcEndsData
import InteractingSLE.Spec.Supplement.Aux85Junction
import InteractingSLE.Spec.Supplement.RLCCondDetHistDisj

/-!
# The stop-line measurable end points of the retained union (item 3 of `AStopSourceInputs`)

Packet PROVE-T15-ASTOP-PROC. In the setting of `RLC.OrdModel.RetOrdAStopSourceSndStatement`:

* **`exists_retEnds_stop`**: there are end points `E : Ω → OrdModel.Ends`, measurable for the stop line's completed
  histories `retSigma76 … d.u d.r` (hence initial in every filtration containing them), such that almost surely at
  every ordinary retained pair `aStopSet (E ω)` is exactly the set of chart reals `z` whose image `d.inv ω z` under the
  chart inverse of `d` lies on the retained union `η₁[0, u] ∪ η₂[0, r]` (the chart image `I_A` of the `A`-part of the
  boundary of the active domain).

Construction: the end points `retEnds` of the stopped capped retained data of `RLC.exists_retStop` (measurable good
data for `retSigma76`, Lemma 7.5); at an ordinary pair their chart equals the chart of `d`
(`RetData.chart_eq_of_agree`), and the end points are the zone end points of Lemma 7.6 (disjoint prefixes,
`retEnds_eq_of_setting`) or of Aux. 85 (touching prefixes, `Aux85.retTouchZonesStatement`, `retEnds_eq_of_touch`),
which bound the retained union in the chart (`aStopSet_zoneData`, `aStopSet_zoneDataT`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Supp7 Sec7 Sec7.Lemma76G Sec7.Lemma76F RetChart RetTouch OrdModel
open LQGMetric (DistOn)

universe v

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type v} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω}

/-- **Item 3 of `AStopSourceInputs`: the chart end points of the retained union**, measurable for the stop line's
completed histories, with `aStopSet (E ω) = I_A` almost surely at ordinary pairs. -/
theorem exists_retEnds_stop (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) :
    ∃ E : Ω → Ends, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] E ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        aStopSet (E ω) = {z : ℂ | z.im = 0 ∧ d.inv ω z ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r} := by
  obtain ⟨ηs₁, ηs₂, hd'R, hag'⟩ := exists_retStop hL75 hκ hκ4 hb hh hη₁ hη₂ (fun _ => 0) d.u d.r
  set d' := stopRet ηs₁ ηs₂ d.u d.r with hd'def
  have hd' : d'.IsMeasGood := RetData.IsMeasGood.mono_sigma hd'R (retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r)
  refine ⟨retEnds d', @measurable_retEnds Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) d' hd'R, ?_⟩
  filter_upwards [hag, hag', ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hagω hag'ω hp₁ hp₂ hord
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  obtain ⟨hG', b₁, b₂⟩ := hag'ω hord.1 hord.2.1
  have hE : ω ∈ d.E := hd.mem_E_of_ordinary hG a₁ a₂ hord
  have hE' : ω ∈ d'.E := hd'.mem_E_of_ordinary hG' b₁ b₂ hord
  have hch : d'.chart ω = d.chart ω :=
    (RetData.chart_eq_of_agree (d := d) (G' := d'.G) (η₁' := d'.η₁) (η₂' := d'.η₂) hG hG'
      (fun s hs => (b₁ s hs).trans (a₁ s hs).symm) (fun t ht => (b₂ t ht).trans (a₂ t ht).symm)).2.2
  rw [RetData.chart_of_mem hE, RetData.chart_of_mem hE'] at hch
  have hfwd : d'.fwd ω = d.fwd ω := congrArg (fun c : (ℂ → ℂ) × (ℂ → ℂ) × (ℂ → ℝ) => c.1) hch
  have hinv : d'.inv ω = d.inv ω := congrArg (fun c : (ℂ → ℂ) × (ℂ → ℂ) × (ℂ → ℝ) => c.2.1) hch
  have hC : IsRetChart (η₁ ω) d.u (η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
    (isRetChart_congr a₁ a₂).1 (hd.isRetChart hE).2
  by_cases hdis : Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)
  · have hx' : x₂ < x₁ := by
      rcases hx.lt_or_eq with h' | h'
      · exact h'
      · exfalso
        refine Set.disjoint_left.1 hdis ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩ ⟨0, ⟨le_rfl, zero_le⟩, ?_⟩
        rw [Sec7.IsPathGood.zero hp₁, Sec7.IsPathGood.zero hp₂, h']
    have hs : IsSetting (η₁ ω) (ζ₁ ω) x₁ d.u (η₂ ω) (ζ₂ ω) x₂ d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
      ⟨hp₁, hp₂, hx', isDisjointPair_of_ordinary hord hdis, hC⟩
    have hs' : IsSetting (η₁ ω) (ζ₁ ω) x₁ d'.u (η₂ ω) (ζ₂ ω) x₂ d'.r (d'.fwd ω) (d.inv ω) (d.lift ω) := by
      rw [hfwd]
      exact hs
    rw [retEnds_eq_of_setting hd' hE' hs' b₁ b₂, hfwd]
    exact aStopSet_zoneData hs
  · have ht := Aux85.retTouchZonesStatement (η₁ ω) (η₂ ω) (ζ₁ ω) (ζ₂ ω) x₁ x₂ d.u d.r (d.fwd ω) (d.inv ω)
      (d.lift ω) hp₁ hp₂ hx hord hdis hC
    have ht' : IsTouchZones (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω)
        (zoneDataT (d'.fwd ω) (activeDomain (η₁ ω) d'.u (η₂ ω) d'.r) (d'.inv ω) (η₁ ω) d'.u (η₂ ω) d'.r) := by
      rw [hfwd, hinv]
      exact ht
    have htip₃ : ∀ s < d'.u, η₁ ω s ≠ η₁ ω d'.u := fun s hs he =>
      (ne_of_lt hs) (hp₁.1 (show (s : ℝ≥0∞) ≤ ζ₁ ω from (ENNReal.coe_le_coe.2 hs.le).trans hord.1.le)
        (show (d.u : ℝ≥0∞) ≤ ζ₁ ω from hord.1.le) he)
    rw [retEnds_eq_of_touch hd' hE' b₁ b₂ ht' hord.2.2.2.2.2.2.1 hord.2.2.2.2.2.1 htip₃ hdis, hfwd, hinv]
    exact aStopSet_zoneDataT ht

/-! ### End points in the chart recentred at a seed (the first continuation) -/

/-- The end points translated by `−c`. -/
def shiftEnds (q : Ends) (c : ℝ) : Ends := (q.1 - c, q.2.1 - c, q.2.2.1 - c, q.2.2.2 - c)

theorem segPt_sub (a b c x : ℝ) : segPt (a - c) (b - c) x = segPt a b x - c := by
  unfold segPt
  push_cast
  ring

theorem mem_seg_sub {a b c : ℝ} {z : ℂ} : z ∈ seg (a - c) (b - c) ↔ z + c ∈ seg a b := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [segPt_sub]; ring⟩
  · rintro ⟨x, hx, hxz⟩
    exact ⟨x, hx, by rw [segPt_sub, hxz]; ring⟩

/-- **Translating the end points translates the A-set.** -/
theorem mem_aStopSet_shiftEnds {q : Ends} {c : ℝ} {z : ℂ} : z ∈ aStopSet (shiftEnds q c) ↔ z + c ∈ aStopSet q := by
  simp only [aStopSet, shiftEnds, mem_union, mem_seg_sub]

/-- **Item 3 of `AStopSourceInputs` in the chart recentred at a stop-line measurable seed `τ`** (the first
continuation): end points measurable for the stop line's completed histories with `aStopSet (E ω)` almost surely
the set of chart reals `z` with `d.inv ω (z + τ ω)` on the retained union. -/
theorem exists_retEnds_seed (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {τ : Ω → ℝ} (hτm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] τ) :
    ∃ E : Ω → Ends, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] E ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        aStopSet (E ω) = {z : ℂ | z.im = 0 ∧ d.inv ω (z + τ ω) ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r} := by
  obtain ⟨E, hEm, hE⟩ := exists_retEnds_stop hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag
  refine ⟨fun ω => shiftEnds (E ω) (τ ω), ?_, ?_⟩
  · have h1 := (measurable_fst.comp hEm).sub hτm
    have h2 := (measurable_fst.comp (measurable_snd.comp hEm)).sub hτm
    have h3 := (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hEm))).sub hτm
    have h4 := (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hEm))).sub hτm
    exact h1.prodMk (h2.prodMk (h3.prodMk h4))
  · filter_upwards [hE] with ω hω hord
    ext z
    rw [mem_aStopSet_shiftEnds, hω hord]
    simp only [mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, add_zero]

end InteractingSLE.RLC.AStopProc
