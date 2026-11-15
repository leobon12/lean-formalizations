/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafClock

/-!
# The first-visit data of one launched piece, pathwise

Packet PROVE-T14-GW4REG. For one sample: the piece of a launch (driver `W` up to its stop `S`, read in the launch
chart `c` with boundary limits `f`), the conditional counterflow trace `γk` (driver `Wk`) and the original
counterflow trace `γ`. If the piece satisfies the measurable events `GW1Z.PieceVisitEvent` (injectivity, visits) and
`FCAt` (GB6's first contacts), and the launch clock and the chart fibres are as in `GW1Z.IsLaunchClock` and
`GW1Z.ChartFiberStatement`, then the piece has its first-visit data `PieceVisitOK` (**`pieceVisitOK_of_events`**):
strict reverse first visits along it, and each point after the seed first visited before every old point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

open GW1Z

/-- Boundary-limit maps of a chart agree on `ℍ̄`. -/
theorem eqOn_of_tendsto_chart {c : Chart} {f f' : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) (hf' : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f' p)))
    {p : ℂ} (hp : p ∈ Hbar) : f' p = f p := by
  have : (𝓝[H] p).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact hp
  exact tendsto_nhds_unique (hf' p hp) (hf p hp)

/-- Two generating traces of the same driver up to `S` agree on `[0, S]`. -/
theorem eqOn_of_isGeneratingTrace {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α α' : ℝ≥0 → ℂ} (hα : IsGeneratingTrace W S α)
    (hα' : IsGeneratingTrace W S α') (hW : ContinuousOn W {s | (s : ℝ≥0∞) < S}) (hW0 : W 0 = 0) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α' t = α t := by
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < S → α' t = α t := fun t ht =>
    (hα'.trace_eq hW hW0 ht).symm.trans (hα.trace_eq hW hW0 ht)
  intro t ht
  rcases ht.lt_or_eq with ht' | ht'
  · exact hlt t ht'
  rcases eq_zero_or_pos t with rfl | htpos
  · rw [show α' 0 = 0 by simpa using hα'.1, show α 0 = 0 by simpa using hα.1]
  have hc : ∀ β : ℝ≥0 → ℂ, IsGeneratingTrace W S β → Tendsto β (𝓝[<] t) (𝓝 (β t)) := fun β hβ =>
    (hβ.2.1 t ht).tendsto.mono_left (nhdsWithin_mono _ fun s (hs : s < t) =>
      (show (s : ℝ≥0∞) ≤ S from ht' ▸ (ENNReal.coe_le_coe.2 hs.le)))
  have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  refine tendsto_nhds_unique ((hc α' hα').congr' ?_) (hc α hα)
  filter_upwards [self_mem_nhdsWithin] with s (hs : s < t)
  exact hlt s (ht' ▸ ENNReal.coe_lt_coe.2 hs)

/-- **The first-visit data of one launched piece, pathwise.** -/
theorem pieceVisitOK_of_events {c : Chart} {f : ℂ → ℂ} (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {C : ℝ} (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C) {A : Set ℂ}
    (hfib : ∀ x ∈ Hbar, ∀ y ∈ Hbar, f x = f y → f x ∉ A → x = y)
    {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace W S η)
    (hWc : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0)
    {Wk W' : ℝ≥0 → ℝ} {γk γ : ℝ≥0 → ℂ} (hγk : IsGeneratingTrace Wk ⊤ γk) (hγktr : Tendsto (fun t => ‖γk t‖) atTop atTop)
    (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    (hγ : IsGeneratingTrace W' ⊤ γ) (hW' : Continuous W') (hW'0 : W' 0 = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓ : StrictMono ℓ)
    (hrange : range ℓ = {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime infinitySourceChart W' A})
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk r z ↔
      infinitySourceChart.tipAt W' (ℓ r) z)
    (hsep : SepAt (fun t => LP.traceAt t W) S)
    (hvisAt : VisAt (fun t => LP.traceAt t W) (fun t => LP.traceAt t Wk) S)
    (hfc : FCAt (fun t => LP.traceAt t W) (fun t => LP.traceAt t Wk) S) :
    PieceVisitOK γ c W S A := by
  have hWlt : ContinuousOn W {s | (s : ℝ≥0∞) < S} :=
    hWc.mono fun s (hs : (s : ℝ≥0∞) < S) => (le_of_lt hs : (s : ℝ≥0∞) ≤ S)
  have hγkc : Continuous γk := Sec5.continuous_of_isGeneratingTrace_top hγk
  have hηc : ContinuousOn η {t | (t : ℝ≥0∞) ≤ S} := hη.2.1
  have hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < S → LP.traceAt (rt q) W = η (rt q) := fun q hq =>
    LP.traceAt_eq_of_isGeneratingTrace hη hWlt hW0 hq
  have hG : ∀ r : ℚ, LP.traceAt (rt r) Wk = γk (rt r) := fun r =>
    LP.traceAt_eq_of_isGeneratingTrace hγk hWk.continuousOn hWk0 ENNReal.coe_lt_top
  have hinj := injOn_of_sepAt hηc hA hsep
  have hvis := visit_of_visAt hηc (by simpa using hη.1) hinj hγkc hγktr hA hG hvisAt
  obtain ⟨-, havoid⟩ := piece_simple_of_visit hf hfib hη hWc hW0 hγk hWk hWk0 hvis hinj
    (notMem_of_clock hrange hiff)
  have hHbar : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → η t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hη hWlt hW0 ht
  have hfin : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → GB11.firstVisit γk (η t) < ⊤ := fun t ht hts => by
    obtain ⟨r, hr, hrt⟩ := hvis t ht hts
    rw [hrt]
    exact lt_of_le_of_lt (GB11.firstVisit_le hr) ENNReal.coe_lt_top
  -- strict reverse first visits in the conditional pair
  have hrel := reverseVisits_of_min hηc hγkc
    (fun a b hab hb => CounterflowRange.exists_rat_mem_H_btwn hη hWlt hW0 hab hb)
    (fun q hq hqS hqH v hv => firstVisit_le_of_fcAt hηc hγkc hA hG hfc hq hqS hqH
      (hfin _ hq hqS.le) hv)
    hfin hinj
  -- through the clock
  have hclk : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S →
      GB11.firstVisit γ (f (η t)) = ℓ (GB11.firstVisit γk (η t)).toNNReal ∧
        (ℓ (GB11.firstVisit γk (η t)).toNNReal : ℝ≥0∞) < firstTipTime infinitySourceChart W' A :=
    fun t ht hts => firstVisit_eq_clock hf hC hfib hγk hWk hWk0 hγ hW' hW'0 hℓ hrange hiff (hHbar t hts)
      (havoid t ht hts) (hfin t ht hts)
  intro f' α' hf' hα'
  have hfα : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → f' (α' t) = f (η t) := fun t ht => by
    rw [eqOn_of_isGeneratingTrace hη hα' hWlt hW0 t ht]
    exact eqOn_of_tendsto_chart hf hf' (hHbar t ht)
  refine ⟨fun t t' ht htt ht' => ?_, fun t ht hts p hp => ?_⟩
  · have hts : (t : ℝ≥0∞) ≤ S := le_trans (ENNReal.coe_le_coe.2 htt.le) ht'
    rw [hfα t' ht', hfα t hts, (hclk t' (ht.trans htt) ht').1, (hclk t ht hts).1]
    refine ENNReal.coe_lt_coe.2 (hℓ ?_)
    have h := hrel t t' ht htt ht'
    exact (ENNReal.toNNReal_lt_toNNReal (hfin _ (ht.trans htt) ht').ne (hfin _ ht hts).ne).2 h
  · rw [hfα t hts, (hclk t ht hts).1]
    exact lt_of_lt_of_le (hclk t ht hts).2 (firstTipTime_le_firstVisit hγ hW' hW'0 hp)

end GW4Leaf

end Theorem14

end InteractingSLE
