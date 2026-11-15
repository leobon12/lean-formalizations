/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetNHRestart
import InteractingSLE.Spec.Supplement.GB1Proof

/-!
# G8's chart estimate from a relative Loewner representation

Packet PROVE-G8-DET, R63. The passive real point itself can serve as the right
characteristic in GB1: its uncentered coordinate is `Re f_s(x) + W_s`.
Thus GB1 gives the gap at `1` directly, with no estimate lost by first passing
to the intervening real junction.

`G8RelativeChartNHStatement` is the explicit remaining geometric input: a
relative continuous driver, its clock, the retained tip's characteristic, and
their identification with the canonical chart. It contains no small-gap bound.
The analytic estimate and the successor frame are proved from this input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap IsForwardSol)

namespace InteractingSLE.RLC

namespace G8Det

/-- GB1 for the passive point itself, rather than the real junction between
it and the driver. Its characteristic is supplied by `GB1.exists_pkg`. -/
theorem tendsto_passive_ratio {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {U x s₀ : ℝ} (hsw : RealSwallowAt W x U) (hx : 0 < x)
    (hs₀ : 0 ≤ s₀) (hs₀U : s₀ < U) {b : ℝ → ℝ}
    (hbW : ∀ s ∈ Ico s₀ U, b s < W s)
    (hb : ∀ s ∈ Ico s₀ U, b s - b s₀ = ∫ r in s₀..s, 2 / (b r - W r))
    (hbi : ∀ s ∈ Ico s₀ U,
      IntervalIntegrable (fun r => 2 / (b r - W r)) volume s₀ s) :
    Tendsto (fun s => (fwdMap W s x).re / (W s - b s)) (𝓝[<] U) (𝓝 0) := by
  let v : ℝ → ℝ := fun s => (fwdMap W s x).re + W s
  have hpkg := fun s (hs : s ∈ Ico s₀ U) =>
    GB1.exists_pkg hW hW0 hx (hs₀.trans hs.1)
      (hsw.2.1 s ⟨hs₀.trans hs.1, hs.2⟩)
  have hWv : ∀ s ∈ Ico s₀ U, W s ≤ v s := by
    intro s hs
    have hpos := (hpkg s hs).2.1 s ⟨hs₀.trans hs.1, le_rfl⟩
    dsimp only [v]
    exact le_add_of_nonneg_left hpos.le
  have hv : ∀ s ∈ Ico s₀ U, v s - v s₀ = ∫ r in s₀..s, 2 / (v r - W r) := by
    intro s hs
    have he := (hpkg s hs).2.2.2.1 s₀ ⟨hs₀, hs.1⟩ s ⟨hs₀.trans hs.1, le_rfl⟩ hs.1
    dsimp only [v]
    simp only [add_sub_cancel_right]
    linarith only [he]
  have hvi : ∀ s ∈ Ico s₀ U,
      IntervalIntegrable (fun r => 2 / (v r - W r)) volume s₀ s := by
    intro s hs
    dsimp only [v]
    simp only [add_sub_cancel_right]
    exact (hpkg s hs).2.2.2.2.mono_set (by
      rw [uIcc_of_le hs.1, uIcc_of_le (hs₀.trans hs.1)]
      exact Icc_subset_Icc_left hs₀)
  have hlim := GB1.tendsto_ratio hW hW0 hsw.1 hx hsw.2.1 hsw.2.2 hs₀U hbW hWv
    (fun s _ => by dsimp only [v]; rw [add_sub_cancel_right]) hb hv hbi hvi
  simpa only [v, add_sub_cancel_right] using hlim

end G8Det

/-- The relative-chain coordinates needed for G8 after a late cut. The old tip
has uncentered coordinate `b`, the new tip `W`, and the real point `1` is the
passive characteristic of `x`. The equations and chart identifications are
geometric data; no vanishing ratio or small-gap estimate is a field. -/
structure G8RelativeChart (α β : ℝ≥0 → ℂ) (σ r : ℝ≥0) where
  W : ℝ → ℝ
  U : ℝ
  x : ℝ
  s₀ : ℝ
  b : ℝ → ℝ
  clock : ℝ≥0 → ℝ
  continuous_W : Continuous W
  W_zero : W 0 = 0
  x_pos : 0 < x
  swallow : RealSwallowAt W x U
  cut_nonneg : 0 ≤ s₀
  cut_lt : s₀ < U
  tip_lt : ∀ s ∈ Ico s₀ U, b s < W s
  characteristic : ∀ s ∈ Ico s₀ U, b s - b s₀ = ∫ t in s₀..s, 2 / (b t - W t)
  integrable : ∀ s ∈ Ico s₀ U,
    IntervalIntegrable (fun t => 2 / (b t - W t)) volume s₀ s
  clock_tendsto : Tendsto clock (𝓝[<] σ) (𝓝[<] U)
  chart_eq : ∀ᶠ u in 𝓝[<] σ,
    Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) (α u) =
      W (clock u) - b (clock u) ∧
    Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) 1 =
      (fwdMap W (clock u) x).re + (W (clock u) - b (clock u))

/-- Exact remaining input: construct the late relative chain and identify its
coordinates with `retFwd` (Aux. 8 and the active-tip order of Aux. 85). This is
not asserted as a theorem in this file. -/
def G8RelativeChartNHStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (σ r : ℝ≥0) (q : ℝ),
    Sec7.Prop74Order.IsCompleteOrderedPair α β → α 0 = 0 → β 0 = 0 →
    Continuous w → w 0 = 0 → IsGeneratingTrace w ⊤ α →
    RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ → 1 < q → α σ = q →
    β r ∈ H → β r ∉ α '' Icc 0 σ → (∀ t ≤ r, ‖β t‖ < 1 / 2) →
    (∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) → Nonempty (G8RelativeChart α β σ r)

namespace G8RelativeChart

/-- The canonical chart gap follows from the relative-chain representation
and the existing GB1 passive-gap theorem. -/
theorem exists_final_gap {α β : ℝ≥0 → ℂ} {σ r : ℝ≥0}
    (d : G8RelativeChart α β σ r) (hσ : 0 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t₁ : ℝ≥0, t₁ < σ ∧ ∀ u : ℝ≥0, t₁ < u → u < σ →
      0 < Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) (α u) ∧
      Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) 1 <
        (1 + ε) * Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) (α u) := by
  have hlim := G8Det.tendsto_passive_ratio d.continuous_W d.W_zero d.swallow d.x_pos
    d.cut_nonneg d.cut_lt d.tip_lt d.characteristic d.integrable
  have hev : ∀ᶠ u in 𝓝[<] σ,
      0 < Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) (α u) ∧
      Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) 1 <
        (1 + ε) * Sec7.Lemma76G.chartPt (retFwd α u β r) (activeDomain α u β r) (α u) := by
    filter_upwards [d.clock_tendsto (Ico_mem_nhdsLT d.cut_lt),
      d.clock_tendsto (hlim (gt_mem_nhds hε)), d.chart_eq] with u hu hratio heq
    have hden : 0 < d.W (d.clock u) - d.b (d.clock u) := sub_pos.2 (d.tip_lt _ hu)
    have hratio' : (fwdMap d.W (d.clock u) d.x).re /
        (d.W (d.clock u) - d.b (d.clock u)) < ε := hratio
    have hgap := (div_lt_iff₀ hden).1 hratio'
    rw [heq.1, heq.2]
    exact ⟨hden, by nlinarith only [hgap]⟩
  obtain ⟨t₁, ht₁, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hσ).1 hev
  exact ⟨t₁, ht₁, fun u htu huσ => hsub ⟨htu, huσ⟩⟩

end G8RelativeChart

/-- The R63 successor from the explicitly named relative-chart construction.
The side/pocket exclusion and every analytic estimate are discharged here. -/
theorem g8DetFrameNHStatement_of_relative (hRel : G8RelativeChartNHStatement) :
    G8DetFrameNHStatement := by
  intro α β w σ r q ε hε hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH
  obtain ⟨d⟩ := hRel α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH
  exact G8Det.exists_final_frame_of_gap hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hsmall
    (G8Det.second_tip_outside_of_no_negative_contact hcop hα0 hq hασ hNH hβH hβoff)
    (d.exists_final_gap (by exact_mod_cast hsw.1) hε)

end InteractingSLE.RLC
