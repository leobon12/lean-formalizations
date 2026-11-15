/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfJunctionPath

/-!
# The local comparison's reference fact at a junction next to the counterflow's own past

Packet PROVE-CFBARRIER3. In the restart chart of the counterflow after a rational time `q`, the counterflow's own past
sides carry the canonical counterflow heights, which correspond to the weight `0` relative to the seed. A boundary arc
of `L` (the left side of the flow line, or `ℝ₋`) that meets the past of the counterflow produces a **junction between
a weight-`0` arc and a barrier arc**: the marks before it have weight `0`, the marks at it carry the cumulative weight
`S ≥ κ/2 − 2` of the barrier arc. PROVE-CFBARRIER2's junction barrier (`CfJunction.ae_trace_ne_junction_right`) needs
both adjacent arcs to be barriers; here the arc before the junction is hittable.

**`ae_trace_ne_zeroSide_right`** (every `κ > 0`): for an integrated `SLE_κ(ρ)` evolution whose right marks strictly
before `x_k > 0` have weight `0` and whose marks at `x_k` have total weight at least `κ/2 − 2`, almost surely the trace
never visits `x_k` before the lifetime. With Lemma GB7a beyond `x_k` (`ae_trace_notMem_zeroSide_right`) the whole
half-open interval `[x_k, a')` is avoided. The left side is the reflection (`ae_trace_ne_zeroSide_left`).

The reference weights `zeroSideWeight` keep the weights at or before `x_k` and set the others to `0`. Under them the gap
`Y = V_k − W` has drift `2/Y + S/Y ≥ κ/(2Y)` exactly (the weight-`0` marks contribute nothing, even when merged with the
driver), so `CfJunction.measure_genCmp_eq_zero` applies. The pathwise half is simpler than at a two-sided junction: at
the first visit `T` of `[x_k, ∞)` (which is at `x_k`) the only marks whose weights change are the left marks and the
right marks beyond `x_k`, all at positive distance from the driver at `T` (at a collision the tip is real and beyond
the mark, `tip_ge_of_collision_right`, and its reflection), so the energy of the drift change is bounded by continuity
alone (no Aux. 61 cutoff).

This is the finite-word fact the return input `CfFirstContactQ.CfReturnStatement` needs at an isolated old contact
(a "loop" of the counterflow into `L` returning to its entry point): there the counterflow's past attached to `∂L`
creates exactly such junctions in the restart chart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5.CfLocalCmp

open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)
open GB7a GB7aAbove4 CfJunction

/-! ### The reference weights and the drift bound -/

section Drift

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {P : Measure Ω}

/-- **The zero-side reference weights**: the actual weights at or before `x_k`, `0` beyond. -/
def zeroSideWeight (xR ρR : Fin nR → ℝ) (k : Fin nR) (j : Fin nR) : ℝ :=
  if xR j ≤ xR k then ρR j else 0

/-- The reference gap drift, pointwise: with weight `0` strictly before `x_k`, only the marks at `x_k` contribute. -/
theorem sum_zeroSideWeight_div {xR ρR : Fin nR → ℝ} {k : Fin nR} (hzero : ∀ j, xR j < xR k → ρR j = 0) (w : ℝ)
    {vR : Fin nR → ℝ} (hG : ∀ j, xR j = xR k → vR j = vR k) :
    ∑ j, zeroSideWeight xR ρR k j / (w - vR j) =
      (∑ j ∈ univ.filter (fun j => xR j = xR k), ρR j) / (w - vR k) := by
  classical
  rw [Finset.sum_div, ← Finset.sum_filter_add_sum_filter_not univ (fun j => xR j = xR k)]
  have h2 : ∑ j ∈ univ.filter (fun j => ¬ xR j = xR k), zeroSideWeight xR ρR k j / (w - vR j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hne := (Finset.mem_filter.1 hj).2
    unfold zeroSideWeight
    split_ifs with hle
    · rw [hzero j (lt_of_le_of_ne hle hne), zero_div]
    · rw [zero_div]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have heq := (Finset.mem_filter.1 hj).2
  simp only [zeroSideWeight, heq.le, ↓reduceIte, hG j heq]

/-- **The zero-side reference repels the mark `k`** (almost surely, whenever `k` is off the driver), when the marks
strictly before `x_k` have weight `0` and the marks at `x_k` have total weight at least `κ/2 − 2`. -/
theorem ae_zeroSide_drift_ge (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {k : Fin nR}
    (hzero : ∀ j, xR j < xR k → ρR j = 0)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i = xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω ≠ VR k t ω →
      0 < VR k t ω - W t ω ∧ κ / (2 * (VR k t ω - W t ω)) ≤ 2 / (VR k t ω - W t ω) -
        ∑ j, zeroSideWeight xR ρR k j / (W t ω - VR j t ω) := by
  filter_upwards [hE.2.2.2.2] with ω hp t ht hne
  have h := hp.isForcePath
  set S := ∑ i ∈ univ.filter (fun i => xR i = xR k), ρR i with hSdef
  have hY : 0 < VR k t ω - W t ω := sub_pos.2 (lt_of_le_of_ne (h.w_le_vR ht k) hne)
  have hG : ∀ j, xR j = xR k → VR j t ω = VR k t ω := fun j hj =>
    Sec2.Assembly.vR_eq_of_eq h ht (by rw [h.vR_zero j, h.vR_zero k, hj]) ⟨zero_le, le_rfl⟩
  refine ⟨hY, ?_⟩
  rw [sum_zeroSideWeight_div hzero (W t ω) (vR := fun j => VR j t ω) hG]
  have e : S / (W t ω - VR k t ω) = -(S / (VR k t ω - W t ω)) := by rw [← neg_sub, div_neg]
  rw [e, sub_neg_eq_add, ← add_div, div_le_div_iff₀ (by positivity) hY]
  nlinarith

end Drift

/-! ### The pathwise half -/

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The tip at a right collision is a real point at or beyond the mark** (one path, before the lifetime). -/
theorem tip_ge_of_collision_right (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hη : IsGeneratingTrace w ζ η)
    {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {j : Fin nR} (hjw : vR j t₀ = w t₀) :
    ∃ x : ℝ, η t₀ = x ∧ xR j ≤ x := by
  have hwc := h.continuousOn_w
  obtain ⟨T₂, ht₀T₂e, hT₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
  have ht₀T₂ : (t₀ : ℝ) < T₂ := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ht₀T₂e)
  have hT₂0 : (0 : ℝ) < T₂ := t₀.coe_nonneg.trans_lt ht₀T₂
  set U : ℝ → ℝ := frozenDrive w T₂ with hUdef
  have hU : Continuous U :=
    continuous_frozenDrive_of_lt hwc (by rw [ENNReal.ofReal_coe_nnreal]; exact hT₂ζ)
  have hUw₂ : ∀ s : ℝ, 0 ≤ s → s < T₂ → U s = w s.toNNReal := fun s hs0 hs =>
    frozenDrive_eq ⟨hs0, hs.le⟩
  have hU0 : U 0 = 0 := by rw [hUw₂ 0 le_rfl hT₂0, Real.toNNReal_zero, h.w_zero]
  set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
  have hηR₂ : IsLoewnerTraceLT U T₂ ηR := isLoewnerTraceLT_of_agree hη hT₂ζ.le hUw₂
  have hltζ : ∀ t : ℝ≥0, (t : ℝ) < T₂ → (t : ℝ≥0∞) < ζ := fun t ht =>
    (ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 ht)).trans hT₂ζ
  obtain ⟨hc, hue, hi, hn⟩ := centredPkg hwc (h.continuousOn_vR j) (fun t ht => h.integrable_gapR ht j)
    (fun t ht => h.vR_eq ht j) (h.volume_collisionR j) hT₂ζ.le hUw₂ t₀.coe_nonneg ht₀T₂
  have hnn : ∀ s ∈ Icc (0 : ℝ) t₀, 0 ≤ vR j s.toNNReal - w s.toNNReal := fun s hs => by
    refine sub_nonneg.2 (h.w_le_vR (hltζ _ ?_) j)
    rw [Real.coe_toNNReal _ hs.1]
    exact hs.2.trans_lt ht₀T₂
  obtain ⟨x, hx, hx0, -⟩ := hηR₂.exists_tip_real_of_collision_right hU hU0 t₀.coe_nonneg ht₀T₂ hc hnn hue hi
    hn (by simp only [Real.toNNReal_coe, hjw, sub_self])
  have hxT : η t₀ = x := by simpa [hηRdef] using hx
  simp only [Real.toNNReal_zero, h.vR_zero j, h.w_zero, sub_zero] at hx0
  exact ⟨x, hxT, hx0⟩

/-- **The zero-side comparison picture from a visit** (one path, no injectivity): if the trace visits the right mark
position `x_k > 0` before the lifetime and the marks strictly before `x_k` have weight `0`, `GenCmpPath` holds for the
zero-side reference weights and the repelled mark `k` at some rational restart time. -/
theorem genCmpPath_of_zeroSide_visit (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η) {k : Fin nR} (hk0 : 0 < xR k)
    (hzero : ∀ j, xR j < xR k → ρR j = 0) (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ η t = xR k) :
    ∃ q : ℚ, GenCmpPath ρL ρR (zeroSideWeight xR ρR k) w vL vR ζ k (q : ℝ).toNNReal := by
  classical
  have h := hp.isForcePath
  have hwc := h.continuousOn_w
  obtain ⟨t₀, ht₀, he₀⟩ := hvis
  have hcont : ContinuousOn η (Icc 0 t₀) :=
    hη.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans ht₀.le
  obtain ⟨T₁, hT₁0, hT₁t₀, X₁, hX₁, hηT₁, hoff₁⟩ := exists_first_visit_le hcont hη.1 hk0 le_rfl he₀
  have hT₁ζ : (T₁ : ℝ≥0∞) < ζ := (ENNReal.coe_le_coe.2 hT₁t₀).trans_lt ht₀
  -- (1) the first visit of `[x_k, ∞)` is at `x_k` (PROVE-CFBARRIER2's step 2)
  have hX₁k : X₁ = xR k := by
    by_contra hne
    have hgt : xR k < X₁ := lt_of_le_of_ne hX₁ (Ne.symm hne)
    have hT₁lt : T₁ < t₀ := lt_of_le_of_ne hT₁t₀ fun he => by
      rw [he, he₀] at hηT₁
      exact hne (Complex.ofReal_injective hηT₁).symm
    obtain ⟨T₂, ht₀T₂e, hT₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
    have ht₀T₂ : (t₀ : ℝ) < T₂ := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ht₀T₂e)
    have hT₂0 : (0 : ℝ) < T₂ := t₀.coe_nonneg.trans_lt ht₀T₂
    set U : ℝ → ℝ := frozenDrive w T₂ with hUdef
    have hU : Continuous U :=
      continuous_frozenDrive_of_lt hwc (by rw [ENNReal.ofReal_coe_nnreal]; exact hT₂ζ)
    have hUw₂ : ∀ s : ℝ, 0 ≤ s → s < T₂ → U s = w s.toNNReal := fun s hs0 hs =>
      frozenDrive_eq ⟨hs0, hs.le⟩
    have hU0 : U 0 = 0 := by rw [hUw₂ 0 le_rfl hT₂0, Real.toNNReal_zero, h.w_zero]
    have hUw : ∀ s : ℝ, 0 ≤ s → s < t₀ → U s = w s.toNNReal := fun s hs0 hs =>
      hUw₂ s hs0 (hs.trans ht₀T₂)
    set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
    have hηR : IsLoewnerTraceLT U t₀ ηR := isLoewnerTraceLT_of_agree hη ht₀.le hUw
    have hlim : Tendsto ηR (𝓝[<] (t₀ : ℝ)) (𝓝 (xR k : ℂ)) := by
      rw [← he₀]
      exact tendsto_comp_toNNReal hη ht₀.le (hT₁0.trans hT₁lt)
    have hyq : (xR k : ℂ) ∉ ηR '' Icc 0 (T₁ : ℝ) := by
      rintro ⟨r, hr, hry⟩
      have hrT : r.toNNReal ≤ T₁ := Real.toNNReal_le_iff_le_coe.2 hr.2
      rcases hrT.lt_or_eq with hlt | heq
      · exact hoff₁ _ hlt (xR k) le_rfl hry
      · have hry' : η r.toNNReal = xR k := hry
        rw [heq, hηT₁] at hry'
        exact hne (Complex.ofReal_injective hry')
    obtain ⟨v, hv⟩ := exists_isForwardSol_at_restart_of_notMem hηR hU hU0 T₁.coe_nonneg
      (NNReal.coe_lt_coe.2 hT₁lt) hk0.ne' hlim hyq
    obtain ⟨v', hv'⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt hU T₁.coe_nonneg (by rw [hU0]; exact hk0)
      hgt hv
    exact trace_ne_of_isForwardSol hηR hU hU0 ⟨T₁.coe_nonneg, NNReal.coe_lt_coe.2 hT₁lt⟩ hv'
      (by simp [hηRdef, hηT₁])
  rw [hX₁k] at hηT₁
  -- (2) the mark `k` collides at `T₁` and not before
  have hkT₁ : vR k T₁ = w T₁ := CfAvoidLeftQ.vR_eq_w_of_off hp hη hT₁0 hT₁ζ hk0 hηT₁
    (fun t ht s hs r hr => hoff₁ s (lt_of_le_of_lt hs ht) r hr) le_rfl
  have hkne : ∀ t : ℝ≥0, t < T₁ → vR k t ≠ w t := fun t ht hcol => by
    obtain ⟨x, hx, hxk⟩ := tip_ge_of_collision_right h hη ((ENNReal.coe_lt_coe.2 ht).trans hT₁ζ) hcol
    exact hoff₁ t ht x hxk hx
  -- (3) the left marks and the right marks beyond `x_k` are off the driver at `T₁`
  have hR : ∀ j, xR k < xR j → 0 < vR j T₁ - w T₁ := fun j hj => by
    refine sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hT₁ζ j) fun hcol => ?_)
    obtain ⟨x, hx, hxj⟩ := tip_ge_of_collision_right h hη hT₁ζ hcol.symm
    rw [hηT₁] at hx
    have := Complex.ofReal_injective hx
    linarith
  have hL : ∀ i, 0 < w T₁ - vL i T₁ := fun i => by
    refine sub_pos.2 (lt_of_le_of_ne (h.vL_le_w hT₁ζ i) fun hcol => ?_)
    obtain ⟨x, hx, hxi⟩ := tip_ge_of_collision_right h.reflect (LP.isGeneratingTrace_reflect hη) hT₁ζ (j := i)
      (by simp only [Pi.neg_apply, hcol])
    simp only [LP.reflectC, hηT₁, Complex.conj_ofReal] at hx
    have hx' : -xR k = x := by exact_mod_cast hx
    simp only [Pi.neg_apply] at hxi
    linarith [hord.2.1 i]
  -- (4) by continuity, the gaps stay above half their values near `T₁`
  have hopen : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} ∈ 𝓝 T₁ :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hT₁ζ
  have hcw : ContinuousAt w T₁ := hwc.continuousAt hopen
  have hev : ∀ᶠ t in 𝓝 T₁, (∀ i, (w T₁ - vL i T₁) / 2 < w t - vL i t) ∧
      ∀ j, xR k < xR j → (vR j T₁ - w T₁) / 2 < vR j t - w t := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun j => ?_)
    · have hc : ContinuousAt (fun t => w t - vL i t) T₁ := hcw.sub ((h.continuousOn_vL i).continuousAt hopen)
      exact hc.eventually (lt_mem_nhds (by linarith [hL i]))
    · by_cases hj : xR k < xR j
      · have hc : ContinuousAt (fun t => vR j t - w t) T₁ := ((h.continuousOn_vR j).continuousAt hopen).sub hcw
        exact (hc.eventually (lt_mem_nhds (by linarith [hR j hj]))).mono fun t ht _ => ht
      · exact Eventually.of_forall fun t ht => absurd ht hj
  obtain ⟨ε, hε, hεev⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max ((T₁ : ℝ) - ε) 0 < T₁ from
    max_lt (by linarith) (NNReal.coe_pos.2 hT₁0))
  have hq0 : (0 : ℝ) < q := (le_max_right _ _).trans_lt hq1
  have hqT : (T₁ : ℝ) - ε < q := (le_max_left _ _).trans_lt hq1
  set qN : ℝ≥0 := (q : ℝ).toNNReal with hqN
  have hqN' : (qN : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have hnear : ∀ t : ℝ≥0, qN ≤ t → t < T₁ → (∀ i, (w T₁ - vL i T₁) / 2 < w t - vL i t) ∧
      ∀ j, xR k < xR j → (vR j T₁ - w T₁) / 2 < vR j t - w t := fun t hqt htT => by
    refine hεev ?_
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 htT.le))]
    have : (q : ℝ) ≤ t := hqN' ▸ NNReal.coe_le_coe.2 hqt
    linarith
  -- (5) the comparison picture on `[q, T₁)`
  set M : ℝ := (∑ i, |ρL i| * (2 / (w T₁ - vL i T₁))) +
    ∑ j, if xR k < xR j then |ρR j| * (2 / (vR j T₁ - w T₁)) else 0 with hMdef
  have hbound : ∀ s : ℝ, (q : ℝ) ≤ s → s < T₁ →
      |(∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
        ∑ j, (zeroSideWeight xR ρR k j - ρR j) / (w s.toNNReal - vR j s.toNNReal)| ≤ M := by
    intro s hqs hsT
    have hs0 : 0 ≤ s := hq0.le.trans hqs
    have hsN : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs0
    have hnear' := hnear s.toNNReal (by rw [← NNReal.coe_le_coe, hsN, hqN']; exact hqs)
      (by rw [← NNReal.coe_lt_coe, hsN]; exact hsT)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have hpos : 0 < w T₁ - vL i T₁ := hL i
      have hgap := hnear'.1 i
      have hgpos : 0 < w s.toNNReal - vL i s.toNNReal := by linarith
      rw [abs_div, abs_neg, abs_of_pos hgpos, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [inv_le_comm₀ hgpos (by positivity), inv_div]
      linarith
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      unfold zeroSideWeight
      by_cases hj : xR k < xR j
      · simp only [not_le.2 hj, hj, ↓reduceIte, zero_sub, abs_div, abs_neg]
        have hpos : 0 < vR j T₁ - w T₁ := hR j hj
        have hgap := hnear'.2 j hj
        have hgpos : 0 < vR j s.toNNReal - w s.toNNReal := by linarith
        rw [show w s.toNNReal - vR j s.toNNReal = -(vR j s.toNNReal - w s.toNNReal) by ring, abs_neg,
          abs_of_pos hgpos, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [inv_le_comm₀ hgpos (by positivity), inv_div]
        linarith
      · simp only [not_lt.1 hj, hj, ↓reduceIte, sub_self, zero_div, abs_zero, le_refl]
  refine ⟨q, T₁, ?_, hT₁ζ.le, fun t hqt htT => ⟨fun i _ => ?_, fun j hj => ?_⟩, ⟨M ^ 2 * T₁, fun t hqt htT => ?_⟩, ?_⟩
  · rw [← NNReal.coe_lt_coe, hqN']
    exact hq2
  · have := (hnear t hqt htT).1 i
    have hpos := hL i
    exact fun he => by linarith
  · have ht0 : 0 < t := lt_of_lt_of_le (by rw [← NNReal.coe_pos, hqN']; exact hq0) hqt
    have htζ : (t : ℝ≥0∞) < ζ := (ENNReal.coe_lt_coe.2 htT).trans hT₁ζ
    rcases lt_trichotomy (xR j) (xR k) with hlt | heq | hgt
    · exfalso
      rcases hj with hj | hj | hj
      · exact hj (hzero j hlt)
      · exact hj (by simp only [zeroSideWeight, hlt.le, ↓reduceIte, hzero j hlt])
      · exact (ne_of_lt hlt) (by rw [hj])
    · have hjk : vR j t = vR k t :=
        Sec2.Assembly.vR_eq_of_eq h htζ (by rw [h.vR_zero j, h.vR_zero k, heq]) ⟨zero_le, le_rfl⟩
      rw [hjk]
      exact fun he => hkne t htT he.symm
    · have := (hnear t hqt htT).2 j hgt
      have hpos := hR j hgt
      exact fun he => by linarith
  · have hqt' : (q : ℝ) ≤ t := hqN' ▸ NNReal.coe_le_coe.2 hqt
    have hle : ∀ s ∈ Set.uIoc (qN : ℝ) t, ‖((∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
        ∑ j, (zeroSideWeight xR ρR k j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2‖ ≤ M ^ 2 := by
      intro s hs
      rw [Set.uIoc_of_le (hqN'.symm ▸ hqt'), hqN'] at hs
      have hb := hbound s hs.1.le (hs.2.trans_lt (NNReal.coe_lt_coe.2 htT))
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rw [hqN', abs_of_nonneg (sub_nonneg.2 hqt')] at hint
    have h1 : (t : ℝ) - q ≤ T₁ := by linarith [NNReal.coe_lt_coe.2 htT]
    rw [hqN']
    calc (∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
          ∑ j, (zeroSideWeight xR ρR k j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2)
        ≤ ‖∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
          ∑ j, (zeroSideWeight xR ρR k j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2‖ := Real.le_norm_self _
      _ ≤ M ^ 2 * ((t : ℝ) - q) := hint
      _ ≤ M ^ 2 * T₁ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · have hc : ContinuousAt (fun t => vR k t - w t) T₁ := ((h.continuousOn_vR k).continuousAt hopen).sub hcw
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio T₁))
    simpa [hkT₁] using this

end Path

/-! ### The zero-side junction barrier -/

section Barrier

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The zero-side junction barrier, right side, every `κ > 0`.** If the right marks strictly before `x_k > 0` have
weight `0` and the marks at `x_k` have total weight at least `κ/2 − 2`, almost surely the trace never visits `x_k`
before the lifetime. -/
theorem ae_trace_ne_zeroSide_right (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k : Fin nR} (hk0 : 0 < xR k)
    (hzero : ∀ j, xR j < xR k → ρR j = 0)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i = xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t ≠ xR k := by
  have hin : ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ η ω t = xR k) →
      ∃ q : ℚ, GenCmpPath ρL ρR (zeroSideWeight xR ρR k) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        (ζ ω) k (q : ℝ).toNNReal := by
    filter_upwards [hE.2.2.2.2, hη] with ω h3 h4 hvis
    exact genCmpPath_of_zeroSide_visit h3 hord h4 hk0 hzero hvis
  have hnull : P (⋃ q : ℚ, {ω | GenCmpPath ρL ρR (zeroSideWeight xR ρR k) (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (ζ ω) k (q : ℝ).toNNReal}) = 0 :=
    measure_iUnion_null fun q => measure_genCmp_eq_zero hκ hE (ae_zeroSide_drift_ge hE hzero hS) _
  filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω hω' t ht he
  exact hω' (mem_iUnion.2 (hω ⟨t, ht, he⟩))

/-- The cumulative weight up to `x_k` is the weight at `x_k` when the marks before it have weight `0`. -/
theorem sum_le_eq_sum_eq_of_zero {xR ρR : Fin nR → ℝ} {k : Fin nR} (hzero : ∀ j, xR j < xR k → ρR j = 0) :
    ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i = ∑ i ∈ univ.filter (fun i => xR i = xR k), ρR i := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun i => xR i ≤ xR k)) (fun i => xR i = xR k),
    Finset.filter_filter, Finset.filter_filter]
  have h2 : ∑ i ∈ univ.filter (fun i => xR i ≤ xR k ∧ ¬ xR i = xR k), ρR i = 0 :=
    Finset.sum_eq_zero fun i hi => hzero i (lt_of_le_of_ne (Finset.mem_filter.1 hi).2.1 (Finset.mem_filter.1 hi).2.2)
  rw [h2, add_zero]
  exact Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩) fun _ _ => rfl

/-- **The zero-side junction with its barrier arc, right side**: under the hypotheses of
`ae_trace_ne_zeroSide_right`, with `a'` at most the next right mark position after `x_k`, almost surely the trace
avoids the half-open interval `[x_k, a')` before the lifetime (Lemma GB7a on `(x_k, a')`). -/
theorem ae_trace_notMem_zeroSide_right (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k : Fin nR} (hk0 : 0 < xR k)
    {a' : ℝ} (hnext : ∀ j, xR k < xR j → a' ≤ xR j) (hzero : ∀ j, xR j < xR k → ρR j = 0)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i = xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ y ∈ Ico (xR k) a', η ω t ≠ y := by
  have hIR := GB7aAbove4.gb7aEvol_right_any hκ hord hE hη (k := k) hnext
    (by rw [sum_le_eq_sum_eq_of_zero hzero]; exact hS)
  filter_upwards [hIR, ae_trace_ne_zeroSide_right hκ hord hE hη hk0 hzero hS] with ω hR hJ t ht y hy
  rcases hy.1.lt_or_eq with hlt | heq
  · exact hR t ht.le y ⟨hlt, hy.2⟩
  · rw [← heq]
    exact hJ t ht

/-- **The zero-side junction barrier, left side** (the reflected evolution and trace `−η̄`): if the left marks strictly
after `x_k < 0` (between `x_k` and the seed) have weight `0` and the marks at `x_k` have total weight at least
`κ/2 − 2`, almost surely the trace never visits `x_k` before the lifetime. -/
theorem ae_trace_ne_zeroSide_left (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k : Fin nL} (hk0 : xL k < 0)
    (hzero : ∀ j, xL k < xL j → ρL j = 0)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xL i = xL k), ρL i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t ≠ xL k := by
  have hER := IsIntegratedSLEEvolution.reflect hE
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) (fun t => LP.reflectC (η ω t)) := by
    filter_upwards [hη] with ω hω
    exact LP.isGeneratingTrace_reflect hω
  have e : univ.filter (fun i => (-xL) i = (-xL) k) = univ.filter (fun i => xL i = xL k) :=
    Finset.filter_congr fun i _ => by simp only [Pi.neg_apply, neg_inj]
  have hJ := ae_trace_ne_zeroSide_right hκ (GB7a.isOrderedForceWord_reflect hord) hER hη' (k := k)
    (by simp only [Pi.neg_apply]; linarith)
    (fun j hj => hzero j (by simp only [Pi.neg_apply, neg_lt_neg_iff] at hj; exact hj)) (by rw [e]; exact hS)
  filter_upwards [hJ] with ω hω t ht he
  refine hω t ht ?_
  rw [he]
  simp [LP.reflectC]

end Barrier

end Sec5.CfLocalCmp

end InteractingSLE
