/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SgkRead
import InteractingSLE.Spec.Supplement.BW1DetWitness
import InteractingSLE.Spec.Sec5.Prop513

/-!
# GW2's stage stop `σ_k`, part 2: the stop of the conditional counterflow is a stopping time

Packet PROVE-GW2-STAGEMEAN, σ round. Under the conditional law at a launch, the conditional counterflow `W_k` and the
original counterflow `W'` satisfy the tip relation of the launch datum (`GW2TipSystem.HasLaunchPairEq`): the tips of
`W_k` through the launch chart `c` and the inversion are the tips of `W'` at the changed times `ℓ(r)`. Then:

* **`physRead_eq`**: the trace of `W'` at `ℓ(r)` is `Φ` of the trace of `W_k` at `r` (`BW1Det.tipRel_iff_traces`);
* **`capRead_eq`**: the reader of `W_k`'s path is the original capacity, `capRead f t (W_k) = 2 ℓ(t)`
  (`Sec5.hcapHit_image_Icc_of_isGeneratingTrace`, `Sec5.CrossRestart.hcapHit_image_ratGrid`);
* **`capStop_eq`**: hence the first rational exceedance of `2s` is the time `t₀` with `ℓ(t₀) = s`;
* **`exists_stop_of_clock`** (`σ_k` for `GW2Stm.exists_unionMean_gw2_stop`): a stopping time `σ` of the driving
  filtration of `W_k`'s coupling, finite and `≤ N`, with almost surely `σ = t₀` whenever `ℓ(t₀) = s` and `t₀ < N`.
  `σ` is a functional of `W_k`'s own killed path (`GW2Sgk.capStop`), so it is the stop `σ_k` of the stage's retained
  counterflow: the original counterflow at its fixed time `s` is `W_k` at `σ_k`.

Conditional helpers with distinct names; the hypotheses are the launch datum's clauses and the regularity of the two
counterflows (Theorem 1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2Sgk

open WangWu (negInv)

theorem negInv_negInv (z : ℂ) : negInv (negInv z) = z := by
  unfold negInv
  rw [inv_neg, inv_inv, neg_neg]

theorem continuous_of_trace_top {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ) : Continuous γ := by
  have := hγ.2.1
  simp only [le_top, ofPred_true] at this
  exact continuousOn_univ.1 this

/-- **The original trace at the changed time is `Φ` of the conditional trace.** -/
theorem physRead_eq {c : Chart} {f : ℂ → ℂ} {C : ℝ} (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C) {w w' : ℝ≥0 → ℝ} {γ γ' : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
    (hw : Continuous w) (hw0 : w 0 = 0) (hγ' : IsGeneratingTrace w' ⊤ γ') (hw' : Continuous w') (hw'0 : w' 0 = 0)
    {r s : ℝ≥0} (hiff : ∀ z, (c.trans infinitySourceChart).tipAt w r z ↔ infinitySourceChart.tipAt w' s z) :
    physRead f (γ r) = γ' s := by
  classical
  obtain ⟨h0, hne⟩ := (BW1Det.tipRel_iff_traces hf hC hγ hw hw0 hγ' hw' hw'0 r s).1 hiff
  by_cases hr : γ r = 0
  · rw [hr, h0.1 hr]
    simp only [physRead, ↓reduceIte]
  · have hH : negInv (γ r) ∈ Hbar := GW4Traverse.negInv_mem_Hbar (GW2aPiece.trace_mem_Hbar hγ hw hw0 r)
    have e : physRead f (γ r) = negInv (bdryB f (negInv (γ r))) := by simp only [physRead, hr, ↓reduceIte]
    have hne' : f (negInv (γ r)) = negInv (γ' s) := hne hr
    rw [e, bdryB_eq hH, hne', negInv_negInv]

/-- **The reader of the conditional counterflow's path is the original capacity `2ℓ(t)`.** -/
theorem capRead_eq {c : Chart} {f : ℂ → ℂ} {C : ℝ} (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C) {w w' : ℝ≥0 → ℝ} {γ γ' : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
    (hw : Continuous w) (hw0 : w 0 = 0) (hγ' : IsGeneratingTrace w' ⊤ γ') (hw' : Continuous w') (hw'0 : w' 0 = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : Monotone ℓ) (hℓ0 : ℓ 0 = 0)
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt w r z ↔
      infinitySourceChart.tipAt w' (ℓ r) z) (t : ℝ≥0) :
    capRead f t w = 2 * (ℓ t : ℝ≥0∞) := by
  have himg : (fun q => physRead f (LP.traceAt q w)) '' Sec5.CrossRestart.ratGrid t =
      (fun q => γ' (ℓ q)) '' Sec5.CrossRestart.ratGrid t := by
    refine image_congr fun q _ => ?_
    rw [LP.traceAt_eq_of_isGeneratingTrace hγ hw.continuousOn hw0 ENNReal.coe_lt_top]
    exact physRead_eq hf hC hγ hw hw0 hγ' hw' hw'0 (hiff q)
  have hΓc : Continuous fun q => γ' (ℓ q) := (continuous_of_trace_top hγ').comp hℓc
  have hIcc : ℓ '' Icc 0 t = Icc 0 (ℓ t) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨zero_le, hℓm hx.2⟩
    · have h1 := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t) hℓc.continuousOn
      rwa [hℓ0] at h1
  unfold capRead
  rw [himg, Sec5.CrossRestart.hcapHit_image_ratGrid hΓc.continuousOn, ← image_image γ' ℓ, hIcc]
  exact Sec5.hcapHit_image_Icc_of_isGeneratingTrace hw' hw'0 hγ' (ℓ t)

/-- **The first rational exceedance of a strictly increasing function** is the time it attains the level. -/
theorem iInf_rat_eq {g : ℝ≥0 → ℝ≥0} (hg : StrictMono g) {s t₀ : ℝ≥0} (ht₀ : g t₀ = s) :
    (⨅ q : ℚ, if 0 ≤ q ∧ s < g (q : ℝ).toNNReal then (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) else ⊤) =
      (t₀ : ℝ≥0∞) := by
  classical
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hc
    have hlt : t₀ < (q : ℝ).toNNReal := ENNReal.coe_lt_coe.1 hq1
    have hcond : 0 ≤ q ∧ s < g (q : ℝ).toNNReal := ⟨hq0, ht₀ ▸ hg hlt⟩
    refine (iInf_le _ q).trans ?_
    simp only [hcond, and_self, ↓reduceIte]
    exact hq2.le
  · refine le_iInf fun q => ?_
    split_ifs with hcond
    · refine le_of_not_gt fun hlt => ?_
      have hlt' : (q : ℝ).toNNReal < t₀ := ENNReal.coe_lt_coe.1 hlt
      have h1 := hg hlt'
      rw [ht₀] at h1
      exact absurd hcond.2 (not_lt.2 h1.le)
    · exact le_top

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- **The stop of the reader is the time at which the clock attains the level**, at one sample with infinite
lifetime. -/
theorem capStop_eq {c : Chart} {f : ℂ → ℂ} {C : ℝ} (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C) {W W' : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤)
    {γ γ' : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace (fun t => W t ω) ⊤ γ) (hw : Continuous fun t => W t ω)
    (hw0 : W 0 ω = 0) (hγ' : IsGeneratingTrace (fun t => W' t ω) ⊤ γ') (hw' : Continuous fun t => W' t ω)
    (hw'0 : W' 0 ω = 0) {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ) (hℓ0 : ℓ 0 = 0)
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt (fun t => W t ω) r z ↔
      infinitySourceChart.tipAt (fun t => W' t ω) (ℓ r) z) {s t₀ : ℝ≥0} (ht₀ : ℓ t₀ = s) :
    capStop f s W ζ ω = (t₀ : ℝ≥0∞) := by
  classical
  have hkill : killedPath W ζ ω = fun t => W t ω := funext fun r => by
    simp only [killedPath, hζ, ENNReal.coe_lt_top, ↓reduceIte]
  have hcap : ∀ q : ℝ≥0, capRead f q (killedPath W ζ ω) = 2 * (ℓ q : ℝ≥0∞) := fun q => by
    rw [hkill]
    exact capRead_eq hf hC hγ hw hw0 hγ' hw' hw'0 hℓc hℓm.monotone hℓ0 hiff q
  have hiffc : ∀ q : ℝ≥0, 2 * (s : ℝ≥0∞) < capRead f q (killedPath W ζ ω) ↔ s < ℓ q := fun q => by
    rw [hcap, show (2 : ℝ≥0∞) * (s : ℝ≥0∞) = ((2 * s : ℝ≥0) : ℝ≥0∞) by push_cast; ring,
      show (2 : ℝ≥0∞) * (ℓ q : ℝ≥0∞) = ((2 * ℓ q : ℝ≥0) : ℝ≥0∞) by push_cast; ring, ENNReal.coe_lt_coe]
    constructor
    · intro h
      exact lt_of_mul_lt_mul_left h zero_le
    · intro h
      exact mul_lt_mul_of_pos_left h (by norm_num)
  unfold capStop
  simp_rw [hiffc]
  exact iInf_rat_eq hℓm ht₀

/-- **The stage stop `σ_k`: a stopping time of the conditional counterflow's driving filtration at which the
original counterflow reaches its fixed time `s`.** The hypotheses are the launch datum's clauses (infinite lifetime, the
clock and the tip relation through the launch chart `c`) and the regularity of the two counterflows. -/
theorem exists_stop_of_clock (P : Measure Ω) {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) {W' : ℝ≥0 → Ω → ℝ}
    {c : Chart} (hc : GW1P.HasProperBdryExt c) {ℓ : Ω → ℝ≥0 → ℝ≥0} (s N : ℝ≥0)
    (hae : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ) ∧
      Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧ (∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ') ∧
      Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧ ℓ ω 0 = 0 ∧
      ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt (fun t => W t ω) r z ↔
        infinitySourceChart.tipAt (fun t => W' t ω) (ℓ ω r) z) :
    ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime (drivingFiltration P hX) σ ∧ (∀ ω, σ ω ≠ ⊤) ∧
      (∀ ω, σ ω ≤ (N : WithTop ℝ≥0)) ∧
      ∀ᵐ ω ∂P, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < N → σ ω = (t₀ : WithTop ℝ≥0) := by
  obtain ⟨f, C, hf, hC⟩ := hc
  have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  refine ⟨fun ω => min (capStop f s W ζ ω) (N : ℝ≥0∞), isStoppingTime_capStop hfc P hX s N,
    fun ω => ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _), fun ω => min_le_right _ _, ?_⟩
  filter_upwards [hae] with ω hω t₀ ht₀ htN
  obtain ⟨hζ, hw, hw0, ⟨γ, hγ⟩, hw', hw'0, ⟨γ', hγ'⟩, hℓc, hℓm, hℓ0, hiff⟩ := hω
  have h1 := capStop_eq hf hC hζ hγ hw hw0 hγ' hw' hw'0 hℓc hℓm hℓ0 hiff ht₀
  show min (capStop f s W ζ ω) (N : ℝ≥0∞) = (t₀ : ℝ≥0∞)
  rw [h1]
  exact min_eq_left (ENNReal.coe_le_coe.2 htN.le)

/-- The clock of a launch datum starts at `0` (its range is an initial segment containing `0`). -/
theorem clock_zero_of_range {ℓ : ℝ≥0 → ℝ≥0} (hℓm : StrictMono ℓ) {T : ℝ≥0∞}
    (hr : range ℓ = {t : ℝ≥0 | (t : ℝ≥0∞) < T}) : ℓ 0 = 0 := by
  have hmem : ℓ 0 ∈ range ℓ := mem_range_self 0
  rw [hr] at hmem
  have h0 : (0 : ℝ≥0) ∈ range ℓ := by
    rw [hr]
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 zero_le) hmem
  obtain ⟨r, hr0⟩ := h0
  exact le_antisymm ((hℓm.monotone (zero_le : (0 : ℝ≥0) ≤ r)).trans hr0.le) zero_le

end InteractingSLE.Theorem14.GW2Sgk
