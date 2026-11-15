/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4a
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# GW2's open lines: counterflow tips, the first tip time in a set, and no contact

Packet PROVE-GW2-STAGEMEAN, R120 round (localization). In the infinity-source chart a counterflow tip at time `t` is
the inverted trace point `−1/γ(t)`; hence the counterflow reaches a closed set `A` (the explored prefix) after the
retained time `s` exactly when it has no contact with `A` on `[0, s]`:

* **`tipAt_infinity_iff`**, `not_tipAt_infinity_of_trace_eq_zero`;
* **`lt_firstTipTime_of_noContact`**: no inverted trace point of `[0, s]` in a compact `A` ⇒ `s < firstTipTime`;
* **`noContact_of_lt_firstTipTime`**: `s < firstTipTime` ⇒ no inverted trace point of `(0, s]` in `A`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Omx

/-- **A counterflow tip in the infinity-source chart is the inverted trace point.** -/
theorem tipAt_infinity_iff {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ≥0} (hγt : γ t ≠ 0) {z : ℂ} :
    infinitySourceChart.tipAt W t z ↔ z = -(γ t)⁻¹ := by
  have hlim := hγ.tendsto_fwdMapInv_mul_I hWc.continuousOn hW0 (t := t) ENNReal.coe_lt_top
  have hinv : ContinuousAt (fun w : ℂ => -w⁻¹) (γ t) := (continuousAt_inv₀ hγt).neg
  have hlim' : Tendsto (fun y : ℝ => infinitySourceChart.2.1
      (QuantumZipper.fwdMapInv (fun r : ℝ => W r.toNNReal) t (y * Complex.I))) (𝓝[>] 0) (𝓝 (-(γ t)⁻¹)) :=
    hinv.tendsto.comp hlim
  constructor
  · intro h
    exact tendsto_nhds_unique h hlim'
  · rintro rfl
    exact hlim'

/-- **No tip where the trace vanishes** (in the infinity-source chart). -/
theorem not_tipAt_infinity_of_trace_eq_zero {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hWc : Continuous W) (hW0 : W 0 = 0) {t : ℝ≥0} (hγt : γ t = 0) (z : ℂ) :
    ¬ infinitySourceChart.tipAt W t z := by
  intro h
  have hlim := hγ.tendsto_fwdMapInv_mul_I hWc.continuousOn hW0 (t := t) ENNReal.coe_lt_top
  rw [hγt] at hlim
  have hWc' : Continuous fun s : ℝ => W s.toNNReal := hWc.comp continuous_real_toNNReal
  have hW0' : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simpa using hW0
  have hne : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
      QuantumZipper.fwdMapInv (fun s : ℝ => W s.toNNReal) t ((y : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hH := QuantumZipper.RS.fwdMapInv_mem_H hWc' hW0' (NNReal.coe_nonneg t)
      (w := (y : ℂ) * Complex.I) (by show 0 < ((y : ℂ) * Complex.I).im; simpa using hy)
    intro h0
    rw [h0] at hH
    exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH))
  have h1 := hlim.mul h
  rw [zero_mul] at h1
  have h2 : Tendsto (fun _ : ℝ => (-1 : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [hne] with y hy
    change QuantumZipper.fwdMapInv _ t _ * -(QuantumZipper.fwdMapInv _ t _)⁻¹ = -1
    field_simp
  have := tendsto_nhds_unique tendsto_const_nhds h2
  norm_num at this

/-- **No contact on `[0, s]` with a closed set: the first tip time in it is after `s`.** -/
theorem lt_firstTipTime_of_noContact {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hWc : Continuous W) (hW0 : W 0 = 0) {A : Set ℂ} (hA : IsCompact A) {s : ℝ≥0}
    (hsep : ∀ t ≤ s, γ t ≠ 0 → -(γ t)⁻¹ ∉ A) :
    (s : ℝ≥0∞) < firstTipTime infinitySourceChart W A := by
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  by_contra hle
  rw [not_lt] at hle
  set τ := firstTipTime infinitySourceChart W A with hτ
  have hτt : τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  set τr : ℝ≥0 := τ.toNNReal with hτr
  have hτeq : (τr : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hτt
  have hτs : τr ≤ s := by
    rw [← hτeq] at hle
    exact_mod_cast hle
  set ε : ℕ → ℝ≥0 := fun n => (1 / ((n : ℝ) + 1)).toNNReal with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by
    simp only [hε, Real.toNNReal_pos]
    positivity
  -- tips in `A` at times approaching `τ` from above
  have key : ∀ n : ℕ, ∃ t : ℝ≥0, (∃ z ∈ A, infinitySourceChart.tipAt W t z) ∧ t < τr + ε n := by
    intro n
    have hlt : τ < ((τr + ε n : ℝ≥0) : ℝ≥0∞) := by
      rw [← hτeq]
      exact_mod_cast lt_add_of_pos_right τr (hεpos n)
    rw [hτ, firstTipTime] at hlt
    obtain ⟨t, ht⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hz, htlt⟩ := iInf_lt_iff.1 ht
    exact ⟨t, hz, by exact_mod_cast htlt⟩
  choose t ht using key
  have hlo : ∀ n, τr ≤ t n := fun n => by
    have h1 : τ ≤ (t n : ℝ≥0∞) :=
      iInf₂_le (f := fun (t : ℝ≥0) (_ : ∃ z ∈ A, infinitySourceChart.tipAt W t z) => (t : ℝ≥0∞)) _ (ht n).1
    rw [← hτeq] at h1
    exact_mod_cast h1
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (continuous_real_toNNReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hε, Function.comp_def] using h
  have hconv : Tendsto t atTop (𝓝 τr) := by
    have hup : Tendsto (fun n => τr + ε n) atTop (𝓝 τr) := by
      simpa using (tendsto_const_nhds (x := τr)).add hεlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hlo fun n => (ht n).2.le
  -- the tip points `−1/γ(t n)` lie in the compact `A`
  have hz : ∀ n, γ (t n) ≠ 0 ∧ -(γ (t n))⁻¹ ∈ A := fun n => by
    obtain ⟨z, hzA, htip⟩ := (ht n).1
    by_cases h0 : γ (t n) = 0
    · exact absurd htip (not_tipAt_infinity_of_trace_eq_zero hγ hWc hW0 h0 z)
    · rw [(tipAt_infinity_iff hγ hWc hW0 h0).1 htip] at hzA
      exact ⟨h0, hzA⟩
  have hγlim : Tendsto (fun n => γ (t n)) atTop (𝓝 (γ τr)) := (hγc.tendsto τr).comp hconv
  by_cases h0 : γ τr = 0
  · -- the inverted points escape every bounded set
    obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall 0
    have hsmall : ∀ᶠ n in atTop, ‖γ (t n)‖ < 1 / (|R| + 1) := by
      have hpos : (0 : ℝ) < 1 / (|R| + 1) := by positivity
      have := (continuous_norm.tendsto _).comp hγlim
      rw [h0, norm_zero] at this
      exact this.eventually (gt_mem_nhds hpos)
    obtain ⟨n, hn⟩ := hsmall.exists
    have hmem := hR (hz n).2
    rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_inv] at hmem
    have hγpos : 0 < ‖γ (t n)‖ := norm_pos_iff.2 (hz n).1
    have h1 : |R| + 1 < ‖γ (t n)‖⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hγpos]
      simpa using hn
    linarith [le_abs_self R]
  · have hlim : Tendsto (fun n => -(γ (t n))⁻¹) atTop (𝓝 (-(γ τr)⁻¹)) :=
      ((continuousAt_inv₀ h0).neg.tendsto).comp hγlim
    have hmem : -(γ τr)⁻¹ ∈ A := hA.isClosed.mem_of_tendsto hlim (Eventually.of_forall fun n => (hz n).2)
    exact hsep τr hτs h0 hmem

/-- **Before the first tip time in a set there is no contact with it.** -/
theorem noContact_of_lt_firstTipTime {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hWc : Continuous W) (hW0 : W 0 = 0) {A : Set ℂ} {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < firstTipTime infinitySourceChart W A) {t : ℝ≥0} (ht : t ≤ s) (hγt : γ t ≠ 0) :
    -(γ t)⁻¹ ∉ A := by
  intro hA
  have htip : infinitySourceChart.tipAt W t (-(γ t)⁻¹) := (tipAt_infinity_iff hγ hWc hW0 hγt).2 rfl
  have hle : firstTipTime infinitySourceChart W A ≤ t :=
    iInf₂_le (f := fun (t : ℝ≥0) (_ : ∃ z ∈ A, infinitySourceChart.tipAt W t z) => (t : ℝ≥0∞)) t ⟨_, hA, htip⟩
  exact absurd (hs.trans_le hle) (not_lt.2 (by exact_mod_cast ht))

end InteractingSLE.Theorem14.GW2Omx
