/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafFC

/-!
# First visits of a launched piece, from the conditional pair to the original counterflow (deterministic)

Packet PROVE-T14-GW4REG. GW1's item 2 (p. 619): "`η[0, T_{w_j}]` has the complete conditional counterflow kernel in
`U_j` from `y` to `w_j`"; item 3: "Every point of `A_j \ {w_j}` has first counterflow visit strictly after
`T_{w_j}`". In the clock form `GW1Z.IsLaunchClock`, the relative tips of the conditional counterflow (read through the
launch chart `c`) at relative time `r` are the original tips at `ℓ(r)`, `ℓ` a strictly increasing clock onto
`[0, T_A)`, `T_A` the first time the original tip is in the old set `A`.

* `reverseVisits_of_min`: GB6's first-contact minimality at dense rational interior-tip times, visits and
  injectivity give strict reverse first visits along the piece on `(0, S]` (relative coordinates);
* `tipAt_infinitySourceChart_iff`, `tipAt_trans_iff`: the tips of a counterflow read through `R(z) = −1/z`, and
  through a chart moving points boundedly;
* **`firstVisit_eq_clock`**: a point `p` of the piece (chart coordinates) off the fibres over `A` and relatively
  visited is first visited by the original counterflow at `ℓ(T_rel(p)) < T_A`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

open GW1Z

/-! ### Strict reverse first visits along a piece (relative coordinates) -/

/-- **Strict reverse first visits along a piece up to its stop** from first-contact minimality at dense rational
interior-tip times, visits of all points after the seed, and injectivity. -/
theorem reverseVisits_of_min {α γ : ℝ≥0 → ℂ} {S : ℝ≥0∞} (hα : ContinuousOn α {t | (t : ℝ≥0∞) ≤ S})
    (hγ : Continuous γ)
    (hD : ∀ a b : ℝ≥0, a < b → (b : ℝ≥0∞) ≤ S → ∃ q : ℚ, a < rt q ∧ rt q < b ∧ (rt q : ℝ≥0∞) < S ∧
      α (rt q) ∈ H)
    (hmin : ∀ q : ℚ, 0 < rt q → (rt q : ℝ≥0∞) < S → α (rt q) ∈ H → ∀ v ≤ rt q,
      GB11.firstVisit γ (α (rt q)) ≤ GB11.firstVisit γ (α v))
    (hvis : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → GB11.firstVisit γ (α t) < ⊤)
    (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ S}) :
    ∀ s s' : ℝ≥0, 0 < s → s < s' → (s' : ℝ≥0∞) ≤ S → GB11.firstVisit γ (α s') < GB11.firstVisit γ (α s) := by
  intro s s' hs hss hs'
  have hsS : (s : ℝ≥0∞) ≤ S := le_trans (ENNReal.coe_le_coe.2 hss.le) hs'
  have hle : GB11.firstVisit γ (α s') ≤ GB11.firstVisit γ (α s) := by
    have hfin := hvis s hs hsS
    set B : ℝ≥0 := (GB11.firstVisit γ (α s)).toNNReal with hB
    have hBeq : (B : ℝ≥0∞) = GB11.firstVisit γ (α s) := ENNReal.coe_toNNReal hfin.ne
    -- rational interior-tip times in `(s, s')` converging to `s'`
    have hseq : ∀ n : ℕ, ∃ q : ℚ, max s (s' - 1 / ((n : ℝ≥0) + 1)) < rt q ∧ rt q < s' ∧
        (rt q : ℝ≥0∞) < S ∧ α (rt q) ∈ H := fun n =>
      hD _ _ (max_lt hss (tsub_lt_self (lt_of_le_of_lt zero_le hss) (by positivity))) hs'
    choose q hq1 hq2 hq3 hq4 using hseq
    have hqt : Tendsto (fun n => rt (q n)) atTop (𝓝 s') := by
      have hlow : Tendsto (fun n : ℕ => s' - 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 s') := by
        have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
          _root_.tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using (tendsto_const_nhds (x := s')).sub h0
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
        (fun n => ((le_max_right _ _).trans_lt (hq1 n)).le) fun n => (hq2 n).le
    have hqs : ∀ n, s < rt (q n) := fun n => (le_max_left _ _).trans_lt (hq1 n)
    -- the first visits of `α(q n)`, attained and bounded by `T(α(s))`
    have hvq : ∀ n, GB11.firstVisit γ (α (rt (q n))) < ⊤ := fun n =>
      hvis _ (hs.trans (hqs n)) (hq3 n).le
    choose t ht htγ htα using fun n => GW4Reg.exists_eq_firstVisit hγ (hvq n)
    have htB : ∀ n, t n ∈ Icc (0 : ℝ≥0) B := fun n => by
      refine ⟨zero_le, ?_⟩
      have : (t n : ℝ≥0∞) ≤ B := by
        rw [ht n, hBeq]
        exact hmin (q n) (hs.trans (hqs n)) (hq3 n) (hq4 n) s (hqs n).le
      exact_mod_cast this
    obtain ⟨t₀, ht₀B, φ, hφ, hφt⟩ := isCompact_Icc.tendsto_subseq htB
    have hαlim : Tendsto (fun n => α (rt (q (φ n)))) atTop (𝓝 (α s')) :=
      (hα s' hs').tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hqt.comp hφ.tendsto_atTop, Eventually.of_forall fun n => (hq3 (φ n)).le⟩)
    have hγlim : Tendsto (fun n => γ (t (φ n))) atTop (𝓝 (γ t₀)) := (hγ.tendsto t₀).comp hφt
    have hγ0 : γ t₀ ≠ 0 := by
      intro h0
      have hinv : Tendsto (fun n => ‖γ (t (φ n))‖) atTop (𝓝 0) := by
        simpa [h0] using hγlim.norm
      have hbig : Tendsto (fun n => ‖α (rt (q (φ n)))‖) atTop atTop := by
        have hpos : ∀ n, 0 < ‖γ (t (φ n))‖ := fun n => norm_pos_iff.2 (htγ (φ n))
        have : (fun n => ‖α (rt (q (φ n)))‖) = fun n => (‖γ (t (φ n))‖)⁻¹ := by
          funext n; rw [← htα (φ n), norm_neg, norm_inv]
        rw [this]
        exact (tendsto_inv_nhdsGT_zero).comp (tendsto_nhdsWithin_iff.2 ⟨hinv, Eventually.of_forall hpos⟩)
      exact not_tendsto_atTop_of_tendsto_nhds hαlim.norm hbig
    have hvisit : -(γ t₀)⁻¹ = α s' := by
      have h1 : Tendsto (fun n => -(γ (t (φ n)))⁻¹) atTop (𝓝 (-(γ t₀)⁻¹)) := (hγlim.inv₀ hγ0).neg
      have h2 : (fun n => -(γ (t (φ n)))⁻¹) = fun n => α (rt (q (φ n))) := funext fun n => htα (φ n)
      rw [h2] at h1
      exact tendsto_nhds_unique h1 hαlim
    calc GB11.firstVisit γ (α s') ≤ t₀ := hvisit ▸ GB11.firstVisit_le hγ0
      _ ≤ B := ENNReal.coe_le_coe.2 ht₀B.2
      _ = GB11.firstVisit γ (α s) := hBeq
  refine lt_of_le_of_ne hle fun heq => ?_
  obtain ⟨T, hT, hγT, hTα⟩ := GW4Reg.exists_eq_firstVisit hγ (hvis s' (hs.trans hss) hs')
  obtain ⟨T', hT', hγT', hT'α⟩ := GW4Reg.exists_eq_firstVisit hγ (hvis s hs hsS)
  have hTT : T = T' := by
    have : (T : ℝ≥0∞) = T' := by rw [hT, hT', heq]
    exact_mod_cast this
  rw [hTT, hT'α] at hTα
  exact hss.ne (hinj hsS hs' hTα)

/-! ### Reading tips -/

/-- The radial limits of a counterflow chain, read through `R(z) = −1/z`: the tip at `s` is `−1/γ(s)`, and there
is none when `γ(s) = 0`. -/
theorem tipAt_infinitySourceChart_iff {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hW : Continuous W) (hW0 : W 0 = 0) (s : ℝ≥0) (z : ℂ) :
    infinitySourceChart.tipAt W s z ↔ γ s ≠ 0 ∧ z = -(γ s)⁻¹ := by
  have hF := hγ.tendsto_fwdMapInv_mul_I hW.continuousOn hW0 (ENNReal.coe_lt_top (r := s))
  have hU : Continuous fun s : ℝ => W s.toNNReal := hW.comp continuous_real_toNNReal
  have hU0 : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simpa using hW0
  unfold Chart.tipAt
  rw [CounterflowRange.infinitySourceChart_inv]
  constructor
  · intro h
    have hne : γ s ≠ 0 := by
      intro h0
      rw [h0] at hF
      have hn : Tendsto (fun y : ℝ => ‖fwdMapInv (fun s : ℝ => W s.toNNReal) s ((y : ℂ) * Complex.I)‖)
          (𝓝[>] 0) (𝓝 0) := by simpa using hF.norm
      have hpos : ∀ᶠ y : ℝ in 𝓝[>] 0,
          0 < ‖fwdMapInv (fun s : ℝ => W s.toNNReal) s ((y : ℂ) * Complex.I)‖ := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        refine norm_pos_iff.2 fun h0 => ?_
        have hH := QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg s)
          (show ((y : ℂ) * Complex.I) ∈ H by show 0 < ((y : ℂ) * Complex.I).im; simpa using hy)
        rw [h0] at hH
        have h00 : (0 : ℝ) < (0 : ℂ).im := hH
        simp at h00
      have hbig := (tendsto_inv_nhdsGT_zero).comp (tendsto_nhdsWithin_iff.2 ⟨hn, hpos⟩)
      have hh := h.norm
      refine not_tendsto_atTop_of_tendsto_nhds hh ?_
      refine hbig.congr fun y => ?_
      simp [norm_neg, norm_inv]
    exact ⟨hne, tendsto_nhds_unique h (hF.inv₀ hne).neg⟩
  · rintro ⟨hne, rfl⟩
    exact (hF.inv₀ hne).neg

/-- A boundary-limit map of a chart agrees with the chart inside `ℍ`. -/
theorem eq_of_tendsto_chart {c : Chart} {f : ℂ → ℂ} (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {w : ℂ} (hw : w ∈ H) : c.2.1 w = f w :=
  tendsto_nhds_unique (tendsto_pure_nhds c.2.1 w)
    ((hf w (le_of_lt hw : (0 : ℝ) ≤ w.im)).mono_left (pure_le_nhdsWithin hw))

/-- **The relative tips of a conditional counterflow read through a launch chart**: if `c⁻¹` has boundary limits `f`
on `ℍ̄` moving points by at most `C`, the tip at `r` read through `c` and `R(z) = −1/z` is `f(−1/γ(r))`, and there is
none when `γ(r) = 0`. -/
theorem tipAt_trans_imp {c : Chart} {f : ℂ → ℂ} (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {C : ℝ} (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C) {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ≥0} {z : ℂ}
    (h : (c.trans infinitySourceChart).tipAt W r z) : γ r ≠ 0 ∧ z = f (-(γ r)⁻¹) := by
  have hne : γ r ≠ 0 := by
    intro h0
    have hF := hγ.tendsto_fwdMapInv_mul_I hW.continuousOn hW0 (ENNReal.coe_lt_top (r := r))
    rw [h0] at hF
    have hU : Continuous fun s : ℝ => W s.toNNReal := hW.comp continuous_real_toNNReal
    have hU0 : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simpa using hW0
    set F : ℝ → ℂ := fun y => fwdMapInv (fun s : ℝ => W s.toNNReal) r ((y : ℂ) * Complex.I) with hFdef
    have hFH : ∀ᶠ y : ℝ in 𝓝[>] 0, F y ∈ H := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg r)
        (show ((y : ℂ) * Complex.I) ∈ H by show 0 < ((y : ℂ) * Complex.I).im; simpa using hy)
    have hn : Tendsto (fun y => ‖F y‖) (𝓝[>] 0) (𝓝 0) := by simpa using hF.norm
    have hpos : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < ‖F y‖ := hFH.mono fun y hy => norm_pos_iff.2 (GW4Traverse.ne_zero_of_mem_H' hy)
    have hbig : Tendsto (fun y => ‖F y‖⁻¹) (𝓝[>] 0) atTop :=
      (tendsto_inv_nhdsGT_zero).comp (tendsto_nhdsWithin_iff.2 ⟨hn, hpos⟩)
    have hbig' : Tendsto (fun y => ‖F y‖⁻¹ - C) (𝓝[>] 0) atTop := tendsto_atTop_add_const_right _ _ hbig
    have hge : ∀ᶠ y : ℝ in 𝓝[>] 0, ‖F y‖⁻¹ - C ≤ ‖(c.trans infinitySourceChart).2.1 (F y)‖ := by
      filter_upwards [hFH] with y hy
      have hwH : -(F y)⁻¹ ∈ H := GW4Traverse.negInv_mem_H' hy
      change ‖F y‖⁻¹ - C ≤ ‖c.2.1 (-(F y)⁻¹)‖
      rw [eq_of_tendsto_chart hf hwH]
      have h1 := hC _ (le_of_lt hwH : (0 : ℝ) ≤ (-(F y)⁻¹).im)
      have h2 : ‖-(F y)⁻¹‖ = ‖F y‖⁻¹ := by rw [norm_neg, norm_inv]
      have h3 := norm_sub_norm_le (-(F y)⁻¹) (f (-(F y)⁻¹))
      rw [norm_sub_rev] at h3
      linarith
    exact not_tendsto_atTop_of_tendsto_nhds h.norm (tendsto_atTop_mono' _ hge hbig')
  exact ⟨hne, tendsto_nhds_unique h (GW2aPiece.tipAt_trans_of_ne_zero hf hγ hW hW0 hne)⟩

/-- **First visits through the launch clock** (GW1 items 2–3). A point `p` of `ℍ̄` (chart coordinates) whose image
`f(p)` is off the old set `A` (and off the fibres over it) and which the conditional counterflow visits is first
visited by the original counterflow at `ℓ(T_rel(p))`, strictly before `T_A`. -/
theorem firstVisit_eq_clock {c : Chart} {f : ℂ → ℂ} (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {C : ℝ} (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C) {A : Set ℂ}
    (hfib : ∀ x ∈ Hbar, ∀ y ∈ Hbar, f x = f y → f x ∉ A → x = y)
    {Wk W' : ℝ≥0 → ℝ} {γk γ : ℝ≥0 → ℂ} (hγk : IsGeneratingTrace Wk ⊤ γk) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    (hγ : IsGeneratingTrace W' ⊤ γ) (hW' : Continuous W') (hW'0 : W' 0 = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓ : StrictMono ℓ)
    (hrange : range ℓ = {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime infinitySourceChart W' A})
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk r z ↔
      infinitySourceChart.tipAt W' (ℓ r) z)
    {p : ℂ} (hp : p ∈ Hbar) (hpA : f p ∉ A) (hvis : GB11.firstVisit γk p < ⊤) :
    GB11.firstVisit γ (f p) = ℓ (GB11.firstVisit γk p).toNNReal ∧
      (ℓ (GB11.firstVisit γk p).toNNReal : ℝ≥0∞) < firstTipTime infinitySourceChart W' A := by
  have hγkc : Continuous γk := Sec5.continuous_of_isGeneratingTrace_top hγk
  obtain ⟨r₀, hr₀, hγr₀, hpr₀⟩ := GW4Reg.exists_eq_firstVisit hγkc hvis
  have hr₀' : (GB11.firstVisit γk p).toNNReal = r₀ := by rw [← hr₀, ENNReal.toNNReal_coe]
  rw [hr₀']
  have htip : infinitySourceChart.tipAt W' (ℓ r₀) (f p) := by
    rw [← hiff, ← hpr₀]
    exact GW2aPiece.tipAt_trans_of_ne_zero hf hγk hWk hWk0 hγr₀
  obtain ⟨hγℓ, hfp⟩ := (tipAt_infinitySourceChart_iff hγ hW' hW'0 _ _).1 htip
  have hlt : (ℓ r₀ : ℝ≥0∞) < firstTipTime infinitySourceChart W' A := by
    have : ℓ r₀ ∈ range ℓ := ⟨r₀, rfl⟩
    rw [hrange] at this
    exact this
  refine ⟨le_antisymm ?_ ?_, hlt⟩
  · rw [hfp]; exact GB11.firstVisit_le hγℓ
  · refine le_iInf₂ fun s hs => ?_
    by_contra hsl
    push Not at hsl
    have hs' : (s : ℝ≥0∞) < firstTipTime infinitySourceChart W' A := lt_trans hsl hlt
    obtain ⟨r', rfl⟩ : s ∈ range ℓ := by rw [hrange]; exact hs'
    have hr'lt : r' < r₀ := hℓ.lt_iff_lt.1 (by exact_mod_cast hsl)
    have htip' : infinitySourceChart.tipAt W' (ℓ r') (f p) :=
      (tipAt_infinitySourceChart_iff hγ hW' hW'0 _ _).2 ⟨hs.1, hs.2.symm⟩
    obtain ⟨hγr', hfeq⟩ := tipAt_trans_imp hf hC hγk hWk hWk0 ((hiff r' (f p)).2 htip')
    have hHbar : -(γk r')⁻¹ ∈ Hbar :=
      GW2aPiece.neg_inv_mem_Hbar (GW2aPiece.trace_mem_Hbar hγk hWk hWk0 r')
    have hpeq : p = -(γk r')⁻¹ := hfib p hp _ hHbar hfeq hpA
    have h1 : GB11.firstVisit γk p ≤ r' := by
      rw [hpeq]; exact GB11.firstVisit_le hγr'
    rw [← hr₀] at h1
    exact absurd (ENNReal.coe_le_coe.1 h1) (not_le.2 hr'lt)

/-- **The first tip time in `A` bounds the first visit of every point of `A`.** -/
theorem firstTipTime_le_firstVisit {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W' ⊤ γ)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {A : Set ℂ} {p : ℂ} (hp : p ∈ A) :
    firstTipTime infinitySourceChart W' A ≤ GB11.firstVisit γ p :=
  le_iInf₂ fun s hs => iInf₂_le s ⟨p, hp, (tipAt_infinitySourceChart_iff hγ hW' hW'0 _ _).2 ⟨hs.1, hs.2.symm⟩⟩

end GW4Leaf

end Theorem14

end InteractingSLE
