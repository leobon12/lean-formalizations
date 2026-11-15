/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71CClock

/-!
# Curves with local Loewner drivers: the canonical driver and its generating trace

Packet PROVE-STRIPSYS10 (specification §7.4.1, proof of Lemma 7.25, p. 414: "the erased counterflow is therefore a
complete continuous traversal […] with a continuous relative driver"; Aux. lemmas 40–41, pp. 203–206; Remark 6.14).

PROVE-LEMMA71C wrote the driver of a *simple* mapped segment by an explicit formula (`Lemma71C.segDrv`: left
difference quotients of the mapping-out functions of the filled prefixes at the points `i (N + 1)`), so that it is
visibly measurable. Simplicity is used there only through Proposition 6.12 on compact intervals
(`Lemma71C.IsSegCurve.exists_localDriver`). The erased pocket traversal of a counterflow of parameter `κ > 4` is not
simple, but Aux. lemma 41 (`Sec6.IsReversePocket.aux41`) gives exactly the same local drivers. This file therefore
states the property alone (`IsDrivenCurve`: continuous, from `0`, and on every `[0, S]` the capacity clock is a
continuous strictly increasing clock of a continuous driver whose hulls are the filled prefixes) and proves for it the
statements of `Lemma71CClock` (same proofs, with the local drivers as hypothesis), and in addition:

* `IsDrivenCurve.continuousOn_capInv`: the inverse capacity clock is continuous below the terminal capacity time;
* **`IsDrivenCurve.isGeneratingTrace`**: the capacity reparametrization `γ ∘ capInv` is a continuous generating
  trace of the canonical driver `segDriver γ` on `[0, T]` for every `T` below the terminal capacity time (and on every
  finite interval when the terminal capacity time is infinite, `isGeneratingTrace_of_capLife_eq_top`).

## Main results

* `IsDrivenCurve`, `isDrivenCurve_of_isSegCurve`;
* `IsDrivenCurve.capInv_spec`, `capInv_eq`, `capInv_of_nonpos`, `capInv_le`, `fillH_capInv_eq`;
* `IsDrivenCurve.segDrv_eq`, `IsDrivenCurve.eventually_tendsto_segDrv`, **`IsDrivenCurve.segDriver_spec`**;
* **`IsDrivenCurve.isGeneratingTrace`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketTraversal

open Lemma71C

/-! ### Curves with local drivers -/

/-- **A curve with local Loewner drivers**: continuous on `[0, ∞)`, from `0`, and on every `[0, S]` its capacity clock
`capClock γ = hcap(fill γ([0, ·]))/2` is a continuous strictly increasing clock (from `0`) of a continuous driver `W`
with `W 0 = 0` whose hulls are the filled prefixes. This is the conclusion of Proposition 6.12 on compact intervals
(`Lemma71C.IsSegCurve.exists_localDriver` for simple curves) and of Aux. lemma 41 for the erased pocket traversal. -/
structure IsDrivenCurve (γ : ℝ → ℂ) : Prop where
  continuousOn : ContinuousOn γ (Ici 0)
  zero : γ 0 = 0
  localDriver : ∀ S : ℝ, 0 < S → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ capClock γ 0 = 0 ∧
    StrictMonoOn (capClock γ) (Icc 0 S) ∧ ContinuousOn (capClock γ) (Icc 0 S) ∧
    ∀ t ∈ Icc 0 S, 0 ≤ capClock γ t ∧ QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t)

/-- A simple mapped segment has local drivers (Proposition 6.12). -/
theorem isDrivenCurve_of_isSegCurve {γ : ℝ → ℂ} (hγ : IsSegCurve γ) : IsDrivenCurve γ :=
  ⟨hγ.1, hγ.2.2.2.1, fun _ hS => hγ.exists_localDriver hS⟩

/-- The capacity reparametrization `s ↦ γ (capInv γ s)` (on `ℝ≥0`). -/
def capTrace (γ : ℝ → ℂ) (s : ℝ≥0) : ℂ := γ (capInv γ s)

namespace IsDrivenCurve

variable {γ : ℝ → ℂ}

/-! ### The capacity clock -/

theorem capClock_zero (hγ : IsDrivenCurve γ) : capClock γ 0 = 0 :=
  (hγ.localDriver 1 one_pos).choose_spec.2.2.1

theorem strictMonoOn_capClock (hγ : IsDrivenCurve γ) : StrictMonoOn (capClock γ) (Ici 0) := by
  intro a ha b hb hab
  obtain ⟨-, -, -, -, hm, -⟩ := hγ.localDriver (b + 1) (by linarith [mem_Ici.1 hb])
  exact hm ⟨ha, by linarith⟩ ⟨hb, by linarith⟩ hab

theorem continuousOn_capClock (hγ : IsDrivenCurve γ) : ContinuousOn (capClock γ) (Ici 0) := by
  intro t ht
  obtain ⟨-, -, -, -, -, hc, -⟩ := hγ.localDriver (t + 1) (by linarith [mem_Ici.1 ht])
  refine (hc t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.2 ⟨Iio (t + 1), isOpen_Iio, by simp, fun x hx => ⟨hx.2, le_of_lt hx.1⟩⟩

theorem capClock_nonneg (hγ : IsDrivenCurve γ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ capClock γ u := by
  rw [← hγ.capClock_zero]
  exact hγ.strictMonoOn_capClock.monotoneOn self_mem_Ici hu hu

/-- Every capacity clock value is below the terminal capacity time. -/
theorem ofReal_capClock_lt (hγ : IsDrivenCurve γ) {u : ℝ} (hu : 0 ≤ u) :
    ENNReal.ofReal (capClock γ u) < capLife γ := by
  obtain ⟨n, hn⟩ := exists_nat_gt u
  have h1 : capClock γ u < capClock γ n := hγ.strictMonoOn_capClock hu (by
    show (0 : ℝ) ≤ n
    positivity) hn
  calc ENNReal.ofReal (capClock γ u) < ENNReal.ofReal (capClock γ n) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hγ.capClock_nonneg hu)).2 h1
    _ ≤ capLife γ := le_iSup (fun n : ℕ => ENNReal.ofReal (capClock γ n)) n

/-- **The inverse clock** hits every capacity time below the terminal one. -/
theorem capInv_spec (hγ : IsDrivenCurve γ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ENNReal.ofReal s < capLife γ) : 0 ≤ capInv γ s ∧ capClock γ (capInv γ s) = s := by
  classical
  obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hs
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hex : ∃ u, 0 ≤ u ∧ capClock γ u = s := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hγ.localDriver ((n : ℝ) + 1) (by positivity)
    have hivt := intermediate_value_Icc hn0 (hc.mono (Icc_subset_Icc_right (by linarith)))
    obtain ⟨u, hu, hus⟩ := hivt ⟨by rw [hγ.capClock_zero]; exact hs0, hn.le⟩
    exact ⟨u, hu.1, hus⟩
  rw [capInv, dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

/-- The inverse clock is the unique preimage. -/
theorem capInv_eq (hγ : IsDrivenCurve γ) {u : ℝ} (hu : 0 ≤ u) : capInv γ (capClock γ u) = u := by
  classical
  have hex : ∃ v, 0 ≤ v ∧ capClock γ v = capClock γ u := ⟨u, hu, rfl⟩
  rw [capInv, dite_eq_left_of_eq_true (eq_true hex)]
  exact hγ.strictMonoOn_capClock.injOn hex.choose_spec.1 hu hex.choose_spec.2

/-- The inverse clock vanishes at nonpositive capacity times. -/
theorem capInv_of_nonpos (hγ : IsDrivenCurve γ) {s : ℝ} (hs : s ≤ 0) : capInv γ s = 0 := by
  classical
  rcases hs.lt_or_eq with hs | rfl
  · have hex : ¬ ∃ u, 0 ≤ u ∧ capClock γ u = s := by
      rintro ⟨u, hu, hus⟩
      linarith [hγ.capClock_nonneg hu]
    rw [capInv, dite_eq_right_of_eq_false (eq_false hex)]
  · have := hγ.capInv_eq le_rfl
    rwa [hγ.capClock_zero] at this

/-- The inverse clock stays in `[0, S]` below `capClock S`. -/
theorem capInv_le (hγ : IsDrivenCurve γ) {S s : ℝ} (hS : 0 ≤ S) (hs0 : 0 ≤ s)
    (hs : s ≤ capClock γ S) : capInv γ s ≤ S := by
  have hlt : ENNReal.ofReal s < capLife γ :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs) (hγ.ofReal_capClock_lt hS)
  obtain ⟨h0, heq⟩ := hγ.capInv_spec hs0 hlt
  by_contra hlt'
  rw [not_le] at hlt'
  have := hγ.strictMonoOn_capClock hS h0 hlt'
  linarith

/-- The inverse clock is strictly increasing below the terminal capacity time. -/
theorem capInv_lt_capInv (hγ : IsDrivenCurve γ) {s s' : ℝ} (hs0 : 0 ≤ s) (hss' : s < s')
    (hs' : ENNReal.ofReal s' < capLife γ) : capInv γ s < capInv γ s' := by
  have hs : ENNReal.ofReal s < capLife γ := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hss'.le) hs'
  obtain ⟨h0, h1⟩ := hγ.capInv_spec hs0 hs
  obtain ⟨h0', h1'⟩ := hγ.capInv_spec (hs0.trans hss'.le) hs'
  by_contra hle
  rw [not_lt] at hle
  have := hγ.strictMonoOn_capClock.monotoneOn h0' h0 hle
  rw [h1, h1'] at this
  linarith

/-! ### The canonical driver -/

/-- On `[0, capClock S]` the filled prefix at capacity time `s` is the Loewner hull of a local driver. -/
theorem fillH_capInv_eq (hγ : IsDrivenCurve γ) {S : ℝ} (hS : 0 < S) {W : ℝ → ℝ}
    (hK : ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t))
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ capClock γ S) :
    fillH (γ '' Icc 0 (capInv γ s)) = QuantumZipper.fwdHull W s := by
  have hlt : ENNReal.ofReal s < capLife γ :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs) (hγ.ofReal_capClock_lt hS.le)
  obtain ⟨h0, heq⟩ := hγ.capInv_spec hs0 hlt
  have hle := hγ.capInv_le hS.le hs0 hs
  rw [← hK _ ⟨h0, hle⟩, heq]

/-- `segG` is the uncentred Loewner flow `f_s + W_s` of a local driver, off the hull. -/
theorem segG_eq (hγ : IsDrivenCurve γ) {S : ℝ} (hS : 0 < S) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (hK : ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t))
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ capClock γ S) {z : ℂ} (hz : z ∈ H)
    (hzK : z ∉ QuantumZipper.fwdHull W s) : segG γ s z = QuantumZipper.fwdMap W s z + W s := by
  have hA := hγ.fillH_capInv_eq hS hK hs0 hs
  simp only [segG, hA]
  exact IsMapOut.eqOn (isHPHull_fwdHull hW hs0)
    (ConformalImage.isMapOut_mapOut (isHPHull_fwdHull hW hs0)) (isMapOut_fwdMap hW hW0 hs0) ⟨hz, hzK⟩

theorem segG_of_nonpos (hγ : IsDrivenCurve γ) {r : ℝ} (hr : r ≤ 0) (z : ℂ) :
    segG γ r z = segG γ 0 z := by
  simp only [segG, hγ.capInv_of_nonpos hr, hγ.capInv_of_nonpos le_rfl]

/-- **The difference quotients at far test points converge to a local driver**: for all large `N`, the point
`i (N + 1)` lies outside every filled prefix up to capacity time `s`, and the quotients at it tend to `W s`. -/
theorem eventually_tendsto_segQuot (hγ : IsDrivenCurve γ) {S : ℝ} (hS : 0 < S) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0)
    (hK : ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t))
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ capClock γ S) :
    ∀ᶠ N : ℕ in atTop, (∀ r ≤ s, zPt N ∉ fillH (γ '' Icc 0 (capInv γ r))) ∧
      Tendsto (fun k : ℕ => segQuot γ s (zPt N) k) atTop (𝓝 (W s)) := by
  obtain ⟨R, hR⟩ := (isBounded_fwdHull hW s).subset_ball 0
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge R
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hzK : ∀ r ≤ s, zPt N ∉ QuantumZipper.fwdHull W r := by
    intro r hr hmem
    have h1 := hR ((QuantumZipper.fwdHull_mono (W := W)).1 hr hmem)
    rw [Metric.mem_ball, dist_zero_right, norm_zPt] at h1
    have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hfill : ∀ r ≤ s, zPt N ∉ fillH (γ '' Icc 0 (capInv γ r)) := by
    intro r hr
    rcases le_or_gt 0 r with hr0 | hr0
    · rw [hγ.fillH_capInv_eq hS hK hr0 (hr.trans hs)]
      exact hzK r hr
    · have e : capInv γ r = capInv γ 0 := by
        rw [hγ.capInv_of_nonpos hr0.le, hγ.capInv_of_nonpos le_rfl]
      rw [e, hγ.fillH_capInv_eq hS hK le_rfl (hγ.capClock_nonneg hS.le)]
      exact hzK 0 hs0
  refine ⟨hfill, ?_⟩
  have hg : ∀ r ∈ Icc 0 s, segG γ r (zPt N) = QuantumZipper.fwdMap W r (zPt N) + W r := fun r hr =>
    hγ.segG_eq hS hW hW0 hK hr.1 (hr.2.trans hs) (zPt_mem_H N) (hzK r hr.2)
  rcases hs0.lt_or_eq with hs0 | hs0
  · exact tendsto_drvQuot hW hs0 (zPt_mem_H N) (hzK s le_rfl) hg
  · subst hs0
    have hne : zPt N ≠ ((W 0 : ℝ) : ℂ) := by
      intro h
      have h1 := congrArg Complex.im h
      rw [Complex.ofReal_im] at h1
      have h2 : (0 : ℝ) < (zPt N).im := zPt_mem_H N
      linarith
    have hq : ∀ k : ℕ, segQuot γ 0 (zPt N) k = W 0 := by
      intro k
      have hk : (0 : ℝ) - 1 / ((k : ℝ) + 1) ≤ 0 := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      have e1 : segG γ (0 - 1 / ((k : ℝ) + 1)) (zPt N) = segG γ 0 (zPt N) := hγ.segG_of_nonpos hk _
      have e2 := hg 0 ⟨le_rfl, le_rfl⟩
      rw [QuantumZipper.B5.fwdMap_zero_time W hne, sub_add_cancel] at e2
      simp only [segQuot, e1, sub_self, mul_zero, div_zero, sub_zero, e2, hW0]
      simp only [zPt, mul_re, I_re, add_re, natCast_re, one_re, zero_mul, I_im, add_im, natCast_im,
        one_im, add_zero, zero_sub, mul_zero, neg_zero]
    simp only [hq]
    exact tendsto_const_nhds

/-- **The formula recovers every local driver** on `[0, capClock S]`. -/
theorem segDrv_eq (hγ : IsDrivenCurve γ) {S : ℝ} (hS : 0 < S) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (hK : ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t))
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ capClock γ S) : segDrv γ s = W s := by
  have hlim : Tendsto (fun N : ℕ => limUnder atTop fun k : ℕ => segQuot γ s (zPt N) k) atTop (𝓝 (W s)) :=
    tendsto_const_nhds.congr' ((hγ.eventually_tendsto_segQuot hS hW hW0 hK hs0 hs).mono
      fun N hN => hN.2.limUnder_eq.symm)
  exact hlim.limUnder_eq

/-- A capacity time below the terminal one lies below the clock at a positive integer time. -/
theorem exists_pos_lt_capClock (hγ : IsDrivenCurve γ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ENNReal.ofReal s < capLife γ) : ∃ n : ℕ, (0 : ℝ) < n ∧ s < capClock γ n := by
  obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hs
  refine ⟨n, ?_, hn⟩
  by_contra h
  push Not at h
  have h0 : (n : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg n)
  rw [h0, hγ.capClock_zero] at hn
  linarith

/-- **Measurable form of the formula**: below the terminal capacity time, for all large `N` the test point
`i (N + 1)` is outside every filled prefix up to `s`, and the difference quotients there tend to `segDrv γ s`. -/
theorem eventually_tendsto_segDrv (hγ : IsDrivenCurve γ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ENNReal.ofReal s < capLife γ) :
    ∀ᶠ N : ℕ in atTop, (∀ r ≤ s, zPt N ∉ fillH (γ '' Icc 0 (capInv γ r))) ∧
      Tendsto (fun k : ℕ => segQuot γ s (zPt N) k) atTop (𝓝 (segDrv γ s)) := by
  obtain ⟨n, hn0, hn⟩ := hγ.exists_pos_lt_capClock hs0 hs
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver n hn0
  have hK' : ∀ t ∈ Icc 0 (n : ℝ), QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t) :=
    fun t ht => (hK t ht).2
  rw [hγ.segDrv_eq hn0 hW hW0 hK' hs0 hn.le]
  exact hγ.eventually_tendsto_segQuot hn0 hW hW0 hK' hs0 hn.le

/-- **The canonical driver up to the terminal capacity time**: it vanishes at `0`, is continuous on
`[0, capLife γ)`, and every filled prefix of `γ` is its Loewner hull at a capacity time `< capLife γ`. -/
theorem segDriver_spec (hγ : IsDrivenCurve γ) :
    segDriver γ 0 = 0 ∧ ContinuousOn (segDriver γ) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife γ} ∧
      ∀ u, 0 ≤ u → ∃ s : ℝ≥0, (s : ℝ≥0∞) < capLife γ ∧
        QuantumZipper.fwdHull (fun r : ℝ => segDriver γ r.toNNReal) s = fillH (γ '' Icc 0 u) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver 1 one_pos
    have := hγ.segDrv_eq one_pos hW hW0 (fun t ht => (hK t ht).2) le_rfl (hγ.capClock_nonneg zero_le_one)
    simp only [segDriver, NNReal.coe_zero, this, hW0]
  · intro s₀ hs₀
    have hs₀' : ENNReal.ofReal (s₀ : ℝ) < capLife γ := by rwa [ENNReal.ofReal_coe_nnreal]
    obtain ⟨n, hn0, hn⟩ := hγ.exists_pos_lt_capClock s₀.coe_nonneg hs₀'
    obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver n hn0
    have hev : segDriver γ =ᶠ[𝓝 s₀] fun s : ℝ≥0 => W s := by
      have hopen : IsOpen {s : ℝ≥0 | (s : ℝ) < capClock γ n} :=
        isOpen_lt NNReal.continuous_coe continuous_const
      filter_upwards [hopen.mem_nhds hn] with s hs
      exact hγ.segDrv_eq hn0 hW hW0 (fun t ht => (hK t ht).2) s.coe_nonneg (le_of_lt hs)
    exact ((hW.comp NNReal.continuous_coe).continuousAt.congr hev.symm).continuousWithinAt
  · intro u hu
    obtain ⟨n, hn⟩ := exists_nat_gt u
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt hu hn
    obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver n hn0
    have hcu := hγ.capClock_nonneg hu
    have hlt : capClock γ u < capClock γ n := hγ.strictMonoOn_capClock hu hn0.le hn
    refine ⟨(capClock γ u).toNNReal, ?_, ?_⟩
    · rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hcu]
      exact hγ.ofReal_capClock_lt hu
    rw [Real.coe_toNNReal _ hcu]
    rw [fwdHull_eq_of_eqOn (W' := W) hcu hlt fun r hr => ?_]
    · exact (hK u ⟨hu, hn.le⟩).2
    · show segDrv γ (r.toNNReal : ℝ) = W r
      rw [Real.coe_toNNReal _ hr.1]
      exact hγ.segDrv_eq hn0 hW hW0 (fun t ht => (hK t ht).2) hr.1 hr.2

/-! ### The capacity reparametrization is a generating trace -/

/-- The inverse clock is continuous (within `[0, ∞)`) at every capacity time below the terminal one. -/
theorem continuousWithinAt_capInv (hγ : IsDrivenCurve γ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ENNReal.ofReal s < capLife γ) : ContinuousWithinAt (capInv γ) (Ici 0) s := by
  obtain ⟨n, hn0, hn⟩ := hγ.exists_pos_lt_capClock hs0 hs
  set c := capClock γ n with hc
  have hcl : ENNReal.ofReal c < capLife γ := hγ.ofReal_capClock_lt hn0.le
  have hmono : StrictMonoOn (capInv γ) (Icc 0 c) := fun a ha b hb hab =>
    hγ.capInv_lt_capInv ha.1 hab (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hb.2) hcl)
  have hsn : capInv γ s < n := by
    obtain ⟨h0, h1⟩ := hγ.capInv_spec hs0 hs
    refine lt_of_le_of_ne (hγ.capInv_le hn0.le hs0 hn.le) fun h => ?_
    rw [h] at h1
    exact absurd hn (by rw [hc, h1]; exact lt_irrefl s)
  have hright : ContinuousWithinAt (capInv γ) (Ici s) s := by
    refine hmono.continuousWithinAt_right_of_exists_between
      (mem_nhdsWithin.2 ⟨Iio c, isOpen_Iio, hn, fun x hx => ⟨hs0.trans hx.2, le_of_lt hx.1⟩⟩) ?_
    intro b hb
    have hu0 : 0 ≤ min b n := le_min ((capInv_nonneg γ s).trans hb.le) hn0.le
    refine ⟨capClock γ (min b n), ⟨hγ.capClock_nonneg hu0,
      hγ.strictMonoOn_capClock.monotoneOn hu0 hn0.le (min_le_right _ _)⟩, ?_⟩
    rw [hγ.capInv_eq hu0]
    exact ⟨lt_min hb hsn, min_le_left _ _⟩
  rcases hs0.lt_or_eq with hs0' | hs0'
  · have hleft : ContinuousWithinAt (capInv γ) (Iic s) s := by
      refine hmono.continuousWithinAt_left_of_exists_between (Icc_mem_nhdsLE_of_mem ⟨hs0', hn.le⟩) ?_
      intro b hb
      have hu0 : 0 ≤ max b 0 := le_max_right _ _
      have hpos : 0 < capInv γ s := by
        obtain ⟨h0, h1⟩ := hγ.capInv_spec hs0 hs
        refine lt_of_le_of_ne h0 fun h => ?_
        rw [← h, hγ.capClock_zero] at h1
        exact hs0'.ne h1
      have hlt : max b 0 < capInv γ s := max_lt hb hpos
      have hle : max b 0 ≤ n := hlt.le.trans hsn.le
      refine ⟨capClock γ (max b 0), ⟨hγ.capClock_nonneg hu0,
        hγ.strictMonoOn_capClock.monotoneOn hu0 hn0.le hle⟩, ?_⟩
      rw [hγ.capInv_eq hu0]
      exact ⟨le_max_left _ _, hlt⟩
    exact (continuousAt_iff_continuous_left_right.2 ⟨hleft, hright⟩).continuousWithinAt
  · subst hs0'
    exact hright

/-- The capacity reparametrization is continuous at every capacity time below the terminal one. -/
theorem continuousAt_capTrace (hγ : IsDrivenCurve γ) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < capLife γ) :
    ContinuousAt (capTrace γ) s := by
  have hs' : ENNReal.ofReal (s : ℝ) < capLife γ := by rwa [ENNReal.ofReal_coe_nnreal]
  have hinv : ContinuousAt (fun r : ℝ≥0 => capInv γ r) s := by
    have h1 := (hγ.continuousWithinAt_capInv s.coe_nonneg hs').comp
      NNReal.continuous_coe.continuousAt.continuousWithinAt (s := univ) fun r _ => r.coe_nonneg
    exact h1.continuousAt Filter.univ_mem
  have h2 := ContinuousWithinAt.comp (f := fun r : ℝ≥0 => capInv γ r) (s := univ)
    (hγ.continuousOn (capInv γ s) (capInv_nonneg γ s)) hinv.continuousWithinAt
    fun r _ => capInv_nonneg γ r
  show ContinuousAt (γ ∘ fun r : ℝ≥0 => capInv γ r) s
  exact h2.continuousAt Filter.univ_mem

/-- The capacity reparametrization of the prefix up to capacity time `t` is the prefix up to `capInv γ t`. -/
theorem image_capTrace (hγ : IsDrivenCurve γ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < capLife γ) :
    capTrace γ '' Icc 0 t = γ '' Icc 0 (capInv γ t) := by
  have ht' : ENNReal.ofReal (t : ℝ) < capLife γ := by rwa [ENNReal.ofReal_coe_nnreal]
  ext z
  constructor
  · rintro ⟨s, ⟨-, hst⟩, rfl⟩
    refine ⟨capInv γ s, ⟨capInv_nonneg γ s, ?_⟩, rfl⟩
    rcases (NNReal.coe_le_coe.2 hst).lt_or_eq with hlt | heq
    · exact (hγ.capInv_lt_capInv s.coe_nonneg hlt ht').le
    · rw [heq]
  · rintro ⟨u, ⟨hu0, hut⟩, rfl⟩
    obtain ⟨-, htc⟩ := hγ.capInv_spec t.coe_nonneg ht'
    have hcu := hγ.capClock_nonneg hu0
    refine ⟨(capClock γ u).toNNReal, ⟨zero_le, ?_⟩, ?_⟩
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hcu, ← htc]
      exact hγ.strictMonoOn_capClock.monotoneOn hu0 (capInv_nonneg γ t) hut
    · simp only [capTrace, Real.coe_toNNReal _ hcu, hγ.capInv_eq hu0]

/-- The Loewner hull of the canonical driver at a capacity time `t` below the terminal one is the filled prefix up to
`capInv γ t`. -/
theorem fwdHull_segDriver (hγ : IsDrivenCurve γ) {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t < capLife γ) :
    QuantumZipper.fwdHull (fun r : ℝ => segDriver γ r.toNNReal) t = fillH (γ '' Icc 0 (capInv γ t)) := by
  obtain ⟨n, hn0, hn⟩ := hγ.exists_pos_lt_capClock ht0 ht
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver n hn0
  obtain ⟨h0, htc⟩ := hγ.capInv_spec ht0 ht
  have hle := hγ.capInv_le hn0.le ht0 hn.le
  rw [fwdHull_eq_of_eqOn (W' := W) ht0 hn fun r hr => ?_]
  · rw [← (hK _ ⟨h0, hle⟩).2, htc]
  · show segDrv γ (r.toNNReal : ℝ) = W r
    rw [Real.coe_toNNReal _ hr.1]
    exact hγ.segDrv_eq hn0 hW hW0 (fun t ht => (hK t ht).2) hr.1 hr.2

/-- **The capacity reparametrization is a continuous generating trace of the canonical driver** on `[0, T]`, for every
`T` below the terminal capacity time. -/
theorem isGeneratingTrace (hγ : IsDrivenCurve γ) {T : ℝ≥0∞} (hT : T < capLife γ) :
    IsGeneratingTrace (segDriver γ) T (capTrace γ) := by
  refine ⟨?_, fun s hs => (hγ.continuousAt_capTrace (lt_of_le_of_lt hs hT)).continuousWithinAt,
    fun t ht => ?_⟩
  · simp only [capTrace, NNReal.coe_zero, hγ.capInv_of_nonpos le_rfl, hγ.zero]
  · have ht' : (t : ℝ≥0∞) < capLife γ := ht.trans hT
    have ht'' : ENNReal.ofReal (t : ℝ) < capLife γ := by rwa [ENNReal.ofReal_coe_nnreal]
    rw [hγ.image_capTrace ht', hγ.fwdHull_segDriver t.coe_nonneg ht'']
    exact isFilling_fillH (isCompact_Icc.image_of_continuousOn
      (hγ.continuousOn.mono fun u hu => hu.1))

/-- **With infinite terminal capacity time**, the capacity reparametrization is a continuous generating trace of the
canonical driver on every finite interval. -/
theorem isGeneratingTrace_of_capLife_eq_top (hγ : IsDrivenCurve γ) (hL : capLife γ = ⊤) (T : ℝ≥0) :
    IsGeneratingTrace (segDriver γ) T (capTrace γ) :=
  hγ.isGeneratingTrace (by rw [hL]; exact ENNReal.coe_lt_top)

/-- With infinite terminal capacity time, the canonical driver is continuous. -/
theorem continuous_segDriver_of_capLife_eq_top (hγ : IsDrivenCurve γ) (hL : capLife γ = ⊤) :
    Continuous (segDriver γ) := by
  rw [← continuousOn_univ]
  refine (hγ.segDriver_spec.2.1).mono fun s _ => ?_
  show (s : ℝ≥0∞) < capLife γ
  rw [hL]
  exact ENNReal.coe_lt_top

end IsDrivenCurve

end InteractingSLE.Sec7.PocketTraversal
