/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71Capacity
import InteractingSLE.Spec.Sec6.DrivingUnconditional
import InteractingSLE.Spec.Dimension.TraceBridge
import QuantumZipper.Proofs.Zipper.B5VHccZero

/-!
# The driver of a mapped segment up to its terminal capacity time, by an explicit formula

Packet PROVE-LEMMA71C. Remark 6.14 (`source/spec/p193-240.md` L478–L493, p. 218): "That proposition gives a continuous
Loewner driver up to the terminal capacity time of `ψ(η_C)`". Proposition 6.12 (`Sec6.exists_driver_of_injOn`) gives
a driver on every compact capacity interval; here the drivers are assembled into one canonical driver up to the
terminal capacity time `capLife γ`, written by an **explicit formula** in the mapping-out functions of the filled
prefixes, so that it is visibly a measurable function of the prefixes (`Lemma71CMeas.lean`; this replaces the
Lusin–Souslin argument suggested in PROVE-LEMMA71's handoff).

## The formula

For the Loewner chain of a continuous driver `W` and a point `z` not swallowed by time `s`, the uncentred flow
`g_r(z) = f_r(z) + W_r = z + ∫₀ʳ 2 / f_x(z) dx` has left derivative `2 / f_s(z)` at `s`, so

  `W_s = Re (g_s(z) − 2 / ∂_s g_s(z))`,   `∂_s g_s(z) = lim_k (k + 1) (g_s(z) − g_{s − 1/(k+1)}(z))`

(`tendsto_drvQuot`). For a simple curve `γ` from `0` the hull at capacity time `s` is the filled prefix
`fill γ([0, capInv γ s])`, and `g_s` is its (canonical) mapping-out function, so the driver is

  `segDrv γ s = lim_N lim_k Re (g_s(z_N) − 2 / ((k+1)(g_s(z_N) − g_{s−1/(k+1)}(z_N))))`,  `z_N = i (N + 1)`

(the outer limit only removes the dependence on a point `z_N` outside the hull; the sequence is eventually constant).

## Main results

* `IsSegCurve γ`: the six conditions of the geometric clause of `Lemma71B.Lemma71KilledSegmentStatement`;
* `capClock γ u = hcap(fill γ([0, u]))/2` (`capClock_zero`, `strictMonoOn_capClock`, `continuousOn_capClock`),
  `capLife γ = sup capClock` (the terminal capacity time), `capInv γ` (its inverse);
* `tendsto_drvQuot`: the left difference quotient formula for the driver;
* **`segDriver_spec`**: for every `IsSegCurve γ`, the canonical driver `segDriver γ` vanishes at `0`, is continuous on
  `[0, capLife γ)`, and every filled prefix of `γ` is its hull at a capacity time `< capLife γ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71C

/-! ### The driver from left difference quotients of the uncentred flow -/

/-- **Left difference quotients of the uncentred Loewner flow recover the driver.** For a continuous driver `W`, a
time `s > 0` and a point `z ∈ ℍ` not swallowed by time `s`, if `g r = f_r(z) + W_r` on `[0, s]`, then
`Re (g s − 2 / ((k + 1) (g s − g (s − 1/(k+1))))) → W s`. -/
theorem tendsto_drvQuot {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ H)
    (hzK : z ∉ QuantumZipper.fwdHull W s) {g : ℝ → ℂ}
    (hg : ∀ r ∈ Icc 0 s, g r = QuantumZipper.fwdMap W r z + W r) :
    Tendsto (fun k : ℕ => (g s - 2 / (((k : ℂ) + 1) * (g s - g (s - 1 / ((k : ℝ) + 1))))).re) atTop
      (𝓝 (W s)) := by
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs.le hz hzK
  have hfu : ∀ r ∈ Icc 0 s, QuantumZipper.fwdMap W r z = u r := fun r hr =>
    QuantumZipper.fwdMap_eq hW hz hu hr
  set f : ℝ → ℂ := fun x => 2 / u x with hfdef
  have hgu : ∀ r ∈ Icc 0 s, g r = z + ∫ x in (0 : ℝ)..r, f x := by
    intro r hr
    rw [hg r hr, hfu r hr, (hu.2 r hr).2]
    ring
  have hfc : ContinuousOn f (Icc 0 s) := continuousOn_const.div hu.1 fun x hx => (hu.2 x hx).1
  have hF : HasDerivWithinAt (fun r => ∫ x in (0 : ℝ)..r, f x) (f s) (Icc 0 s) s := by
    have : Fact (s ∈ Icc (0 : ℝ) s) := ⟨⟨hs.le, le_rfl⟩⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right (hfc.intervalIntegrable_of_Icc hs.le)
      (hfc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s) (hfc s ⟨hs.le, le_rfl⟩)
  have hslope := hasDerivWithinAt_iff_tendsto_slope.1 hF
  -- the times `s − 1/(k+1)` approach `s` from inside `[0, s)`
  have hr : Tendsto (fun k : ℕ => s - 1 / ((k : ℝ) + 1)) atTop (𝓝[Icc 0 s \ {s}] s) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_sub s
      simpa only [sub_zero] using this
    · obtain ⟨K, hK⟩ := exists_nat_gt (1 / s)
      filter_upwards [eventually_ge_atTop K] with k hk
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hlt : 1 / ((k : ℝ) + 1) < s := by
        rw [div_lt_iff₀ hk1]
        have h1 : 1 / s < (k : ℝ) + 1 := lt_of_lt_of_le hK (by exact_mod_cast Nat.le_succ_of_le hk)
        rw [div_lt_iff₀ hs] at h1
        linarith
      refine ⟨⟨by linarith, by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity]⟩, ?_⟩
      simp only [mem_singleton_iff, sub_eq_self, one_div, inv_eq_zero]
      exact hk1.ne'
  have hq : Tendsto (fun k : ℕ => ((k : ℂ) + 1) * (g s - g (s - 1 / ((k : ℝ) + 1)))) atTop (𝓝 (f s)) := by
    refine (hslope.comp hr).congr' ?_
    filter_upwards [hr (self_mem_nhdsWithin)] with k hk
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp only [Function.comp_apply, slope_def_module]
    rw [hgu s ⟨hs.le, le_rfl⟩, hgu _ hk.1]
    have e : (s - 1 / ((k : ℝ) + 1) - s)⁻¹ = -((k : ℝ) + 1) := by
      rw [sub_sub_cancel_left, inv_neg, one_div, inv_inv]
    rw [e]
    simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one]
    ring
  have hfs : f s ≠ 0 := div_ne_zero two_ne_zero (hu.2 s ⟨hs.le, le_rfl⟩).1
  have h2 : Tendsto (fun k : ℕ => 2 / (((k : ℂ) + 1) * (g s - g (s - 1 / ((k : ℝ) + 1))))) atTop
      (𝓝 (u s)) := by
    have := (tendsto_const_nhds (x := (2 : ℂ))).div hq hfs
    have e : (2 : ℂ) / f s = u s := by
      simp only [hfdef]
      rw [div_div_eq_mul_div]
      ring
    rwa [e] at this
  have h3 := (tendsto_const_nhds (x := g s)).sub h2
  have e3 : g s - u s = (W s : ℂ) := by
    rw [hg s ⟨hs.le, le_rfl⟩, hfu s ⟨hs.le, le_rfl⟩]
    ring
  rw [e3] at h3
  have := (Complex.continuous_re.tendsto _).comp h3
  simpa only [Function.comp_def, Complex.ofReal_re] using this

/-! ### Curves of the mapped-segment clause and their capacity clock -/

/-- **The six conditions of the geometric clause** of `Lemma71B.Lemma71KilledSegmentStatement`: a continuous simple
path in `ℍ̄` from `0` to `∞` whose real times are nowhere dense. -/
def IsSegCurve (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Ici 0) ∧ InjOn γ (Ici 0) ∧ MapsTo γ (Ici 0) Hbar ∧ γ 0 = 0 ∧
    Tendsto (fun t => ‖γ t‖) atTop atTop ∧ interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ u).im = 0} = ∅

/-- The capacity clock `u ↦ hcap(fill γ([0, u]))/2`. -/
def capClock (γ : ℝ → ℂ) (u : ℝ) : ℝ := ConformalImage.hcapSet (fillH (γ '' Icc 0 u)) / 2

/-- **The terminal capacity time** `sup_u hcap(fill γ([0, u]))/2`. -/
def capLife (γ : ℝ → ℂ) : ℝ≥0∞ := ⨆ n : ℕ, ENNReal.ofReal (capClock γ n)

open scoped Classical in
/-- The inverse of the capacity clock (`0` off its range). -/
def capInv (γ : ℝ → ℂ) (s : ℝ) : ℝ := if h : ∃ u, 0 ≤ u ∧ capClock γ u = s then h.choose else 0

/-- The mapping-out function of the filled prefix at capacity time `s`. -/
def segG (γ : ℝ → ℂ) (s : ℝ) (z : ℂ) : ℂ := ConformalImage.mapOut (fillH (γ '' Icc 0 (capInv γ s))) z

/-- The left difference-quotient approximation of the driver at capacity time `s`, read at `z`. -/
def segQuot (γ : ℝ → ℂ) (s : ℝ) (z : ℂ) (k : ℕ) : ℝ :=
  (segG γ s z - 2 / (((k : ℂ) + 1) * (segG γ s z - segG γ (s - 1 / ((k : ℝ) + 1)) z))).re

/-- The test points `i (N + 1)`. -/
def zPt (N : ℕ) : ℂ := I * ((N : ℂ) + 1)

/-- **The canonical driver of a mapped segment** (at capacity time `s`). -/
def segDrv (γ : ℝ → ℂ) (s : ℝ) : ℝ :=
  limUnder atTop fun N : ℕ => limUnder atTop fun k : ℕ => segQuot γ s (zPt N) k

/-- The canonical driver as a process on `ℝ≥0`. -/
def segDriver (γ : ℝ → ℂ) (s : ℝ≥0) : ℝ := segDrv γ s

theorem capInv_nonneg (γ : ℝ → ℂ) (s : ℝ) : 0 ≤ capInv γ s := by
  classical
  unfold capInv
  split_ifs with h
  · exact h.choose_spec.1
  · exact le_rfl

theorem zPt_mem_H (N : ℕ) : zPt N ∈ H := by
  show 0 < (zPt N).im
  simp only [zPt, mul_im, I_re, add_re, natCast_re, one_re, zero_mul, I_im, add_im, natCast_im, one_im,
    add_zero, one_mul, zero_add]
  positivity

theorem norm_zPt (N : ℕ) : ‖zPt N‖ = (N : ℝ) + 1 := by
  rw [zPt, norm_mul, norm_I, one_mul]
  have : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

section Clock

variable {γ : ℝ → ℂ}

/-- **Local drivers** (Proposition 6.12 on `[0, S]`, `Sec6.exists_driver_of_injOn`): the capacity clock is the
clock of a continuous driver on `[0, S]`. -/
theorem IsSegCurve.exists_localDriver (hγ : IsSegCurve γ) {S : ℝ} (hS : 0 < S) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ capClock γ 0 = 0 ∧ StrictMonoOn (capClock γ) (Icc 0 S) ∧
      ContinuousOn (capClock γ) (Icc 0 S) ∧
      ∀ t ∈ Icc 0 S, 0 ≤ capClock γ t ∧ QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t) := by
  obtain ⟨hc, hinj, hH, h0, hinf, hR⟩ := hγ
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hσ⟩ := Sec6.exists_driver_of_injOn ordConnected_Ici hc hinj hH
    self_mem_Ici h0 (Lemma71.not_isBounded_image_Ici hinf) hR hS (mem_Ici.2 hS.le)
  have heq : EqOn σ (capClock γ) (Icc 0 S) := fun t ht => by
    obtain ⟨hσt, hK, -⟩ := hσ t ht
    have := Lemma71.hcapSet_eq_of_fwdHull_eq hW hW0 hσt hK
    simp only [capClock, this]
    ring
  refine ⟨W, hW, hW0, ?_, hσm.congr heq, hσc.congr heq.symm, fun t ht => ?_⟩
  · rw [← heq ⟨le_rfl, hS.le⟩, hσ0]
  · rw [← heq ht]
    exact ⟨(hσ t ht).1, (hσ t ht).2.1⟩

theorem IsSegCurve.capClock_zero (hγ : IsSegCurve γ) : capClock γ 0 = 0 :=
  (hγ.exists_localDriver one_pos).choose_spec.2.2.1

theorem IsSegCurve.strictMonoOn_capClock (hγ : IsSegCurve γ) : StrictMonoOn (capClock γ) (Ici 0) := by
  intro a ha b hb hab
  obtain ⟨-, -, -, -, hm, -⟩ := hγ.exists_localDriver (show (0 : ℝ) < b + 1 by linarith [mem_Ici.1 hb])
  exact hm ⟨ha, by linarith⟩ ⟨hb, by linarith⟩ hab

theorem IsSegCurve.continuousOn_capClock (hγ : IsSegCurve γ) : ContinuousOn (capClock γ) (Ici 0) := by
  intro t ht
  obtain ⟨-, -, -, -, -, hc, -⟩ := hγ.exists_localDriver (show (0 : ℝ) < t + 1 by linarith [mem_Ici.1 ht])
  refine (hc t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin.2 ⟨Iio (t + 1), isOpen_Iio, by simp, fun x hx => ⟨hx.2, le_of_lt hx.1⟩⟩

theorem IsSegCurve.capClock_nonneg (hγ : IsSegCurve γ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ capClock γ u := by
  rw [← hγ.capClock_zero]
  exact hγ.strictMonoOn_capClock.monotoneOn self_mem_Ici hu hu

/-- Every capacity clock value is below the terminal capacity time. -/
theorem IsSegCurve.ofReal_capClock_lt (hγ : IsSegCurve γ) {u : ℝ} (hu : 0 ≤ u) :
    ENNReal.ofReal (capClock γ u) < capLife γ := by
  obtain ⟨n, hn⟩ := exists_nat_gt u
  have h1 : capClock γ u < capClock γ n := hγ.strictMonoOn_capClock hu (by
    show (0 : ℝ) ≤ n
    positivity) hn
  calc ENNReal.ofReal (capClock γ u) < ENNReal.ofReal (capClock γ n) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hγ.capClock_nonneg hu)).2 h1
    _ ≤ capLife γ := le_iSup (fun n : ℕ => ENNReal.ofReal (capClock γ n)) n

/-- A capacity time below the terminal one is below some clock value at an integer time. -/
theorem exists_lt_capClock_of_lt_capLife {s : ℝ} (hs : ENNReal.ofReal s < capLife γ) :
    ∃ n : ℕ, s < capClock γ n := by
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hs
  refine ⟨n, ?_⟩
  by_contra hle
  exact absurd hn (not_lt.2 (ENNReal.ofReal_le_ofReal (not_lt.1 hle)))

/-- **The inverse clock** hits every capacity time below the terminal one. -/
theorem IsSegCurve.capInv_spec (hγ : IsSegCurve γ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ENNReal.ofReal s < capLife γ) : 0 ≤ capInv γ s ∧ capClock γ (capInv γ s) = s := by
  classical
  obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hs
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hex : ∃ u, 0 ≤ u ∧ capClock γ u = s := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hγ.exists_localDriver (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
    have hivt := intermediate_value_Icc hn0 (hc.mono (Icc_subset_Icc_right (by linarith)))
    obtain ⟨u, hu, hus⟩ := hivt ⟨by rw [hγ.capClock_zero]; exact hs0, hn.le⟩
    exact ⟨u, hu.1, hus⟩
  rw [capInv, dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

/-- The inverse clock is the unique preimage. -/
theorem IsSegCurve.capInv_eq (hγ : IsSegCurve γ) {u : ℝ} (hu : 0 ≤ u) : capInv γ (capClock γ u) = u := by
  classical
  have hex : ∃ v, 0 ≤ v ∧ capClock γ v = capClock γ u := ⟨u, hu, rfl⟩
  rw [capInv, dite_eq_left_of_eq_true (eq_true hex)]
  exact hγ.strictMonoOn_capClock.injOn hex.choose_spec.1 hu hex.choose_spec.2

/-- The inverse clock vanishes at nonpositive capacity times. -/
theorem IsSegCurve.capInv_of_nonpos (hγ : IsSegCurve γ) {s : ℝ} (hs : s ≤ 0) : capInv γ s = 0 := by
  classical
  rcases hs.lt_or_eq with hs | rfl
  · have hex : ¬ ∃ u, 0 ≤ u ∧ capClock γ u = s := by
      rintro ⟨u, hu, hus⟩
      linarith [hγ.capClock_nonneg hu]
    rw [capInv, dite_eq_right_of_eq_false (eq_false hex)]
  · have := hγ.capInv_eq le_rfl
    rwa [hγ.capClock_zero] at this

/-- The inverse clock stays in `[0, S]` below `capClock S`. -/
theorem IsSegCurve.capInv_le (hγ : IsSegCurve γ) {S s : ℝ} (hS : 0 ≤ S) (hs0 : 0 ≤ s)
    (hs : s ≤ capClock γ S) : capInv γ s ≤ S := by
  have hlt : ENNReal.ofReal s < capLife γ :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs) (hγ.ofReal_capClock_lt hS)
  obtain ⟨h0, heq⟩ := hγ.capInv_spec hs0 hlt
  by_contra hlt'
  rw [not_le] at hlt'
  have := hγ.strictMonoOn_capClock hS h0 hlt'
  linarith

end Clock

/-! ### The canonical driver -/

section Driver

variable {γ : ℝ → ℂ}

/-- On `[0, capClock S]` the filled prefix at capacity time `s` is the Loewner hull of a local driver. -/
theorem IsSegCurve.fillH_capInv_eq (hγ : IsSegCurve γ) {S : ℝ} (hS : 0 < S) {W : ℝ → ℝ}
    (hK : ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t))
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ capClock γ S) :
    fillH (γ '' Icc 0 (capInv γ s)) = QuantumZipper.fwdHull W s := by
  have hlt : ENNReal.ofReal s < capLife γ :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs) (hγ.ofReal_capClock_lt hS.le)
  obtain ⟨h0, heq⟩ := hγ.capInv_spec hs0 hlt
  have hle := hγ.capInv_le hS.le hs0 hs
  rw [← hK _ ⟨h0, hle⟩, heq]

/-- `segG` is the uncentred Loewner flow `f_s + W_s` of a local driver, off the hull. -/
theorem IsSegCurve.segG_eq (hγ : IsSegCurve γ) {S : ℝ} (hS : 0 < S) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (hK : ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t))
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ capClock γ S) {z : ℂ} (hz : z ∈ H)
    (hzK : z ∉ QuantumZipper.fwdHull W s) : segG γ s z = QuantumZipper.fwdMap W s z + W s := by
  have hA := hγ.fillH_capInv_eq hS hK hs0 hs
  simp only [segG, hA]
  exact IsMapOut.eqOn (isHPHull_fwdHull hW hs0)
    (ConformalImage.isMapOut_mapOut (isHPHull_fwdHull hW hs0)) (isMapOut_fwdMap hW hW0 hs0) ⟨hz, hzK⟩

theorem IsSegCurve.segG_of_nonpos (hγ : IsSegCurve γ) {r : ℝ} (hr : r ≤ 0) (z : ℂ) :
    segG γ r z = segG γ 0 z := by
  simp only [segG, hγ.capInv_of_nonpos hr, hγ.capInv_of_nonpos le_rfl]

/-- **The difference quotients at far test points converge to a local driver**: for all large `N`, the point
`i (N + 1)` lies outside every filled prefix up to capacity time `s`, and the quotients at it tend to `W s`. -/
theorem IsSegCurve.eventually_tendsto_segQuot (hγ : IsSegCurve γ) {S : ℝ} (hS : 0 < S) {W : ℝ → ℝ}
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
theorem IsSegCurve.segDrv_eq (hγ : IsSegCurve γ) {S : ℝ} (hS : 0 < S) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (hK : ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t))
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ capClock γ S) : segDrv γ s = W s := by
  have hlim : Tendsto (fun N : ℕ => limUnder atTop fun k : ℕ => segQuot γ s (zPt N) k) atTop (𝓝 (W s)) :=
    tendsto_const_nhds.congr' ((hγ.eventually_tendsto_segQuot hS hW hW0 hK hs0 hs).mono
      fun N hN => hN.2.limUnder_eq.symm)
  exact hlim.limUnder_eq

/-- **Measurable form of the formula**: below the terminal capacity time, for all large `N` the test point
`i (N + 1)` is outside every filled prefix up to `s`, and the difference quotients there tend to `segDrv γ s`. -/
theorem IsSegCurve.eventually_tendsto_segDrv (hγ : IsSegCurve γ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ENNReal.ofReal s < capLife γ) :
    ∀ᶠ N : ℕ in atTop, (∀ r ≤ s, zPt N ∉ fillH (γ '' Icc 0 (capInv γ r))) ∧
      Tendsto (fun k : ℕ => segQuot γ s (zPt N) k) atTop (𝓝 (segDrv γ s)) := by
  obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hs
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    push Not at h
    have h0 : (n : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg n)
    rw [h0, hγ.capClock_zero] at hn
    linarith
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.exists_localDriver hn0
  have hK' : ∀ t ∈ Icc 0 (n : ℝ), QuantumZipper.fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t) :=
    fun t ht => (hK t ht).2
  rw [hγ.segDrv_eq hn0 hW hW0 hK' hs0 hn.le]
  exact hγ.eventually_tendsto_segQuot hn0 hW hW0 hK' hs0 hn.le

/-- **The canonical driver of a mapped segment, up to its terminal capacity time** (Remark 6.14 with Proposition
6.12): it vanishes at `0`, is continuous on `[0, capLife γ)`, and every filled prefix of `γ` is its Loewner hull at a
capacity time `< capLife γ`. -/
theorem IsSegCurve.segDriver_spec (hγ : IsSegCurve γ) :
    segDriver γ 0 = 0 ∧ ContinuousOn (segDriver γ) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife γ} ∧
      ∀ u, 0 ≤ u → ∃ s : ℝ≥0, (s : ℝ≥0∞) < capLife γ ∧
        QuantumZipper.fwdHull (fun r : ℝ => segDriver γ r.toNNReal) s = fillH (γ '' Icc 0 u) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.exists_localDriver one_pos
    have := hγ.segDrv_eq one_pos hW hW0 (fun t ht => (hK t ht).2) le_rfl (hγ.capClock_nonneg zero_le_one)
    simp only [segDriver, NNReal.coe_zero, this, hW0]
  · intro s₀ hs₀
    have hs₀' : ENNReal.ofReal (s₀ : ℝ) < capLife γ := by rwa [ENNReal.ofReal_coe_nnreal]
    obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hs₀'
    have hn0 : (0 : ℝ) < n := by
      by_contra h
      push Not at h
      have h0 : (n : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg n)
      rw [h0, hγ.capClock_zero] at hn
      exact absurd hn (not_lt.2 s₀.coe_nonneg)
    obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.exists_localDriver hn0
    have hev : segDriver γ =ᶠ[𝓝 s₀] fun s : ℝ≥0 => W s := by
      have hopen : IsOpen {s : ℝ≥0 | (s : ℝ) < capClock γ n} :=
        isOpen_lt NNReal.continuous_coe continuous_const
      filter_upwards [hopen.mem_nhds hn] with s hs
      exact hγ.segDrv_eq hn0 hW hW0 (fun t ht => (hK t ht).2) s.coe_nonneg (le_of_lt hs)
    exact ((hW.comp NNReal.continuous_coe).continuousAt.congr hev.symm).continuousWithinAt
  · intro u hu
    obtain ⟨n, hn⟩ := exists_nat_gt u
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt hu hn
    obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.exists_localDriver hn0
    have hcu := hγ.capClock_nonneg hu
    have hlt : capClock γ u < capClock γ n := hγ.strictMonoOn_capClock hu hn0.le hn
    refine ⟨(capClock γ u).toNNReal, hγ.ofReal_capClock_lt hu, ?_⟩
    rw [Real.coe_toNNReal _ hcu]
    rw [fwdHull_eq_of_eqOn (W' := W) hcu hlt fun r hr => ?_]
    · exact (hK u ⟨hu, hn.le⟩).2
    · show segDrv γ (r.toNNReal : ℝ) = W r
      rw [Real.coe_toNNReal _ hr.1]
      exact hγ.segDrv_eq hn0 hW hW0 (fun t ht => (hK t ht).2) hr.1 hr.2

end Driver

end InteractingSLE.Sec7.Lemma71C
