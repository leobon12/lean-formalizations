/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripDrift

/-!
# Restarting a strip path at a strip time: the renormalized future

Packet PROVE-ZHAN-A4. Astra, *Formalization proofs* L1559–L1569 (the whole-tail Girsanov step of the strip endpoint
theorem): "Start at deterministic integers `n` … On each no-cutoff event the complete original tail is a
constant-drift reference tail … The inverse map of the finite prefix is analytic along the top, and takes finite top
points to finite top points. Pullback proves precisely (ii)."

This file is the deterministic restart. For a strip path `(w, v)` (`IsStripPath`) and a strip time `n`, let
`a = s(n)` be the chordal time, `g = w_a − v_a > 0` the gap and `c = g²`. The renormalized future

  `ŵ(r) = (w(a + c r) − w_a)/g`,   `v̂(r) = (v(a + c r) − w_a)/g`,   `ζ̂ = (ζ − a)/c`

is again a strip path (`v̂(0) = −1`), its strip clock is `t̂(r) = t(a + c r) − n`, and its strip driver is
`ξ̂_t = ξ_{n+t} − ξ_n`.

## Main results

* `IsStripPath.chordT_spec`, `IsStripPath.exists_gt`: the chordal time at a strip time lies in the strip life and
  inverts the strip clock; the strip life has no last time;
* `isStripLife_rs_iff`: `r` is in the strip life of the restart iff `a + c r` is in the original strip life;
* `stripClock_rs`: the strip clock of the restart.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

open Strip

variable {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-! ### The chordal time at a strip time -/

theorem IsStripPath.chordT_spec (h : IsStripPath w v ζ) (t : ℝ≥0) :
    IsStripLife w v ζ (chordT w v t) ∧ ((chordT w v t : ℝ≥0) : ℝ) = chordalTime (extPath w) (extPath v) t ∧
      stripClock (extPath w) (extPath v) (chordT w v t) = t := by
  obtain ⟨S, hS, hT⟩ := h.2.2 t
  have hm := h.2.1 S hS
  have ht : (t : ℝ) ∈ Icc 0 (stripClock (extPath w) (extPath v) S) := ⟨t.2, hT⟩
  have hmem := hm.chordalTime_mem ht
  have hc : ((chordT w v t : ℝ≥0) : ℝ) = chordalTime (extPath w) (extPath v) t := by
    simp only [chordT]; exact Real.coe_toNNReal _ hmem.1
  refine ⟨hS.mono ?_, hc, by rw [hc]; exact hm.stripClock_chordalTime ht⟩
  rw [← NNReal.coe_le_coe, hc]; exact hmem.2

/-- The strip clock is monotone along the strip life. -/
theorem IsStripPath.stripClock_le (h : IsStripPath w v ζ) {s s' : ℝ≥0} (hs' : IsStripLife w v ζ s')
    (hss' : s ≤ s') : stripClock (extPath w) (extPath v) s ≤ stripClock (extPath w) (extPath v) s' :=
  (h.2.1 s' hs').strictMonoOn_stripClock.monotoneOn ⟨s.2, hss'⟩ ⟨s'.2, le_rfl⟩ hss'

/-- The strip life of a strip path has no last time. -/
theorem IsStripPath.exists_gt (h : IsStripPath w v ζ) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    ∃ s' : ℝ≥0, s < s' ∧ IsStripLife w v ζ s' := by
  obtain ⟨S, hS, hT⟩ := h.2.2 (stripClock (extPath w) (extPath v) s + 1)
  refine ⟨S, lt_of_not_ge fun hSs => ?_, hS⟩
  have := h.stripClock_le hs hSs
  linarith

theorem gap_pos_of_isStripLife {s : ℝ≥0} (hs : IsStripLife w v ζ s) : 0 < w s - v s :=
  sub_pos.2 (hs.2 s le_rfl)

/-! ### The renormalized restart -/

/-- The gap `g = w_a − v_a` at the chordal time `a = s(n)` of the strip time `n`. -/
def rsGap (w v : ℝ≥0 → ℝ) (n : ℝ≥0) : ℝ := w (chordT w v n) - v (chordT w v n)

/-- The time scale `c = g²` of the restart. -/
def rsScale (w v : ℝ≥0 → ℝ) (n : ℝ≥0) : ℝ≥0 := ⟨rsGap w v n ^ 2, sq_nonneg _⟩

/-- The renormalized restarted driver `ŵ(r) = (w(a + c r) − w_a)/g`. -/
def rsW (w v : ℝ≥0 → ℝ) (n : ℝ≥0) : ℝ≥0 → ℝ := fun r =>
  (w (chordT w v n + rsScale w v n * r) - w (chordT w v n)) / rsGap w v n

/-- The renormalized restarted end mark `v̂(r) = (v(a + c r) − w_a)/g`. -/
def rsV (w v : ℝ≥0 → ℝ) (n : ℝ≥0) : ℝ≥0 → ℝ := fun r =>
  (v (chordT w v n + rsScale w v n * r) - w (chordT w v n)) / rsGap w v n

/-- The renormalized restarted lifetime `ζ̂ = (ζ − a)/c`. -/
def rsZ (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (n : ℝ≥0) : ℝ≥0∞ := (ζ - chordT w v n) / rsScale w v n

theorem coe_rsScale (w v : ℝ≥0 → ℝ) (n : ℝ≥0) : ((rsScale w v n : ℝ≥0) : ℝ) = rsGap w v n ^ 2 := rfl

theorem IsStripPath.rsGap_pos (h : IsStripPath w v ζ) (n : ℝ≥0) : 0 < rsGap w v n :=
  gap_pos_of_isStripLife (h.chordT_spec n).1

theorem IsStripPath.rsScale_pos (h : IsStripPath w v ζ) (n : ℝ≥0) : 0 < rsScale w v n := by
  rw [← NNReal.coe_pos, coe_rsScale]; exact pow_pos (h.rsGap_pos n) 2

@[simp] theorem rsW_zero (w v : ℝ≥0 → ℝ) (n : ℝ≥0) : rsW w v n 0 = 0 := by simp [rsW]

theorem IsStripPath.rsV_zero (h : IsStripPath w v ζ) (n : ℝ≥0) : rsV w v n 0 = -1 := by
  have hg := (h.rsGap_pos n).ne'
  simp only [rsV, mul_zero, add_zero]
  rw [div_eq_iff hg, rsGap]; ring

/-- **The strip life of the restart.** -/
theorem IsStripPath.isStripLife_rs_iff (h : IsStripPath w v ζ) (n : ℝ≥0) (r : ℝ≥0) :
    IsStripLife (rsW w v n) (rsV w v n) (rsZ w v ζ n) r ↔
      IsStripLife w v ζ (chordT w v n + rsScale w v n * r) := by
  set a := chordT w v n with ha_def
  set c := rsScale w v n with hc_def
  have ha := (h.chordT_spec n).1
  have hg := h.rsGap_pos n
  have hc := h.rsScale_pos n
  have hlt : (r : ℝ≥0∞) < rsZ w v ζ n ↔ ((a + c * r : ℝ≥0) : ℝ≥0∞) < ζ := by
    rw [rsZ, ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.coe_ne_zero.2 hc.ne'))
      (Or.inl ENNReal.coe_ne_top), lt_tsub_iff_right, ← ha_def, ← hc_def]
    push_cast; rw [add_comm, mul_comm]
  have hrs : ∀ r' : ℝ≥0, rsV w v n r' < rsW w v n r' ↔ v (a + c * r') < w (a + c * r') := fun r' => by
    simp only [rsV, rsW, ← ha_def, ← hc_def]
    rw [div_lt_div_iff_of_pos_right hg]; constructor <;> intro h' <;> linarith
  rw [IsStripLife, IsStripLife, hlt]
  refine and_congr_right fun _ => ⟨fun hall s hs => ?_, fun hall r' hr' => (hrs r').2 (hall _ ?_)⟩
  · rcases le_or_gt s a with hsa | hsa
    · exact ha.2 s hsa
    · have hsr : (s - a) / c ≤ r := by
        rw [div_le_iff₀ hc, mul_comm]; exact tsub_le_iff_left.2 hs
      have := (hrs ((s - a) / c)).1 (hall _ hsr)
      rwa [mul_div_cancel₀ _ hc.ne', add_tsub_cancel_of_le hsa.le] at this
  · gcongr

/-! ### Reading the restart on `ℝ` -/

theorem toNNReal_affine (a c : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    (a + c * x.toNNReal : ℝ≥0) = ((c : ℝ) * x + a).toNNReal := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by positivity)]
  push_cast
  rw [Real.coe_toNNReal _ hx]; ring

theorem extPath_rsW (w v : ℝ≥0 → ℝ) (n : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    extPath (rsW w v n) x =
      (extPath w ((rsScale w v n : ℝ) * x + chordT w v n) - w (chordT w v n)) / rsGap w v n := by
  simp only [extPath, rsW, toNNReal_affine _ _ hx]

theorem extPath_rsV (w v : ℝ≥0 → ℝ) (n : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    extPath (rsV w v n) x =
      (extPath v ((rsScale w v n : ℝ) * x + chordT w v n) - w (chordT w v n)) / rsGap w v n := by
  simp only [extPath, rsV, toNNReal_affine _ _ hx]

theorem extPath_rsW_sub_rsV (w v : ℝ≥0 → ℝ) (n : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    extPath (rsW w v n) x - extPath (rsV w v n) x =
      (extPath w ((rsScale w v n : ℝ) * x + chordT w v n) -
        extPath v ((rsScale w v n : ℝ) * x + chordT w v n)) / rsGap w v n := by
  rw [extPath_rsW _ _ _ hx, extPath_rsV _ _ _ hx]; ring

/-- The affine map `x ↦ c x + a` sends `[0, r]` into `[0, a + c r]`. -/
theorem mapsTo_affine (a c r : ℝ≥0) :
    MapsTo (fun x : ℝ => (c : ℝ) * x + a) (Icc 0 r) (Icc 0 ((a + c * r : ℝ≥0) : ℝ)) := by
  intro x hx
  refine ⟨by have := hx.1; positivity, ?_⟩
  push_cast
  have := mul_le_mul_of_nonneg_left hx.2 (NNReal.coe_nonneg c)
  linarith

/-- **The strip clock of the restart**: `t̂(r) = t(a + c r) − n` on the strip life. -/
theorem IsStripPath.stripClock_rs (h : IsStripPath w v ζ) (n : ℝ≥0) {r : ℝ≥0}
    (hr : IsStripLife w v ζ (chordT w v n + rsScale w v n * r)) :
    stripClock (extPath (rsW w v n)) (extPath (rsV w v n)) r =
      stripClock (extPath w) (extPath v) ((chordT w v n + rsScale w v n * r : ℝ≥0) : ℝ) - n := by
  set a := chordT w v n with ha_def
  set c := rsScale w v n with hc_def
  set g := rsGap w v n with hg_def
  have hg := h.rsGap_pos n
  have hc : (c : ℝ) ≠ 0 := (NNReal.coe_pos.2 (h.rsScale_pos n)).ne'
  have hm := h.2.1 _ hr
  set D : ℝ → ℝ := fun u => ((extPath w u - extPath v u) ^ 2)⁻¹ with hD
  have hint : ∫ x in (0 : ℝ)..r, ((extPath (rsW w v n) x - extPath (rsV w v n) x) ^ 2)⁻¹ =
      ∫ x in (0 : ℝ)..r, (c : ℝ) * D ((c : ℝ) * x + a) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (NNReal.coe_nonneg r)] at hx
    simp only [hD]
    rw [extPath_rsW_sub_rsV _ _ _ hx.1, ← hg_def, ← ha_def, ← hc_def, div_pow, inv_div,
      coe_rsScale, ← hg_def]
    field_simp
  have hsub := intervalIntegral.integral_interval_sub_left (μ := volume) (f := D) (a := 0)
    (b := ((a + c * r : ℝ≥0) : ℝ)) (c := (a : ℝ))
    (hm.intervalIntegrable_inv_sq ⟨le_rfl, hm.nonneg⟩ ⟨hm.nonneg, le_rfl⟩)
    (hm.intervalIntegrable_inv_sq ⟨le_rfl, hm.nonneg⟩ ⟨a.2, by
      push_cast; have := mul_nonneg (NNReal.coe_nonneg c) (NNReal.coe_nonneg r); linarith⟩)
  have hclk := (h.chordT_spec n).2.2
  rw [stripClock, hint, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_add D hc, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul,
    mul_zero, zero_add, ← hclk, stripClock, stripClock, hsub]
  congr 1; push_cast; ring

/-- **The end-mark equation and the separated-pair property of the restart.** -/
theorem IsStripPath.isSepMark_rs (h : IsStripPath w v ζ) (n : ℝ≥0) {r : ℝ≥0}
    (hr : IsStripLife w v ζ (chordT w v n + rsScale w v n * r)) :
    IsSepMark (extPath (rsW w v n)) (extPath (rsV w v n)) r := by
  set a := chordT w v n with ha_def
  set c := rsScale w v n with hc_def
  set g := rsGap w v n with hg_def
  have hg := h.rsGap_pos n
  have hc : (c : ℝ) ≠ 0 := (NNReal.coe_pos.2 (h.rsScale_pos n)).ne'
  have hm := h.2.1 _ hr
  have ha := (h.chordT_spec n).1
  have hma := h.2.1 _ ha
  have hmaps := mapsTo_affine a c r
  have hS0 : (a : ℝ) ∈ Icc 0 ((a + c * r : ℝ≥0) : ℝ) := ⟨a.2, by
    push_cast; have := mul_nonneg (NNReal.coe_nonneg c) (NNReal.coe_nonneg r); linarith⟩
  have hcw : ContinuousOn (fun x : ℝ => (extPath w ((c : ℝ) * x + a) - w a) / g) (Icc 0 r) :=
    ((hm.continuousOn_w.comp (by fun_prop) hmaps).sub continuousOn_const).div_const _
  have hcv : ContinuousOn (fun x : ℝ => (extPath v ((c : ℝ) * x + a) - w a) / g) (Icc 0 r) :=
    ((hm.continuousOn_v.comp (by fun_prop) hmaps).sub continuousOn_const).div_const _
  -- the integrand of the end-mark equation
  set E : ℝ → ℝ := fun u => 2 / (extPath v u - extPath w u) with hE
  have hEc : ContinuousOn E (Icc 0 ((a + c * r : ℝ≥0) : ℝ)) :=
    continuousOn_const.div (hm.continuousOn_v.sub hm.continuousOn_w) fun u hu =>
      (sub_neg.2 (hm.lt u hu)).ne
  refine ⟨r.2, hcw.congr fun x hx => extPath_rsW _ _ _ hx.1, hcv.congr fun x hx => extPath_rsV _ _ _ hx.1,
    fun x hx => ?_, fun x hx => ?_⟩
  · rw [extPath_rsW _ _ _ hx.1, extPath_rsV _ _ _ hx.1]
    exact div_lt_div_of_pos_right (by linarith [hm.lt _ (hmaps hx)]) hg
  · have hux := hmaps hx
    have hint : ∫ y in (0 : ℝ)..x, 2 / (extPath (rsV w v n) y - extPath (rsW w v n) y) =
        ∫ y in (0 : ℝ)..x, g * E ((c : ℝ) * y + a) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le hx.1] at hy
      have hy0 := hy.1
      show _ = g * (2 / (extPath v ((c : ℝ) * y + a) - extPath w ((c : ℝ) * y + a)))
      rw [extPath_rsV _ _ _ hy0, extPath_rsW _ _ _ hy0, ← ha_def, ← hc_def, ← hg_def, div_sub_div_same,
        sub_sub_sub_cancel_right, div_div_eq_mul_div]
      ring
    have h1 : extPath v ((c : ℝ) * x + a) = -1 + ∫ u in (0 : ℝ)..((c : ℝ) * x + a), E u := hm.eq _ hux
    have h0 : v a = -1 + ∫ u in (0 : ℝ)..(a : ℝ), E u := by
      have := hma.eq a ⟨NNReal.coe_nonneg a, le_rfl⟩
      rw [extPath_coe] at this
      exact this
    have hsub := intervalIntegral.integral_interval_sub_left (μ := volume) (f := E) (a := 0)
      (b := (c : ℝ) * x + a) (c := (a : ℝ))
      ((hEc.mono (uIcc_subset_Icc ⟨le_rfl, hm.nonneg⟩ hux)).intervalIntegrable)
      ((hEc.mono (uIcc_subset_Icc ⟨le_rfl, hm.nonneg⟩ hS0)).intervalIntegrable)
    rw [extPath_rsV _ _ _ hx.1, hint, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add E hc, smul_eq_mul, mul_zero, zero_add, ← ha_def, ← hc_def,
      ← hg_def, h1]
    generalize ∫ u in (a : ℝ)..((c : ℝ) * x + a), E u = I at hsub ⊢
    generalize ∫ u in (0 : ℝ)..((c : ℝ) * x + a), E u = J at hsub ⊢
    generalize ∫ u in (0 : ℝ)..(a : ℝ), E u = K at hsub h0
    have hgc : (c : ℝ) = g ^ 2 := coe_rsScale w v n
    have hga : g = w a - v a := rfl
    have hg0 : g ≠ 0 := hg.ne'
    have key : -1 + J - w a = I - g := by rw [hga]; linarith
    rw [key, hgc]
    field_simp
    ring

/-- **The restart is a strip path.** -/
theorem IsStripPath.rs (h : IsStripPath w v ζ) (n : ℝ≥0) :
    IsStripPath (rsW w v n) (rsV w v n) (rsZ w v ζ n) := by
  refine ⟨rsW_zero w v n, fun r hr => h.isSepMark_rs n ((h.isStripLife_rs_iff n r).1 hr), fun T => ?_⟩
  set a := chordT w v n with ha_def
  set c := rsScale w v n with hc_def
  have hc := h.rsScale_pos n
  have ha := (h.chordT_spec n).1
  obtain ⟨S, hS, hTS⟩ := h.2.2 (T + n)
  set S' := max S a with hS'
  have hS'l : IsStripLife w v ζ S' := by
    rcases le_total S a with hle | hle
    · rw [hS', max_eq_right hle]; exact ha
    · rw [hS', max_eq_left hle]; exact hS
  have haS' : a ≤ S' := le_max_right _ _
  have hr : a + c * ((S' - a) / c) = S' := by
    rw [mul_div_cancel₀ _ hc.ne', add_tsub_cancel_of_le haS']
  refine ⟨(S' - a) / c, (h.isStripLife_rs_iff n _).2 (by rw [hr]; exact hS'l), ?_⟩
  rw [h.stripClock_rs n (by rw [hr]; exact hS'l), hr]
  have := h.stripClock_le hS'l (le_max_left S a)
  linarith

/-- **The strip driver of the restart**: `ξ̂_t = ξ_{n+t} − ξ_n`. -/
theorem IsStripPath.stripDriver_rs (h : IsStripPath w v ζ) (n t : ℝ≥0) :
    stripDriver (extPath (rsW w v n)) (extPath (rsV w v n)) t =
      stripDriver (extPath w) (extPath v) ((n + t : ℝ≥0) : ℝ) - stripDriver (extPath w) (extPath v) n := by
  have hc := h.rsScale_pos n
  have hg := h.rsGap_pos n
  obtain ⟨ha, hac, hna⟩ := h.chordT_spec n
  obtain ⟨hs, hsc, hns⟩ := h.chordT_spec (n + t)
  set a := chordT w v n with ha_def
  set c := rsScale w v n with hc_def
  set g := rsGap w v n with hg_def
  set s' := chordT w v (n + t) with hs'_def
  -- `a ≤ s'`
  have has : a ≤ s' := by
    by_contra hlt
    have hlt := not_le.1 hlt
    have := (h.2.1 a ha).stripClock_lt ⟨NNReal.coe_nonneg s', NNReal.coe_le_coe.2 hlt.le⟩
      ⟨NNReal.coe_nonneg a, le_rfl⟩ (NNReal.coe_lt_coe.2 hlt)
    rw [hna, hns] at this
    push_cast at this
    linarith [NNReal.coe_nonneg t]
  set r' := (s' - a) / c with hr'_def
  have hr : a + c * r' = s' := by
    rw [hr'_def, mul_div_cancel₀ _ hc.ne', add_tsub_cancel_of_le has]
  have hlife : IsStripLife w v ζ (a + c * r') := by rw [hr]; exact hs
  have hclk : stripClock (extPath (rsW w v n)) (extPath (rsV w v n)) r' = t := by
    rw [h.stripClock_rs n hlife, hr, hns]; push_cast; ring
  have hchord : chordalTime (extPath (rsW w v n)) (extPath (rsV w v n)) t = r' := by
    rw [← hclk]; exact (h.isSepMark_rs n hlife).chordalTime_stripClock ⟨r'.2, le_rfl⟩
  have hgap : extPath (rsW w v n) r' - extPath (rsV w v n) r' = (w s' - v s') / g := by
    rw [extPath_rsW_sub_rsV _ _ _ (NNReal.coe_nonneg r'), ← ha_def, ← hc_def, ← hg_def]
    have : (c : ℝ) * r' + a = (s' : ℝ) := by rw [← hr]; push_cast; ring
    rw [this, extPath_coe, extPath_coe]
  have hpos : 0 < w s' - v s' := gap_pos_of_isStripLife hs
  unfold stripDriver
  rw [hchord, hgap, ← hsc, ← hac, extPath_coe, extPath_coe, extPath_coe, extPath_coe,
    Real.log_div hpos.ne' hg.ne']
  push_cast
  have hga : g = w a - v a := rfl
  rw [hga]
  ring

/-- **The restart of a strip path with strip driver `ξ` has strip driver `ξ_{n+·} − ξ_n`.** -/
theorem HasStripDriver.rs {ξ : ℝ≥0 → ℝ} (h : HasStripDriver w v ζ ξ) (n : ℝ≥0) :
    HasStripDriver (rsW w v n) (rsV w v n) (rsZ w v ζ n) (fun t => ξ (n + t) - ξ n) :=
  ⟨h.1.rs n, fun t => by rw [h.1.stripDriver_rs n t, h.2, h.2]⟩

end Zhan

end InteractingSLE
