/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Loewner
import InteractingSLE.Spec.Sec4.UpperDrift

/-!
# Strip Loewner evolutions through the half-plane (ruling R36)

Packet PROVE-ZHAN-A. The strip `S_π = {0 < Im z < π}` (`piStrip`) is mapped onto `ℍ` by the exponential chart
`z ↦ e^z − 1` (`stripExp`): the source `0` goes to `0`, the lower line `ℝ` to `(−1, ∞)`, the upper line `ℝ + iπ`
to `(−∞, −1)`, the end `−∞` to `−1` and the end `+∞` to `∞`. Following ruling R36 there is no separate strip
Loewner theory: a strip evolution is the chordal `ℍ` evolution of the exponential image, with the added mark
`v_s = g_s(−1)` (the image of `−∞`), renormalized by the real affine map `x ↦ e^t (x − v_s)` (which fixes `0 = ` the
image of `−∞` and `∞`) and run on the explicit clock

  `t(s) = ∫₀ˢ (w_u − v_u)⁻² du = −½ log g_s'(−1)`                                     (`stripClock`).

With `s(t)` the inverse clock (`chordalTime`), the strip map, driver and real points are

  `ψ_t(z) = t + log (g_{s(t)}(e^z − 1) − v_{s(t)})`,   `ξ_t = t + log (w_{s(t)} − v_{s(t)})`,
  `p_t = t + log |y_{s(t)} − v_{s(t)}|` for a real chordal point path `y`,

and the strip Loewner equation `∂_t ψ_t(z) = coth((ψ_t(z) − ξ_t)/2)` is a theorem (`hasDerivAt_stripMap`).

## Main definitions

* `stripClock w v`, `chordalTime w v`: the clock and its inverse;
* `stripMap w v t z` (`ψ_t`), `stripDriver w v t` (`ξ_t`), `stripPoint w v y t` (real points);
* `cothHalfC z = (e^z + 1)/(e^z − 1)` (`= coth (z/2)`).

## Main results

* `IsSepMark.stripClock_chordalTime`, `IsSepMark.chordalTime_stripClock`: the two clocks are inverse;
* `IsSepMark.hasDerivAt_chordalTime`: `s'(t) = (w − v)²(s(t))`;
* `IsSepMark.hasDerivAt_stripMap`: the strip Loewner equation.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open QuantumZipper (H fwdMap fwdHull IsForwardSol)

namespace InteractingSLE

namespace Strip

/-! ### The strip, its exponential chart and `coth` -/

/-- The strip `S_π = {0 < Im z < π}`. -/
def piStrip : Set ℂ := {z | 0 < z.im ∧ z.im < Real.pi}

/-- The exponential chart `z ↦ e^z − 1` of `S_π` onto `ℍ` (source `0 ↦ 0`, `−∞ ↦ −1`, `+∞ ↦ ∞`). -/
def stripExp (z : ℂ) : ℂ := exp z - 1

/-- `coth (z/2) = (e^z + 1)/(e^z − 1)`. -/
def cothHalfC (z : ℂ) : ℂ := (exp z + 1) / (exp z - 1)

@[simp] theorem stripExp_zero : stripExp 0 = 0 := by simp [stripExp]

theorem stripExp_im_pos {z : ℂ} (hz : z ∈ piStrip) : 0 < (stripExp z).im := by
  simp only [stripExp, sub_im, one_im, sub_zero, exp_im]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2)

/-! ### The strip clock and its inverse -/

/-- The strip clock `t(s) = ∫₀ˢ (w_u − v_u)⁻² du` of a driver `w` and the mark path `v = g(−1)`. -/
def stripClock (w v : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in (0 : ℝ)..s, ((w u - v u) ^ 2)⁻¹

/-- The chordal time at strip time `t`: the first `s ≥ 0` with `t ≤ t(s)` (the inverse of `stripClock`). -/
def chordalTime (w v : ℝ → ℝ) (t : ℝ) : ℝ := sInf {s | 0 ≤ s ∧ t ≤ stripClock w v s}

/-- `(w, v)` is a driver with a separated left mark started at `−1`, on `[0, S]`: both paths are continuous on
`[0, S]`, `v < w` there, and `v_s = −1 + ∫₀ˢ 2/(v − w)` (the chordal force-point equation of `g_s(−1)`). -/
structure IsSepMark (w v : ℝ → ℝ) (S : ℝ) : Prop where
  nonneg : 0 ≤ S
  continuousOn_w : ContinuousOn w (Icc 0 S)
  continuousOn_v : ContinuousOn v (Icc 0 S)
  lt : ∀ s ∈ Icc 0 S, v s < w s
  eq : ∀ s ∈ Icc 0 S, v s = -1 + ∫ u in (0 : ℝ)..s, 2 / (v u - w u)

namespace IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

theorem continuousOn_inv_sq (h : IsSepMark w v S) :
    ContinuousOn (fun u => ((w u - v u) ^ 2)⁻¹) (Icc 0 S) :=
  ((h.continuousOn_w.sub h.continuousOn_v).pow 2).inv₀ fun u hu =>
    pow_ne_zero 2 (sub_ne_zero.2 (h.lt u hu).ne')

theorem inv_sq_pos (h : IsSepMark w v S) {u : ℝ} (hu : u ∈ Icc 0 S) : 0 < ((w u - v u) ^ 2)⁻¹ :=
  inv_pos.2 (pow_pos (sub_pos.2 (h.lt u hu)) 2)

theorem intervalIntegrable_inv_sq (h : IsSepMark w v S) {a b : ℝ} (ha : a ∈ Icc 0 S) (hb : b ∈ Icc 0 S) :
    IntervalIntegrable (fun u => ((w u - v u) ^ 2)⁻¹) volume a b :=
  (h.continuousOn_inv_sq.mono (uIcc_subset_Icc ha hb)).intervalIntegrable

theorem continuousOn_stripClock (h : IsSepMark w v S) : ContinuousOn (stripClock w v) (Icc 0 S) := by
  have hI := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := S)
    (f := fun u => ((w u - v u) ^ 2)⁻¹)
    (by rw [uIcc_of_le h.nonneg]; exact h.continuousOn_inv_sq.integrableOn_Icc)
  rwa [uIcc_of_le h.nonneg] at hI

@[simp] theorem stripClock_zero (w v : ℝ → ℝ) : stripClock w v 0 = 0 := by simp [stripClock]

theorem stripClock_lt (h : IsSepMark w v S) {a b : ℝ} (ha : a ∈ Icc 0 S) (hb : b ∈ Icc 0 S) (hab : a < b) :
    stripClock w v a < stripClock w v b := by
  have hsub : stripClock w v b - stripClock w v a = ∫ u in a..b, ((w u - v u) ^ 2)⁻¹ := by
    rw [stripClock, stripClock, intervalIntegral.integral_interval_sub_left
      (h.intervalIntegrable_inv_sq ⟨le_rfl, h.nonneg⟩ hb) (h.intervalIntegrable_inv_sq ⟨le_rfl, h.nonneg⟩ ha)]
  have hpos : 0 < ∫ u in a..b, ((w u - v u) ^ 2)⁻¹ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (h.intervalIntegrable_inv_sq ha hb)
      (fun u hu => h.inv_sq_pos ⟨ha.1.trans hu.1.le, hu.2.le.trans hb.2⟩) hab
  linarith

theorem strictMonoOn_stripClock (h : IsSepMark w v S) : StrictMonoOn (stripClock w v) (Icc 0 S) :=
  fun _ ha _ hb hab => h.stripClock_lt ha hb hab

theorem stripClock_nonneg (h : IsSepMark w v S) {s : ℝ} (hs : s ∈ Icc 0 S) : 0 ≤ stripClock w v s := by
  rcases hs.1.eq_or_lt with h0 | h0
  · rw [← h0, stripClock_zero]
  · exact (stripClock_zero w v ▸ h.stripClock_lt ⟨le_rfl, h.nonneg⟩ hs h0).le

/-- The chordal time at a strip time `t ∈ [0, t(S)]` is the unique `s ∈ [0, S]` with `t(s) = t`. -/
theorem isLeast_chordalTime (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    ∃ s ∈ Icc 0 S, stripClock w v s = t ∧ IsLeast {s | 0 ≤ s ∧ t ≤ stripClock w v s} s := by
  obtain ⟨s, hs, hst⟩ := intermediate_value_Icc h.nonneg h.continuousOn_stripClock
    (by rw [stripClock_zero]; exact ht)
  refine ⟨s, hs, hst, ⟨hs.1, hst.ge⟩, fun r hr => ?_⟩
  by_contra hlt
  have hlt := not_le.1 hlt
  have := h.stripClock_lt ⟨hr.1, hlt.le.trans hs.2⟩ hs hlt
  linarith [hr.2]

theorem chordalTime_mem (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    chordalTime w v t ∈ Icc 0 S := by
  obtain ⟨s, hs, -, hl⟩ := h.isLeast_chordalTime ht
  rw [chordalTime, hl.csInf_eq]; exact hs

theorem stripClock_chordalTime (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    stripClock w v (chordalTime w v t) = t := by
  obtain ⟨s, -, hst, hl⟩ := h.isLeast_chordalTime ht
  rw [chordalTime, hl.csInf_eq, hst]

theorem chordalTime_stripClock (h : IsSepMark w v S) {s : ℝ} (hs : s ∈ Icc 0 S) :
    chordalTime w v (stripClock w v s) = s := by
  have ht : stripClock w v s ∈ Icc 0 (stripClock w v S) :=
    ⟨h.stripClock_nonneg hs, h.strictMonoOn_stripClock.monotoneOn hs ⟨h.nonneg, le_rfl⟩ hs.2⟩
  exact h.strictMonoOn_stripClock.injOn (h.chordalTime_mem ht) hs (h.stripClock_chordalTime ht)

@[simp] theorem chordalTime_zero (h : IsSepMark w v S) : chordalTime w v 0 = 0 := by
  simpa using h.chordalTime_stripClock ⟨le_rfl, h.nonneg⟩

theorem strictMonoOn_chordalTime (h : IsSepMark w v S) :
    StrictMonoOn (chordalTime w v) (Icc 0 (stripClock w v S)) := by
  intro a ha b hb hab
  by_contra hle
  have hle := not_lt.1 hle
  have := h.strictMonoOn_stripClock.monotoneOn (h.chordalTime_mem hb) (h.chordalTime_mem ha) hle
  rw [h.stripClock_chordalTime ha, h.stripClock_chordalTime hb] at this
  linarith

/-- `t(s)` has derivative `(w_s − v_s)⁻²` at interior times. -/
theorem hasDerivAt_stripClock (h : IsSepMark w v S) {s : ℝ} (hs : s ∈ Ioo 0 S) :
    HasDerivAt (stripClock w v) ((w s - v s) ^ 2)⁻¹ s := by
  have hc : ContinuousOn (fun u => ((w u - v u) ^ 2)⁻¹) (Ioo 0 S) :=
    h.continuousOn_inv_sq.mono Ioo_subset_Icc_self
  exact intervalIntegral.integral_hasDerivAt_right
    (h.intervalIntegrable_inv_sq ⟨le_rfl, h.nonneg⟩ ⟨hs.1.le, hs.2.le⟩)
    (hc.stronglyMeasurableAtFilter isOpen_Ioo s hs)
    (hc.continuousAt (isOpen_Ioo.mem_nhds hs))

theorem chordalTime_mem_Ioo (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Ioo 0 (stripClock w v S)) :
    chordalTime w v t ∈ Ioo 0 S := by
  have hm := h.chordalTime_mem (Ioo_subset_Icc_self ht)
  refine ⟨hm.1.lt_of_ne fun h0 => ?_, hm.2.lt_of_ne fun hS => ?_⟩
  · have := h.stripClock_chordalTime (Ioo_subset_Icc_self ht)
    rw [← h0, stripClock_zero] at this; linarith [ht.1]
  · have := h.stripClock_chordalTime (Ioo_subset_Icc_self ht)
    rw [hS] at this; linarith [ht.2]

theorem continuousAt_chordalTime (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Ioo 0 (stripClock w v S)) :
    ContinuousAt (chordalTime w v) t := by
  refine continuousAt_of_monotoneOn_of_image_mem_nhds
    (h.strictMonoOn_chordalTime.monotoneOn.mono Ioo_subset_Icc_self) (isOpen_Ioo.mem_nhds ht) ?_
  have himg : chordalTime w v '' Ioo 0 (stripClock w v S) = Ioo 0 S := by
    ext s
    constructor
    · rintro ⟨t', ht', rfl⟩; exact h.chordalTime_mem_Ioo ht'
    · intro hs
      have hs' : s ∈ Icc 0 S := Ioo_subset_Icc_self hs
      refine ⟨stripClock w v s, ⟨?_, ?_⟩, h.chordalTime_stripClock hs'⟩
      · simpa using h.stripClock_lt ⟨le_rfl, h.nonneg⟩ hs' hs.1
      · exact h.stripClock_lt hs' ⟨h.nonneg, le_rfl⟩ hs.2
  rw [himg]
  exact isOpen_Ioo.mem_nhds (h.chordalTime_mem_Ioo ht)

/-- `s'(t) = (w − v)²(s(t))`. -/
theorem hasDerivAt_chordalTime (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Ioo 0 (stripClock w v S)) :
    HasDerivAt (chordalTime w v)
      ((w (chordalTime w v t) - v (chordalTime w v t)) ^ 2) t := by
  have hs := h.chordalTime_mem_Ioo ht
  have hd := (h.hasDerivAt_stripClock hs).of_local_left_inverse (h.continuousAt_chordalTime ht)
    (inv_ne_zero (pow_ne_zero 2 (sub_ne_zero.2 (h.lt _ (Ioo_subset_Icc_self hs)).ne')))
    (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) fun t' ht' =>
      h.stripClock_chordalTime (Ioo_subset_Icc_self ht'))
  rwa [inv_inv] at hd

/-- A positive lower bound for the clock rate `(w − v)⁻²` on `[0, S]`. -/
theorem exists_pos_le_inv_sq (h : IsSepMark w v S) :
    ∃ m > 0, ∀ u ∈ Icc 0 S, m ≤ ((w u - v u) ^ 2)⁻¹ := by
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 h.nonneg) h.continuousOn_inv_sq
  exact ⟨_, h.inv_sq_pos hu₀, fun u hu => hmin hu⟩

theorem mul_sub_le_stripClock_sub (h : IsSepMark w v S) {m : ℝ}
    (hm : ∀ u ∈ Icc 0 S, m ≤ ((w u - v u) ^ 2)⁻¹) {a b : ℝ} (ha : a ∈ Icc 0 S) (hb : b ∈ Icc 0 S)
    (hab : a ≤ b) : m * (b - a) ≤ stripClock w v b - stripClock w v a := by
  rw [stripClock, stripClock, intervalIntegral.integral_interval_sub_left
    (h.intervalIntegrable_inv_sq ⟨le_rfl, h.nonneg⟩ hb) (h.intervalIntegrable_inv_sq ⟨le_rfl, h.nonneg⟩ ha)]
  have := intervalIntegral.integral_mono_on hab intervalIntegrable_const (h.intervalIntegrable_inv_sq ha hb)
    fun u hu => hm u ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
  simpa [mul_comm] using this

/-- The inverse clock is Lipschitz on `[0, t(S)]`, hence continuous. -/
theorem continuousOn_chordalTime (h : IsSepMark w v S) :
    ContinuousOn (chordalTime w v) (Icc 0 (stripClock w v S)) := by
  obtain ⟨m, hm0, hm⟩ := h.exists_pos_le_inv_sq
  have key : ∀ t ∈ Icc 0 (stripClock w v S), ∀ t' ∈ Icc 0 (stripClock w v S), t ≤ t' →
      chordalTime w v t' - chordalTime w v t ≤ m⁻¹ * (t' - t) := by
    intro t ht t' ht' htt'
    have hle := h.strictMonoOn_chordalTime.monotoneOn ht ht' htt'
    have := h.mul_sub_le_stripClock_sub hm (h.chordalTime_mem ht) (h.chordalTime_mem ht') hle
    rw [h.stripClock_chordalTime ht, h.stripClock_chordalTime ht'] at this
    rw [inv_mul_eq_div, le_div_iff₀ hm0]; linarith
  refine (LipschitzOnWith.of_dist_le_mul (K := ⟨m⁻¹, (inv_pos.2 hm0).le⟩) fun t ht t' ht' => ?_).continuousOn
  simp only [Real.dist_eq]
  rcases le_total t t' with htt' | htt'
  · have h1 := key t ht t' ht' htt'
    have h2 := h.strictMonoOn_chordalTime.monotoneOn ht ht' htt'
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h2), abs_sub_comm, abs_of_nonneg (sub_nonneg.2 htt')]
    exact h1
  · have h1 := key t' ht' t ht htt'
    have h2 := h.strictMonoOn_chordalTime.monotoneOn ht' ht htt'
    rw [abs_of_nonneg (sub_nonneg.2 h2), abs_of_nonneg (sub_nonneg.2 htt')]
    exact h1

theorem mapsTo_chordalTime (h : IsSepMark w v S) :
    MapsTo (chordalTime w v) (Icc 0 (stripClock w v S)) (Icc 0 S) := fun _ ht => h.chordalTime_mem ht

theorem v_zero (h : IsSepMark w v S) : v 0 = -1 := by
  simpa using h.eq 0 ⟨le_rfl, h.nonneg⟩

/-- The mark path has derivative `2/(v − w)` at interior times. -/
theorem hasDerivAt_v (h : IsSepMark w v S) {s : ℝ} (hs : s ∈ Ioo 0 S) :
    HasDerivAt v (2 / (v s - w s)) s := by
  have hc : ContinuousOn (fun u => 2 / (v u - w u)) (Icc 0 S) :=
    continuousOn_const.div (h.continuousOn_v.sub h.continuousOn_w) fun u hu =>
      sub_ne_zero.2 (h.lt u hu).ne
  have hc' : ContinuousOn (fun u => 2 / (v u - w u)) (Ioo 0 S) := hc.mono Ioo_subset_Icc_self
  have hI := intervalIntegral.integral_hasDerivAt_right
    ((hc.mono (uIcc_subset_Icc ⟨le_rfl, h.nonneg⟩ ⟨hs.1.le, hs.2.le⟩)).intervalIntegrable)
    (hc'.stronglyMeasurableAtFilter isOpen_Ioo s hs) (hc'.continuousAt (isOpen_Ioo.mem_nhds hs))
  refine (hI.const_add (-1)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr using h.eq r (Ioo_subset_Icc_self hr)

end IsSepMark

/-! ### The strip map, the strip driver and real points -/

/-- The strip map `ψ_t(z) = t + log (g_{s(t)}(e^z − 1) − v_{s(t)})`, where `g_s = f_s + w_s` and `f_s` is the
centred forward flow `fwdMap w s` (ruling R36: the affine renormalization `x ↦ e^t (x − v_s)` of `g_s`, read in
the logarithmic chart). -/
def stripMap (w v : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  t + log (fwdMap w (chordalTime w v t) (stripExp z) + w (chordalTime w v t) - v (chordalTime w v t))

/-- The strip driver `ξ_t = t + log (w_{s(t)} − v_{s(t)})`. -/
def stripDriver (w v : ℝ → ℝ) (t : ℝ) : ℝ :=
  t + Real.log (w (chordalTime w v t) - v (chordalTime w v t))

/-- The strip coordinate of a real chordal point path `y` (for instance a force point `V = g(x)`):
`t + log |y_{s(t)} − v_{s(t)}|`. It is a point of the lower line `ℝ` if `y > v` and the real part of a point of the
upper line `ℝ + iπ` if `y < v`. -/
def stripPoint (w v y : ℝ → ℝ) (t : ℝ) : ℝ :=
  t + Real.log |y (chordalTime w v t) - v (chordalTime w v t)|

/-- `coth((ψ − ξ)/2)` in chordal coordinates: if `e^{ψ − ξ} = G/a` with `a > 0` and `G = f + a`, `f ≠ 0`, then
`coth((ψ − ξ)/2) = (f + 2a)/f`. -/
theorem cothHalfC_log_sub_log {f : ℂ} {a : ℝ} (ha : 0 < a) (hG : f + a ≠ 0) :
    cothHalfC (log (f + a) - (Real.log a : ℂ)) = (f + 2 * a) / f := by
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 ha.ne'
  have he : exp (log (f + a) - (Real.log a : ℂ)) = (f + a) / a := by
    rw [exp_sub, exp_log hG, ← ofReal_exp, Real.exp_log ha]
  rw [cothHalfC, he, div_add_one ha', div_sub_one ha', div_div_div_cancel_right₀ ha',
    show f + a - a = f by ring, show f + a + a = f + 2 * a by ring]

/-- A real path solving `y_s = c + ∫₀ˢ 2/(y − w)` on `[0, S]` has derivative `2/(y_s − w_s)` at every interior time
where `y_s ≠ w_s`. -/
theorem hasDerivAt_of_eq_integral {w y : ℝ → ℝ} {S c : ℝ} (hw : ContinuousOn w (Icc 0 S))
    (hy : ContinuousOn y (Icc 0 S))
    (hint : IntervalIntegrable (fun u => 2 / (y u - w u)) volume 0 S)
    (heq : ∀ s ∈ Icc 0 S, y s = c + ∫ u in (0 : ℝ)..s, 2 / (y u - w u)) {s : ℝ} (hs : s ∈ Ioo 0 S)
    (hys : y s ≠ w s) : HasDerivAt y (2 / (y s - w s)) s := by
  have hS : 0 ≤ S := hs.1.le.trans hs.2.le
  have hcs : ContinuousAt (fun u => y u - w u) s :=
    ((hy.sub hw).mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds hs)
  set U := Ioo 0 S ∩ (fun u => y u - w u) ⁻¹' {0}ᶜ with hU
  have hUo : IsOpen U :=
    ((hy.sub hw).mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_compl_singleton
  have hsU : s ∈ U := ⟨hs, sub_ne_zero.2 hys⟩
  have hcU : ContinuousOn (fun u => 2 / (y u - w u)) U :=
    continuousOn_const.div ((hy.sub hw).mono (inter_subset_left.trans Ioo_subset_Icc_self))
      fun u hu => hu.2
  have hI := intervalIntegral.integral_hasDerivAt_right
    (hint.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hS]; exact ⟨hs.1.le, hs.2.le⟩)))
    (hcU.stronglyMeasurableAtFilter hUo s hsU) (hcU.continuousAt (hUo.mem_nhds hsU))
  refine (hI.const_add c).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr using heq r (Ioo_subset_Icc_self hr)

/-- `tanh (x/2) = (e^x − 1)/(e^x + 1)`. -/
theorem tanh_half_eq (x : ℝ) : Real.tanh (x / 2) = (Real.exp x - 1) / (Real.exp x + 1) := by
  have h := Sec4.one_sub_tanh_half_div_two x
  have h1 : 0 < 1 + Real.exp x := by positivity
  field_simp at h
  rw [eq_div_iff (by positivity)]
  linarith

namespace IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

/-- The strip driver starts at `0`. -/
theorem stripDriver_zero (h : IsSepMark w v S) (hw0 : w 0 = 0) : stripDriver w v 0 = 0 := by
  simp [stripDriver, h.chordalTime_zero, hw0, h.v_zero]

theorem continuousOn_stripDriver (h : IsSepMark w v S) :
    ContinuousOn (stripDriver w v) (Icc 0 (stripClock w v S)) := by
  have hc : ContinuousOn (fun t => w (chordalTime w v t) - v (chordalTime w v t))
      (Icc 0 (stripClock w v S)) :=
    (h.continuousOn_w.comp h.continuousOn_chordalTime h.mapsTo_chordalTime).sub
      (h.continuousOn_v.comp h.continuousOn_chordalTime h.mapsTo_chordalTime)
  exact continuousOn_id.add (hc.log fun t ht => (sub_pos.2 (h.lt _ (h.chordalTime_mem ht))).ne')

/-- In chordal coordinates, `ψ_t(z) − ξ_t = log (f + a) − log a` with `f = f_{s(t)}(e^z − 1)`, `a = w − v`. -/
theorem stripMap_sub_stripDriver (w v : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    stripMap w v t z - stripDriver w v t =
      log (fwdMap w (chordalTime w v t) (stripExp z) +
        ((w (chordalTime w v t) - v (chordalTime w v t) : ℝ) : ℂ)) -
        (Real.log (w (chordalTime w v t) - v (chordalTime w v t)) : ℂ) := by
  simp only [stripMap, stripDriver]
  push_cast
  rw [add_sub_assoc (fwdMap _ _ _)]
  ring

/-- The strip map starts at the identity of `S_π`. -/
theorem stripMap_zero (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) : stripMap w v 0 z = z := by
  have hz₀ : 0 < (stripExp z).im := stripExp_im_pos hz
  have h0 := Ito.fwdMap_eq_sub_add_integral_of_continuousOn h.nonneg h.continuousOn_w hz₀ hsol
    ⟨le_rfl, h.nonneg⟩
  simp only [intervalIntegral.integral_same, add_zero] at h0
  simp only [stripMap, h.chordalTime_zero, ofReal_zero, zero_add, h.v_zero]
  rw [h0, show stripExp z - (w 0 : ℂ) + (w 0 : ℂ) - ((-1 : ℝ) : ℂ) = exp z by
    simp only [stripExp]; push_cast; ring]
  exact log_exp (by linarith [hz.1, Real.pi_pos]) hz.2.le

/-- `ψ_t(z)` is continuous in the strip time on `[0, t(S)]`. -/
theorem continuousOn_stripMap (h : IsSepMark w v S) {z : ℂ} (hz : 0 < (stripExp z).im)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) :
    ContinuousOn (fun t => stripMap w v t z) (Icc 0 (stripClock w v S)) := by
  have hG : ContinuousOn (fun r => fwdMap w r (stripExp z) + (w r : ℂ) - (v r : ℂ)) (Icc 0 S) :=
    ((Ito.continuousOn_fwdMap_of_continuousOn h.nonneg h.continuousOn_w hz hsol).add
      (continuous_ofReal.comp_continuousOn h.continuousOn_w)).sub
      (continuous_ofReal.comp_continuousOn h.continuousOn_v)
  have hslit : ∀ r ∈ Icc 0 S, fwdMap w r (stripExp z) + (w r : ℂ) - (v r : ℂ) ∈ slitPlane := by
    intro r hr
    refine mem_slitPlane_iff.2 (Or.inr ?_)
    have := Ito.im_fwdMap_pos_of_continuousOn h.nonneg h.continuousOn_w hz hsol hr
    simp only [sub_im, add_im, ofReal_im, add_zero, sub_zero]
    exact this.ne'
  exact (continuous_ofReal.comp_continuousOn continuousOn_id).add
    ((hG.comp h.continuousOn_chordalTime h.mapsTo_chordalTime).clog fun t ht =>
      hslit _ (h.chordalTime_mem ht))

/-- `e^{ψ_t(z) − ξ_t} = (f + a)/a ≠ 1` (`f = f_{s(t)}(e^z − 1) ≠ 0`, `a = w − v > 0`). -/
theorem exp_stripMap_sub_stripDriver_ne_one (h : IsSepMark w v S) {z : ℂ} (hz : 0 < (stripExp z).im)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    exp (stripMap w v t z - stripDriver w v t) ≠ 1 := by
  have hs := h.chordalTime_mem ht
  set s := chordalTime w v t
  set f := fwdMap w s (stripExp z)
  have ha : 0 < w s - v s := sub_pos.2 (h.lt s hs)
  have hfim : 0 < f.im := Ito.im_fwdMap_pos_of_continuousOn h.nonneg h.continuousOn_w hz hsol hs
  have hGa : f + ((w s - v s : ℝ) : ℂ) ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this; linarith
  rw [stripMap_sub_stripDriver, exp_sub, exp_log hGa, ← ofReal_exp, Real.exp_log ha]
  intro h1
  have ha' : ((w s - v s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 ha.ne'
  rw [div_eq_one_iff_eq ha', add_eq_right] at h1
  rw [h1, zero_im] at hfim
  exact lt_irrefl _ hfim

theorem continuousOn_cothHalfC_stripMap (h : IsSepMark w v S) {z : ℂ} (hz : 0 < (stripExp z).im)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) :
    ContinuousOn (fun t => cothHalfC (stripMap w v t z - stripDriver w v t))
      (Icc 0 (stripClock w v S)) := by
  have hd : ContinuousOn (fun t => stripMap w v t z - (stripDriver w v t : ℂ)) (Icc 0 (stripClock w v S)) :=
    (h.continuousOn_stripMap hz hsol).sub (continuous_ofReal.comp_continuousOn h.continuousOn_stripDriver)
  have he := Complex.continuous_exp.comp_continuousOn hd
  exact (he.add continuousOn_const).div (he.sub continuousOn_const) fun t ht =>
    sub_ne_zero.2 (h.exp_stripMap_sub_stripDriver_ne_one hz hsol ht)

/-- **The strip Loewner equation** `∂_t ψ_t(z) = coth((ψ_t(z) − ξ_t)/2)`, at every interior strip time, for a
point `z` whose exponential image `e^z − 1 ∈ ℍ` is not swallowed by the chordal flow on `[0, S]`. -/
theorem hasDerivAt_stripMap (h : IsSepMark w v S) {z : ℂ} (hz : 0 < (stripExp z).im)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) {t : ℝ} (ht : t ∈ Ioo 0 (stripClock w v S)) :
    HasDerivAt (fun t => stripMap w v t z) (cothHalfC (stripMap w v t z - stripDriver w v t)) t := by
  set s := chordalTime w v t with hs_def
  have hs : s ∈ Ioo 0 S := h.chordalTime_mem_Ioo ht
  have hsI : s ∈ Icc 0 S := Ioo_subset_Icc_self hs
  set z₀ := stripExp z
  -- the chordal flow `g_r(z₀) = f_r(z₀) + w_r` at the interior time `s`
  have hW := Ito.continuous_clampDrv h.nonneg h.continuousOn_w
  have hz₀ := Ito.mem_diff_fwdHull_clampDrv h.nonneg h.continuousOn_w hz hsol
  have hg : HasDerivAt (fun r => fwdMap w r z₀ + (w r : ℂ)) (2 / fwdMap w s z₀) s := by
    have h1 := (Ito.hasDerivWithinAt_fwdMap_add hW h.nonneg hz₀ hsI).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
    rw [Ito.fwdMap_clampDrv_of_le hsI.2] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
    rw [Ito.fwdMap_clampDrv_of_le hr.2, Ito.clampDrv_eqOn hr]
  have hG : HasDerivAt (fun r => fwdMap w r z₀ + (w r : ℂ) - (v r : ℂ))
      (2 / fwdMap w s z₀ - ((2 / (v s - w s) : ℝ) : ℂ)) s :=
    hg.sub (h.hasDerivAt_v hs).ofReal_comp
  have hGt := hG.scomp t (h.hasDerivAt_chordalTime ht)
  -- the quantities at time `s`
  set f := fwdMap w s z₀ with hf_def
  set a := w s - v s with ha_def
  have ha : 0 < a := sub_pos.2 (h.lt s hsI)
  have hfim : 0 < f.im := Ito.im_fwdMap_pos_of_continuousOn h.nonneg h.continuousOn_w hz hsol hsI
  have hf0 : f ≠ 0 := fun h0 => by rw [h0, zero_im] at hfim; exact lt_irrefl _ hfim
  have hGs : f + (w s : ℂ) - (v s : ℂ) = f + a := by rw [ha_def]; push_cast; ring
  have hslit : f + (w s : ℂ) - (v s : ℂ) ∈ slitPlane := by
    rw [hGs]; exact mem_slitPlane_iff.2 (Or.inr (by simpa using hfim.ne'))
  have hGa0 : f + (a : ℂ) ≠ 0 := by rw [← hGs]; exact slitPlane_ne_zero hslit
  have hlog := (hasDerivAt_id' t |>.ofReal_comp).add (hGt.clog_real hslit)
  have hfun : (fun t => stripMap w v t z) = ((fun y : ℝ => ((id y : ℝ) : ℂ)) + fun t =>
      log (((fun r => fwdMap w r z₀ + (w r : ℂ) - (v r : ℂ)) ∘ chordalTime w v) t)) := by
    funext t'; simp [stripMap, z₀]
  rw [hfun]
  refine hlog.congr_deriv ?_
  -- the value: `coth((ψ − ξ)/2)` in chordal coordinates
  have hψξ : stripMap w v t z - stripDriver w v t = log (f + a) - (Real.log a : ℂ) := by
    change ((t : ℂ) + log (f + (w s : ℂ) - (v s : ℂ))) - ((t + Real.log a : ℝ) : ℂ) = _
    rw [hGs]; push_cast; ring
  have hva : v s - w s = -a := by rw [ha_def]; ring
  rw [hψξ, cothHalfC_log_sub_log ha hGa0, Function.comp_apply, ← hs_def]
  change (((1 : ℝ) : ℂ) + a ^ 2 • (2 / f - ((2 / (v s - w s) : ℝ) : ℂ)) /
    (f + (w s : ℂ) - (v s : ℂ))) = _
  rw [hGs, hva]
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 ha.ne'
  rw [real_smul]
  push_cast
  field_simp
  ring

/-- **The integrated strip Loewner equation** `ψ_t(z) = z + ∫₀ᵗ coth((ψ_u(z) − ξ_u)/2) du` on `[0, t(S)]`. -/
theorem stripMap_eq_add_integral (h : IsSepMark w v S) {z : ℂ} (hz : z ∈ piStrip)
    (hsol : ∃ u, IsForwardSol w (stripExp z) S u) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    stripMap w v t z = z + ∫ u in (0 : ℝ)..t, cothHalfC (stripMap w v u z - stripDriver w v u) := by
  have hz₀ := stripExp_im_pos hz
  have hsub : Icc 0 t ⊆ Icc 0 (stripClock w v S) := Icc_subset_Icc le_rfl ht.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    ((h.continuousOn_stripMap hz₀ hsol).mono hsub)
    (fun u hu => h.hasDerivAt_stripMap hz₀ hsol ⟨hu.1, hu.2.trans_le ht.2⟩)
    (((h.continuousOn_cothHalfC_stripMap hz₀ hsol).mono hsub).intervalIntegrable_of_Icc ht.1),
    h.stripMap_zero hz hsol]
  ring

/-- The chordal clock in strip coordinates: `s'(t) = (w − v)² = e^{2(ξ_t − t)}` (Astra L1503,
`u'(t) = e^{2(ξ_t − t)}`). -/
theorem hasDerivAt_chordalTime_eq_exp (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Ioo 0 (stripClock w v S)) :
    HasDerivAt (chordalTime w v) (Real.exp (2 * (stripDriver w v t - t))) t := by
  refine (h.hasDerivAt_chordalTime ht).congr_deriv ?_
  have ha : 0 < w (chordalTime w v t) - v (chordalTime w v t) :=
    sub_pos.2 (h.lt _ (h.chordalTime_mem (Ioo_subset_Icc_self ht)))
  rw [stripDriver, add_sub_cancel_left, show (2 : ℝ) * Real.log (w (chordalTime w v t) -
    v (chordalTime w v t)) = ((2 : ℕ) : ℝ) * Real.log (w (chordalTime w v t) - v (chordalTime w v t)) by
    norm_num, Real.exp_nat_mul, Real.exp_log ha]

/-- The derivative of `t ↦ log |y_{s(t)} − v_{s(t)}|`-based strip points: `1 + 2a/d`, `a = w − v`, `d = y − w`. -/
theorem hasDerivAt_stripPoint_aux (h : IsSepMark w v S) {y : ℝ → ℝ} (hy : ContinuousOn y (Icc 0 S))
    (hint : IntervalIntegrable (fun u => 2 / (y u - w u)) volume 0 S)
    (heq : ∀ s ∈ Icc 0 S, y s = y 0 + ∫ u in (0 : ℝ)..s, 2 / (y u - w u)) {t : ℝ}
    (ht : t ∈ Ioo 0 (stripClock w v S)) (hyw : y (chordalTime w v t) ≠ w (chordalTime w v t))
    (hyv : y (chordalTime w v t) ≠ v (chordalTime w v t)) :
    HasDerivAt (stripPoint w v y)
      (1 + 2 * (w (chordalTime w v t) - v (chordalTime w v t)) /
        (y (chordalTime w v t) - w (chordalTime w v t))) t := by
  set s := chordalTime w v t with hs_def
  have hs : s ∈ Ioo 0 S := h.chordalTime_mem_Ioo ht
  have hyd := hasDerivAt_of_eq_integral h.continuousOn_w hy hint heq hs hyw
  have hD : HasDerivAt (fun r => y r - v r) (2 / (y s - w s) - 2 / (v s - w s)) s :=
    hyd.sub (h.hasDerivAt_v hs)
  have hDt := hD.comp t (h.hasDerivAt_chordalTime ht)
  have hlog := (hasDerivAt_id t).add (hDt.log (sub_ne_zero.2 hyv))
  have hfun : stripPoint w v y = (id + fun t => Real.log (((fun r => y r - v r) ∘ chordalTime w v) t)) := by
    funext t'; simp [stripPoint, Real.log_abs]
  rw [hfun]
  refine hlog.congr_deriv ?_
  have ha : 0 < w s - v s := sub_pos.2 (h.lt s (Ioo_subset_Icc_self hs))
  have hd : y s - w s ≠ 0 := sub_ne_zero.2 hyw
  have hvw : v s - w s ≠ 0 := sub_ne_zero.2 (h.lt s (Ioo_subset_Icc_self hs)).ne
  have hyv' : y s - v s ≠ 0 := sub_ne_zero.2 hyv
  simp only [Function.comp_apply, ← hs_def]
  field_simp
  ring

/-- **Lower points**: a real point path `y > v` (the image of a lower boundary point of `S_π`) solves
`p' = coth((p − ξ)/2)` in the strip clock. -/
theorem hasDerivAt_stripPoint_of_lt (h : IsSepMark w v S) {y : ℝ → ℝ} (hy : ContinuousOn y (Icc 0 S))
    (hint : IntervalIntegrable (fun u => 2 / (y u - w u)) volume 0 S)
    (heq : ∀ s ∈ Icc 0 S, y s = y 0 + ∫ u in (0 : ℝ)..s, 2 / (y u - w u)) {t : ℝ}
    (ht : t ∈ Ioo 0 (stripClock w v S)) (hyw : y (chordalTime w v t) ≠ w (chordalTime w v t))
    (hvy : v (chordalTime w v t) < y (chordalTime w v t)) :
    HasDerivAt (stripPoint w v y) (Sec4.cothHalf (stripPoint w v y t - stripDriver w v t)) t := by
  refine (h.hasDerivAt_stripPoint_aux hy hint heq ht hyw hvy.ne').congr_deriv ?_
  set s := chordalTime w v t
  have ha : 0 < w s - v s := sub_pos.2 (h.lt s (h.chordalTime_mem (Ioo_subset_Icc_self ht)))
  have hd : y s - w s ≠ 0 := sub_ne_zero.2 hyw
  have he : Real.exp (stripPoint w v y t - stripDriver w v t) = (y s - v s) / (w s - v s) := by
    rw [stripPoint, stripDriver, show t + Real.log |y s - v s| - (t + Real.log (w s - v s)) =
      Real.log |y s - v s| - Real.log (w s - v s) by ring, Real.exp_sub, Real.exp_log (abs_pos.2
      (sub_ne_zero.2 hvy.ne')), Real.exp_log ha, abs_of_pos (sub_pos.2 hvy)]
  rw [Sec4.cothHalf, he, div_add_one ha.ne', div_sub_one ha.ne', div_div_div_cancel_right₀ ha.ne',
    show y s - v s - (w s - v s) = y s - w s by ring]
  field_simp
  ring

/-- **Upper points**: a real point path `y < v` (the image of an upper boundary point `x + iπ` of `S_π`, with strip
real part `p`) solves `p' = tanh((p − ξ)/2)` in the strip clock (`coth((p + iπ − ξ)/2) = tanh((p − ξ)/2)`). -/
theorem hasDerivAt_stripPoint_of_gt (h : IsSepMark w v S) {y : ℝ → ℝ} (hy : ContinuousOn y (Icc 0 S))
    (hint : IntervalIntegrable (fun u => 2 / (y u - w u)) volume 0 S)
    (heq : ∀ s ∈ Icc 0 S, y s = y 0 + ∫ u in (0 : ℝ)..s, 2 / (y u - w u)) {t : ℝ}
    (ht : t ∈ Ioo 0 (stripClock w v S)) (hyv : y (chordalTime w v t) < v (chordalTime w v t)) :
    HasDerivAt (stripPoint w v y) (Real.tanh ((stripPoint w v y t - stripDriver w v t) / 2)) t := by
  have hvw := h.lt _ (h.chordalTime_mem (Ioo_subset_Icc_self ht))
  refine (h.hasDerivAt_stripPoint_aux hy hint heq ht (hyv.trans hvw).ne hyv.ne).congr_deriv ?_
  set s := chordalTime w v t
  have ha : 0 < w s - v s := sub_pos.2 hvw
  have hd : y s - w s ≠ 0 := sub_ne_zero.2 (hyv.trans hvw).ne
  have he : Real.exp (stripPoint w v y t - stripDriver w v t) = (v s - y s) / (w s - v s) := by
    rw [stripPoint, stripDriver, show t + Real.log |y s - v s| - (t + Real.log (w s - v s)) =
      Real.log |y s - v s| - Real.log (w s - v s) by ring, Real.exp_sub, Real.exp_log (abs_pos.2
      (sub_ne_zero.2 hyv.ne)), Real.exp_log ha, abs_of_neg (sub_neg.2 hyv), neg_sub]
  rw [tanh_half_eq, he, div_add_one ha.ne', div_sub_one ha.ne', div_div_div_cancel_right₀ ha.ne',
    show v s - y s + (w s - v s) = -(y s - w s) by ring]
  field_simp
  ring

end IsSepMark

/-! ### Strip hulls and strip traces -/

/-- The strip hull at strip time `t`: the points of `S_π` whose exponential image is swallowed by the chordal flow
by chordal time `s(t)`. -/
def stripHull (w v : ℝ → ℝ) (t : ℝ) : Set ℂ :=
  {z ∈ piStrip | stripExp z ∈ fwdHull w (chordalTime w v t)}

/-- The strip trace of a chordal trace `η` (exponential chart, inverse clock): `t ↦ log (1 + η(s(t)))`. A chordal
point of `(−∞, −1)` (the image of the upper line) has strip image on `ℝ + iπ` (principal logarithm). -/
def stripTrace (w v : ℝ → ℝ) (η : NNReal → ℂ) (t : ℝ) : ℂ :=
  log (1 + η (chordalTime w v t).toNNReal)

theorem log_one_add_stripExp {z : ℂ} (hz : z ∈ piStrip) : log (1 + stripExp z) = z := by
  rw [stripExp, add_sub_cancel]
  exact log_exp (by linarith [hz.1, Real.pi_pos]) hz.2.le

end Strip

end InteractingSLE
