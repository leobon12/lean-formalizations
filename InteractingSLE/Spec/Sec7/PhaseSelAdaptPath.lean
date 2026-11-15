/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelAdaptMain

/-!
# §7.4, Aux. lemma 122 before an announced lifetime: continuing a force path after a time

Packet PROVE-STRIPSYS6 (specification §7.4, Aux. lemma 122, `source/spec/p385-432.md` L104–L131: "Consider a
continuous Loewner trace from zero in `ℍ`, with continuous driver and positive stopping lifetime `T`"; the coordinates
are only defined, and only nice, before `T`).

`PhaseSelAdapt.aux122_adapt` needs globally defined coordinates. To apply it at an announcing time `σ < T`, the
coordinates are continued after `σ` by the Loewner flow of the frozen driver: `W̃_t = W_{t∧σ}` and
`Ṽ_t = W_σ ± √((V_σ − W_σ)² + 4(t − σ))` for `t ≥ σ` (`+` on the right, `−` on the left). This file proves, for one
path, that the continuation is a force path for every realization (`isForcePath_contV_right`,
`isForcePath_contV_left`), with its monotonicity, ordering, index monotonicity, merging and separation.

## Main definitions

* `contW w s`, `contV e w v s`: the driver frozen after `s` and a force point continued after `s` on the side `e`.

## Main results

* `contV_of_le`, `contV_of_ge`, `continuous_contW`, `continuous_contV`;
* `isForcePath_neg`: reflection of force paths;
* **`isForcePath_contV_right`**, **`isForcePath_contV_left`**;
* `monotone_contV_right`, `antitone_contV_left`, `contV_right_le`/`le_contV_left` (index monotonicity),
  `contV_eq_of_eq` (merging), `contV_ne_contW` (separation after `s`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSelAdapt

open MartChar

/-! ### The continued paths -/

/-- The driver frozen after time `s`. -/
def contW (w : ℝ≥0 → ℝ) (s : ℝ≥0) (t : ℝ≥0) : ℝ := w (min t s)

/-- A force point continued after time `s` by the Loewner flow of the frozen driver, on the side `e` (`e = 1`: right,
`e = −1`: left): `w_{t∧s} + e √((v_{t∧s} − w_{t∧s})² + 4(t − t∧s))`. -/
def contV (e : ℝ) (w v : ℝ≥0 → ℝ) (s : ℝ≥0) (t : ℝ≥0) : ℝ :=
  w (min t s) + e * Real.sqrt ((v (min t s) - w (min t s)) ^ 2 + 4 * ((t : ℝ) - ((min t s : ℝ≥0) : ℝ)))

variable {w v : ℝ≥0 → ℝ} {s t : ℝ≥0}

theorem contW_of_le (h : t ≤ s) : contW w s t = w t := by
  simp only [contW, min_eq_left h]

theorem contW_of_ge (h : s ≤ t) : contW w s t = w s := by
  simp only [contW, min_eq_right h]

theorem contV_of_ge (e : ℝ) (h : s ≤ t) :
    contV e w v s t = w s + e * Real.sqrt ((v s - w s) ^ 2 + 4 * ((t : ℝ) - s)) := by
  simp only [contV, min_eq_right h]

theorem contV_right_of_le (hord : w t ≤ v t) (h : t ≤ s) : contV 1 w v s t = v t := by
  simp only [contV, min_eq_left h, sub_self, mul_zero, add_zero, one_mul, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (sub_nonneg.2 hord)]
  ring

theorem contV_left_of_le (hord : v t ≤ w t) (h : t ≤ s) : contV (-1) w v s t = v t := by
  simp only [contV, min_eq_left h, sub_self, mul_zero, add_zero, Real.sqrt_sq_eq_abs,
    abs_of_nonpos (sub_nonpos.2 hord)]
  ring

theorem contV_sub_contW (e : ℝ) (t : ℝ≥0) : contV e w v s t - contW w s t =
    e * Real.sqrt ((v (min t s) - w (min t s)) ^ 2 + 4 * ((t : ℝ) - ((min t s : ℝ≥0) : ℝ))) := by
  simp only [contV, contW]
  ring

/-- After `s` the continued force point is strictly away from the frozen driver. -/
theorem contV_ne_contW {e : ℝ} (he : e ≠ 0) (h : s < t) : contV e w v s t ≠ contW w s t := by
  intro heq
  have h0 := contV_sub_contW (w := w) (v := v) (s := s) e t
  rw [heq, sub_self, min_eq_right h.le] at h0
  have hpos : 0 < (v s - w s) ^ 2 + 4 * ((t : ℝ) - s) := by
    have : (s : ℝ) < t := h
    nlinarith [sq_nonneg (v s - w s)]
  have := mul_ne_zero he (Real.sqrt_pos.2 hpos).ne'
  exact this h0.symm

theorem contV_left_le_contW (t : ℝ≥0) : contV (-1) w v s t ≤ contW w s t := by
  have h := contV_sub_contW (w := w) (v := v) (s := s) (-1) t
  have h0 := Real.sqrt_nonneg ((v (min t s) - w (min t s)) ^ 2 + 4 * ((t : ℝ) - ((min t s : ℝ≥0) : ℝ)))
  linarith

theorem contW_le_contV_right (t : ℝ≥0) : contW w s t ≤ contV 1 w v s t := by
  have h := contV_sub_contW (w := w) (v := v) (s := s) 1 t
  have h0 := Real.sqrt_nonneg ((v (min t s) - w (min t s)) ^ 2 + 4 * ((t : ℝ) - ((min t s : ℝ≥0) : ℝ)))
  linarith

theorem continuous_contW (hw : ContinuousOn w (Iic s)) : Continuous (contW w s) :=
  hw.comp_continuous (continuous_id.min continuous_const) fun t => min_le_right t s

theorem continuous_contV (e : ℝ) (hw : ContinuousOn w (Iic s)) (hv : ContinuousOn v (Iic s)) :
    Continuous (contV e w v s) := by
  have hm : Continuous fun t : ℝ≥0 => min t s := continuous_id.min continuous_const
  have hwc : Continuous fun t : ℝ≥0 => w (min t s) := hw.comp_continuous hm fun t => min_le_right t s
  have hvc : Continuous fun t : ℝ≥0 => v (min t s) := hv.comp_continuous hm fun t => min_le_right t s
  have hc : Continuous fun t : ℝ≥0 => ((min t s : ℝ≥0) : ℝ) := NNReal.continuous_coe.comp hm
  exact hwc.add (continuous_const.mul (((hvc.sub hwc).pow 2).add
    (continuous_const.mul (NNReal.continuous_coe.sub hc))).sqrt)

/-! ### Reflection of force paths -/

/-- **Reflection**: `(−w, −v)` is a force path iff `(w, v)` is. -/
theorem isForcePath_neg (h : IsForcePath w v) : IsForcePath (fun t => -w t) (fun t => -v t) := by
  obtain ⟨hc, hm, hd, hn⟩ := h
  refine ⟨hc.neg, hm.symm.imp (fun h => h.neg) (fun h => h.neg), fun u hu hne => ?_, ?_⟩
  · have hne' : v u.toNNReal ≠ w u.toNNReal := fun h => hne (by simp only [h])
    refine ((hd u hu hne').neg).congr_deriv ?_
    show -(2 / (v u.toNNReal - w u.toNNReal)) = 2 / (-v u.toNNReal - -w u.toNNReal)
    rw [show -v u.toNNReal - -w u.toNNReal = -(v u.toNNReal - w u.toNNReal) by ring, div_neg]
  · convert hn using 3
    simp only [neg_inj]

/-! ### The right continuation is a force path -/

theorem hasDerivAt_sqrt_affine {a c u : ℝ} (hpos : 0 < a ^ 2 + 4 * (u - c)) :
    HasDerivAt (fun r : ℝ => Real.sqrt (a ^ 2 + 4 * (r - c))) (2 / Real.sqrt (a ^ 2 + 4 * (u - c))) u := by
  have h1 : HasDerivAt (fun r : ℝ => a ^ 2 + 4 * (r - c)) 4 u := by
    simpa using ((hasDerivAt_id u).sub_const c).const_mul (4 : ℝ) |>.const_add (a ^ 2)
  have h2 := (Real.hasDerivAt_sqrt hpos.ne').comp u h1
  have hs : Real.sqrt (a ^ 2 + 4 * (u - c)) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  refine h2.congr_deriv ?_
  rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (mul_ne_zero two_ne_zero hs) hs]
  ring

theorem monotone_contV_right (hord : ∀ t ≤ s, w t ≤ v t) (hmono : MonotoneOn v (Iic s)) :
    Monotone (contV 1 w v s) := by
  intro t t' htt'
  rcases le_total t' s with h' | h'
  · rw [contV_right_of_le (hord _ h') h', contV_right_of_le (hord _ (htt'.trans h')) (htt'.trans h')]
    exact hmono (mem_Iic.2 (htt'.trans h')) (mem_Iic.2 h') htt'
  · rw [contV_of_ge 1 h', one_mul]
    rcases le_total t s with h | h
    · rw [contV_right_of_le (hord _ h) h]
      calc v t ≤ v s := hmono (mem_Iic.2 h) (mem_Iic.2 le_rfl) h
        _ = w s + Real.sqrt ((v s - w s) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (sub_nonneg.2 (hord s le_rfl))]; ring
        _ ≤ _ := by gcongr; have : (s : ℝ) ≤ t' := h'; linarith
    · rw [contV_of_ge 1 h, one_mul]
      gcongr

/-- **The right continuation is a force path**: a right force point `v ≥ w`, monotone, continuous and a force path of
`w` up to the time `s` (derivative condition at every `0 < u ≤ s`, collision set null in `[0, s]`), continued after `s`
by `w_s + √((v_s − w_s)² + 4(t − s))`, is a force path of the frozen driver for all times. -/
theorem isForcePath_contV_right (hw : ContinuousOn w (Iic s)) (hv : ContinuousOn v (Iic s))
    (hord : ∀ t ≤ s, w t ≤ v t) (hmono : MonotoneOn v (Iic s))
    (hder : ∀ u : ℝ, 0 < u → u ≤ s → v u.toNNReal ≠ w u.toNNReal →
      HasDerivAt (fun r : ℝ => v r.toNNReal) (2 / (v u.toNNReal - w u.toNNReal)) u)
    (hnull : volume {u : ℝ | 0 ≤ u ∧ u ≤ s ∧ v u.toNNReal = w u.toNNReal} = 0) :
    IsForcePath (contW w s) (contV 1 w v s) := by
  set a : ℝ := v s - w s with ha
  have hs0 : (0 : ℝ) ≤ s := s.coe_nonneg
  -- the continued force point as a function of real time, on both sides of `s`
  have hle : ∀ r : ℝ, r ≤ s → contV 1 w v s r.toNNReal = v r.toNNReal ∧ contW w s r.toNNReal = w r.toNNReal :=
    fun r hr => by
      have hr' : r.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 hr
      exact ⟨contV_right_of_le (hord _ hr') hr', contW_of_le hr'⟩
  have hge : ∀ r : ℝ, (s : ℝ) ≤ r → contV 1 w v s r.toNNReal = w s + Real.sqrt (a ^ 2 + 4 * (r - s)) ∧
      contW w s r.toNNReal = w s := fun r hr => by
    have hr' : s ≤ r.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hs0.trans hr)]; exact hr
    rw [contV_of_ge 1 hr', contW_of_ge hr', Real.coe_toNNReal _ (hs0.trans hr), one_mul]
    exact ⟨rfl, rfl⟩
  refine ⟨continuous_contV 1 hw hv, Or.inl (monotone_contV_right hord hmono), fun u hu hne => ?_, ?_⟩
  · -- the derivative
    rcases lt_trichotomy u s with hus | hus | hus
    · have hev : (fun r : ℝ => contV 1 w v s r.toNNReal) =ᶠ[𝓝 u] fun r => v r.toNNReal :=
        (eventually_lt_nhds hus).mono fun r hr => (hle r hr.le).1
      obtain ⟨h1, h2⟩ := hle u hus.le
      rw [h1, h2] at hne ⊢
      exact (hder u hu hus.le hne).congr_of_eventuallyEq hev
    · subst hus
      obtain ⟨h1, h2⟩ := hle s le_rfl
      rw [h1, h2] at hne ⊢
      simp only [Real.toNNReal_coe] at hne ⊢
      have hapos : 0 < a := lt_of_le_of_ne (sub_nonneg.2 (hord s le_rfl)) (fun h => hne (by linarith))
      have hL : HasDerivWithinAt (fun r : ℝ => contV 1 w v s r.toNNReal) (2 / (v s - w s)) (Iic (s : ℝ)) s := by
        have := (hder s hu le_rfl (by simpa only [Real.toNNReal_coe] using hne)).hasDerivWithinAt
          (s := Iic (s : ℝ))
        simp only [Real.toNNReal_coe] at this
        refine this.congr (fun r hr => (hle r hr).1) ?_
        simpa only [Real.toNNReal_coe] using (hle s le_rfl).1
      have hR : HasDerivWithinAt (fun r : ℝ => contV 1 w v s r.toNNReal) (2 / (v s - w s)) (Ici (s : ℝ)) s := by
        have hpos : 0 < a ^ 2 + 4 * ((s : ℝ) - s) := by simp only [sub_self, mul_zero, add_zero]; positivity
        have hd := ((hasDerivAt_sqrt_affine (c := (s : ℝ)) hpos).const_add (w s)).hasDerivWithinAt
          (s := Ici (s : ℝ))
        have hval : 2 / Real.sqrt (a ^ 2 + 4 * ((s : ℝ) - s)) = 2 / (v s - w s) := by
          simp only [sub_self, mul_zero, add_zero, ha]
          rw [Real.sqrt_sq (by rw [← ha]; exact hapos.le)]
        rw [hval] at hd
        refine hd.congr (fun r hr => (hge r hr).1) ?_
        exact (hge s le_rfl).1
      have := hL.union hR
      rw [Iic_union_Ici] at this
      exact this.hasDerivAt Filter.univ_mem
    · have hpos : ∀ r : ℝ, (s : ℝ) < r → 0 < a ^ 2 + 4 * (r - s) := fun r hr => by
        nlinarith [sq_nonneg a]
      have hev : (fun r : ℝ => contV 1 w v s r.toNNReal) =ᶠ[𝓝 u] fun r => w s + Real.sqrt (a ^ 2 + 4 * (r - s)) :=
        (eventually_gt_nhds hus).mono fun r hr => (hge r hr.le).1
      obtain ⟨h1, h2⟩ := hge u hus.le
      rw [h1, h2, add_sub_cancel_left]
      exact ((hasDerivAt_sqrt_affine (hpos u hus)).const_add (w s)).congr_of_eventuallyEq hev
  · -- the collision set is null
    refine measure_mono_null (fun u hu => ?_) hnull
    obtain ⟨hu0, heq⟩ := hu
    rcases le_or_gt u s with hus | hus
    · obtain ⟨h1, h2⟩ := hle u hus
      exact ⟨hu0, hus, by rw [← h1, ← h2]; exact heq⟩
    · exfalso
      have hlt : s < u.toNNReal := (Real.lt_toNNReal_iff_coe_lt).2 hus
      exact contV_ne_contW one_ne_zero hlt heq

/-! ### The left continuation, by reflection -/

theorem contV_left_eq_neg (w v : ℝ≥0 → ℝ) (s : ℝ≥0) :
    contV (-1) w v s = fun t => -contV 1 (fun t => -w t) (fun t => -v t) s t := by
  funext t
  simp only [contV]
  rw [show -v (min t s) - -w (min t s) = -(v (min t s) - w (min t s)) by ring, neg_sq]
  ring

theorem contW_neg (w : ℝ≥0 → ℝ) (s : ℝ≥0) : contW (fun t => -w t) s = fun t => -contW w s t := rfl

/-- **The left continuation is a force path** (reflection of `isForcePath_contV_right`). -/
theorem isForcePath_contV_left (hw : ContinuousOn w (Iic s)) (hv : ContinuousOn v (Iic s))
    (hord : ∀ t ≤ s, v t ≤ w t) (hanti : AntitoneOn v (Iic s))
    (hder : ∀ u : ℝ, 0 < u → u ≤ s → v u.toNNReal ≠ w u.toNNReal →
      HasDerivAt (fun r : ℝ => v r.toNNReal) (2 / (v u.toNNReal - w u.toNNReal)) u)
    (hnull : volume {u : ℝ | 0 ≤ u ∧ u ≤ s ∧ v u.toNNReal = w u.toNNReal} = 0) :
    IsForcePath (contW w s) (contV (-1) w v s) := by
  have h := isForcePath_contV_right (w := fun t => -w t) (v := fun t => -v t) (s := s) hw.neg hv.neg
    (fun t ht => neg_le_neg (hord t ht)) (fun a ha b hb hab => neg_le_neg (hanti ha hb hab))
    (fun u hu hus hne => by
      have hne' : v u.toNNReal ≠ w u.toNNReal := fun h => hne (by rw [h])
      refine ((hder u hu hus hne').neg).congr_deriv ?_
      show -(2 / (v u.toNNReal - w u.toNNReal)) = 2 / (-v u.toNNReal - -w u.toNNReal)
      rw [show -v u.toNNReal - -w u.toNNReal = -(v u.toNNReal - w u.toNNReal) by ring, div_neg])
    (by convert hnull using 3; simp only [neg_inj])
  have h2 := isForcePath_neg h
  rw [contV_left_eq_neg]
  convert h2 using 2
  simp [contW]

/-! ### Monotonicity, index order, merging -/

theorem antitone_contV_left (hord : ∀ t ≤ s, v t ≤ w t) (hanti : AntitoneOn v (Iic s)) :
    Antitone (contV (-1) w v s) := by
  have h := monotone_contV_right (w := fun t => -w t) (v := fun t => -v t) (s := s)
    (fun t ht => neg_le_neg (hord t ht)) (fun a ha b hb hab => neg_le_neg (hanti ha hb hab))
  rw [contV_left_eq_neg]
  exact fun a b hab => neg_le_neg (h hab)

/-- The continued right force points keep their order. -/
theorem contV_right_le {v' : ℝ≥0 → ℝ} (hord : ∀ t ≤ s, w t ≤ v t) (hle : ∀ t ≤ s, v t ≤ v' t) (t : ℝ≥0) :
    contV 1 w v s t ≤ contV 1 w v' s t := by
  rcases le_total t s with h | h
  · rw [contV_right_of_le (hord t h) h, contV_right_of_le ((hord t h).trans (hle t h)) h]
    exact hle t h
  · rw [contV_of_ge 1 h, contV_of_ge 1 h]
    have h0 : 0 ≤ v s - w s := sub_nonneg.2 (hord s le_rfl)
    have h1 : v s - w s ≤ v' s - w s := sub_le_sub_right (hle s le_rfl) _
    have h2 : (v s - w s) ^ 2 ≤ (v' s - w s) ^ 2 := pow_le_pow_left₀ h0 h1 2
    gcongr

/-- The continued left force points keep their order. -/
theorem contV_left_le {v' : ℝ≥0 → ℝ} (hord : ∀ t ≤ s, v t ≤ w t) (hle : ∀ t ≤ s, v' t ≤ v t) (t : ℝ≥0) :
    contV (-1) w v' s t ≤ contV (-1) w v s t := by
  have h := contV_right_le (w := fun t => -w t) (v := fun t => -v t) (v' := fun t => -v' t) (s := s)
    (fun t ht => neg_le_neg (hord t ht)) (fun t ht => neg_le_neg (hle t ht)) t
  rw [contV_left_eq_neg, contV_left_eq_neg]
  exact neg_le_neg h

/-- **Merged continued force points stay merged** (on one side, `e = ±1`, with the order `e (v − w) ≥ 0`, when the
original points stay merged up to `s`). -/
theorem contV_eq_of_eq {e : ℝ} (he : e = 1 ∨ e = -1) {v' : ℝ≥0 → ℝ}
    (hsg : 0 ≤ e * (v s - w s)) (hsg' : 0 ≤ e * (v' s - w s))
    (hval : ∀ t ≤ s, contV e w v s t = v t ∧ contV e w v' s t = v' t)
    (hmerge : ∀ t₀ t, t₀ ≤ t → t ≤ s → v t₀ = v' t₀ → v t = v' t) {t₀ t : ℝ≥0} (ht : t₀ ≤ t)
    (h0 : contV e w v s t₀ = contV e w v' s t₀) : contV e w v s t = contV e w v' s t := by
  have hss : v s = v' s := by
    rcases le_total t₀ s with h | h
    · rw [(hval t₀ h).1, (hval t₀ h).2] at h0
      exact hmerge t₀ s h le_rfl h0
    · rw [contV_of_ge e h, contV_of_ge e h] at h0
      have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
      have hq := mul_left_cancel₀ he0 (add_left_cancel h0)
      have hc : (0 : ℝ) ≤ 4 * ((t₀ : ℝ) - s) := by
        have : (s : ℝ) ≤ t₀ := h; linarith
      have hsq := (Real.sqrt_inj (by positivity) (by positivity)).1 hq
      have hsq' : (v s - w s) ^ 2 = (v' s - w s) ^ 2 := by linarith
      have habs := (sq_eq_sq_iff_abs_eq_abs _ _).1 hsq'
      rcases he with rfl | rfl
      · rw [one_mul] at hsg hsg'
        rw [abs_of_nonneg hsg, abs_of_nonneg hsg'] at habs
        linarith
      · have h1 : v s - w s ≤ 0 := by linarith
        have h2 : v' s - w s ≤ 0 := by linarith
        rw [abs_of_nonpos h1, abs_of_nonpos h2] at habs
        linarith
  rcases le_total t s with h | h
  · rw [(hval t h).1, (hval t h).2]
    rw [(hval t₀ (ht.trans h)).1, (hval t₀ (ht.trans h)).2] at h0
    exact hmerge t₀ t ht h h0
  · rw [contV_of_ge e h, contV_of_ge e h, hss]

end PhaseSelAdapt

end Sec7

end InteractingSLE
