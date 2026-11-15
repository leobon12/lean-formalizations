/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFieldFar
import InteractingSLE.Spec.ZhanGT4.DualSeedChain

/-!
# Zhan's A.1.6, the seeded field II: the own-chart marks through the opposite-hull map

Packet PROVE-ZHAN-GT4-A20. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L500, R38): "In the remaining formulas the symbol `g_j(p_m)` means `V_j^m` when `p_m` is a
seed of curve `j` … At positive own time, differentiating (D13)–(D15) by Itô and the force ODE is the same cancelled
calculation leading to (D8)."

In the uniform own-chart design of PROVE-ZHAN-GT4-A19 (`DualSeedGen`), every mark enters the seeded density through its
own-chart force coordinate `V_t` (`V' = 2/(V − W)` at positive times) and the opposite-hull map:
`B_{m,0}(t) = F_t(V_t)`, `B_{m,1}(t) = F_t'(V_t)` (`F_t = ownExt … t`, the reflected `h_j`). This file proves their
time derivatives, the inputs of A19's `seedTimeT`: by (D1) at the frozen point (`DualSeedFieldFar`) and the force ODE
(chain rule `hasDerivWithinAt_comp_of_partial`), the `h'(V)/(V − W)` terms cancel:

* **`hasDerivWithinAt_markVal`**: `∂_t F_t(V_t) = 2A₁²/(F_t(V_t) − A₀)` (as for an alive point, (D3));
* **`hasDerivWithinAt_markDeriv`**: `∂_t F_t'(V_t) = F_t'(V_t)(−2A₁²/(F_t(V_t) − A₀)² + 2/(V_t − W_t)²)` (A7's (D3)
  rate plus the own-chart rate of the force coordinate);

within any set of times `J ⊆ [0, T]` along which `V` follows the force ODE, at a time `t` at which `V_t ≠ W_t`,
`F_t(V_t) ≠ A₀(t) = W'(a(t))` and a disc around `V_t` misses `g_s(A)` for `s` near `t`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

theorem mem_ball_ofReal_iff {x y r : ℝ} : (x : ℂ) ∈ ball (y : ℂ) r ↔ |x - y| < r := by
  rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

/-- At a real point of a disc missing `g_t(A)` every derivative of `F_t` is real. -/
theorem iterDeriv_im_of_clear {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {v ρ : ℝ} (hρ : 0 < ρ)
    (hdisj : Disjoint (ball (v : ℂ) ρ) ((fun z => fwdMap W t z + W t) '' A)) (k : ℕ) :
    (deriv^[k] (ownExt W W' a φ t) v).im = 0 := by
  obtain ⟨hd, -, -, hreal, -, -⟩ := h.ownExt_props ht hdisj
  exact im_iterDeriv_eq_zero_of_real hd (fun y hy => hreal _ hy (by simp)) k v (mem_ball_self (by positivity))

/-- `F_t'(W_t) = A₁(t)` as a complex number. -/
theorem deriv_ownExt_driver_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    deriv (ownExt W W' a φ t) (W t) = (frzA W W' a φ 1 t : ℂ) := by
  have := h.iterDeriv_driver_im ht 1
  simp only [Function.iterate_one] at this
  rw [eq_ofReal_re_of_im_eq_zero this]
  simp [frzA]

omit h in
/-- The iterated derivatives are holomorphic and jointly continuous on a box with clearance. -/
theorem farBox_iterDeriv (h : OwnData W A φ T a W') {b c y r : ℝ} (hJ : Icc b c ⊆ Icc 0 T)
    (hdisj : ∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * r)) ((fun z => fwdMap W t z + W t) '' A)) (k : ℕ) :
    (∀ s ∈ Icc b c, DifferentiableOn ℂ (deriv^[k] (ownExt W W' a φ s)) (ball (y : ℂ) r)) ∧
      ContinuousOn (fun q : ℝ × ℂ => deriv^[k] (ownExt W W' a φ q.1) q.2) (Icc b c ×ˢ ball (y : ℂ) r) := by
  induction k with
  | zero => exact ⟨fun s hs => (h.box_props hJ hdisj hs).1, h.continuousOn_box hJ hdisj⟩
  | succ j ih =>
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [Function.iterate_succ_apply']
      exact (ih.1 s hs).deriv isOpen_ball
    · have := continuousOn_deriv_of_holo (F := fun s => deriv^[j] (ownExt W W' a φ s)) ih.1 ih.2
      simpa only [Function.iterate_succ_apply'] using this

/-- **The chain rule along a mark** (any order `k`), from the time derivative of `Re F_s^{(k)}` at the frozen point
`V_t` on a box around `t` where a disc around `V_t` misses every `g_s(A)`. -/
theorem hasDerivWithinAt_iterDeriv_mark {J : Set ℝ} (hJ : J ⊆ Icc 0 T) {V : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (hV : HasDerivWithinAt V (2 / (V t - W t)) J t) {η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (hdisj : ∀ s ∈ Icc (max 0 (t - η)) (min T (t + η)),
      Disjoint (ball (V t : ℂ) (2 * r)) ((fun z => fwdMap W s z + W s) '' A)) (k : ℕ) {ft : ℝ}
    (hft : HasDerivWithinAt (fun s => (deriv^[k] (ownExt W W' a φ s) (V t)).re) ft
      (Icc (max 0 (t - η)) (min T (t + η))) t) :
    HasDerivWithinAt (fun s => (deriv^[k] (ownExt W W' a φ s) (V s)).re)
      (ft + (deriv^[k + 1] (ownExt W W' a φ t) (V t)).re * (2 / (V t - W t))) J t := by
  set b := max 0 (t - η) with hb
  set c := min T (t + η) with hc
  have hJc : Icc b c ⊆ Icc 0 T := fun s hs => (mem_box_of_abs_lt (T := T) hs).1
  have htb : t ∈ Icc b c := mem_box_self hη ht
  have hmem : J ∩ Icc b c ∈ 𝓝[J] t := inter_mem self_mem_nhdsWithin (nhdsWithin_mono t hJ (box_mem_nhds hη))
  obtain ⟨hd, hcont⟩ := h.farBox_iterDeriv hJc hdisj k
  obtain ⟨-, hcont1⟩ := h.farBox_iterDeriv hJc hdisj (k + 1)
  have hfx : ∀ᶠ p in 𝓝[J ∩ Icc b c] t ×ˢ 𝓝 (V t),
      HasDerivAt (fun x : ℝ => (deriv^[k] (ownExt W W' a φ p.1) x).re)
        ((deriv^[k + 1] (ownExt W W' a φ p.1) p.2).re) p.2 := by
    filter_upwards [Filter.prod_mem_prod (mem_of_superset self_mem_nhdsWithin inter_subset_right)
      (Metric.ball_mem_nhds (V t) hr)] with p hp
    have hpB : (p.2 : ℂ) ∈ ball (V t : ℂ) r := by
      rw [mem_ball_ofReal_iff]; have := hp.2; rwa [Metric.mem_ball, Real.dist_eq] at this
    have := (((hd p.1 hp.1).differentiableAt (isOpen_ball.mem_nhds hpB)).hasDerivAt).real_of_complex
    rw [Function.iterate_succ_apply']
    exact this
  have hmap : Tendsto (fun p : ℝ × ℝ => (p.1, (p.2 : ℂ))) (𝓝[J ∩ Icc b c] t ×ˢ 𝓝 (V t))
      (𝓝[Icc b c ×ˢ ball (V t : ℂ) r] (t, (V t : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc' : Continuous fun p : ℝ × ℝ => (p.1, (p.2 : ℂ)) :=
        continuous_fst.prodMk (continuous_ofReal.comp continuous_snd)
      refine (hc'.tendsto (t, V t)).mono_left ?_
      rw [nhds_prod_eq]
      exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
    · filter_upwards [Filter.prod_mem_prod (mem_of_superset self_mem_nhdsWithin inter_subset_right)
        (Metric.ball_mem_nhds (V t) hr)] with p hp
      refine ⟨hp.1, ?_⟩
      rw [mem_ball_ofReal_iff]; have := hp.2; rwa [Metric.mem_ball, Real.dist_eq] at this
  have hcx : Tendsto (fun p : ℝ × ℝ => (deriv^[k + 1] (ownExt W W' a φ p.1) p.2).re)
      (𝓝[J ∩ Icc b c] t ×ˢ 𝓝 (V t)) (𝓝 ((deriv^[k + 1] (ownExt W W' a φ t) (V t)).re)) := by
    have h1 := (hcont1 (t, (V t : ℂ)) ⟨htb, mem_ball_self hr⟩).tendsto.comp hmap
    exact (Complex.continuous_re.tendsto _).comp h1
  exact (hasDerivWithinAt_comp_of_partial (s := J ∩ Icc b c)
    (f := fun τ x => (deriv^[k] (ownExt W W' a φ τ) x).re)
    (fx := fun τ x => (deriv^[k + 1] (ownExt W W' a φ τ) x).re) (v := V)
    (hft.mono inter_subset_right) (hV.mono inter_subset_left) hfx hcx).mono_of_mem_nhdsWithin hmem

section Mark

variable {J : Set ℝ} (hJ : J ⊆ Icc 0 T) {V : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
  (hV : HasDerivWithinAt V (2 / (V t - W t)) J t) {ρ η₀ : ℝ} (hρ : 0 < ρ) (hη₀ : 0 < η₀)
  (hcl : ∀ s ∈ Icc (max 0 (t - η₀)) (min T (t + η₀)),
    Disjoint (ball (V t : ℂ) ρ) ((fun z => fwdMap W s z + W s) '' A))
  (hVW : V t ≠ W t) (hVF : (ownExt W W' a φ t (V t)).re ≠ W' (a t))
include hJ ht hV hρ hη₀ hcl hVW hVF

omit hJ hV in
/-- The far box around the mark, with the real data at the mark. -/
theorem exists_markBox : ∃ η > (0 : ℝ), ∃ r > (0 : ℝ),
    (∀ s ∈ Icc (max 0 (t - η)) (min T (t + η)),
      Disjoint (ball (V t : ℂ) (2 * r)) ((fun z => fwdMap W s z + W s) '' A)) ∧
    (∀ s ∈ Icc (max 0 (t - η)) (min T (t + η)), ∀ z ∈ ball (V t : ℂ) r, z - W s ≠ 0) ∧
    (∀ s ∈ Icc (max 0 (t - η)) (min T (t + η)), ∀ z ∈ ball (V t : ℂ) r,
      ownExt W W' a φ s z - ownExt W W' a φ s (W s) ≠ 0) ∧
    (∀ k, deriv^[k] (ownExt W W' a φ t) (V t) = ((deriv^[k] (ownExt W W' a φ t) (V t)).re : ℂ)) := by
  have hbox : t ∈ Icc (max 0 (t - η₀)) (min T (t + η₀)) := mem_box_self hη₀ ht
  have hreal : ∀ k, deriv^[k] (ownExt W W' a φ t) (V t) = ((deriv^[k] (ownExt W W' a φ t) (V t)).re : ℂ) :=
    fun k => eq_ofReal_re_of_im_eq_zero (h.iterDeriv_im_of_clear ht hρ (hcl t hbox) k)
  have hVFc : ownExt W W' a φ t (V t) ≠ ownExt W W' a φ t (W t) := by
    rw [h.ownExt_driver ht]
    have e := hreal 0
    simp only [Function.iterate_zero, id] at e
    rw [e]
    exact_mod_cast hVF
  obtain ⟨η, hη, r, hr, h1, h2, h3⟩ := h.exists_farBox ht hρ hη₀ hcl hVW hVFc
  exact ⟨η, hη, r, hr, h1, h2, h3, hreal⟩

/-- **(D3) along a mark**: `∂_t F_t(V_t) = 2A₁²/(F_t(V_t) − A₀)` within `J`. -/
theorem hasDerivWithinAt_markVal :
    HasDerivWithinAt (fun s => (ownExt W W' a φ s (V s)).re)
      (2 * frzA W W' a φ 1 t ^ 2 / ((ownExt W W' a φ t (V t)).re - W' (a t))) J t := by
  obtain ⟨η, hη, r, hr, hdisj, hWf, hF0, hreal⟩ := h.exists_markBox ht hρ hη₀ hcl hVW hVF
  have hJc : Icc (max 0 (t - η)) (min T (t + η)) ⊆ Icc 0 T := fun s hs => (mem_box_of_abs_lt (T := T) hs).1
  have hft := h.hasDerivWithinAt_re_ownExt_far hJc hdisj hWf hF0 (mem_box_self hη ht) (mem_ball_self hr)
  have key := h.hasDerivWithinAt_iterDeriv_mark hJ ht hV hη hr hdisj 0 (ft := _)
    (by simpa only [Function.iterate_zero, id] using hft)
  simp only [Function.iterate_zero, id, zero_add, Function.iterate_one] at key
  refine key.congr_deriv ?_
  have h0 := hreal 0
  have h1 := hreal 1
  simp only [Function.iterate_zero, id, Function.iterate_one] at h0 h1
  rw [re_dFar_of_real h0 (h.ownExt_driver ht) (h.deriv_ownExt_driver_eq ht) h1]
  ring

/-- **The derivative factor along a mark**: `∂_t F_t'(V_t) = F_t'(V_t)(−2A₁²/(F_t(V_t) − A₀)² + 2/(V_t − W_t)²)`
within `J`. -/
theorem hasDerivWithinAt_markDeriv :
    HasDerivWithinAt (fun s => (deriv (ownExt W W' a φ s) (V s)).re)
      ((deriv (ownExt W W' a φ t) (V t)).re * (-2 * frzA W W' a φ 1 t ^ 2 /
        ((ownExt W W' a φ t (V t)).re - W' (a t)) ^ 2 + 2 / (V t - W t) ^ 2)) J t := by
  obtain ⟨η, hη, r, hr, hdisj, hWf, hF0, hreal⟩ := h.exists_markBox ht hρ hη₀ hcl hVW hVF
  have hJc : Icc (max 0 (t - η)) (min T (t + η)) ⊆ Icc 0 T := fun s hs => (mem_box_of_abs_lt (T := T) hs).1
  have htb := mem_box_self hη ht
  have hft := h.hasDerivWithinAt_re_deriv_ownExt_far hJc hdisj hWf hF0 htb (mem_ball_self hr)
  have key := h.hasDerivWithinAt_iterDeriv_mark hJ ht hV hη hr hdisj 1 (ft := _)
    (by simpa only [Function.iterate_one] using hft)
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id] at key
  refine key.congr_deriv ?_
  have h0 := hreal 0
  have h1 := hreal 1
  have h2 := hreal 2
  simp only [Function.iterate_zero, id, Function.iterate_succ_apply'] at h0 h1 h2
  obtain ⟨hd, -⟩ := h.farBox_iterDeriv hJc hdisj 0
  have hdF : DifferentiableOn ℂ (ownExt W W' a φ t) (ball (V t : ℂ) r) := by
    simpa only [Function.iterate_zero, id] using hd t htb
  have hVB : (V t : ℂ) ∈ ball (V t : ℂ) r := mem_ball_self hr
  have hf := (hdF.differentiableAt (isOpen_ball.mem_nhds hVB)).hasDerivAt
  have hf' := ((hdF.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hVB)).hasDerivAt
  have hu0 : (ownExt W W' a φ t (V t)).re - W' (a t) ≠ 0 := sub_ne_zero.2 hVF
  have hx0 : V t - W t ≠ 0 := sub_ne_zero.2 hVW
  rw [re_deriv_dFar_of_real hf hf' h0 (h.ownExt_driver ht) (h.deriv_ownExt_driver_eq ht) h1 h2 hu0 hx0]
  ring

end Mark

end OwnData

end InteractingSLE.ZhanGT4
