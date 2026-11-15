/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTildeFrozen

/-!
# Zhan's A.1.6, the seeded field I: (D1) away from the driver

Packet PROVE-ZHAN-GT4-A20. Source: Astra, *Follow-up proofs*, §A.1.1 and §A.1.6
(`source/external/AstraIG1/ig1_followup_proofs.txt` L255–L266, L426–L500, R38): "(D1)
`∂_t h_t(z) = 2A₁²/(h_t(z) − A₀) − 2h_t'(z)/(z − W_t)`", and for a seed mark "the opposite-hull map `h_j` is analytic
across the entire relevant real interval … At positive own time, differentiating (D13)–(D15) by Itô and the force ODE is
the same cancelled calculation leading to (D8)."

The seeded density evaluates the reflected own-time map `F_t = ownExt … t` (A4) at the own-chart force coordinates
`V^m_t` of the marks. A seed coordinate is a real point away from the driver (`V^m_t ≠ W_t` at positive times) that need
not be the image of an alive point, so its time derivative cannot be read off the image chain (A7's `frzImg`); it needs
(D1) at real points away from the driver. A4 proved (D1) only on discs containing the driver
(`hasDerivWithinAt_ownExt_box`, in the removable form `dHat`). Here, on a **far box** `[b, c] × B(y, r)` (every
`g_t(A)` missing `B(y, 2r)`, the driver off the disc, `F_t(z) ≠ F_t(W_t)` on the disc), with
`dFar f a z = 2f'(a)²/(f(z) − f(a)) − 2f'(z)/(z − a)`:

* `hasDerivWithinAt_ownExt_upper_far`: (D1) at every upper point off `g_t(A)` (the driver's clearance gives the rate);
* `integral_identity_far`: `F_t − F_b = ∫_b^t dFar_s ds` on the whole disc (identity theorem from the upper half);
* **`hasDerivWithinAt_ownExt_far`**, **`hasDerivWithinAt_deriv_ownExt_far`**: `∂_t F_t(z) = dFar_t(z)` and
  `∂_t F_t'(z) = ∂_z dFar_t(z)` at every point of the disc, real points included;
* `exists_farBox`: a far box around every real point `v ≠ W_{t₀}` with `F_{t₀}(v) ≠ F_{t₀}(W_{t₀})` and clearance.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-- **The right side of (D1) away from the base point**: `2f'(a)²/(f(z) − f(a)) − 2f'(z)/(z − a)`. -/
def dFar (f : ℂ → ℂ) (a z : ℂ) : ℂ := 2 * deriv f a ^ 2 / (f z - f a) - 2 * deriv f z / (z - a)

/-- The derivative of `dFar f a` in `z`. -/
theorem hasDerivAt_dFar {f : ℂ → ℂ} {a z : ℂ} (hf : HasDerivAt f (deriv f z) z)
    (hf' : HasDerivAt (deriv f) (deriv (deriv f) z) z) (h0 : f z - f a ≠ 0) (h1 : z - a ≠ 0) :
    HasDerivAt (dFar f a)
      (-(2 * deriv f a ^ 2 * deriv f z) / (f z - f a) ^ 2 - 2 * deriv (deriv f) z / (z - a)
        + 2 * deriv f z / (z - a) ^ 2) z := by
  have h := ((hasDerivAt_const z (2 * deriv f a ^ 2)).div (hf.sub_const (f a)) h0).sub
    ((hf'.const_mul 2).div ((hasDerivAt_id z).sub_const a) h1)
  have e : dFar f a = fun w => 2 * deriv f a ^ 2 / (f w - f a) - 2 * deriv f w / (id w - a) := by
    funext w; simp [dFar]
  rw [e]
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- **The real part of `dFar` at real data.** -/
theorem re_dFar_of_real {f : ℂ → ℂ} {x w u v d e : ℝ} (hu : f x = u) (hv : f w = v) (hd : deriv f w = d)
    (he : deriv f x = e) :
    (dFar f w x).re = 2 * d ^ 2 / (u - v) - 2 * e / (x - w) := by
  unfold dFar
  rw [hu, hv, hd, he]
  rw [show (2 * (d : ℂ) ^ 2 / ((u : ℂ) - v) - 2 * (e : ℂ) / ((x : ℂ) - w)) =
    ((2 * d ^ 2 / (u - v) - 2 * e / (x - w) : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_re _

/-- The real part of `∂_z dFar` at real data. -/
theorem re_deriv_dFar_of_real {f : ℂ → ℂ} {x w u v d e e2 : ℝ} (hf : HasDerivAt f (deriv f x) x)
    (hf' : HasDerivAt (deriv f) (deriv (deriv f) x) x) (hu : f x = u) (hv : f w = v) (hd : deriv f w = d)
    (he : deriv f x = e) (he2 : deriv (deriv f) x = e2) (h0 : u - v ≠ 0) (h1 : x - w ≠ 0) :
    (deriv (dFar f w) x).re = -(2 * d ^ 2 * e) / (u - v) ^ 2 - 2 * e2 / (x - w) + 2 * e / (x - w) ^ 2 := by
  have h0' : f x - f w ≠ 0 := by
    rw [hu, hv, ← ofReal_sub]; exact_mod_cast h0
  have h1' : (x : ℂ) - w ≠ 0 := by rw [← ofReal_sub]; exact_mod_cast h1
  rw [(hasDerivAt_dFar hf hf' h0' h1').deriv, hu, hv, hd, he, he2]
  rw [show (-(2 * (d : ℂ) ^ 2 * e) / ((u : ℂ) - v) ^ 2 - 2 * (e2 : ℂ) / ((x : ℂ) - w) + 2 * (e : ℂ) / ((x : ℂ) - w) ^ 2)
    = ((-(2 * d ^ 2 * e) / (u - v) ^ 2 - 2 * e2 / (x - w) + 2 * e / (x - w) ^ 2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_re _

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

/-- **(D1) at upper points away from the driver**: for `z ∈ ℍ \ g_t(A)`,
`∂_t F_t(z) = 2F_t'(W_t)²/(F_t(z) − F_t(W_t)) − 2F_t'(z)/(z − W_t)` (the rate comes from the driver's clearance). -/
theorem hasDerivWithinAt_ownExt_upper_far {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {z : ℂ} (hzH : 0 < z.im)
    (hzE : z ∉ (fun z => fwdMap W t z + W t) '' A) :
    HasDerivWithinAt (fun s => ownExt W W' a φ s z) (dFar (ownExt W W' a φ t) (W t) z) (Icc 0 T) t := by
  set F := ownExt W W' a φ t with hFdef
  obtain ⟨ρ, hρ, hcl⟩ := h.exists_clearance
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
  obtain ⟨hFd, -, -, -, -, hFR⟩ := h.ownExt_props ht (hcl t ht)
  obtain ⟨-, him, hder⟩ := (h.rate t ht R hR).2.2.2 (ρ / 2) (by positivity) F hFd (hFR R hR)
  have hzA := h.invMap_not_mem ht hzH hzE
  have hcore := hasDerivWithinAt_ownMap_core h.cont h.zero h.hull h.mapOut (h.disjoint_A_K ⟨h.pos.le, le_rfl⟩)
    h.contW' h.a0 h.mono h.img ht hder hzH hzA
  have hfun : (fun s => ownExt W W' a φ s z) = fun s => ownMap W W' a φ s z := by
    funext s; simp [ownExt, hzH]
  rw [hfun]
  refine hcore.congr_deriv ?_
  have hat : 0 ≤ a t := by rw [← h.a0]; exact h.mono.monotoneOn ⟨le_rfl, h.pos.le⟩ ht ht.1
  have hsp := hasDerivAt_ownMap_space h.cont h.zero ht.1 h.hull h.mapOut h.contW' hat hzH hzA
    (h.phi_invMap_not_mem ht hzH hzA)
  have hFz : F z = ownMap W W' a φ t z := by simp [hFdef, ownExt, hzH]
  have hdF : deriv F z = deriv (fun y => fwdMap W' (a t) (φ (invMap W t y)) + (W' (a t) : ℂ)) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [QuantumZipper.isOpen_H.mem_nhds hzH] with w hw
    have hw' : (0 : ℝ) < w.im := hw
    simp [hFdef, ownExt, ownMap, hw']
  have hA1 : deriv F (W t) = ((deriv F (W t)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hA0 : F (W t) = W' (a t) := h.ownExt_driver ht
  unfold dFar
  rw [hdF, hsp.deriv, hFz, hA0]
  conv_rhs => rw [hA1]
  have hzW : z - (W t : ℂ) ≠ 0 := fun h0 => by
    have : (z - (W t : ℂ)).im = 0 := by rw [h0, zero_im]
    rw [sub_im, ofReal_im, sub_zero] at this; linarith
  have hE := Complex.exp_ne_zero (logDerivFwd W t (invMap W t z))
  have hcancel : ownMap W W' a φ t z - (W' (a t) : ℂ) = fwdMap W' (a t) (φ (invMap W t z)) := by
    simp only [ownMap]; ring
  rw [hcancel]
  push_cast
  field_simp
  ring

/-! ### The far box -/

omit h in
theorem continuousOn_deriv_driver (h : OwnData W A φ T a W') {b c : ℝ} (hJ : Icc b c ⊆ Icc 0 T) :
    ContinuousOn (fun s => deriv (ownExt W W' a φ s) (W s)) (Icc b c) := by
  have := (h.continuousOn_iterDeriv 1).mono hJ
  simpa only [Function.iterate_one] using this

omit h in
theorem continuousOn_ownExt_driver (h : OwnData W A φ T a W') {b c : ℝ} (hJ : Icc b c ⊆ Icc 0 T) :
    ContinuousOn (fun s => ownExt W W' a φ s (W s)) (Icc b c) := by
  have := (h.continuousOn_iterDeriv 0).mono hJ
  simpa only [Function.iterate_zero, id] using this

section FarBox

variable {b c y r : ℝ} (hJ : Icc b c ⊆ Icc 0 T)
  (hdisj : ∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * r)) ((fun z => fwdMap W t z + W t) '' A))
  (hWf : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) r, z - W t ≠ 0)
  (hF0 : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) r, ownExt W W' a φ t z - ownExt W W' a φ t (W t) ≠ 0)
include hJ hdisj hWf hF0

/-- `dFar` is jointly continuous on the far box. -/
theorem continuousOn_dFar_box :
    ContinuousOn (fun q : ℝ × ℂ => dFar (ownExt W W' a φ q.1) (W q.1) q.2) (Icc b c ×ˢ ball (y : ℂ) r) := by
  have hF := h.continuousOn_box hJ hdisj
  have hF' := continuousOn_deriv_of_holo (F := fun s => ownExt W W' a φ s)
    (fun s hs => (h.box_props hJ hdisj hs).1) hF
  have hd1 : ContinuousOn (fun q : ℝ × ℂ => deriv (ownExt W W' a φ q.1) (W q.1)) (Icc b c ×ˢ ball (y : ℂ) r) :=
    (h.continuousOn_deriv_driver hJ).comp continuousOn_fst fun q hq => hq.1
  have hF0c : ContinuousOn (fun q : ℝ × ℂ => ownExt W W' a φ q.1 (W q.1)) (Icc b c ×ˢ ball (y : ℂ) r) :=
    (h.continuousOn_ownExt_driver hJ).comp continuousOn_fst fun q hq => hq.1
  have hWc : ContinuousOn (fun q : ℝ × ℂ => ((W q.1 : ℝ) : ℂ)) (Icc b c ×ˢ ball (y : ℂ) r) :=
    (continuous_ofReal.comp (h.cont.comp continuous_fst)).continuousOn
  simp only [dFar]
  exact ((continuousOn_const.mul (hd1.pow 2)).div (hF.sub hF0c) fun q hq => hF0 q.1 hq.1 q.2 hq.2).sub
    ((continuousOn_const.mul hF').div (continuousOn_snd.sub hWc) fun q hq => hWf q.1 hq.1 q.2 hq.2)

/-- `dFar` is holomorphic on the far disc. -/
theorem differentiableOn_dFar_box {t : ℝ} (ht : t ∈ Icc b c) :
    DifferentiableOn ℂ (dFar (ownExt W W' a φ t) (W t)) (ball (y : ℂ) r) := by
  have hd := (h.box_props hJ hdisj ht).1
  have e : dFar (ownExt W W' a φ t) (W t) = fun z => 2 * deriv (ownExt W W' a φ t) (W t) ^ 2 /
      (ownExt W W' a φ t z - ownExt W W' a φ t (W t)) - 2 * deriv (ownExt W W' a φ t) z / (z - W t) := rfl
  rw [e]
  exact ((differentiableOn_const _).div (hd.sub (differentiableOn_const _)) fun z hz => hF0 t ht z hz).sub
    (((differentiableOn_const _).mul (hd.deriv isOpen_ball)).div (differentiableOn_id.sub (differentiableOn_const _))
      fun z hz => hWf t ht z hz)

omit hWf hF0 in
/-- (D1) on the upper half of the far disc. -/
theorem hasDerivWithinAt_far_upper {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r)
    (hzH : 0 < z.im) :
    HasDerivWithinAt (fun s => ownExt W W' a φ s z) (dFar (ownExt W W' a φ t) (W t) z) (Icc 0 T) t := by
  refine h.hasDerivWithinAt_ownExt_upper_far (hJ ht) hzH fun hE => Set.disjoint_left.1 (hdisj t ht) ?_ hE
  exact ball_subset_ball (by have := pos_of_mem_ball hz; linarith) hz

theorem continuousOn_dFar_time {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    ContinuousOn (fun s => dFar (ownExt W W' a φ s) (W s) z) (Icc b c) := by
  have hcl : Continuous fun s : ℝ => (s, z) := continuous_id.prodMk continuous_const
  have hc := (h.continuousOn_dFar_box hJ hdisj hWf hF0).comp hcl.continuousOn
    (fun s hs => (⟨hs, hz⟩ : (s, z) ∈ Icc b c ×ˢ ball (y : ℂ) r))
  simp only [Function.comp_def] at hc
  exact hc

/-- The time-integral identity on the upper half of the far disc. -/
theorem integral_identity_far_upper {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r)
    (hzH : 0 < z.im) :
    ownExt W W' a φ t z = ownExt W W' a φ b z + ∫ s in b..t, dFar (ownExt W W' a φ s) (W s) z := by
  have hsub : Icc b t ⊆ Icc b c := Icc_subset_Icc_right ht.2
  have hc : c ∈ Icc b c := ⟨ht.1.trans ht.2, le_rfl⟩
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    ((h.continuousOn_ownExt_time hJ hdisj hz).mono hsub) (fun x hx => ?_)
    (((h.continuousOn_dFar_time hJ hdisj hWf hF0 hz).mono hsub).intervalIntegrable_of_Icc ht.1)
  · rw [key]; ring
  · have hx' : x ∈ Icc b c := hsub (Ioo_subset_Icc_self hx)
    refine (h.hasDerivWithinAt_far_upper hJ hdisj hx' hz hzH).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT_of_mem ⟨(hJ hx').1, lt_of_lt_of_le hx.2 (ht.2.trans (hJ hc).2)⟩)

/-- **The time-integral identity on the whole far disc** (identity theorem). -/
theorem integral_identity_far {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    ownExt W W' a φ t z = ownExt W W' a φ b z + ∫ s in b..t, dFar (ownExt W W' a φ s) (W s) z := by
  have hb : b ∈ Icc b c := ⟨le_rfl, ht.1.trans ht.2⟩
  have hr : 0 < r := pos_of_mem_ball hz
  set Φ : ℂ → ℂ := fun w => ownExt W W' a φ t w - ownExt W W' a φ b w -
    ∫ s in b..t, dFar (ownExt W W' a φ s) (W s) w with hΦ
  have hsub : Icc b t ⊆ Icc b c := Icc_subset_Icc_right ht.2
  have hd' : ∀ s ∈ Icc b t, DifferentiableOn ℂ (dFar (ownExt W W' a φ s) (W s)) (ball (y : ℂ) r) :=
    fun s hs => h.differentiableOn_dFar_box hJ hdisj hWf hF0 (hsub hs)
  have hc' := (h.continuousOn_dFar_box hJ hdisj hWf hF0).mono (prod_mono hsub le_rfl)
  have hΦd : DifferentiableOn ℂ Φ (ball (y : ℂ) r) := by
    refine ((h.box_props hJ hdisj ht).1.sub (h.box_props hJ hdisj hb).1).sub fun w hw => ?_
    exact (hasDerivAt_integral_of_holo_Icc (F := fun s => dFar (ownExt W W' a φ s) (W s)) hd' hc' hw
      ⟨ht.1, le_rfl⟩).differentiableAt.differentiableWithinAt
  set z₀ : ℂ := (y : ℂ) + ((r / 2 : ℝ) : ℂ) * I with hz₀
  have hz₀B : z₀ ∈ ball (y : ℂ) r := by
    rw [mem_ball, dist_eq_norm, hz₀, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hz₀H : 0 < z₀.im := by simp [hz₀]; linarith
  have hev : Φ =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [(isOpen_ball.inter QuantumZipper.isOpen_H).mem_nhds ⟨hz₀B, hz₀H⟩] with w hw
    simp only [hΦ, Pi.zero_apply]
    rw [h.integral_identity_far_upper hJ hdisj hWf hF0 ht hw.1 hw.2]
    ring
  have h0 := (hΦd.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hz₀B hev hz
  simp only [hΦ, Pi.zero_apply] at h0
  linear_combination h0

/-- **(D1) at every point of the far disc, real points included**: `∂_t F_t(z) = dFar_t(z)` within `[b, c]`. -/
theorem hasDerivWithinAt_ownExt_far {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    HasDerivWithinAt (fun s => ownExt W W' a φ s z) (dFar (ownExt W W' a φ t) (W t) z) (Icc b c) t := by
  have h1 := (hasDerivWithinAt_integral_base (h.continuousOn_dFar_time hJ hdisj hWf hF0 hz) ht).const_add
    (ownExt W W' a φ b z)
  exact h1.congr (fun s hs => h.integral_identity_far hJ hdisj hWf hF0 hs hz)
    (h.integral_identity_far hJ hdisj hWf hF0 ht hz)

theorem continuousOn_deriv_dFar_box :
    ContinuousOn (fun q : ℝ × ℂ => deriv (dFar (ownExt W W' a φ q.1) (W q.1)) q.2)
      (Icc b c ×ˢ ball (y : ℂ) r) :=
  continuousOn_deriv_of_holo (F := fun s => dFar (ownExt W W' a φ s) (W s))
    (fun _ hs => h.differentiableOn_dFar_box hJ hdisj hWf hF0 hs) (h.continuousOn_dFar_box hJ hdisj hWf hF0)

/-- `F_s' = F_b' + ∫_b^s ∂_z dFar` on the far disc. -/
theorem deriv_ownExt_eq_far {s : ℝ} (hs : s ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    deriv (ownExt W W' a φ s) z =
      deriv (ownExt W W' a φ b) z + ∫ σ in b..s, deriv (dFar (ownExt W W' a φ σ) (W σ)) z := by
  have hb : b ∈ Icc b c := ⟨le_rfl, hs.1.trans hs.2⟩
  have hsub : Icc b s ⊆ Icc b c := Icc_subset_Icc_right hs.2
  have hd' : ∀ σ ∈ Icc b s, DifferentiableOn ℂ (dFar (ownExt W W' a φ σ) (W σ)) (ball (y : ℂ) r) :=
    fun σ hσ => h.differentiableOn_dFar_box hJ hdisj hWf hF0 (hsub hσ)
  have hc' := (h.continuousOn_dFar_box hJ hdisj hWf hF0).mono (prod_mono hsub le_rfl)
  have hI := hasDerivAt_integral_of_holo_Icc (F := fun σ => dFar (ownExt W W' a φ σ) (W σ)) hd' hc' hz
    ⟨hs.1, le_rfl⟩
  have hFb := ((h.box_props hJ hdisj hb).1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have heq : ownExt W W' a φ s =ᶠ[𝓝 z]
      fun w => ownExt W W' a φ b w + ∫ σ in b..s, dFar (ownExt W W' a φ σ) (W σ) w := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using h.integral_identity_far hJ hdisj hWf hF0 hs hw
  have hsum : HasDerivAt (fun w => ownExt W W' a φ b w + ∫ σ in b..s, dFar (ownExt W W' a φ σ) (W σ) w)
      (deriv (ownExt W W' a φ b) z + ∫ σ in b..s, deriv (dFar (ownExt W W' a φ σ) (W σ)) z) z := hFb.add hI
  rw [heq.deriv_eq, hsum.deriv]

/-- **The time derivative of `F_t'` on the far disc**: `∂_t F_t'(z) = ∂_z dFar_t(z)` within `[b, c]`. -/
theorem hasDerivWithinAt_deriv_ownExt_far {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    HasDerivWithinAt (fun s => deriv (ownExt W W' a φ s) z)
      (deriv (dFar (ownExt W W' a φ t) (W t)) z) (Icc b c) t := by
  have hcl : Continuous fun s : ℝ => (s, z) := continuous_id.prodMk continuous_const
  have hc := (h.continuousOn_deriv_dFar_box hJ hdisj hWf hF0).comp hcl.continuousOn
    (fun s hs => (⟨hs, hz⟩ : (s, z) ∈ Icc b c ×ˢ ball (y : ℂ) r))
  simp only [Function.comp_def] at hc
  have h1 := (hasDerivWithinAt_integral_base hc ht).const_add (deriv (ownExt W W' a φ b) z)
  exact h1.congr (fun s hs => h.deriv_ownExt_eq_far hJ hdisj hWf hF0 hs hz)
    (h.deriv_ownExt_eq_far hJ hdisj hWf hF0 ht hz)

/-- (D1), real form, on the far disc. -/
theorem hasDerivWithinAt_re_ownExt_far {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ} (hx : (x : ℂ) ∈ ball (y : ℂ) r) :
    HasDerivWithinAt (fun s => (ownExt W W' a φ s x).re) ((dFar (ownExt W W' a φ t) (W t) x).re) (Icc b c) t := by
  have := (Complex.reCLM.hasFDerivAt (x := ownExt W W' a φ t x)).comp_hasDerivWithinAt t
    (h.hasDerivWithinAt_ownExt_far hJ hdisj hWf hF0 ht hx)
  simpa [Function.comp_def] using this

/-- `∂_t Re F_t'(x) = Re ∂_z dFar_t(x)` on the far disc. -/
theorem hasDerivWithinAt_re_deriv_ownExt_far {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ}
    (hx : (x : ℂ) ∈ ball (y : ℂ) r) :
    HasDerivWithinAt (fun s => (deriv (ownExt W W' a φ s) x).re)
      ((deriv (dFar (ownExt W W' a φ t) (W t)) x).re) (Icc b c) t := by
  have := (Complex.reCLM.hasFDerivAt (x := deriv (ownExt W W' a φ t) x)).comp_hasDerivWithinAt t
    (h.hasDerivWithinAt_deriv_ownExt_far hJ hdisj hWf hF0 ht hx)
  simpa [Function.comp_def] using this

end FarBox

/-- **A far box around a real point.** If `B(v, ρ)` misses every `g_s(A)` for `s` near `t₀`, `v ≠ W_{t₀}` and
`F_{t₀}(v) ≠ F_{t₀}(W_{t₀})`, then on a neighbourhood `[max 0 (t₀ − η), min T (t₀ + η)]` of `t₀` and a disc
`B(v, r)` the far-box hypotheses hold. -/
theorem exists_farBox {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) T) {v ρ η₀ : ℝ} (hρ : 0 < ρ) (hη₀ : 0 < η₀)
    (hcl : ∀ s ∈ Icc (max 0 (t₀ - η₀)) (min T (t₀ + η₀)),
      Disjoint (ball (v : ℂ) ρ) ((fun z => fwdMap W s z + W s) '' A))
    (hvW : v ≠ W t₀) (hvF : ownExt W W' a φ t₀ v ≠ ownExt W W' a φ t₀ (W t₀)) :
    ∃ η > (0 : ℝ), ∃ r > (0 : ℝ),
      (∀ s ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)),
        Disjoint (ball (v : ℂ) (2 * r)) ((fun z => fwdMap W s z + W s) '' A)) ∧
      (∀ s ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)), ∀ z ∈ ball (v : ℂ) r, z - W s ≠ 0) ∧
      (∀ s ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)), ∀ z ∈ ball (v : ℂ) r,
        ownExt W W' a φ s z - ownExt W W' a φ s (W s) ≠ 0) := by
  set b₁ := max 0 (t₀ - η₀) with hb₁
  set c₁ := min T (t₀ + η₀) with hc₁
  have hJ₁ : Icc b₁ c₁ ⊆ Icc 0 T := fun s hs => (mem_box_of_abs_lt (T := T) hs).1
  have ht₀₁ : t₀ ∈ Icc b₁ c₁ := mem_box_self hη₀ ht₀
  set r₁ := ρ / 2 with hr₁
  have hr₁pos : 0 < r₁ := by positivity
  have hdisj₁ : ∀ s ∈ Icc b₁ c₁, Disjoint (ball (v : ℂ) (2 * r₁)) ((fun z => fwdMap W s z + W s) '' A) := by
    intro s hs; rw [show 2 * r₁ = ρ by ring]; exact hcl s hs
  have hF := h.continuousOn_box hJ₁ hdisj₁
  have hF0c : ContinuousOn (fun q : ℝ × ℂ => ownExt W W' a φ q.1 (W q.1)) (Icc b₁ c₁ ×ˢ ball (v : ℂ) r₁) :=
    (h.continuousOn_ownExt_driver hJ₁).comp continuousOn_fst fun q hq => hq.1
  have hWc : Continuous fun q : ℝ × ℂ => ((W q.1 : ℝ) : ℂ) := continuous_ofReal.comp (h.cont.comp continuous_fst)
  set g : ℝ × ℂ → ℂ := fun q => (q.2 - W q.1) * (ownExt W W' a φ q.1 q.2 - ownExt W W' a φ q.1 (W q.1)) with hg
  have hgc : ContinuousOn g (Icc b₁ c₁ ×ˢ ball (v : ℂ) r₁) :=
    (continuousOn_snd.sub hWc.continuousOn).mul (hF.sub hF0c)
  have hg0 : g (t₀, v) ≠ 0 := by
    refine mul_ne_zero ?_ (sub_ne_zero.2 hvF)
    rw [← ofReal_sub]; exact_mod_cast sub_ne_zero.2 hvW
  obtain ⟨ε, hε, hεg⟩ := Metric.continuousWithinAt_iff.1 (hgc (t₀, (v : ℂ)) ⟨ht₀₁, mem_ball_self hr₁pos⟩)
    ‖g (t₀, v)‖ (norm_pos_iff.2 hg0)
  set r := min (r₁ / 2) (ε / 2) with hr
  have hrpos : 0 < r := by positivity
  set η := min η₀ (ε / 2) with hη
  have hηpos : 0 < η := by positivity
  have hsub : ∀ s ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)), s ∈ Icc b₁ c₁ ∧ |s - t₀| ≤ η := fun s hs => by
    obtain ⟨h1, h2⟩ := mem_box_of_abs_lt (T := T) hs
    refine ⟨⟨max_le h1.1 ?_, le_min h1.2 ?_⟩, h2⟩
    · linarith [(abs_le.1 h2).1, min_le_left η₀ (ε / 2)]
    · linarith [(abs_le.1 h2).2, min_le_left η₀ (ε / 2)]
  have hgne : ∀ s ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)), ∀ z ∈ ball (v : ℂ) r, g (s, z) ≠ 0 := by
    intro s hs z hz
    have hz₁ : z ∈ ball (v : ℂ) r₁ := ball_subset_ball (by
      linarith [min_le_left (r₁ / 2) (ε / 2)]) hz
    have hd : dist (s, z) (t₀, (v : ℂ)) < ε := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq]
      exact ⟨lt_of_le_of_lt ((hsub s hs).2.trans (min_le_right _ _)) (by linarith),
        lt_of_lt_of_le (mem_ball.1 hz) ((min_le_right _ _).trans (by linarith))⟩
    have h1 := hεg ⟨(hsub s hs).1, hz₁⟩ hd
    intro h0
    rw [h0, dist_eq_norm, zero_sub, norm_neg] at h1
    exact lt_irrefl _ h1
  refine ⟨η, hηpos, r, hrpos, fun s hs => ?_, fun s hs z hz => left_ne_zero_of_mul (hgne s hs z hz),
    fun s hs z hz => right_ne_zero_of_mul (hgne s hs z hz)⟩
  refine Set.disjoint_of_subset_left (ball_subset_ball ?_) (hcl s (hsub s hs).1)
  linarith [min_le_left (r₁ / 2) (ε / 2)]

end OwnData

end InteractingSLE.ZhanGT4
