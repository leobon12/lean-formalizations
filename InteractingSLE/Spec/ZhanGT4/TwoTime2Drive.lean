/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoTime2Ext

/-!
# (D1) up to the driver and (D2)

Packet PROVE-ZHAN-GT4-A4. Source: Astra, *Follow-up proofs and dependency audit*, Part A.1.1
(`source/external/AstraIG1/ig1_followup_proofs.txt` L255–L266, ruling R38): (D1)
`∂_t h_t(z) = 2A₁²/(h_t(z) − A₀) − 2h_t'(z)/(z − W_t)`; "the apparent singularity at `W_j` is removable. Taylor expansion
gives (D2) `∂_t h_t(W_t) = −3A₂`, `∂_t h_t'(W_t)/A₁ = A₂²/(2A₁²) − (4/3)A₃/A₁`."

On a box `[b, c] × B(y, r)` (`[b, c] ⊆ [0, T]`, every `g_t(A)` missing `B(y, 2r)`, every `W_t ∈ B(y, r)`), the reflected
own-time map `F_t = ownExt … t` is holomorphic and jointly continuous (`TwoTime2Ext.lean`). With `q_t = dslope F_t W_t`
and the removable quotient `D̂_t = dHat F_t W_t` (`TwoTime2Dslope.lean`), where `q ≠ 0`:

* `D̂` and `∂_z D̂` are jointly continuous (divided differences in integral form, `dslope_eq_integral`);
* `∂_t F_t(z) = D̂_t(z)` at **every** point of the disc, the driver included (`hasDerivWithinAt_ownExt_box`): on the
  upper half it is (D1); the identity `F_t − F_b = ∫_b^t D̂_s ds` extends from the upper half-disc to the disc by the
  identity theorem;
* `∂_t F_t'(z) = ∂_z D̂_t(z)` (`hasDerivWithinAt_deriv_ownExt_box`), and at `z = W_t` the values are (D2).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-- **Joint continuity of divided differences** of a jointly continuous holomorphic family at a moving base point. -/
theorem continuousOn_dslope_family {G : ℝ → ℂ → ℂ} {Z : ℝ → ℂ} {b c : ℝ} {y : ℂ} {r : ℝ}
    (hG : ∀ t ∈ Icc b c, DifferentiableOn ℂ (G t) (ball y r))
    (hGc : ContinuousOn (fun q : ℝ × ℂ => G q.1 q.2) (Icc b c ×ˢ ball y r))
    (hZ : ContinuousOn Z (Icc b c)) (hZm : ∀ t ∈ Icc b c, Z t ∈ ball y r) :
    ContinuousOn (fun q : ℝ × ℂ => dslope (G q.1) (Z q.1) q.2) (Icc b c ×ˢ ball y r) := by
  have hdc := continuousOn_deriv_of_holo hG hGc
  have hseg : ∀ t ∈ Icc b c, ∀ z ∈ ball y r, ∀ θ ∈ Icc (0 : ℝ) 1, Z t + (θ : ℂ) * (z - Z t) ∈ ball y r :=
    fun t ht z hz θ hθ => by
      have := (convex_ball y r) (hZm t ht) hz (sub_nonneg.2 hθ.2) hθ.1 (by ring)
      convert this using 1
      simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]; ring
  have hg : ContinuousOn (fun p : (ℝ × ℂ) × ℝ => deriv (G p.1.1) (Z p.1.1 + (p.2 : ℂ) * (p.1.2 - Z p.1.1)))
      ((Icc b c ×ˢ ball y r) ×ˢ Icc 0 1) := by
    have hmap : ContinuousOn (fun p : (ℝ × ℂ) × ℝ => (p.1.1, Z p.1.1 + (p.2 : ℂ) * (p.1.2 - Z p.1.1)))
        ((Icc b c ×ˢ ball y r) ×ˢ Icc 0 1) := by
      have hZc : ContinuousOn (fun p : (ℝ × ℂ) × ℝ => Z p.1.1) ((Icc b c ×ˢ ball y r) ×ˢ Icc 0 1) :=
        hZ.comp (continuous_fst.comp continuous_fst).continuousOn fun p hp => hp.1.1
      refine (continuous_fst.comp continuous_fst).continuousOn.prodMk (hZc.add ?_)
      exact (continuous_ofReal.comp continuous_snd).continuousOn.mul
        ((continuous_snd.comp continuous_fst).continuousOn.sub hZc)
    exact hdc.comp hmap fun p hp => ⟨hp.1.1, hseg _ hp.1.1 _ hp.1.2 _ hp.2⟩
  refine (continuousOn_integral_unit (g := fun q θ => deriv (G q.1) (Z q.1 + (θ : ℂ) * (q.2 - Z q.1))) hg).congr
    fun q hq => ?_
  exact dslope_eq_integral isOpen_ball (convex_ball y r) (hG q.1 hq.1) (hZm q.1 hq.1) hq.2

/-- The fundamental theorem of calculus within `[b, c]`, integrating from `b`. -/
theorem hasDerivWithinAt_integral_base {f : ℝ → ℂ} {b c t : ℝ} (hf : ContinuousOn f (Icc b c))
    (ht : t ∈ Icc b c) : HasDerivWithinAt (fun s => ∫ r in b..s, f r) (f t) (Icc b c) t := by
  have : Fact (t ∈ Icc b c) := ⟨ht⟩
  have hint : IntervalIntegrable f MeasureTheory.volume b t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hf.mono (Icc_subset_Icc_right ht.2)
  exact intervalIntegral.integral_hasDerivWithinAt_right hint
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
  {b c y r : ℝ} (hJ : Icc b c ⊆ Icc 0 T)
  (hdisj : ∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * r)) ((fun z => fwdMap W t z + W t) '' A))
  (hWm : ∀ t ∈ Icc b c, (W t : ℂ) ∈ ball (y : ℂ) r)
include h hJ hdisj hWm

omit hWm in
theorem box_props {t : ℝ} (ht : t ∈ Icc b c) :
    DifferentiableOn ℂ (ownExt W W' a φ t) (ball (y : ℂ) r) ∧
      EqOn (ownExt W W' a φ t) (ownMap W W' a φ t) (ball (y : ℂ) r ∩ H) := by
  obtain ⟨h1, h2, -⟩ := h.ownExt_props (hJ ht) (hdisj t ht)
  rw [show 2 * r / 2 = r by ring] at h1 h2
  exact ⟨h1, h2⟩

omit hWm in
theorem continuousOn_box :
    ContinuousOn (fun q : ℝ × ℂ => ownExt W W' a φ q.1 q.2) (Icc b c ×ˢ ball (y : ℂ) r) := by
  have := h.continuousOn_ownExt hJ hdisj
  rwa [show 2 * r / 2 = r by ring] at this

theorem continuousOn_q_box :
    ContinuousOn (fun q : ℝ × ℂ => dslope (ownExt W W' a φ q.1) (W q.1) q.2) (Icc b c ×ˢ ball (y : ℂ) r) :=
  continuousOn_dslope_family (G := fun t => ownExt W W' a φ t) (Z := fun t => (W t : ℂ))
    (fun _ ht => (h.box_props hJ hdisj ht).1) (h.continuousOn_box hJ hdisj)
    (continuous_ofReal.comp h.cont).continuousOn hWm

theorem differentiableOn_q_box {t : ℝ} (ht : t ∈ Icc b c) :
    DifferentiableOn ℂ (dslope (ownExt W W' a φ t) (W t)) (ball (y : ℂ) r) :=
  differentiableOn_dslope_of_isOpen isOpen_ball (hWm t ht) (h.box_props hJ hdisj ht).1

theorem continuousOn_dHat_box (hq0 : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) r, dslope (ownExt W W' a φ t) (W t) z ≠ 0) :
    ContinuousOn (fun q : ℝ × ℂ => dHat (ownExt W W' a φ q.1) (W q.1) q.2) (Icc b c ×ˢ ball (y : ℂ) r) := by
  have hq := h.continuousOn_q_box hJ hdisj hWm
  have hqd := fun t ht => h.differentiableOn_q_box hJ hdisj hWm (t := t) ht
  have hq' := continuousOn_deriv_of_holo (F := fun t => dslope (ownExt W W' a φ t) (W t)) hqd hq
  have hu := continuousOn_dslope_family (G := fun t => dslope (ownExt W W' a φ t) (W t))
    (Z := fun t => (W t : ℂ)) hqd hq (continuous_ofReal.comp h.cont).continuousOn hWm
  have hqa : ContinuousOn (fun q : ℝ × ℂ => dslope (ownExt W W' a φ q.1) (W q.1) (W q.1))
      (Icc b c ×ˢ ball (y : ℂ) r) := by
    have hcl : Continuous fun q : ℝ × ℂ => (q.1, (W q.1 : ℂ)) :=
      continuous_fst.prodMk (continuous_ofReal.comp (h.cont.comp continuous_fst))
    exact hq.comp hcl.continuousOn fun q hq => ⟨hq.1, hWm q.1 hq.1⟩
  refine (((continuousOn_const (c := (2 : ℂ))).mul ((hu.neg.mul (hq.add hqa)).sub (hq.mul hq'))).div hq
    fun q hq' => hq0 q.1 hq'.1 q.2 hq'.2).congr fun q _ => ?_
  simp only [dHat, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]

theorem differentiableOn_dHat_box (hq0 : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) r, dslope (ownExt W W' a φ t) (W t) z ≠ 0)
    {t : ℝ} (ht : t ∈ Icc b c) :
    DifferentiableOn ℂ (dHat (ownExt W W' a φ t) (W t)) (ball (y : ℂ) r) :=
  differentiableOn_dHat isOpen_ball (hWm t ht) (h.box_props hJ hdisj ht).1 (hq0 t ht)

/-- (D1) on the upper half of the box disc, in the removable form `D̂`. -/
theorem hasDerivWithinAt_box_upper (hq0 : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) r, dslope (ownExt W W' a φ t) (W t) z ≠ 0)
    {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) (hzH : 0 < z.im) :
    HasDerivWithinAt (fun s => ownExt W W' a φ s z) (dHat (ownExt W W' a φ t) (W t) z) (Icc 0 T) t := by
  have hr2 : 2 * r / 2 = r := by ring
  have h1 := h.hasDerivWithinAt_ownExt_upper (hJ ht) (hdisj t ht) (by rw [hr2]; exact hWm t ht)
    (by rw [hr2]; exact hz) hzH
  refine h1.congr_deriv ?_
  have hzW : z ≠ W t := fun h' => by
    have : z.im = 0 := by rw [h']; simp
    linarith
  rw [dHat_eq isOpen_ball (hWm t ht) (h.box_props hJ hdisj ht).1 hz hzW (hq0 t ht z hz)]

variable (hq0 : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) r, dslope (ownExt W W' a φ t) (W t) z ≠ 0)
include hq0

theorem continuousOn_dHat_time {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    ContinuousOn (fun s => dHat (ownExt W W' a φ s) (W s) z) (Icc b c) := by
  have hcl : Continuous fun s : ℝ => (s, z) := continuous_id.prodMk continuous_const
  have hc := (h.continuousOn_dHat_box hJ hdisj hWm hq0).comp hcl.continuousOn
    (fun s hs => (⟨hs, hz⟩ : (s, z) ∈ Icc b c ×ˢ ball (y : ℂ) r))
  simp only [Function.comp_def] at hc
  exact hc

omit hq0 hWm in
theorem continuousOn_ownExt_time {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    ContinuousOn (fun s => ownExt W W' a φ s z) (Icc b c) := by
  have hcl : Continuous fun s : ℝ => (s, z) := continuous_id.prodMk continuous_const
  have hc := (h.continuousOn_box hJ hdisj).comp hcl.continuousOn
    (fun s hs => (⟨hs, hz⟩ : (s, z) ∈ Icc b c ×ˢ ball (y : ℂ) r))
  simp only [Function.comp_def] at hc
  exact hc

/-- The time-integral identity on the upper half of the box disc. -/
theorem integral_identity_upper {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) (hzH : 0 < z.im) :
    ownExt W W' a φ t z =
      ownExt W W' a φ b z + ∫ s in b..t, dHat (ownExt W W' a φ s) (W s) z := by
  have hsub : Icc b t ⊆ Icc b c := Icc_subset_Icc_right ht.2
  have hc : c ∈ Icc b c := ⟨ht.1.trans ht.2, le_rfl⟩
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    ((h.continuousOn_ownExt_time hJ hdisj hz).mono hsub) (fun x hx => ?_)
    (((h.continuousOn_dHat_time hJ hdisj hWm hq0 hz).mono hsub).intervalIntegrable_of_Icc ht.1)
  · rw [key]; ring
  · have hx' : x ∈ Icc b c := hsub (Ioo_subset_Icc_self hx)
    refine (h.hasDerivWithinAt_box_upper hJ hdisj hWm hq0 hx' hz hzH).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT_of_mem ⟨(hJ hx').1, lt_of_lt_of_le hx.2 (ht.2.trans (hJ hc).2)⟩)

/-- **The time-integral identity on the whole box disc** (identity theorem). -/
theorem integral_identity {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    ownExt W W' a φ t z =
      ownExt W W' a φ b z + ∫ s in b..t, dHat (ownExt W W' a φ s) (W s) z := by
  have hb : b ∈ Icc b c := ⟨le_rfl, ht.1.trans ht.2⟩
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (hWm b hb)
  set Φ : ℂ → ℂ := fun w => ownExt W W' a φ t w - ownExt W W' a φ b w -
    ∫ s in b..t, dHat (ownExt W W' a φ s) (W s) w with hΦ
  have hsub : Icc b t ⊆ Icc b c := Icc_subset_Icc_right ht.2
  have hd' : ∀ s ∈ Icc b t, DifferentiableOn ℂ (dHat (ownExt W W' a φ s) (W s)) (ball (y : ℂ) r) :=
    fun s hs => h.differentiableOn_dHat_box hJ hdisj hWm hq0 (hsub hs)
  have hc' := (h.continuousOn_dHat_box hJ hdisj hWm hq0).mono (prod_mono hsub le_rfl)
  have hΦd : DifferentiableOn ℂ Φ (ball (y : ℂ) r) := by
    refine ((h.box_props hJ hdisj ht).1.sub (h.box_props hJ hdisj hb).1).sub fun w hw => ?_
    exact (hasDerivAt_integral_of_holo_Icc (F := fun s => dHat (ownExt W W' a φ s) (W s)) hd' hc' hw
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
    rw [h.integral_identity_upper hJ hdisj hWm hq0 ht hw.1 hw.2]
    ring
  have h0 := (hΦd.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hz₀B hev hz
  simp only [hΦ, Pi.zero_apply] at h0
  linear_combination h0

/-- **(D1) at every point of the box disc, the driver included**: `∂_t F_t(z) = D̂_t(z)` within `[b, c]`. -/
theorem hasDerivWithinAt_ownExt_box {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    HasDerivWithinAt (fun s => ownExt W W' a φ s z) (dHat (ownExt W W' a φ t) (W t) z) (Icc b c) t := by
  have h1 := (hasDerivWithinAt_integral_base (h.continuousOn_dHat_time hJ hdisj hWm hq0 hz) ht).const_add
    (ownExt W W' a φ b z)
  exact h1.congr (fun s hs => h.integral_identity hJ hdisj hWm hq0 hs hz)
    (h.integral_identity hJ hdisj hWm hq0 ht hz)

theorem continuousOn_deriv_dHat_box :
    ContinuousOn (fun q : ℝ × ℂ => deriv (dHat (ownExt W W' a φ q.1) (W q.1)) q.2) (Icc b c ×ˢ ball (y : ℂ) r) :=
  continuousOn_deriv_of_holo (F := fun s => dHat (ownExt W W' a φ s) (W s))
    (fun _ hs => h.differentiableOn_dHat_box hJ hdisj hWm hq0 hs) (h.continuousOn_dHat_box hJ hdisj hWm hq0)

/-- `F_s' = F_b' + ∫_b^s ∂_z D̂` on the box disc. -/
theorem deriv_ownExt_eq {s : ℝ} (hs : s ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    deriv (ownExt W W' a φ s) z =
      deriv (ownExt W W' a φ b) z + ∫ σ in b..s, deriv (dHat (ownExt W W' a φ σ) (W σ)) z := by
  have hb : b ∈ Icc b c := ⟨le_rfl, hs.1.trans hs.2⟩
  have hsub : Icc b s ⊆ Icc b c := Icc_subset_Icc_right hs.2
  have hd' : ∀ σ ∈ Icc b s, DifferentiableOn ℂ (dHat (ownExt W W' a φ σ) (W σ)) (ball (y : ℂ) r) :=
    fun σ hσ => h.differentiableOn_dHat_box hJ hdisj hWm hq0 (hsub hσ)
  have hc' := (h.continuousOn_dHat_box hJ hdisj hWm hq0).mono (prod_mono hsub le_rfl)
  have hI := hasDerivAt_integral_of_holo_Icc (F := fun σ => dHat (ownExt W W' a φ σ) (W σ)) hd' hc' hz
    ⟨hs.1, le_rfl⟩
  have hFb := ((h.box_props hJ hdisj hb).1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have heq : ownExt W W' a φ s =ᶠ[𝓝 z]
      fun w => ownExt W W' a φ b w + ∫ σ in b..s, dHat (ownExt W W' a φ σ) (W σ) w := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using h.integral_identity hJ hdisj hWm hq0 hs hw
  have hsum : HasDerivAt (fun w => ownExt W W' a φ b w + ∫ σ in b..s, dHat (ownExt W W' a φ σ) (W σ) w)
      (deriv (ownExt W W' a φ b) z + ∫ σ in b..s, deriv (dHat (ownExt W W' a φ σ) (W σ)) z) z := hFb.add hI
  rw [heq.deriv_eq, hsum.deriv]

/-- **The time derivative of `F_t'`**: `∂_t F_t'(z) = ∂_z D̂_t(z)` within `[b, c]`, on the whole box disc. -/
theorem hasDerivWithinAt_deriv_ownExt_box {t : ℝ} (ht : t ∈ Icc b c) {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    HasDerivWithinAt (fun s => deriv (ownExt W W' a φ s) z)
      (deriv (dHat (ownExt W W' a φ t) (W t)) z) (Icc b c) t := by
  have hcl : Continuous fun s : ℝ => (s, z) := continuous_id.prodMk continuous_const
  have hc := (h.continuousOn_deriv_dHat_box hJ hdisj hWm hq0).comp hcl.continuousOn
    (fun s hs => (⟨hs, hz⟩ : (s, z) ∈ Icc b c ×ˢ ball (y : ℂ) r))
  simp only [Function.comp_def] at hc
  have h1 := (hasDerivWithinAt_integral_base hc ht).const_add (deriv (ownExt W W' a φ b) z)
  exact h1.congr (fun s hs => h.deriv_ownExt_eq hJ hdisj hWm hq0 hs hz) (h.deriv_ownExt_eq hJ hdisj hWm hq0 ht hz)

omit h hJ hdisj in
theorem deriv_ownExt_drive_ne_zero {t : ℝ} (ht : t ∈ Icc b c) : deriv (ownExt W W' a φ t) (W t) ≠ 0 := by
  have := hq0 t ht (W t) (hWm t ht)
  rwa [dslope_same] at this

/-- **(D2), first identity**: `D̂_t(W_t) = −3 F_t''(W_t)`, i.e. `∂_t h_t(W_t) = −3A₂`. -/
theorem dHat_drive {t : ℝ} (ht : t ∈ Icc b c) :
    dHat (ownExt W W' a φ t) (W t) (W t) = -3 * deriv (deriv (ownExt W W' a φ t)) (W t) :=
  dHat_self isOpen_ball (hWm t ht) (h.box_props hJ hdisj ht).1 (deriv_ownExt_drive_ne_zero hWm hq0 ht)

/-- **(D2), second identity**: `∂_z D̂_t(W_t) = F''²/(2F') − (4/3)F'''` at `W_t`, i.e.
`∂_t h_t'(W_t)/A₁ = A₂²/(2A₁²) − (4/3)A₃/A₁`. -/
theorem deriv_dHat_drive {t : ℝ} (ht : t ∈ Icc b c) :
    deriv (dHat (ownExt W W' a φ t) (W t)) (W t) =
      deriv (deriv (ownExt W W' a φ t)) (W t) ^ 2 / (2 * deriv (ownExt W W' a φ t) (W t)) -
        4 / 3 * deriv (deriv (deriv (ownExt W W' a φ t))) (W t) :=
  (hasDerivAt_dHat_self isOpen_ball (hWm t ht) (h.box_props hJ hdisj ht).1
    (deriv_ownExt_drive_ne_zero hWm hq0 ht)).deriv

end OwnData

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

omit h in
theorem mem_box_of_abs_lt {t₀ η t : ℝ} (ht : t ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η))) :
    t ∈ Icc (0 : ℝ) T ∧ |t - t₀| ≤ η := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨⟨le_trans (le_max_left _ _) h1, le_trans h2 (min_le_left _ _)⟩, abs_le.2 ⟨?_, ?_⟩⟩
  · linarith [le_trans (le_max_right _ _) h1]
  · linarith [le_trans h2 (min_le_right _ _)]

omit h in
theorem box_mem_nhds {t₀ η : ℝ} (hη : 0 < η) :
    Icc (max 0 (t₀ - η)) (min T (t₀ + η)) ∈ 𝓝[Icc 0 T] t₀ :=
  mem_nhdsWithin.2 ⟨Ioo (t₀ - η) (t₀ + η), isOpen_Ioo, ⟨by linarith, by linarith⟩,
    fun x hx => ⟨max_le hx.2.1 hx.1.1.le, le_min hx.2.2 hx.1.2.le⟩⟩

omit h in
theorem mem_box_self {t₀ η : ℝ} (hη : 0 < η) (ht₀ : t₀ ∈ Icc (0 : ℝ) T) :
    t₀ ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)) :=
  ⟨max_le ht₀.1 (by linarith), le_min ht₀.2 (by linarith)⟩

/-- **A box around every time.** For `t₀ ∈ [0, T]` there are `η, r > 0` such that on
`[b, c] = [max 0 (t₀ − η), min T (t₀ + η)]` (a neighbourhood of `t₀` in `[0, T]`) every `g_t(A)` misses
`B(W_{t₀}, 2r)`, every `W_t ∈ B(W_{t₀}, r)`, and `q_t = dslope F_t W_t` does not vanish on `B(W_{t₀}, r)`. -/
theorem exists_box {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) T) :
    ∃ η > (0 : ℝ), ∃ r > (0 : ℝ),
      (∀ t ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)),
        Disjoint (ball (W t₀ : ℂ) (2 * r)) ((fun z => fwdMap W t z + W t) '' A)) ∧
      (∀ t ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)), (W t : ℂ) ∈ ball (W t₀ : ℂ) r) ∧
      (∀ t ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)), ∀ z ∈ ball (W t₀ : ℂ) r,
        dslope (ownExt W W' a φ t) (W t) z ≠ 0) := by
  obtain ⟨ρ, hρ, hcl⟩ := h.exists_clearance
  set r₁ := ρ / 4 with hr₁
  have hr₁pos : 0 < r₁ := by positivity
  -- continuity of the driver at `t₀`
  have hWc : ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ t, |t - t₀| ≤ η → ‖(W t : ℂ) - W t₀‖ < ε := by
    intro ε hε
    obtain ⟨η, hη, hηW⟩ := Metric.continuous_iff.1 h.cont t₀ ε hε
    refine ⟨η / 2, by positivity, fun t ht => ?_⟩
    have := hηW t (by rw [Real.dist_eq]; linarith)
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rwa [Real.dist_eq] at this
  obtain ⟨η₁, hη₁, hη₁W⟩ := hWc (r₁ / 2) (by positivity)
  set b₁ := max 0 (t₀ - η₁)
  set c₁ := min T (t₀ + η₁)
  have hbox₁ : ∀ t ∈ Icc b₁ c₁, t ∈ Icc (0 : ℝ) T ∧ ‖(W t : ℂ) - W t₀‖ < r₁ / 2 := fun t ht => by
    obtain ⟨h1, h2⟩ := mem_box_of_abs_lt (T := T) ht
    exact ⟨h1, hη₁W t h2⟩
  have hJ₁ : Icc b₁ c₁ ⊆ Icc 0 T := fun t ht => (hbox₁ t ht).1
  have hdisj₁ : ∀ t ∈ Icc b₁ c₁, Disjoint (ball (W t₀ : ℂ) (2 * r₁)) ((fun z => fwdMap W t z + W t) '' A) := by
    intro t ht
    refine Set.disjoint_of_subset_left (fun z hz => ?_) (hcl t (hbox₁ t ht).1)
    rw [mem_ball, dist_eq_norm] at hz ⊢
    have := (hbox₁ t ht).2
    calc ‖z - W t‖ = ‖(z - W t₀) - ((W t : ℂ) - W t₀)‖ := by ring_nf
      _ ≤ ‖z - W t₀‖ + ‖(W t : ℂ) - W t₀‖ := norm_sub_le _ _
      _ < ρ := by linarith
  have hWm₁ : ∀ t ∈ Icc b₁ c₁, (W t : ℂ) ∈ ball (W t₀ : ℂ) r₁ := fun t ht => by
    rw [mem_ball, dist_eq_norm]; linarith [(hbox₁ t ht).2]
  have ht₀₁ : t₀ ∈ Icc b₁ c₁ := mem_box_self hη₁ ht₀
  -- `q(t₀, W_{t₀}) = A₁(t₀) ≠ 0`
  have hq₀ : dslope (ownExt W W' a φ t₀) (W t₀) (W t₀) ≠ 0 := by
    rw [dslope_same]
    obtain ⟨R, hR⟩ := (h.isHPHull_E ht₀).exists_isMapOut
    obtain ⟨hFd, -, -, -, -, hFR⟩ := h.ownExt_props ht₀ (hdisj₁ t₀ ht₀₁)
    rw [show 2 * r₁ / 2 = r₁ by ring] at hFd hFR
    obtain ⟨-, -, -, hrate⟩ := h.rate t₀ ht₀ R hR
    obtain ⟨hpos, -, -⟩ := hrate r₁ hr₁pos _ hFd (hFR R hR)
    intro h0; rw [h0, zero_re] at hpos; exact lt_irrefl _ hpos
  -- continuity of `q` at `(t₀, W_{t₀})`
  have hqc := h.continuousOn_q_box hJ₁ hdisj₁ hWm₁
  obtain ⟨ε, hε, hεq⟩ := Metric.continuousWithinAt_iff.1 (hqc (t₀, (W t₀ : ℂ)) ⟨ht₀₁, mem_ball_self hr₁pos⟩)
    ‖dslope (ownExt W W' a φ t₀) (W t₀) (W t₀)‖ (norm_pos_iff.2 hq₀)
  set r := min r₁ (ε / 2) with hr
  have hrpos : 0 < r := by positivity
  obtain ⟨η₂, hη₂, hη₂W⟩ := hWc r hrpos
  set η := min η₁ (min η₂ (ε / 2)) with hη
  have hηpos : 0 < η := by positivity
  have hsub : ∀ t ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)), t ∈ Icc b₁ c₁ ∧ |t - t₀| ≤ η := fun t ht => by
    obtain ⟨h1, h2⟩ := mem_box_of_abs_lt (T := T) ht
    refine ⟨⟨max_le h1.1 ?_, le_min h1.2 ?_⟩, h2⟩
    · linarith [(abs_le.1 h2).1, min_le_left η₁ (min η₂ (ε / 2))]
    · linarith [(abs_le.1 h2).2, min_le_left η₁ (min η₂ (ε / 2))]
  refine ⟨η, hηpos, r, hrpos, fun t ht => ?_, fun t ht => ?_, fun t ht z hz => ?_⟩
  · exact Set.disjoint_of_subset_left (ball_subset_ball (by linarith [min_le_left r₁ (ε / 2)]))
      (hdisj₁ t (hsub t ht).1)
  · rw [mem_ball, dist_eq_norm]
    exact hη₂W t ((hsub t ht).2.trans ((min_le_right _ _).trans (min_le_left _ _)))
  · have hz₁ : z ∈ ball (W t₀ : ℂ) r₁ := ball_subset_ball (min_le_left _ _) hz
    have hd : dist (t, z) (t₀, (W t₀ : ℂ)) < ε := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq]
      refine ⟨lt_of_le_of_lt ((hsub t ht).2.trans ((min_le_right _ _).trans (min_le_right _ _))) (by linarith),
        lt_of_lt_of_le (mem_ball.1 hz) ((min_le_right _ _).trans (by linarith))⟩
    have h1 := hεq ⟨(hsub t ht).1, hz₁⟩ hd
    intro h0
    simp only at h1
    rw [h0, dist_eq_norm, zero_sub, norm_neg] at h1
    exact lt_irrefl _ h1

end OwnData

end InteractingSLE.ZhanGT4
