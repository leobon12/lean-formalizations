/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteDet

/-!
# Moving seed factors are continuous, including on the diagonal

Packet PROVE-ZHAN-GT4-A22. Moving clear discs give local common holomorphic
boxes. The existing parameter derivative and divided-difference theorems
then give continuity at every time, including the entrance time.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (fwdMap)

namespace OwnData

variable {W W' a : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ}
    (h : OwnData W A φ T a W')
include h

/-- Two continuous coordinates meeting at a clear point fit in one common
holomorphic time box near their meeting time. -/
theorem exists_holo_moving_box {U V : ℝ → ℝ} {r t : ℝ} (hr : 0 < r)
    (hU : ContinuousOn U (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (hclear : ∀ s ∈ Icc (0 : ℝ) T, Disjoint (ball (U s : ℂ) r)
      ((fun z => fwdMap W s z + W s) '' A))
    (ht : t ∈ Icc (0 : ℝ) T) (he : V t = U t) :
    ∃ b c : ℝ, Icc b c ⊆ Icc 0 T ∧ Icc b c ∈ 𝓝[Icc 0 T] t ∧ t ∈ Icc b c ∧
      (∀ s ∈ Icc b c, (U s : ℂ) ∈ ball (U t : ℂ) (r / 4) ∧
        (V s : ℂ) ∈ ball (U t : ℂ) (r / 4)) ∧
      (∀ s ∈ Icc b c, DifferentiableOn ℂ (ownExt W W' a φ s) (ball (U t : ℂ) (r / 4))) ∧
      ContinuousOn (fun p : ℝ × ℂ => ownExt W W' a φ p.1 p.2)
        (Icc b c ×ˢ ball (U t : ℂ) (r / 4)) := by
  have hr8 : 0 < r / 8 := by positivity
  have hUnear : {s : ℝ | dist (U s) (U t) < r / 8} ∈ 𝓝[Icc 0 T] t :=
    (hU t ht).preimage_mem_nhdsWithin (ball_mem_nhds _ hr8)
  have hVnear : {s : ℝ | dist (V s) (U t) < r / 8} ∈ 𝓝[Icc 0 T] t := by
    rw [← he]
    exact (hV t ht).preimage_mem_nhdsWithin (ball_mem_nhds _ hr8)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhdsWithin_iff.1 (inter_mem hUnear hVnear)
  let b := max 0 (t - η / 2)
  let c := min T (t + η / 2)
  have hJ : Icc b c ⊆ Icc 0 T := fun s hs => ⟨(le_max_left _ _).trans hs.1, hs.2.trans (min_le_left _ _)⟩
  have hnear : ∀ s ∈ Icc b c, dist (U s) (U t) < r / 8 ∧ dist (V s) (U t) < r / 8 := by
    intro s hs
    apply hηsub
    refine ⟨?_, hJ hs⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have hlow := (le_max_right (0 : ℝ) (t - η / 2)).trans hs.1
    have hhigh := hs.2.trans (min_le_right T (t + η / 2))
    constructor <;> linarith
  have hdisj : ∀ s ∈ Icc b c, Disjoint (ball (U t : ℂ) (r / 2))
      ((fun z => fwdMap W s z + W s) '' A) := by
    intro s hs
    refine (hclear s (hJ hs)).mono_left ?_
    intro z hz
    have hu := (hnear s hs).1
    rw [mem_ball] at hz ⊢
    have heq : dist (U t : ℂ) (U s : ℂ) = dist (U s) (U t) := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        Real.dist_eq, abs_sub_comm]
    have hh := dist_triangle z (U t : ℂ) (U s : ℂ)
    rw [heq] at hh
    linarith
  refine ⟨b, c, hJ, box_mem_nhdsWithin_Icc (half_pos hη), ?_, ?_, ?_, ?_⟩
  · exact ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩
  · intro s hs
    have hdist : ∀ x : ℝ, dist (x : ℂ) (U t : ℂ) = dist x (U t) := fun x => by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]
    constructor <;> rw [mem_ball, hdist] <;> linarith [(hnear s hs).1, (hnear s hs).2]
  · intro s hs
    simpa only [show r / 2 / 2 = r / 4 by ring] using (h.ownExt_props (hJ hs) (hdisj s hs)).1
  · simpa only [show r / 2 / 2 = r / 4 by ring] using h.continuousOn_ownExt hJ hdisj

/-- Every derivative of the own map is continuous along a continuous clear
real coordinate, also at the entrance time. -/
theorem continuousOn_iterDeriv_moving {V : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hV : ContinuousOn V (Icc 0 T))
    (hclear : ∀ s ∈ Icc (0 : ℝ) T, Disjoint (ball (V s : ℂ) r)
      ((fun z => fwdMap W s z + W s) '' A)) (k : ℕ) :
    ContinuousOn (fun t => deriv^[k] (ownExt W W' a φ t) (V t)) (Icc 0 T) := by
  intro t ht
  obtain ⟨b, c, hJ, hJn, htJ, hm, hd, hc⟩ := h.exists_holo_moving_box hr hV hV hclear ht rfl
  have hdc : ∀ k : ℕ,
      (∀ s ∈ Icc b c, DifferentiableOn ℂ (deriv^[k] (ownExt W W' a φ s)) (ball (V t : ℂ) (r / 4))) ∧
      ContinuousOn (fun p : ℝ × ℂ => deriv^[k] (ownExt W W' a φ p.1) p.2)
        (Icc b c ×ˢ ball (V t : ℂ) (r / 4)) := by
    intro j
    induction j with
    | zero => exact ⟨hd, hc⟩
    | succ j ih =>
        refine ⟨?_, ?_⟩
        · intro s hs
          simpa only [Function.iterate_succ_apply'] using (ih.1 s hs).deriv isOpen_ball
        · simpa only [Function.iterate_succ_apply'] using continuousOn_deriv_of_holo ih.1 ih.2
  have hcomp := (hdc k).2.comp
    (continuousOn_id.prodMk (continuous_ofReal.comp_continuousOn (hV.mono hJ)))
    (fun s hs => ⟨hs, (hm s hs).1⟩)
  exact (hcomp t htJ).mono_of_mem_nhdsWithin hJn

/-- Moving real divided differences are continuous through every meeting
of the coordinates; away from a meeting use the quotient formula. -/
theorem continuousOn_dslope_moving {U V : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hU : ContinuousOn U (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (hclearU : ∀ s ∈ Icc (0 : ℝ) T, Disjoint (ball (U s : ℂ) r)
      ((fun z => fwdMap W s z + W s) '' A))
    (hclearV : ∀ s ∈ Icc (0 : ℝ) T, Disjoint (ball (V s : ℂ) r)
      ((fun z => fwdMap W s z + W s) '' A)) :
    ContinuousOn (fun t => dslope (fun x : ℝ => (ownExt W W' a φ t x).re) (U t) (V t))
      (Icc 0 T) := by
  have hFU := continuous_re.comp_continuousOn (h.continuousOn_iterDeriv_moving hr hU hclearU 0)
  have hFV := continuous_re.comp_continuousOn (h.continuousOn_iterDeriv_moving hr hV hclearV 0)
  intro t ht
  by_cases he : V t = U t
  · obtain ⟨b, c, hJ, hJn, htJ, hm, hd, hc⟩ := h.exists_holo_moving_box hr hU hV hclearU ht he
    exact ((continuousOn_dslope_real_family hd hc (hU.mono hJ) (hV.mono hJ)
      (fun s hs => (hm s hs).1) (fun s hs => (hm s hs).2)) t htJ).mono_of_mem_nhdsWithin hJn
  · have hden := (hV.sub hU) t ht
    have hn := hden.eventually_ne (sub_ne_zero.2 he)
    apply ((hFV.sub hFU) t ht |>.div hden (sub_ne_zero.2 he)).congr_of_eventuallyEq
    · filter_upwards [hn] with s hs
      rw [dslope_of_ne _ (sub_ne_zero.1 hs), slope_def_field]
      rfl
    · rw [dslope_of_ne _ he, slope_def_field]
      rfl

end OwnData

namespace SeedData

/-- Clear-interval geometry and the remote scales give continuity of the
normalized density and all band gaps, with no own-gap assumption at zero. -/
theorem continuousOn_normEll_gapVal_of_remoteScale {n : ℕ} (s : SeedData n)
    {A : Set ℂ} {T r L₀ L : ℝ} {I : ℝ → Set ℝ}
    (h : OwnData s.W A s.φ T s.a s.W')
    {v₀ : ℝ → ℂ} (hv₀ : QuantumZipper.IsForwardSol s.W' s.ζ₀ (s.a T) v₀)
    (hr : 0 < r) (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t))
    (hWI : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ I t)
    (hVI : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ I t)
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (ball (x : ℂ) r)
      ((fun z => fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t,
      deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hremote : ∀ t ∈ Icc (0 : ℝ) T, s.RemoteScale t L)
    (hVc : ∀ m, ContinuousOn (s.V m) (Icc 0 T))
    (hV₀c : ContinuousOn s.V₀ (Icc 0 T)) (hG₀c : ContinuousOn s.G₀ (Icc 0 T)) :
    ContinuousOn s.normEll (Icc 0 T) ∧ ∀ i, ContinuousOn (s.gapVal i) (Icc 0 T) := by
  have nz : ∀ {u l : ℝ}, InScale l u → u ≠ 0 := by
    intro u l hu he
    have hh := hu.1
    rw [he, abs_zero] at hh
    exact (not_le_of_gt (Real.exp_pos _)) hh
  have hGne : ∀ t ∈ Icc (0 : ℝ) T, s.G₀ t ≠ 0 := by
    intro t ht
    exact (div_ne_zero_iff.1 (nz (hremote t ht).A21)).2
  have hA0 : ContinuousOn (s.A 0) (Icc 0 T) := h.continuousOn_frzA 0
  have hA1 : ContinuousOn (s.A 1) (Icc 0 T) := h.continuousOn_frzA 1
  have hA20 : ContinuousOn s.A20 (Icc 0 T) :=
    fun t ht => (h.hasDerivWithinAt_frzImg hv₀ ht).continuousWithinAt
  have hA21num : ContinuousOn (frzImgD s.W' s.a s.ζ₀) (Icc 0 T) :=
    fun t ht => (h.hasDerivWithinAt_frzImgD hv₀ ht).continuousWithinAt
  have hA21 : ContinuousOn s.A21 (Icc 0 T) := hA21num.div hG₀c hGne
  have hL : ContinuousOn s.L (Icc 0 T) :=
    fun t ht => (h.hasDerivWithinAt_frzLogF ht).continuousWithinAt
  have hB : ∀ k m, ContinuousOn (fun t => s.F k t (s.V m t)) (Icc 0 T) := fun k m =>
    continuous_re.comp_continuousOn (h.continuousOn_iterDeriv_moving hr (hVc m)
      (fun t ht => hclear t ht _ (hVI t ht m)) k)
  have hdiff : ∀ t ∈ Icc (0 : ℝ) T, DifferentiableOn ℝ (s.F 0 t) (I t) := by
    intro t ht x hx
    have hd := (h.ownExt_props ht (hclear t ht x hx)).1
    have hdx := hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    exact hdx.hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt
  have hF1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, s.F 1 t x = deriv (s.F 0 t) x := by
    intro t ht x hx
    have hd := (h.ownExt_props ht (hclear t ht x hx)).1
    exact (s.deriv_F_zero
      (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity))))).symm
  have hds : ∀ m k, ContinuousOn (fun t => dslope (s.F 0 t) (s.V k t) (s.V m t)) (Icc 0 T) :=
    fun m k => h.continuousOn_dslope_moving hr (hVc k) (hVc m)
      (fun t ht => hclear t ht _ (hVI t ht k)) (fun t ht => hclear t ht _ (hVI t ht m))
  have hdW : ∀ m, ContinuousOn (fun t => dslope (s.F 0 t) (s.V m t) (s.W t)) (Icc 0 T) :=
    fun m => h.continuousOn_dslope_moving hr (hVc m) h.cont.continuousOn
      (fun t ht => hclear t ht _ (hVI t ht m)) (fun t ht => hclear t ht _ (hWI t ht))
  refine ⟨s.continuousOn_normEll_of_factors hA21 (fun t ht => nz (hremote t ht).A21) hL
    (hB 1) ?_ ?_ ?_ (fun m k _ => hds m k) ?_ hA1 ?_ ?_ ?_ hdW ?_,
    s.continuousOn_gapVal hA0 hA20 hA21 (hB 0) (hB 1) h.cont.continuousOn hV₀c hVc⟩
  · intro m t ht
    rw [B1, hF1 t ht _ (hVI t ht m)]
    exact ((Real.exp_pos _).trans_le (hb t ht _ (hVI t ht m)).1).ne'
  · intro m
    exact (hA20.sub (hB 0 m)).div (hV₀c.sub (hVc m))
      (fun t ht => (div_ne_zero_iff.1 (nz ((hremote t ht).mark m))).2)
  · intro m t ht
    exact nz ((hremote t ht).mark m)
  · intro m k _ t ht
    exact nz (inScale_dslope_of_deriv_bounds (hI t ht) (hdiff t ht) (hb t ht)
      (hVI t ht k) (hVI t ht m))
  · intro t ht
    exact (h.frzA_one_pos ht).ne'
  · exact (hA0.sub hA20).div (h.cont.continuousOn.sub hV₀c)
      (fun t ht => (div_ne_zero_iff.1 (nz (hremote t ht).driver)).2)
  · intro t ht
    exact nz (hremote t ht).driver
  · intro m t ht
    exact nz (inScale_dslope_of_deriv_bounds (hI t ht) (hdiff t ht) (hb t ht)
      (hVI t ht m) (hWI t ht))

end SeedData

end InteractingSLE.ZhanGT4
