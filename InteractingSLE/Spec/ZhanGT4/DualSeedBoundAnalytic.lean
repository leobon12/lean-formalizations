/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBound

/-!
# Derivative and divided-difference inputs for the seeded bound

Packet PROVE-ZHAN-GT4-A22. The derivative comparison at a clear real point
extends the driver-only upper bound of A6. Joint continuity of divided
differences is reused from A4, including coincident seed coordinates.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H fwdMap)

namespace OwnData

/-- At every clear real point the derivative of the reflected mapping-out
function is real, strictly positive, and at most one. -/
theorem deriv_ownExt_real {W W' a : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T t x r : ℝ}
    (h : OwnData W A φ T a W') (ht : t ∈ Icc (0 : ℝ) T) (hr : 0 < r)
    (hdisj : Disjoint (ball (x : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) :
    (deriv (ownExt W W' a φ t) x).im = 0 ∧
      0 < (deriv (ownExt W W' a φ t) x).re ∧
      (deriv (ownExt W W' a φ t) x).re ≤ 1 := by
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
  obtain ⟨G, hG, -⟩ := ConformalImageFull.IsMapOut.exists_isRefl
    (h.isHPHull_E ht) hR hr hdisj
  obtain ⟨hd, -, -, hreal, -, hRe⟩ := h.ownExt_props ht hdisj
  have hr2 : 0 < r / 2 := by positivity
  have hEq := ConformalImageFull.eqOn_ball_of_eqOn_upper hr2 hd hG.diff
    (fun z hz => (hRe R hR hz).trans (hG.eqOn hz).symm)
  have hderiv : deriv (ownExt W W' a φ t) x = deriv G x := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (x := (x : ℂ)) hr2)] with z hz
    exact hEq hz
  have hnot : ∀ z ∈ ball (x : ℂ) (r / 2) ∩ H,
      z ∈ H \ ((fun z => fwdMap W t z + W t) '' A) := by
    intro z hz
    exact ⟨hz.2, fun hzE => Set.disjoint_left.1 hdisj
      (ball_subset_ball (by linarith) hz.1) hzE⟩
  have hup : ∀ z ∈ ball (x : ℂ) (r / 2) ∩ H, 0 < (G z).im := by
    intro z hz
    rw [hG.eqOn hz]
    exact hR.1.2.mapsTo (hnot z hz)
  obtain ⟨hpos, heq⟩ := hG.deriv_pos hr hup
  have hxb : (x : ℂ) ∈ ball (x : ℂ) (r / 2) := mem_ball_self hr2
  refine ⟨?_, ?_, ?_⟩
  · rw [hderiv, heq, Complex.ofReal_im]
  · rw [hderiv]; exact hpos
  · have hu := re_deriv_le_of_im_le (G₁ := ownExt W W' a φ t) (G₂ := id)
      hr2 (hd.differentiableAt (isOpen_ball.mem_nhds hxb)) differentiableAt_id
      (hreal _ hxb (by simp)) (by simp) (fun ε hε => ?_)
    · simpa only [deriv_id, one_re] using hu
    · have hz : (x : ℂ) + (ε : ℂ) * I ∈ ball (x : ℂ) (r / 2) ∩ H :=
        ConformalImageFull.mem_ball_inter_H hε.1 hε.2
      rw [hRe R hR hz]
      exact hR.im_le (h.isHPHull_E ht) (hnot _ hz)

end OwnData

/-- Real restriction commutes with a divided difference, also on its diagonal. -/
theorem dslope_restrict_re {G : ℂ → ℂ} {u v : ℝ}
    (hG : DifferentiableAt ℂ G u) :
    dslope (fun x : ℝ => (G x).re) u v = (dslope G (u : ℂ) (v : ℂ)).re := by
  by_cases hvu : v = u
  · subst v
    rw [dslope_same, dslope_same, hG.hasDerivAt.real_of_complex.deriv]
  · have hne : (v : ℂ) ≠ (u : ℂ) := fun he => hvu (Complex.ofReal_injective he)
    rw [dslope_of_ne _ hvu, dslope_of_ne _ hne, slope_def_field, slope_def_field]
    rw [← Complex.ofReal_sub, Complex.div_ofReal_re, Complex.sub_re]

/-- Divided differences along two moving real coordinates are continuous for
a jointly continuous holomorphic family. This includes their meeting times. -/
theorem continuousOn_dslope_real_family {G : ℝ → ℂ → ℂ}
    {U V : ℝ → ℝ} {b c : ℝ} {y : ℂ} {r : ℝ}
    (hG : ∀ t ∈ Icc b c, DifferentiableOn ℂ (G t) (ball y r))
    (hGc : ContinuousOn (fun q : ℝ × ℂ => G q.1 q.2) (Icc b c ×ˢ ball y r))
    (hU : ContinuousOn U (Icc b c)) (hV : ContinuousOn V (Icc b c))
    (hUm : ∀ t ∈ Icc b c, (U t : ℂ) ∈ ball y r)
    (hVm : ∀ t ∈ Icc b c, (V t : ℂ) ∈ ball y r) :
    ContinuousOn (fun t => dslope (fun x : ℝ => (G t x).re) (U t) (V t)) (Icc b c) := by
  have hUc := continuous_ofReal.comp_continuousOn hU
  have hVc := continuous_ofReal.comp_continuousOn hV
  have hd := continuousOn_dslope_family hG hGc hUc hUm
  have hc := continuous_re.comp_continuousOn
    (hd.comp (continuousOn_id.prodMk hVc) (fun t ht => ⟨ht, hVm t ht⟩))
  apply hc.congr
  intro t ht
  exact dslope_restrict_re
    ((hG t ht).differentiableAt (isOpen_ball.mem_nhds (hUm t ht)))

/-- Positive derivative bounds control the normalized seed factors even when
their two coordinates coincide. -/
theorem inScale_dslope_of_deriv_bounds {f : ℝ → ℝ} {I : Set ℝ} {L u v : ℝ}
    (hI : Convex ℝ I) (hd : DifferentiableOn ℝ f I)
    (hb : ∀ x ∈ I, deriv f x ∈ Icc (Real.exp (-L)) (Real.exp L))
    (hu : u ∈ I) (hv : v ∈ I) : InScale L (dslope f u v) := by
  have hs := dslope_mem_Icc_of_deriv_mem_Icc hI hd hb hu hv
  have hpos := (Real.exp_pos (-L)).trans_le hs.1
  exact ⟨by simpa only [abs_of_pos hpos] using hs.1,
    by simpa only [abs_of_pos hpos] using hs.2⟩

namespace SeedData

/-- The deterministic bound for the seed factors from an interval derivative
estimate. Only the separated other-source factors remain as individual scale
assumptions. -/
theorem abs_normEll_le_of_deriv_bounds {n : ℕ} (d : SeedData n)
    {t L : ℝ} {I : Set ℝ} (hL : 0 ≤ L) (hI : Convex ℝ I)
    (hd : DifferentiableOn ℝ (d.F 0 t) I)
    (hb : ∀ x ∈ I, deriv (d.F 0 t) x ∈ Icc (Real.exp (-L)) (Real.exp L))
    (hF1 : ∀ x ∈ I, d.F 1 t x = deriv (d.F 0 t) x)
    (hW : d.W t ∈ I) (hV : ∀ m, d.V m t ∈ I)
    (h21 : InScale L (d.A21 t)) (hlogF : |d.L t| ≤ L)
    (h2m : ∀ m, InScale L ((d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t)))
    (h0 : InScale L ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t))) :
    |d.normEll t| ≤ coefTot d.κ d.r * L := by
  have h1 : ∀ x ∈ I, InScale L (d.F 1 t x) := by
    intro x hx
    rw [hF1 x hx]
    have hb' := hb x hx
    have hpos := (Real.exp_pos (-L)).trans_le hb'.1
    exact ⟨by simpa only [abs_of_pos hpos] using hb'.1,
      by simpa only [abs_of_pos hpos] using hb'.2⟩
  exact d.abs_normEll_le_of_inScale hL h21 hlogF (fun m => h1 _ (hV m)) h2m
    (fun m k _ => inScale_dslope_of_deriv_bounds hI hd hb (hV k) (hV m))
    (h1 _ hW) h0 (fun m => inScale_dslope_of_deriv_bounds hI hd hb (hV m) hW)

end SeedData

end InteractingSLE.ZhanGT4
