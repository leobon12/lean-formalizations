/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux57Square
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import QuantumZipper.Proofs.Complex.TopoEilenberg

/-!
# A connected set in the closed upper half-plane joining two real points traps the real points in between

Packet PROVE-LEMMA76B (the planar separation behind Aux. lemmas 69–70, specification pp. 273–275: "the bounded Jordan
component is above [the lower closing arc]"). Let `K ⊆ ℍ̄` be compact and preconnected, containing the real points
`u < v`, and let `y ∈ (u, v)` be a real point off `K`. Then `y` is trapped by `K`: a ball about `y` misses the
unbounded domain `ℍ \ fill K`.

## Proof (Eilenberg's criterion)

With `p = y + iδ`, `p' = y − iδ` (`2δ` below the distance from `y` to `K`) and the real segment `S = [u, v]`, the
compact set `Λ = K ∪ S` separates `p` from `p'`: otherwise `R(z) = (z − p)/(z − p')` has a continuous logarithm `L` on
`Λ` (`QuantumZipper.CA.Topo.hasLogOn_of_not_separates`). On `K` the explicit logarithm
`L₀ = log(−i(z − p)) − log(−i(z − p'))` is continuous (`K` misses the vertical segment `[y, p]`), and on `S` so is
`M = log(i(z − p)) − log(−i(z − p')) + iπ`; both differ from `L` by constants in `2πiℤ`. At a real point `x`,
`L₀(x) − M(x) = log(−w) − log w − iπ` with `w = i(x − p) = δ + i(x − y)`, which is `0` for `x < y` and `−2πi` for
`x > y` (`arg (−w) = arg w ± π`). Comparing at `u` and `v` is a contradiction. The point `p'` lies in the unbounded
component of `Λᶜ` (the open lower half-plane), so the component of `p` is bounded, and it contains the half-disc
`B(y, 2δ) ∩ ℍ`, whose points are therefore in bounded components of `ℍ \ K`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open scoped Real

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

/-! ### The explicit logarithms -/

section Logs

/-- `log(−w) − log w = −iπ` for `Im w > 0`. -/
theorem log_neg_sub_log_of_im_pos {w : ℂ} (hw : 0 < w.im) : log (-w) - log w = -(π * I) := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl _ hw
  rw [log, log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hw]
  push_cast
  ring

/-- `log(−w) − log w = iπ` for `Im w < 0`. -/
theorem log_neg_sub_log_of_im_neg {w : ℂ} (hw : w.im < 0) : log (-w) - log w = π * I := by
  rw [log, log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hw]
  push_cast
  ring

theorem mem_slitPlane_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ∈ slitPlane := Or.inl hw

end Logs

/-! ### The trapping lemma -/

/-- **A connected compact set in the closed upper half-plane joining two real points traps every real point in
between that it misses.** -/
theorem isTrappedAt_of_isPreconnected {K : Set ℂ} (hK : IsCompact K) (hKc : IsPreconnected K)
    (hKim : ∀ w ∈ K, 0 ≤ w.im) {u v y : ℝ} (hu : (u : ℂ) ∈ K) (hv : (v : ℂ) ∈ K) (huy : u < y) (hyv : y < v)
    (hy : (y : ℂ) ∉ K) : HalfPlaneSep.IsTrappedAt K y := by
  -- the clearance of `y`
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl (y : ℂ) hy
  set δ := r / 2 with hδdef
  have hδ : 0 < δ := half_pos hr
  set p : ℂ := (y : ℂ) + (δ : ℂ) * I with hp
  set p' : ℂ := (y : ℂ) - (δ : ℂ) * I with hp'
  set S : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc u v with hS
  set Λ := K ∪ S with hΛ
  have hScpt : IsCompact S := isCompact_Icc.image continuous_ofReal
  have hScon : IsPreconnected S := isPreconnected_Icc.image _ continuous_ofReal.continuousOn
  have hΛc : IsCompact Λ := hK.union hScpt
  have hSim : ∀ w ∈ S, w.im = 0 := by rintro _ ⟨t, -, rfl⟩; simp
  have hKfar : ∀ z ∈ K, r ≤ dist z y := fun z hz => not_lt.1 fun h => hrK (mem_ball.2 h) hz
  have hpball : p ∈ ball (y : ℂ) r := by
    rw [mem_ball, hp, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_eq_abs, abs_of_pos hδ]
    linarith
  have hpim : p.im = δ := by simp [hp]
  have hp'im : p'.im = -δ := by simp [hp']
  -- `Λ` separates `p` from `p'`
  have hsep : p' ∉ connectedComponentIn Λᶜ p := by
    intro hmem
    obtain ⟨L, hLc, hL⟩ := QuantumZipper.CA.Topo.hasLogOn_of_not_separates hΛc hmem
    -- the explicit logarithm on `K`
    set L₀ : ℂ → ℂ := fun z => log (-I * (z - p)) - log (-I * (z - p')) with hL₀
    have hK₁ : ∀ z ∈ K, -I * (z - p) ∈ slitPlane := by
      intro z hz
      rw [mem_slitPlane_iff]
      by_contra hcon
      push Not at hcon
      obtain ⟨hre, him⟩ := hcon
      have h1 : (-I * (z - p)).re = z.im - δ := by simp [hp]
      have h2 : (-I * (z - p)).im = -(z.re - y) := by simp [hp]
      rw [h1] at hre
      rw [h2, neg_eq_zero, sub_eq_zero] at him
      have hzim := hKim z hz
      have hd := hKfar z hz
      rw [dist_eq_norm] at hd
      have hzy : z - (y : ℂ) = ((z.im : ℝ) : ℂ) * I := Complex.ext (by simp [him]) (by simp)
      rw [hzy, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hzim] at hd
      linarith
    have hK₂ : ∀ z ∈ K, -I * (z - p') ∈ slitPlane := by
      intro z hz
      refine mem_slitPlane_of_re_pos ?_
      have : (-I * (z - p')).re = z.im + δ := by simp [hp']
      rw [this]
      linarith [hKim z hz]
    have hL₀c : ContinuousOn L₀ K := by
      refine ContinuousOn.sub ?_ ?_
      · exact ContinuousOn.clog ((continuous_const.mul (continuous_id.sub continuous_const)).continuousOn) hK₁
      · exact ContinuousOn.clog ((continuous_const.mul (continuous_id.sub continuous_const)).continuousOn) hK₂
    have hpK : ∀ z ∈ K, z - p' ≠ 0 := fun z hz h => by
      have := congrArg Complex.im h
      rw [sub_im, hp'im, zero_im] at this
      linarith [hKim z hz]
    have hexpK : ∀ z ∈ K, exp (L z) = exp (L₀ z) := by
      intro z hz
      rw [hL z (Or.inl hz), hL₀, exp_sub, exp_log (slitPlane_ne_zero (hK₁ z hz)),
        exp_log (slitPlane_ne_zero (hK₂ z hz))]
      have hI : (-I : ℂ) ≠ 0 := neg_ne_zero.2 I_ne_zero
      rw [mul_div_mul_left _ _ hI]
    obtain ⟨n, hn⟩ := exists_int_eqOn_of_exp_eq hKc (hLc.mono subset_union_left) hL₀c hexpK
    -- the explicit logarithm on `S`
    set M : ℂ → ℂ := fun z => log (I * (z - p)) - log (-I * (z - p')) + π * I with hM
    have hS₁ : ∀ z ∈ S, I * (z - p) ∈ slitPlane := by
      intro z hz
      refine mem_slitPlane_of_re_pos ?_
      have : (I * (z - p)).re = δ - z.im := by simp [hp]
      rw [this, hSim z hz]
      linarith
    have hS₂ : ∀ z ∈ S, -I * (z - p') ∈ slitPlane := by
      intro z hz
      refine mem_slitPlane_of_re_pos ?_
      have : (-I * (z - p')).re = z.im + δ := by simp [hp']
      rw [this, hSim z hz]
      linarith
    have hMc : ContinuousOn M S := by
      refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) continuousOn_const
      · exact ContinuousOn.clog ((continuous_const.mul (continuous_id.sub continuous_const)).continuousOn) hS₁
      · exact ContinuousOn.clog ((continuous_const.mul (continuous_id.sub continuous_const)).continuousOn) hS₂
    have hexpS : ∀ z ∈ S, exp (L z) = exp (M z) := by
      intro z hz
      rw [hL z (Or.inr hz), hM, exp_add, exp_sub, exp_log (slitPlane_ne_zero (hS₁ z hz)),
        exp_log (slitPlane_ne_zero (hS₂ z hz)), exp_pi_mul_I]
      have hzp' : z - p' ≠ 0 := fun h => by
        have := congrArg Complex.im h
        rw [sub_im, hp'im, zero_im, hSim z hz] at this
        linarith
      field_simp
    obtain ⟨m, hm⟩ := exists_int_eqOn_of_exp_eq hScon (hLc.mono subset_union_right) hMc hexpS
    -- comparison at the two endpoints
    have huS : (u : ℂ) ∈ S := ⟨u, ⟨le_rfl, (huy.trans hyv).le⟩, rfl⟩
    have hvS : (v : ℂ) ∈ S := ⟨v, ⟨(huy.trans hyv).le, le_rfl⟩, rfl⟩
    have hdiff : ∀ x : ℝ, L₀ x - M x = log (-(I * ((x : ℂ) - p))) - log (I * ((x : ℂ) - p)) - π * I := by
      intro x
      simp only [hL₀, hM]
      rw [show -I * ((x : ℂ) - p) = -(I * ((x : ℂ) - p)) by ring]
      ring
    have him : ∀ x : ℝ, (I * ((x : ℂ) - p)).im = x - y := by intro x; simp [hp]
    have hu' : L₀ u - M u = 0 := by
      rw [hdiff, log_neg_sub_log_of_im_neg (by rw [him]; linarith)]
      ring
    have hv' : L₀ v - M v = -(2 * π * I) := by
      rw [hdiff, log_neg_sub_log_of_im_pos (by rw [him]; linarith)]
      ring
    have e₁ := hn u hu
    have e₂ := hm u huS
    have e₃ := hn v hv
    have e₄ := hm v hvS
    have key : (L₀ v - M v) - (L₀ u - M u) = 0 := by linear_combination e₄ - e₃ - e₂ + e₁
    rw [hu', hv'] at key
    have hpi : (2 * π * I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    exact hpi (by linear_combination -key)
  -- the component of `p` is bounded
  obtain ⟨R, hR, hΛR⟩ := hΛc.isBounded.subset_ball_lt 0 0
  have hfar : {w : ℂ | R < ‖w‖} ⊆ connectedComponentIn Λᶜ p' := by
    have hlow : {w : ℂ | w.im < 0} ⊆ Λᶜ := by
      intro w hw hwΛ
      rcases hwΛ with h | h
      · exact absurd (hKim w h) (not_le.2 hw)
      · exact absurd (hSim w h) (ne_of_lt hw)
    have hp'low : p' ∈ {w : ℂ | w.im < 0} := by
      show p'.im < 0
      rw [hp'im]
      linarith
    have hlowc : {w : ℂ | w.im < 0} ⊆ connectedComponentIn Λᶜ p' :=
      (convex_halfSpace_lt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected.subset_connectedComponentIn
        hp'low hlow
    have hout : {w : ℂ | R < ‖w‖} ⊆ Λᶜ := fun w hw hwΛ => by
      have := mem_ball_zero_iff.1 (hΛR hwΛ)
      exact lt_irrefl _ (this.trans hw)
    have hm : (-(((R + 1 : ℝ) : ℂ) * I)) ∈ {w : ℂ | R < ‖w‖} ∩ {w : ℂ | w.im < 0} := by
      refine ⟨?_, ?_⟩
      · show R < ‖-(((R + 1 : ℝ) : ℂ) * I)‖
        rw [norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      · show (-(((R + 1 : ℝ) : ℂ) * I)).im < 0
        simp
        linarith
    have h1 := (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R).subset_connectedComponentIn hm.1 hout
    rw [← connectedComponentIn_eq (hlowc hm.2)] at h1
    exact h1
  have hp'Λ : p' ∈ Λᶜ := by
    intro h
    rcases h with h | h
    · have := hKim p' h
      rw [hp'im] at this
      linarith
    · have := hSim p' h
      rw [hp'im] at this
      linarith
  have hbdd : Bornology.IsBounded (connectedComponentIn Λᶜ p) := by
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun w hw => ?_
    rw [mem_closedBall_zero_iff]
    by_contra hwR
    have hw' := hfar (show R < ‖w‖ from not_le.1 hwR)
    apply hsep
    rw [connectedComponentIn_eq hw, ← connectedComponentIn_eq hw']
    exact mem_connectedComponentIn hp'Λ
  -- the half-disc is in the component of `p`
  have hdisc : ball (y : ℂ) r ∩ H ⊆ Λᶜ := by
    rintro w ⟨hwb, hwH⟩ hwΛ
    rcases hwΛ with h | h
    · exact hrK hwb h
    · exact (ne_of_gt (show (0 : ℝ) < w.im from hwH)) (hSim w h)
  have hpH : p ∈ H := by
    show 0 < p.im
    rw [hpim]
    exact hδ
  have hdiscc : ball (y : ℂ) r ∩ H ⊆ connectedComponentIn Λᶜ p :=
    ((convex_ball _ _).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).isPreconnected
      |>.subset_connectedComponentIn ⟨hpball, hpH⟩ hdisc
  refine ⟨r, hr, Set.disjoint_left.2 fun z hzb hz => ?_⟩
  obtain ⟨hzK, hzu⟩ := (HalfPlaneSep.mem_H_diff_fillH_of_isClosed hK.isClosed).1 hz
  apply hzu
  have hHK : H \ K ⊆ Λᶜ := fun w hw hwΛ => by
    rcases hwΛ with h | h
    · exact hw.2 h
    · exact (ne_of_gt (show (0 : ℝ) < w.im from hw.1)) (hSim w h)
  refine hbdd.subset ((connectedComponentIn_mono z hHK).trans ?_)
  rw [connectedComponentIn_eq (hdiscc ⟨hzb, hzK.1⟩)]

end Sec7

end InteractingSLE
