/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.D9Clear

/-!
# (D9), second part: bounds on the reflected own-time map near the driver

Packet PROVE-ZHAN-GT4-A6. Source: Astra, *Follow-up proofs*, Part A.1.3 (`ig1_followup_proofs.txt` L320–L333):
"Applying the normal-family and reflection argument to `h_j` on that neighborhood gives positive lower and finite upper
bounds for `h_j'`, and finite bounds for its next derivatives."

Given a clearance `r` of the frozen image hull `E_t = g_t(A)` from the driver (`exists_le_norm_fwdMap_uniform`), the
reflected own-time map `F_t = ownExt … t` (the Schwarz reflection of `h_t`, the mapping-out function of `E_t`) satisfies,
with constants depending only on `r`:

* `A_{1,1} = F_t'(W_t)` is real with `0 < A_{1,1} ≤ 1` (`OwnData.deriv_ownExt_driver_le_one`); the upper bound is the
  height comparison `Im h_t(z) ≤ Im z` differentiated at the real point `W_t` (`re_deriv_le_of_im_le`);
* `|F_t'| ≤ 96` on `B(W_t, r/2)`, `|F_t''| ≤ 384/r` on `B(W_t, r/4)`, `|F_t'''| ≤ 3072/r²` on `B(W_t, r/8)`,
  `|F_t''''| ≤ 49152/r³` on `B(W_t, r/16)` (`OwnData.norm_deriv_ownExt_le`, …, from the `96`-Lipschitz bound and
  Cauchy's estimate `norm_deriv_le_of_norm_le_ball`).

The lower bound on `A_{1,1}` needs the other time (D3) and is proved separately.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdHull)

/-! ### Comparison of derivatives at a real point -/

/-- **Height comparison gives derivative comparison at a real point.** If `G₁, G₂` are complex differentiable at a
real point `x`, real there, and `Im G₁ ≤ Im G₂` on a vertical segment above `x`, then `Re G₁'(x) ≤ Re G₂'(x)`. -/
theorem re_deriv_le_of_im_le {G₁ G₂ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (h₁ : DifferentiableAt ℂ G₁ x) (h₂ : DifferentiableAt ℂ G₂ x)
    (h₁x : (G₁ x).im = 0) (h₂x : (G₂ x).im = 0)
    (hle : ∀ ε ∈ Ioo 0 r, (G₁ (x + ε * I)).im ≤ (G₂ (x + ε * I)).im) :
    (deriv G₁ x).re ≤ (deriv G₂ x).re := by
  have hp : HasDerivAt (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * I) I 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).const_add (x : ℂ)
    simpa using this
  have hp0 : (x : ℂ) + ((0 : ℝ) : ℂ) * I = x := by simp
  have hcomp : ∀ G : ℂ → ℂ, DifferentiableAt ℂ G x →
      HasDerivAt (fun ε : ℝ => (G ((x : ℂ) + (ε : ℂ) * I)).im) (deriv G x).re 0 := by
    intro G hG
    have h1 : HasDerivAt (G ∘ fun ε : ℝ => (x : ℂ) + (ε : ℂ) * I) (deriv G x * I) 0 := by
      have hG' : HasDerivAt G (deriv G x) ((x : ℂ) + ((0 : ℝ) : ℂ) * I) := by
        rw [hp0]; exact hG.hasDerivAt
      exact hG'.comp (0 : ℝ) hp
    have h2 := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h2
  have hφ := (hcomp G₂ h₂).sub (hcomp G₁ h₁)
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hφ).mono_left
    (nhdsWithin_mono (0 : ℝ) (fun ε (hε : ε ∈ Ioi (0 : ℝ)) => ne_of_gt hε))
  have hge : 0 ≤ (deriv G₂ x).re - (deriv G₁ x).re := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
    rw [slope_def_field]
    have h0 : (G₂ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im - (G₁ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im = 0 := by
      rw [hp0, h₁x, h₂x, sub_zero]
    simp only [Pi.sub_apply]
    rw [h0, sub_zero, sub_zero]
    exact div_nonneg (sub_nonneg.2 (hle ε hε)) hε.1.le
  linarith

/-! ### Cauchy's estimate on a disc -/

/-- **Cauchy's estimate**: a function holomorphic and bounded by `C` on `B(c, ρ)` has derivative bounded by `2C/ρ` on
`B(c, ρ/2)`. -/
theorem norm_deriv_le_of_norm_le_ball {f : ℂ → ℂ} {c : ℂ} {ρ C : ℝ}
    (hf : DifferentiableOn ℂ f (ball c ρ)) (hb : ∀ z ∈ ball c ρ, ‖f z‖ ≤ C) {z : ℂ}
    (hz : z ∈ ball c (ρ / 2)) : ‖deriv f z‖ ≤ 2 * C / ρ := by
  have hρ : 0 < ρ := by have := pos_of_mem_ball hz; linarith
  have hsub : closedBall z (ρ / 2) ⊆ ball c ρ := by
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball] at hz ⊢
    linarith [dist_triangle w z c]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < ρ / 2)
    (hf.diffContOnCl_ball hsub) (fun w hw => hb w (hsub (sphere_subset_closedBall hw)))
  calc ‖deriv f z‖ ≤ C / (ρ / 2) := h
    _ = 2 * C / ρ := by field_simp

/-- Iterated form: a holomorphic function on `B(c, ρ)` whose derivative is bounded by `C` there has second derivative
bounded by `2C/ρ` on `B(c, ρ/2)`. -/
theorem norm_deriv_deriv_le_of_norm_le_ball {f : ℂ → ℂ} {c : ℂ} {ρ C : ℝ}
    (hf : DifferentiableOn ℂ f (ball c ρ)) (hb : ∀ z ∈ ball c ρ, ‖deriv f z‖ ≤ C) {z : ℂ}
    (hz : z ∈ ball c (ρ / 2)) : ‖deriv (deriv f) z‖ ≤ 2 * C / ρ :=
  norm_deriv_le_of_norm_le_ball (hf.deriv isOpen_ball) hb hz

/-! ### The reflected own-time map near the driver -/

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

omit h in
/-- A clearance of `A`'s image from the driver is a disc around the driver missing `E_t = g_t(A)`. -/
theorem disjoint_ball_of_le_norm {r : ℝ} {t : ℝ} (hcl : ∀ z ∈ A, r ≤ ‖fwdMap W t z‖) :
    Disjoint (ball (W t : ℂ) r) ((fun z => fwdMap W t z + W t) '' A) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨z, hz, rfl⟩
  have h1 := hcl z hz
  rw [mem_ball, dist_eq_norm, add_sub_cancel_right] at hw
  linarith

/-- `|F_t'| ≤ 96` on `B(y, r/2)` when `B(y, r)` misses `E_t`. -/
theorem norm_deriv_ownExt_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {y r : ℝ}
    (hdisj : Disjoint (ball (y : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) {z : ℂ}
    (hz : z ∈ ball (y : ℂ) (r / 2)) : ‖deriv (ownExt W W' a φ t) z‖ ≤ 96 := by
  have hlip : LipschitzOnWith (96 : NNReal) (ownExt W W' a φ t) (ball (y : ℂ) (r / 2)) := by
    refine LipschitzOnWith.of_dist_le_mul fun w hw z hz => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have := h.norm_ownExt_sub_le ht hdisj hz hw
    simpa using this
  have := norm_deriv_le_of_lipschitzOn (isOpen_ball.mem_nhds hz) hlip
  simpa using this

/-- `|F_t''| ≤ 384/r` on `B(y, r/4)`. -/
theorem norm_deriv2_ownExt_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {y r : ℝ}
    (hdisj : Disjoint (ball (y : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) {z : ℂ}
    (hz : z ∈ ball (y : ℂ) (r / 4)) : ‖deriv (deriv (ownExt W W' a φ t)) z‖ ≤ 384 / r := by
  have hd := (h.ownExt_props ht hdisj).1
  have hz' : z ∈ ball (y : ℂ) (r / 2 / 2) := by
    have e : r / 2 / 2 = r / 4 := by ring
    rw [e]; exact hz
  have h1 := norm_deriv_deriv_le_of_norm_le_ball hd
    (fun w hw => h.norm_deriv_ownExt_le ht hdisj hw) hz'
  calc _ ≤ 2 * 96 / (r / 2) := h1
    _ = 384 / r := by ring

/-- `|F_t'''| ≤ 3072/r²` on `B(y, r/8)`. -/
theorem norm_deriv3_ownExt_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {y r : ℝ}
    (hdisj : Disjoint (ball (y : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) {z : ℂ}
    (hz : z ∈ ball (y : ℂ) (r / 8)) : ‖deriv (deriv (deriv (ownExt W W' a φ t))) z‖ ≤ 3072 / r ^ 2 := by
  have hd := (h.ownExt_props ht hdisj).1
  have hsub : ball (y : ℂ) (r / 4) ⊆ ball (y : ℂ) (r / 2) := ball_subset_ball (by
    have : 0 ≤ r := by have := pos_of_mem_ball hz; linarith
    linarith)
  have hd2 : DifferentiableOn ℂ (deriv (deriv (ownExt W W' a φ t))) (ball (y : ℂ) (r / 4)) :=
    ((hd.deriv isOpen_ball).deriv isOpen_ball).mono hsub
  have hz' : z ∈ ball (y : ℂ) (r / 4 / 2) := by
    have e : r / 4 / 2 = r / 8 := by ring
    rw [e]; exact hz
  have h1 := norm_deriv_le_of_norm_le_ball hd2 (fun w hw => h.norm_deriv2_ownExt_le ht hdisj hw) hz'
  calc _ ≤ 2 * (384 / r) / (r / 4) := h1
    _ = 3072 / r ^ 2 := by ring

/-- `|F_t''''| ≤ 49152/r³` on `B(y, r/16)`. -/
theorem norm_deriv4_ownExt_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {y r : ℝ}
    (hdisj : Disjoint (ball (y : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) {z : ℂ}
    (hz : z ∈ ball (y : ℂ) (r / 16)) :
    ‖deriv (deriv (deriv (deriv (ownExt W W' a φ t)))) z‖ ≤ 49152 / r ^ 3 := by
  have hd := (h.ownExt_props ht hdisj).1
  have hsub : ball (y : ℂ) (r / 8) ⊆ ball (y : ℂ) (r / 2) := ball_subset_ball (by
    have : 0 ≤ r := by have := pos_of_mem_ball hz; linarith
    linarith)
  have hd3 : DifferentiableOn ℂ (deriv (deriv (deriv (ownExt W W' a φ t)))) (ball (y : ℂ) (r / 8)) :=
    (((hd.deriv isOpen_ball).deriv isOpen_ball).deriv isOpen_ball).mono hsub
  have hz' : z ∈ ball (y : ℂ) (r / 8 / 2) := by
    have e : r / 8 / 2 = r / 16 := by ring
    rw [e]; exact hz
  have h1 := norm_deriv_le_of_norm_le_ball hd3 (fun w hw => h.norm_deriv3_ownExt_le ht hdisj hw) hz'
  calc _ ≤ 2 * (3072 / r ^ 2) / (r / 8) := h1
    _ = 49152 / r ^ 3 := by ring

/-- **`A_{1,1} = F_t'(W_t)` is real, positive and at most one.** The upper bound is the height comparison
`Im h_t(z) ≤ Im z` (`IsMapOut.im_le`) differentiated at the real point `W_t`. -/
theorem deriv_ownExt_driver {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {r : ℝ} (hr : 0 < r)
    (hdisj : Disjoint (ball (W t : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) :
    (deriv (ownExt W W' a φ t) (W t)).im = 0 ∧ 0 < (deriv (ownExt W W' a φ t) (W t)).re ∧
      (deriv (ownExt W W' a φ t) (W t)).re ≤ 1 := by
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
  obtain ⟨hd, -, -, hreal, -, hRe⟩ := h.ownExt_props ht hdisj
  have hr2 : 0 < r / 2 := by linarith
  obtain ⟨hpos, him, -⟩ := (h.rate t ht R hR).2.2.2 (r / 2) hr2 (ownExt W W' a φ t) hd (hRe R hR)
  refine ⟨him, hpos, ?_⟩
  have hWB : (W t : ℂ) ∈ ball (W t : ℂ) (r / 2) := mem_ball_self hr2
  have hdiff : DifferentiableAt ℂ (ownExt W W' a φ t) (W t) :=
    hd.differentiableAt (isOpen_ball.mem_nhds hWB)
  have hle := re_deriv_le_of_im_le (G₁ := ownExt W W' a φ t) (G₂ := id) (x := W t) hr2 hdiff
    differentiableAt_id (hreal _ hWB (by simp)) (by simp) (fun ε hε => ?_)
  · simpa using hle
  · have hzB : (W t : ℂ) + (ε : ℂ) * I ∈ ball (W t : ℂ) (r / 2) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
      exact hε.2
    have hzH : (W t : ℂ) + (ε : ℂ) * I ∈ H := by
      show 0 < ((W t : ℂ) + (ε : ℂ) * I).im
      simp [hε.1]
    have hzE : (W t : ℂ) + (ε : ℂ) * I ∉ (fun z => fwdMap W t z + W t) '' A := fun hE =>
      Set.disjoint_left.1 hdisj (ball_subset_ball (by linarith) hzB) hE
    rw [hRe R hR ⟨hzB, hzH⟩]
    exact hR.im_le (h.isHPHull_E ht) ⟨hzH, hzE⟩

end OwnData

end InteractingSLE.ZhanGT4
