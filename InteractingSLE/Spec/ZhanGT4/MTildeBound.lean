/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.ItoFieldFrozen
import InteractingSLE.Spec.ZhanGT4.D9Bound

/-!
# (D9) for the field of `M̃`: local bounds near the driver

Packet PROVE-ZHAN-GT4-A7. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L341, R38: "Applying
the normal-family and reflection argument to `h_j` on that neighborhood gives positive lower and finite upper bounds for
`h_j'`, and finite bounds for its next derivatives"), made quantitative from PROVE-ZHAN-GT4-A6's bounds.

A holomorphic `G` on `B(w, R₀)` with `|G'| ≤ M₁`, `|G''| ≤ M₂` and `Re G'(w) ≥ a₀ > 0` has, on `B(w, ρ)` with
`ρ = min R₀ (a₀/(2M₂))`, `Re G' ≥ a₀/2` and `Re dslope G w ≥ a₀/2` (so the divided difference `q` of A4's removable
form never vanishes), and the removable form `D̂ = dHat G w` of (D1) and its derivative are bounded:
`|D̂| ≤ 24M₁²/(ρa₀)` on `B(w, ρ/2)`, `|∂D̂| ≤ 96M₁²/(ρ²a₀)` on `B(w, ρ/4)` (`local_bounds`). With A6's bounds for
`F_t = ownExt … t` (`|F'| ≤ 96`, `|F''| ≤ 384/r` on `B(W_t, r/4)`, `r` the clearance), this gives every box hypothesis
of PROVE-ZHAN-GT4-A4 for a frozen center (`OwnData.box_of_clearance`).

## Main results

* `local_bounds`: the generic local bounds;
* `OwnData.box_of_clearance`: from a clearance `r` and `A₁ ≥ a₀` on `[0, T]`, for every piece `[b, c]` on which the
  driver stays within `ρ/24` of a center `y` (`ρ = min (r/4) (a₀ r/768)`), the box hypotheses (`hdisj`, `hWm`, `hq0`) on
  `B(y, ρ/8)` and, on the real region `|x − y| < ρ/8`, `Re F_t' ≥ a₀/2` and the bounds on `F_t`, `D̂_t`, `∂D̂_t`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-! ### Generic local bounds -/

section Generic

variable {G : ℂ → ℂ} {w : ℂ} {R₀ M₁ M₂ a₀ : ℝ}

/-- The mean value inequality on a ball for a holomorphic function. -/
theorem norm_sub_le_of_ball {f : ℂ → ℂ} {c : ℂ} {ρ C : ℝ} (hf : DifferentiableOn ℂ f (ball c ρ))
    (hb : ∀ z ∈ ball c ρ, ‖deriv f z‖ ≤ C) {z z' : ℂ} (hz : z ∈ ball c ρ) (hz' : z' ∈ ball c ρ) :
    ‖f z' - f z‖ ≤ C * ‖z' - z‖ :=
  Convex.norm_image_sub_le_of_norm_deriv_le (fun _x hx => hf.differentiableAt (isOpen_ball.mem_nhds hx)) hb
    (convex_ball c ρ) hz hz'

/-- **Local bounds near a point with `Re G' ≥ a₀`.** -/
theorem local_bounds (hG : DifferentiableOn ℂ G (ball w R₀)) (hM₁ : ∀ z ∈ ball w R₀, ‖deriv G z‖ ≤ M₁)
    (hM₂ : ∀ z ∈ ball w R₀, ‖deriv (deriv G) z‖ ≤ M₂) (hR₀ : 0 < R₀) (hM₂p : 0 < M₂) (ha₀ : 0 < a₀)
    (hw : a₀ ≤ (deriv G w).re) :
    (∀ z ∈ ball w (min R₀ (a₀ / (2 * M₂))), a₀ / 2 ≤ (deriv G z).re ∧ a₀ / 2 ≤ (dslope G w z).re ∧
        ‖dslope G w z‖ ≤ M₁) ∧
      (∀ z ∈ ball w (min R₀ (a₀ / (2 * M₂)) / 2),
        ‖dHat G w z‖ ≤ 24 * M₁ ^ 2 / (min R₀ (a₀ / (2 * M₂)) * a₀)) ∧
      (∀ z ∈ ball w (min R₀ (a₀ / (2 * M₂)) / 4),
        ‖deriv (dHat G w) z‖ ≤ 96 * M₁ ^ 2 / (min R₀ (a₀ / (2 * M₂)) ^ 2 * a₀)) ∧
      DifferentiableOn ℂ (dHat G w) (ball w (min R₀ (a₀ / (2 * M₂)) / 2)) := by
  set ρ := min R₀ (a₀ / (2 * M₂)) with hρdef
  have hρ : 0 < ρ := lt_min hR₀ (by positivity)
  have hρR : ρ ≤ R₀ := min_le_left _ _
  have hρa : ρ ≤ a₀ / (2 * M₂) := min_le_right _ _
  have hsub : ball w ρ ⊆ ball w R₀ := ball_subset_ball hρR
  have hwB : w ∈ ball w ρ := mem_ball_self hρ
  have hGρ : DifferentiableOn ℂ G (ball w ρ) := hG.mono hsub
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ w (hsub hwB))
  -- `G'` is `M₂`-Lipschitz on the ball
  have hG'd : DifferentiableOn ℂ (deriv G) (ball w ρ) := hGρ.deriv isOpen_ball
  have hlip : ∀ z ∈ ball w ρ, ‖deriv G z - deriv G w‖ ≤ a₀ / 2 := fun z hz => by
    have h1 := norm_sub_le_of_ball hG'd (fun x hx => hM₂ x (hsub hx)) hwB hz
    have h2 : ‖z - w‖ < ρ := by rw [← dist_eq_norm]; exact hz
    calc ‖deriv G z - deriv G w‖ ≤ M₂ * ‖z - w‖ := h1
      _ ≤ M₂ * ρ := mul_le_mul_of_nonneg_left h2.le hM₂p.le
      _ ≤ M₂ * (a₀ / (2 * M₂)) := mul_le_mul_of_nonneg_left hρa hM₂p.le
      _ = a₀ / 2 := by field_simp
  have hre : ∀ z ∈ ball w ρ, a₀ / 2 ≤ (deriv G z).re := fun z hz => by
    have h1 := hlip z hz
    have h2 : |(deriv G z - deriv G w).re| ≤ ‖deriv G z - deriv G w‖ := abs_re_le_norm _
    rw [sub_re] at h2
    have := neg_abs_le ((deriv G z).re - (deriv G w).re)
    linarith
  -- `g = G − G'(w) · id` has small derivative, so the divided difference stays near `G'(w)`
  have hdsl : ∀ z ∈ ball w ρ, ‖dslope G w z - deriv G w‖ ≤ a₀ / 2 ∧ ‖dslope G w z‖ ≤ M₁ := fun z hz => by
    rcases eq_or_ne z w with rfl | hzw
    · rw [dslope_same, sub_self, norm_zero]
      exact ⟨by positivity, hM₁ z (hsub hz)⟩
    have hzw' : z - w ≠ 0 := sub_ne_zero.2 hzw
    have hgd : DifferentiableOn ℂ (fun ξ => G ξ - deriv G w * ξ) (ball w ρ) :=
      hGρ.sub ((differentiableOn_id).const_mul _)
    have hgb : ∀ x ∈ ball w ρ, ‖deriv (fun ξ => G ξ - deriv G w * ξ) x‖ ≤ a₀ / 2 := fun x hx => by
      have hdx : HasDerivAt (fun ξ => G ξ - deriv G w * ξ) (deriv G x - deriv G w) x := by
        have h1 := (hGρ.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
        have h2 := (hasDerivAt_id x).const_mul (deriv G w)
        have h3 := h1.sub h2
        simp only [mul_one] at h3
        exact h3
      rw [hdx.deriv]; exact hlip x hx
    have h1 := norm_sub_le_of_ball hgd hgb hwB hz
    have h2 := norm_sub_le_of_ball hGρ (fun x hx => hM₁ x (hsub hx)) hwB hz
    rw [dslope_of_ne _ hzw, slope_def_field]
    have e : (G z - G w) / (z - w) - deriv G w = ((G z - deriv G w * z) - (G w - deriv G w * w)) / (z - w) := by
      field_simp; ring
    refine ⟨?_, ?_⟩
    · rw [e, norm_div]
      rw [div_le_iff₀ (norm_pos_iff.2 hzw')]
      exact h1
    · rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hzw')]
      exact h2
  have hqre : ∀ z ∈ ball w ρ, a₀ / 2 ≤ (dslope G w z).re := fun z hz => by
    have h1 := (hdsl z hz).1
    have h2 : |(dslope G w z - deriv G w).re| ≤ ‖dslope G w z - deriv G w‖ := abs_re_le_norm _
    rw [sub_re] at h2
    have := neg_abs_le ((dslope G w z).re - (deriv G w).re)
    linarith
  have hq0 : ∀ z ∈ ball w ρ, dslope G w z ≠ 0 := fun z hz h0 => by
    have := hqre z hz; rw [h0, zero_re] at this; linarith
  have hqnorm : ∀ z ∈ ball w ρ, a₀ / 2 ≤ ‖dslope G w z‖ := fun z hz =>
    (hqre z hz).trans ((le_abs_self _).trans (abs_re_le_norm _))
  have hsub2 : ball w (ρ / 2) ⊆ ball w ρ := ball_subset_ball (by linarith)
  have hwB2 : w ∈ ball w (ρ / 2) := mem_ball_self (by positivity)
  have hqd : DifferentiableOn ℂ (dslope G w) (ball w ρ) := differentiableOn_dslope_of_isOpen isOpen_ball hwB hGρ
  have hq' : ∀ z ∈ ball w (ρ / 2), ‖deriv (dslope G w) z‖ ≤ 2 * M₁ / ρ := fun z hz =>
    norm_deriv_le_of_norm_le_ball hqd (fun x hx => (hdsl x hx).2) hz
  have hqd2 : DifferentiableOn ℂ (dslope G w) (ball w (ρ / 2)) := hqd.mono hsub2
  have hu : ∀ z ∈ ball w (ρ / 2), ‖dslope (dslope G w) w z‖ ≤ 2 * M₁ / ρ := fun z hz => by
    rcases eq_or_ne z w with rfl | hzw
    · rw [dslope_same]; exact hq' z hz
    · rw [dslope_of_ne _ hzw, slope_def_field, norm_div, div_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hzw))]
      exact norm_sub_le_of_ball hqd2 hq' hwB2 hz
  have hqw : ‖dslope G w w‖ ≤ M₁ := (hdsl w hwB).2
  -- the bound on `D̂`
  have hDb : ∀ z ∈ ball w (ρ / 2), ‖dHat G w z‖ ≤ 24 * M₁ ^ 2 / (ρ * a₀) := fun z hz => by
    have hzρ := hsub2 hz
    have hqz := hqnorm z hzρ
    have hqzp : 0 < ‖dslope G w z‖ := lt_of_lt_of_le (by positivity) hqz
    unfold dHat
    rw [norm_div, div_le_iff₀ hqzp]
    have hnum : ‖2 * (-(dslope (dslope G w) w z) * (dslope G w z + dslope G w w) - dslope G w z *
        deriv (dslope G w) z)‖ ≤ 2 * (2 * M₁ / ρ * (M₁ + M₁) + M₁ * (2 * M₁ / ρ)) := by
      rw [norm_mul, Complex.norm_two]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_neg]
        exact mul_le_mul (hu z hz) ((norm_add_le _ _).trans (add_le_add (hdsl z hzρ).2 hqw))
          (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        exact mul_le_mul (hdsl z hzρ).2 (hq' z hz) (norm_nonneg _) hM₁0
    calc _ ≤ 2 * (2 * M₁ / ρ * (M₁ + M₁) + M₁ * (2 * M₁ / ρ)) := hnum
      _ = 24 * M₁ ^ 2 / (ρ * a₀) * (a₀ / 2) := by field_simp; ring
      _ ≤ 24 * M₁ ^ 2 / (ρ * a₀) * ‖dslope G w z‖ := mul_le_mul_of_nonneg_left hqz (by positivity)
  have hDd : DifferentiableOn ℂ (dHat G w) (ball w (ρ / 2)) :=
    differentiableOn_dHat isOpen_ball hwB2 (hGρ.mono hsub2) fun z hz => hq0 z (hsub2 hz)
  refine ⟨fun z hz => ⟨hre z hz, hqre z hz, (hdsl z hz).2⟩, hDb, fun z hz => ?_, hDd⟩
  have hz' : z ∈ ball w (ρ / 2 / 2) := by rw [show ρ / 2 / 2 = ρ / 4 by ring]; exact hz
  calc _ ≤ 2 * (24 * M₁ ^ 2 / (ρ * a₀)) / (ρ / 2) := norm_deriv_le_of_norm_le_ball hDd hDb hz'
    _ = 96 * M₁ ^ 2 / (ρ ^ 2 * a₀) := by field_simp; ring

end Generic

/-! ### The box hypotheses from a clearance and a lower bound on `A₁` -/

/-- The working radius `ρ = min (r/4) (a₀/(2 · 384/r))` of the local bounds for `F_t`. -/
def clrRad (r a₀ : ℝ) : ℝ := min (r / 4) (a₀ / (2 * (384 / r)))

theorem clrRad_pos {r a₀ : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) : 0 < clrRad r a₀ :=
  lt_min (by positivity) (by positivity)

theorem clrRad_le {r a₀ : ℝ} : clrRad r a₀ ≤ r / 4 := min_le_left _ _

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

/-- **The box hypotheses for a frozen center, quantitatively** ((D9) for the own map near the driver). Let `r` be a
clearance of `g_t(A)` from the driver and `A₁ ≥ a₀` on `[0, T]`, and `ρ = clrRad r a₀`. On every piece `[b, c]` on
which the driver stays within `ρ/24` of a center `y`: `g_t(A)` misses `B(y, ρ/4)`, the driver is in `B(y, ρ/8)`, the
divided difference of `F_t` at the driver does not vanish on `B(y, ρ/8)`, and there `Re F_t' ≥ a₀/2`, `|F_t'| ≤ 96`,
`|F_t''| ≤ 384/r`, `|F_t'''| ≤ 3072/r²`, `|F_t''''| ≤ 49152/r³`, `|F_t(z) − F_t(W_t)| ≤ 96|z − W_t|`,
`|D̂_t| ≤ 24·96²/(ρa₀)`, `|∂D̂_t| ≤ 96·96²/(ρ²a₀)`. -/
theorem box_of_clearance {r a₀ : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀)
    (hclr : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball (W t : ℂ) r) ((fun z => fwdMap W t z + W t) '' A))
    (hA1 : ∀ t ∈ Icc (0 : ℝ) T, a₀ ≤ frzA W W' a φ 1 t) {b c y : ℝ} (hJ : Icc b c ⊆ Icc 0 T)
    (hWy : ∀ t ∈ Icc b c, |W t - y| < clrRad r a₀ / 24) :
    (∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * (clrRad r a₀ / 8))) ((fun z => fwdMap W t z + W t) '' A)) ∧
    (∀ t ∈ Icc b c, (W t : ℂ) ∈ ball (y : ℂ) (clrRad r a₀ / 8)) ∧
    (∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) (clrRad r a₀ / 8), dslope (ownExt W W' a φ t) (W t) z ≠ 0) ∧
    (∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) (clrRad r a₀ / 8),
      a₀ / 2 ≤ (deriv (ownExt W W' a φ t) z).re ∧ ‖deriv (ownExt W W' a φ t) z‖ ≤ 96 ∧
      ‖deriv (deriv (ownExt W W' a φ t)) z‖ ≤ 384 / r ∧
      ‖deriv (deriv (deriv (ownExt W W' a φ t))) z‖ ≤ 3072 / r ^ 2 ∧
      ‖deriv (deriv (deriv (deriv (ownExt W W' a φ t)))) z‖ ≤ 49152 / r ^ 3 ∧
      ‖ownExt W W' a φ t z - ownExt W W' a φ t (W t)‖ ≤ 96 * ‖z - W t‖ ∧
      ‖dHat (ownExt W W' a φ t) (W t) z‖ ≤ 24 * 96 ^ 2 / (clrRad r a₀ * a₀) ∧
      ‖deriv (dHat (ownExt W W' a φ t) (W t)) z‖ ≤ 96 * 96 ^ 2 / (clrRad r a₀ ^ 2 * a₀)) := by
  set ρ := clrRad r a₀ with hρdef
  have hρ : 0 < ρ := clrRad_pos hr ha₀
  have hρr : ρ ≤ r / 4 := clrRad_le
  -- distances
  have hnear : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) (ρ / 8), ‖z - W t‖ < ρ / 6 := fun t ht z hz => by
    have h1 : ‖z - y‖ < ρ / 8 := by rw [← dist_eq_norm]; exact hz
    have h2 : ‖((y : ℂ) - W t)‖ < ρ / 24 := by
      rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hWy t ht
    calc ‖z - W t‖ = ‖(z - y) + ((y : ℂ) - W t)‖ := by ring_nf
      _ ≤ ‖z - y‖ + ‖((y : ℂ) - W t)‖ := norm_add_le _ _
      _ < ρ / 8 + ρ / 24 := add_lt_add h1 h2
      _ = ρ / 6 := by ring
  have hin : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) (ρ / 8), ∀ s, ρ / 6 ≤ s → z ∈ ball (W t : ℂ) s :=
    fun t ht z hz s hs => by
      rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le (hnear t ht z hz) hs
  -- the local bounds at each time
  have hloc : ∀ t ∈ Icc b c, _ := fun t ht => local_bounds (G := ownExt W W' a φ t) (w := (W t : ℂ))
    (R₀ := r / 4) (M₁ := 96) (M₂ := 384 / r)
    ((h.ownExt_props (hJ ht) (hclr t (hJ ht))).1.mono (ball_subset_ball (by linarith)))
    (fun z hz => h.norm_deriv_ownExt_le (hJ ht) (hclr t (hJ ht)) (ball_subset_ball (by linarith) hz))
    (fun z hz => h.norm_deriv2_ownExt_le (hJ ht) (hclr t (hJ ht)) hz) (by positivity) (by positivity) ha₀
    (hA1 t (hJ ht))
  have e : min (r / 4) (a₀ / (2 * (384 / r))) = ρ := rfl
  simp only [e] at hloc
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht z hz => ?_, fun t ht z hz => ?_⟩
  · refine (hclr t (hJ ht)).mono_left fun z hz => ?_
    have h1 : ‖z - y‖ < ρ / 4 := by rw [← dist_eq_norm]; rw [show 2 * (ρ / 8) = ρ / 4 by ring] at hz; exact hz
    have h2 : ‖((y : ℂ) - W t)‖ < ρ / 24 := by
      rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hWy t ht
    rw [mem_ball, dist_eq_norm]
    calc ‖z - W t‖ = ‖(z - y) + ((y : ℂ) - W t)‖ := by ring_nf
      _ ≤ ‖z - y‖ + ‖((y : ℂ) - W t)‖ := norm_add_le _ _
      _ < ρ / 4 + ρ / 24 := add_lt_add h1 h2
      _ ≤ r := by linarith
  · rw [mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    linarith [hWy t ht]
  · intro h0
    have h' := ((hloc t ht).1 z (hin t ht z hz _ (by linarith))).2.1
    rw [h0, zero_re] at h'
    linarith
  · have hz4 : z ∈ ball (W t : ℂ) (ρ / 4) := hin t ht z hz _ (by linarith)
    have hzρ : z ∈ ball (W t : ℂ) ρ := hin t ht z hz _ (by linarith)
    obtain ⟨l1, l2, l3, -⟩ := hloc t ht
    refine ⟨(l1 z hzρ).1,
      h.norm_deriv_ownExt_le (hJ ht) (hclr t (hJ ht)) (hin t ht z hz _ (by linarith)),
      h.norm_deriv2_ownExt_le (hJ ht) (hclr t (hJ ht)) (hin t ht z hz _ (by linarith)),
      h.norm_deriv3_ownExt_le (hJ ht) (hclr t (hJ ht)) (hin t ht z hz _ (by linarith)),
      h.norm_deriv4_ownExt_le (hJ ht) (hclr t (hJ ht)) (hin t ht z hz _ (by linarith)),
      h.norm_ownExt_sub_le (hJ ht) (hclr t (hJ ht)) (mem_ball_self (by positivity))
        (hin t ht z hz _ (by linarith)), ?_, ?_⟩
    · exact l2 z (hin t ht z hz _ (by linarith))
    · exact l3 z hz4

end OwnData

/-! ### Uniform bounds for the formal functions at a scale `L` -/

section Scale

/-- `u` is at scale `L`: `e^{−L} ≤ |u| ≤ e^L`. -/
def InScale (L u : ℝ) : Prop := Real.exp (-L) ≤ |u| ∧ |u| ≤ Real.exp L

variable {L : ℝ}

theorem abs_log_le_of_inScale {u : ℝ} (h : InScale L u) : |Real.log u| ≤ L := by
  have hu : 0 < |u| := lt_of_lt_of_le (Real.exp_pos _) h.1
  rw [← Real.log_abs, abs_le]
  constructor
  · rw [Real.le_log_iff_exp_le hu]; exact h.1
  · rw [Real.log_le_iff_le_exp hu]; exact h.2

theorem abs_div_le_of_inScale {p q : ℝ} (hp : |p| ≤ Real.exp L) (hq : InScale L q) :
    |p / q| ≤ Real.exp (2 * L) := by
  have hq0 : 0 < |q| := lt_of_lt_of_le (Real.exp_pos _) hq.1
  rw [abs_div, div_le_iff₀ hq0]
  calc |p| ≤ Real.exp L := hp
    _ = Real.exp (2 * L) * Real.exp (-L) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (2 * L) * |q| := mul_le_mul_of_nonneg_left hq.1 (Real.exp_pos _).le

theorem exp_mono_le {k l : ℝ} (hL : 0 ≤ L) (hkl : k ≤ l) : Real.exp (k * L) ≤ Real.exp (l * L) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hkl hL)

/-- The universal bound `U(L) = 8(1 + L)e^{6L}`. -/
def scaleBound (L : ℝ) : ℝ := 8 * (1 + L) * Real.exp (6 * L)

theorem le_scaleBound (hL : 0 ≤ L) :
    L ≤ scaleBound L ∧ Real.exp L ≤ scaleBound L ∧ Real.exp (2 * L) ≤ scaleBound L ∧
      2 * Real.exp (2 * L) ≤ scaleBound L ∧ Real.exp (2 * L) + Real.exp (4 * L) ≤ scaleBound L ∧
      Real.exp (2 * L) + 3 * Real.exp (4 * L) + 2 * Real.exp (6 * L) ≤ scaleBound L ∧
      L + Real.exp L ≤ scaleBound L := by
  have e1 : Real.exp L ≤ Real.exp (6 * L) := by
    have := exp_mono_le (L := L) hL (show (1 : ℝ) ≤ 6 by norm_num); simpa using this
  have e2 : Real.exp (2 * L) ≤ Real.exp (6 * L) := exp_mono_le hL (by norm_num)
  have e4 : Real.exp (4 * L) ≤ Real.exp (6 * L) := exp_mono_le hL (by norm_num)
  have h6 : 1 ≤ Real.exp (6 * L) := Real.one_le_exp (by positivity)
  have hLe : L ≤ L * Real.exp (6 * L) := le_mul_of_one_le_right hL h6
  have hE : 0 ≤ Real.exp (6 * L) := (Real.exp_pos _).le
  unfold scaleBound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end Scale

section FormalBounds

variable {κ : ℝ} {n : ℕ} {r : Fin n → ℝ} {L : ℝ}

/-- The total size of the coefficients of `M̃`. -/
def coefTot (κ : ℝ) {n : ℕ} (r : Fin n → ℝ) : ℝ :=
  |dualAlpha κ| + |(3 * κ - 8) / 16| + |dualLambda κ| + 1 +
    ∑ m, (|r m| + |dualGamma κ (r m)| + |κ / 4 * r m|) + pairSum (fun m k => |dualDelta κ (r m) (r k)|)

theorem pairSum_nonneg {f : Fin n → Fin n → ℝ} (hf : ∀ m k, 0 ≤ f m k) : 0 ≤ pairSum f :=
  Finset.sum_nonneg fun p _ => hf p.1 p.2

theorem abs_pairSum_le {f g : Fin n → Fin n → ℝ} (hfg : ∀ m k, m < k → |f m k| ≤ g m k) :
    |pairSum f| ≤ pairSum g := by
  unfold pairSum
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => hfg p.1 p.2
    (Finset.mem_filter.1 hp).2)

theorem pairSum_mul_const (f : Fin n → Fin n → ℝ) (C : ℝ) :
    pairSum (fun m k => f m k * C) = pairSum f * C := by
  unfold pairSum; rw [Finset.sum_mul]

theorem abs_sum_mul_le {X : Fin n → ℝ} {B : ℝ} (hX : ∀ m, |X m| ≤ B) :
    |∑ m, r m * X m| ≤ (∑ m, |r m|) * B := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hX m) (abs_nonneg _)

theorem coefTot_ge : 0 ≤ ∑ m, (|r m| + |dualGamma κ (r m)| + |κ / 4 * r m|) ∧
    0 ≤ pairSum (fun m k => |dualDelta κ (r m) (r k)|) ∧
    |dualAlpha κ| + 1 / 2 + ∑ m, |r m| ≤ coefTot κ r ∧ 0 ≤ coefTot κ r := by
  have h1 : 0 ≤ ∑ m, (|r m| + |dualGamma κ (r m)| + |κ / 4 * r m|) := Finset.sum_nonneg fun m _ => by positivity
  have h2 : 0 ≤ pairSum (fun m k => |dualDelta κ (r m) (r k)|) := pairSum_nonneg fun _ _ => abs_nonneg _
  have h3 : ∑ m, |r m| ≤ ∑ m, (|r m| + |dualGamma κ (r m)| + |κ / 4 * r m|) :=
    Finset.sum_le_sum fun m _ => by have := abs_nonneg (dualGamma κ (r m)); have := abs_nonneg (κ / 4 * r m); linarith
  refine ⟨h1, h2, ?_, ?_⟩ <;> unfold coefTot <;>
    nlinarith [abs_nonneg (dualAlpha κ), abs_nonneg ((3 * κ - 8) / 16), abs_nonneg (dualLambda κ)]

/-- **The space-part functions are bounded at scale `L`.** -/
theorem abs_dualLogSpace_le (hL : 0 ≤ L) {f f1 f2 f3 f4 A0 df df1 dA0 : ℝ} {B0 dB0 : Fin n → ℝ}
    (h1 : InScale L f1) (h0 : InScale L (f - A0)) (hm : ∀ m, InScale L (f - B0 m)) (h2 : |f2| ≤ Real.exp L)
    (h3 : |f3| ≤ Real.exp L) (h4 : |f4| ≤ Real.exp L) (hdf : |df| ≤ Real.exp L) (hdf1 : |df1| ≤ Real.exp L)
    (hdA0 : |dA0| ≤ Real.exp L) (hdB0 : ∀ m, |dB0 m| ≤ Real.exp L) :
    |dualLogSpace κ r f f1 A0 B0| ≤ coefTot κ r * scaleBound L ∧
      |dualLogSpaceX κ r f f1 f2 A0 B0| ≤ coefTot κ r * scaleBound L ∧
      |dualLogSpaceXX κ r f f1 f2 f3 A0 B0| ≤ coefTot κ r * scaleBound L ∧
      |dualLogSpaceXXX κ r f f1 f2 f3 f4 A0 B0| ≤ coefTot κ r * scaleBound L ∧
      |dualLogSpaceT κ r f f1 A0 B0 df df1 dA0 dB0| ≤ coefTot κ r * scaleBound L := by
  obtain ⟨-, -, hc, hc0⟩ := coefTot_ge (κ := κ) (r := r)
  obtain ⟨sL, s1, s2, s22, s24, s246, -⟩ := le_scaleBound hL
  have hsB : 0 ≤ scaleBound L := hL.trans sL
  have hex : 0 ≤ Real.exp L := (Real.exp_pos _).le
  have hf1e : |f1| ≤ Real.exp L := h1.2
  have hfe : |f - A0| ≤ Real.exp L := h0.2
  -- a generic three-term combination
  have comb : ∀ X Y : ℝ, ∀ Z : Fin n → ℝ, ∀ B : ℝ, |X| ≤ B → |Y| ≤ B → (∀ m, |Z m| ≤ B) → B ≤ scaleBound L →
      |dualAlpha κ * X - 1 / 2 * Y + ∑ m, r m * Z m| ≤ coefTot κ r * scaleBound L := by
    intro X Y Z B hX hY hZ hB
    have hB0 : 0 ≤ B := (abs_nonneg _).trans hX
    have e1 : |dualAlpha κ * X| ≤ |dualAlpha κ| * B := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hX (abs_nonneg _)
    have e2 : |1 / 2 * Y| ≤ 1 / 2 * B := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; exact mul_le_mul_of_nonneg_left hY (by norm_num)
    have e3 := abs_sum_mul_le (r := r) hZ
    calc |dualAlpha κ * X - 1 / 2 * Y + ∑ m, r m * Z m|
        ≤ |dualAlpha κ * X| + |1 / 2 * Y| + |∑ m, r m * Z m| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
      _ ≤ (|dualAlpha κ| + 1 / 2 + ∑ m, |r m|) * B := by nlinarith
      _ ≤ coefTot κ r * scaleBound L := mul_le_mul hc hB hB0 hc0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact comb _ _ _ L (abs_log_le_of_inScale h1) (abs_log_le_of_inScale h0)
      (fun m => abs_log_le_of_inScale (hm m)) sL
  · exact comb _ _ _ _ (abs_div_le_of_inScale h2 h1) (abs_div_le_of_inScale hf1e h0)
      (fun m => abs_div_le_of_inScale hf1e (hm m)) s2
  · have q : ∀ (p1 p2 q0 : ℝ), |p1| ≤ Real.exp L → |p2| ≤ Real.exp L → InScale L q0 →
        |p1 / q0 - (p2 / q0) ^ 2| ≤ Real.exp (2 * L) + Real.exp (4 * L) := fun p1 p2 q0 hp1 hp2 hq => by
      have a1 := abs_div_le_of_inScale hp1 hq
      have a2 := abs_div_le_of_inScale hp2 hq
      have a3 : |(p2 / q0) ^ 2| ≤ Real.exp (4 * L) := by
        rw [abs_pow, show 4 * L = 2 * L + 2 * L by ring, Real.exp_add, sq]
        exact mul_le_mul a2 a2 (abs_nonneg _) (Real.exp_pos _).le
      exact (abs_sub _ _).trans (add_le_add a1 a3)
    exact comb _ _ _ _ (q _ _ _ h3 h2 h1) (q _ _ _ h2 hf1e h0) (fun m => q _ _ _ h2 hf1e (hm m)) s24
  · have q : ∀ (p1 p2 p3 q0 : ℝ), |p1| ≤ Real.exp L → |p2| ≤ Real.exp L → |p3| ≤ Real.exp L → InScale L q0 →
        |p1 / q0 - 3 * (p2 / q0) * (p3 / q0) + 2 * (p3 / q0) ^ 3| ≤
          Real.exp (2 * L) + 3 * Real.exp (4 * L) + 2 * Real.exp (6 * L) := fun p1 p2 p3 q0 hp1 hp2 hp3 hq => by
      have a1 := abs_div_le_of_inScale hp1 hq
      have a2 := abs_div_le_of_inScale hp2 hq
      have a3 := abs_div_le_of_inScale hp3 hq
      have m23 : |3 * (p2 / q0) * (p3 / q0)| ≤ 3 * Real.exp (4 * L) := by
        rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_mul,
          show 4 * L = 2 * L + 2 * L by ring, Real.exp_add]
        exact mul_le_mul_of_nonneg_left (mul_le_mul a2 a3 (abs_nonneg _) (Real.exp_pos _).le) (by norm_num)
      have c3 : |2 * (p3 / q0) ^ 3| ≤ 2 * Real.exp (6 * L) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow,
          show 6 * L = 2 * L + 2 * L + 2 * L by ring, Real.exp_add, Real.exp_add]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have := pow_le_pow_left₀ (abs_nonneg _) a3 3
        calc |p3 / q0| ^ 3 ≤ Real.exp (2 * L) ^ 3 := this
          _ = _ := by ring
      exact (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add a1 m23)) c3)
    exact comb _ _ _ _ (q _ _ _ _ h4 h3 h2 h1) (q _ _ _ _ h3 h2 hf1e h0)
      (fun m => q _ _ _ _ h3 h2 hf1e (hm m)) s246
  · have q : ∀ (p1 p2 q0 : ℝ), |p1| ≤ Real.exp L → |p2| ≤ Real.exp L → InScale L q0 →
        |(p1 - p2) / q0| ≤ 2 * Real.exp (2 * L) := fun p1 p2 q0 hp1 hp2 hq => by
      have hq0 : 0 < |q0| := lt_of_lt_of_le (Real.exp_pos _) hq.1
      rw [abs_div, div_le_iff₀ hq0]
      calc |p1 - p2| ≤ |p1| + |p2| := abs_sub _ _
        _ ≤ 2 * Real.exp L := by linarith
        _ = 2 * Real.exp (2 * L) * Real.exp (-L) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ 2 * Real.exp (2 * L) * |q0| := mul_le_mul_of_nonneg_left hq.1 (by positivity)
    have hd1 : |df1 / f1| ≤ 2 * Real.exp (2 * L) := (abs_div_le_of_inScale hdf1 h1).trans (by
      have := Real.exp_pos (2 * L); linarith)
    exact comb _ _ _ _ hd1 (q _ _ _ hdf hdA0 h0) (fun m => q _ _ _ hdf (hdB0 m) (hm m)) s22

end FormalBounds

section FormalBoundsTime

variable {κ : ℝ} {n : ℕ} {r : Fin n → ℝ} {L : ℝ}

/-- **The time-part functions are bounded at scale `L`.** -/
theorem abs_dualLogTime_le (hL : 0 ≤ L) {A21 lF A20 dA21 dL dA20 : ℝ} {B0 B1 dB0 dB1 : Fin n → ℝ}
    (h21 : InScale L A21) (hB1 : ∀ m, InScale L (B1 m)) (h2m : ∀ m, InScale L (A20 - B0 m))
    (hmk : ∀ m k, m ≠ k → InScale L (B0 m - B0 k)) (hlF : |lF| ≤ Real.exp L) (hd21 : |dA21| ≤ Real.exp L)
    (hdL : |dL| ≤ Real.exp L) (hd20 : |dA20| ≤ Real.exp L) (hdB0 : ∀ m, |dB0 m| ≤ Real.exp L)
    (hdB1 : ∀ m, |dB1 m| ≤ Real.exp L) :
    |dualLogTime κ r A21 lF A20 B0 B1| ≤ coefTot κ r * scaleBound L ∧
      |dualLogTimeT κ r A21 A20 B0 B1 dA21 dL dA20 dB0 dB1| ≤ coefTot κ r * scaleBound L := by
  obtain ⟨h1, h2, -, hc0⟩ := coefTot_ge (κ := κ) (r := r)
  obtain ⟨sL, s1, s2, s22, -, -, sLe⟩ := le_scaleBound hL
  have hex := Real.exp_pos L
  have he2 := Real.exp_pos (2 * L)
  have hle1 : Real.exp L ≤ 2 * Real.exp (2 * L) := by
    have := Real.exp_le_exp.2 (show L ≤ 2 * L by linarith); linarith
  have hlogle : L ≤ L + Real.exp L := by linarith
  -- a generic combination
  have comb : ∀ (X Y : ℝ) (Z1 Z2 : Fin n → ℝ) (P : Fin n → Fin n → ℝ) (B : ℝ), |X| ≤ B → |Y| ≤ B →
      (∀ m, |Z1 m| ≤ B) → (∀ m, |Z2 m| ≤ B) → (∀ m k, m < k → |P m k| ≤ B) → B ≤ scaleBound L →
      |(3 * κ - 8) / 16 * X - dualLambda κ * Y + ∑ m, (dualGamma κ (r m) * Z1 m + -(κ / 4) * r m * Z2 m)
        + pairSum (fun m k => dualDelta κ (r m) (r k) * P m k)| ≤ coefTot κ r * scaleBound L := by
    intro X Y Z1 Z2 P B hX hY hZ1 hZ2 hP hB
    have hB0 : 0 ≤ B := (abs_nonneg _).trans hX
    have e1 : |(3 * κ - 8) / 16 * X| ≤ |(3 * κ - 8) / 16| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hX (abs_nonneg _)
    have e2 : |dualLambda κ * Y| ≤ |dualLambda κ| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hY (abs_nonneg _)
    have e3 : |∑ m, (dualGamma κ (r m) * Z1 m + -(κ / 4) * r m * Z2 m)| ≤
        (∑ m, (|r m| + |dualGamma κ (r m)| + |κ / 4 * r m|)) * B := by
      rw [Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      have a1 : |dualGamma κ (r m) * Z1 m| ≤ |dualGamma κ (r m)| * B := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hZ1 m) (abs_nonneg _)
      have a2 : |-(κ / 4) * r m * Z2 m| ≤ |κ / 4 * r m| * B := by
        rw [abs_mul, show -(κ / 4) * r m = -(κ / 4 * r m) by ring, abs_neg]
        exact mul_le_mul_of_nonneg_left (hZ2 m) (abs_nonneg _)
      have a3 := abs_nonneg (r m)
      calc _ ≤ |dualGamma κ (r m) * Z1 m| + |-(κ / 4) * r m * Z2 m| := abs_add_le _ _
        _ ≤ (|r m| + |dualGamma κ (r m)| + |κ / 4 * r m|) * B := by nlinarith
    have e4 : |pairSum (fun m k => dualDelta κ (r m) (r k) * P m k)| ≤
        pairSum (fun m k => |dualDelta κ (r m) (r k)|) * B := by
      rw [← pairSum_mul_const]
      refine abs_pairSum_le fun m k hmk => ?_
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hP m k hmk) (abs_nonneg _)
    have hsum : |(3 * κ - 8) / 16 * X - dualLambda κ * Y + ∑ m, (dualGamma κ (r m) * Z1 m + -(κ / 4) * r m * Z2 m)
        + pairSum (fun m k => dualDelta κ (r m) (r k) * P m k)| ≤ coefTot κ r * B := by
      have t1 := abs_add_le ((3 * κ - 8) / 16 * X - dualLambda κ * Y +
        ∑ m, (dualGamma κ (r m) * Z1 m + -(κ / 4) * r m * Z2 m)) (pairSum (fun m k => dualDelta κ (r m) (r k) * P m k))
      have t2 := abs_add_le ((3 * κ - 8) / 16 * X - dualLambda κ * Y)
        (∑ m, (dualGamma κ (r m) * Z1 m + -(κ / 4) * r m * Z2 m))
      have t3 := abs_sub ((3 * κ - 8) / 16 * X) (dualLambda κ * Y)
      unfold coefTot
      nlinarith [abs_nonneg (dualAlpha κ)]
    exact hsum.trans (mul_le_mul_of_nonneg_left hB hc0)
  refine ⟨?_, ?_⟩
  · refine comb _ _ _ _ _ (L + Real.exp L) ((abs_log_le_of_inScale h21).trans hlogle) (by linarith)
      (fun m => (abs_log_le_of_inScale (hB1 m)).trans hlogle)
      (fun m => (abs_log_le_of_inScale (h2m m)).trans hlogle)
      (fun m k hlt => (abs_log_le_of_inScale (hmk m k hlt.ne)).trans hlogle) sLe
  · have q : ∀ (p1 p2 q0 : ℝ), |p1| ≤ Real.exp L → |p2| ≤ Real.exp L → InScale L q0 →
        |(p1 - p2) / q0| ≤ 2 * Real.exp (2 * L) := fun p1 p2 q0 hp1 hp2 hq => by
      have hq0 : 0 < |q0| := lt_of_lt_of_le (Real.exp_pos _) hq.1
      rw [abs_div, div_le_iff₀ hq0]
      calc |p1 - p2| ≤ |p1| + |p2| := abs_sub _ _
        _ ≤ 2 * Real.exp L := by linarith
        _ = 2 * Real.exp (2 * L) * Real.exp (-L) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ 2 * Real.exp (2 * L) * |q0| := mul_le_mul_of_nonneg_left hq.1 (by positivity)
    refine comb _ _ _ _ _ (2 * Real.exp (2 * L)) ((abs_div_le_of_inScale hd21 h21).trans (by linarith))
      (hdL.trans hle1) (fun m => (abs_div_le_of_inScale (hdB1 m) (hB1 m)).trans (by linarith))
      (fun m => q _ _ _ hd20 (hdB0 m) (h2m m)) (fun m k hlt => q _ _ _ (hdB0 m) (hdB0 k) (hmk m k hlt.ne)) s22

end FormalBoundsTime

/-! ### Assembly: the log-field of `M̃` on a frozen-center piece -/

/-- The cut-off scale `ρ_c = min (clrRad r a₀/24) (γ/768)` of a frozen-center piece. -/
def cutRad (r a₀ γ : ℝ) : ℝ := min (clrRad r a₀ / 24) (γ / 768)

/-- The rate bound `C_F = ¼(384/(r a₀))² + ⅙ · 3072/(r² a₀)` for `∂_t log F`. -/
def rateBound (r a₀ : ℝ) : ℝ := 1 / 4 * (384 / (r * a₀)) ^ 2 + 1 / 6 * (3072 / (r ^ 2 * a₀))

/-- **The numerical conditions on the scale `L`** given the (D9) constants. -/
structure ScaleOK (r a₀ γ Γ lam T L : ℝ) : Prop where
  L0 : 0 ≤ L
  la : lam ≤ L
  a : Real.exp (-L) ≤ a₀ / 2
  g : Real.exp (-L) ≤ γ / 2
  c96 : 96 ≤ Real.exp L
  r2 : 384 / r ≤ Real.exp L
  r3 : 3072 / r ^ 2 ≤ Real.exp L
  r4 : 49152 / r ^ 3 ≤ Real.exp L
  G : Γ + γ / 2 ≤ Real.exp L
  D : 24 * 96 ^ 2 / (clrRad r a₀ * a₀) ≤ Real.exp L
  D' : 96 * 96 ^ 2 / (clrRad r a₀ ^ 2 * a₀) ≤ Real.exp L
  g2 : 2 / γ ≤ Real.exp L
  gl : 2 * Real.exp lam / γ ^ 2 ≤ Real.exp L
  rate : rateBound r a₀ ≤ Real.exp L
  logF : T * rateBound r a₀ ≤ Real.exp L

end InteractingSLE.ZhanGT4
