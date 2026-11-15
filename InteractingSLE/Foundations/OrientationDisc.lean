/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.OrientationWinding
import QuantumZipper.Proofs.Complex.BasicsUnivalent

/-!
# A univalent map of the closed disc preserves orientation: the boundary loop winds once

Packet PROVE-ORIENT. Let `g` be continuous and injective on the closed unit disc and holomorphic on the open disc.
Then the image `t ↦ g (e^{2πit})` of the positively oriented unit circle winds **once, positively**, about every point
`g w₀`, `|w₀| < 1` (`windNum_comp_circleMap_one_eq_one`). This is the orientation of the boundary correspondence of a
Riemann map with a Carathéodory extension (the reflected map `w ↦ conj (g w)` has every topological property of `g`,
and its loop winds `−1` times).

## Proof

* **Small circles** (`windNum_comp_circleMap_eq_one_of_lt`): for `|w₀| < r < 1`, the homotopy
  `H(t, s) = (c t - w₀) · dslope g w₀ (w₀ + s (c t - w₀))`, `c t = r e^{2πit}`, runs in `ℂ \ {0}` (injectivity, and
  `g'(w₀) ≠ 0`, QuantumZipper's `deriv_ne_zero_of_injOn`) from `t ↦ (c t - w₀) g'(w₀)` (degree `1`, Rouché against
  `t ↦ c t · g'(w₀)`) to `t ↦ g (c t) - g w₀` (QuantumZipper's `loopDeg_homotopy`).
* **The boundary circle**: `g` is uniformly continuous on the compact closed disc, so for `r` close to `1` the loop at
  radius `r` stays closer to the boundary loop than the boundary loop is to `g w₀` (Rouché,
  `windNum_eq_of_norm_sub_lt'`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

open QuantumZipper.CA.Topo (loopDeg loopDeg_homotopy loopDeg_eq_of_norm_sub_lt loopDeg_unique slice)

namespace InteractingSLE.Orientation

/-- The circle `t ↦ r e^{2πit}` as a loop on `[0, 1]`. -/
theorem circleMap_two_pi_one (r : ℝ) : circleMap 0 r (2 * π * 1) = circleMap 0 r (2 * π * 0) := by
  simpa using periodic_circleMap 0 r 0

theorem norm_circleMap_zero' {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
  rw [norm_circleMap_zero, abs_of_nonneg hr]

/-- **The degree of `t ↦ (c t - w₀) d`** is `1` for `|w₀| < r` and `d ≠ 0`, `c t = r e^{2πit}`. -/
theorem loopDeg_circle_sub_mul {r : ℝ} (hr : 0 < r) {w₀ d : ℂ} (hw₀ : ‖w₀‖ < r) (hd : d ≠ 0)
    (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t = (circleMap 0 r (2 * π * (t : ℝ)) - w₀) * d)
    (hγ0 : ∀ t, γ t ≠ 0) : loopDeg γ hγ0 = 1 := by
  have hrd : (r : ℂ) * d ≠ 0 := mul_ne_zero (by exact_mod_cast hr.ne') hd
  let δ : C(unitInterval, ℂ) := ⟨fun t => circleMap 0 r (2 * π * (t : ℝ)) * d, by unfold circleMap; fun_prop⟩
  have hδ0 : ∀ t, δ t ≠ 0 := fun t => mul_ne_zero (circleMap_ne_center hr.ne') hd
  have hγc : γ 0 = γ 1 := by rw [hγ, hγ]; simp only [Set.Icc.coe_zero, Set.Icc.coe_one, circleMap_two_pi_one]
  have hδc : δ 0 = δ 1 := by
    change circleMap 0 r (2 * π * ((0 : unitInterval) : ℝ)) * d = circleMap 0 r (2 * π * ((1 : unitInterval) : ℝ)) * d
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one, circleMap_two_pi_one]
  rw [loopDeg_eq_of_norm_sub_lt γ δ hγ0 hδ0 hγc hδc fun t => ?_]
  · refine loopDeg_unique δ hδ0 hδc (L := fun t => log ((r : ℂ) * d) + (2 * π * (t : ℝ) : ℝ) * I)
      (by fun_prop) (fun t => ?_) (n := 1) ?_
    · change exp (log ((r : ℂ) * d) + (2 * π * (t : ℝ) : ℝ) * I) = circleMap 0 r (2 * π * (t : ℝ)) * d
      rw [exp_add, exp_log hrd, circleMap]
      push_cast
      ring
    · simp
  · rw [hγ t]
    change ‖(circleMap 0 r (2 * π * (t : ℝ)) - w₀) * d - circleMap 0 r (2 * π * (t : ℝ)) * d‖ <
      ‖circleMap 0 r (2 * π * (t : ℝ)) * d‖
    rw [show (circleMap 0 r (2 * π * (t : ℝ)) - w₀) * d - circleMap 0 r (2 * π * (t : ℝ)) * d = -w₀ * d by ring,
      norm_mul, norm_mul, norm_neg, norm_circleMap_zero' hr.le]
    exact mul_lt_mul_of_pos_right hw₀ (norm_pos_iff.2 hd)

variable {g : ℂ → ℂ}

/-- **Small circles wind once**: for `g` holomorphic and injective on the open unit disc and `|w₀| < r < 1`, the loop
`t ↦ g (r e^{2πit})` winds once about `g w₀`. -/
theorem windNum_comp_circleMap_eq_one_of_lt (hgd : DifferentiableOn ℂ g (ball 0 1)) (hgi : InjOn g (ball 0 1))
    {w₀ : ℂ} {r : ℝ} (hw₀r : ‖w₀‖ < r) (hr1 : r < 1) :
    windNum (fun t : ℝ => g (circleMap 0 r (2 * π * t))) (g w₀) = 1 := by
  have hr : 0 < r := (norm_nonneg w₀).trans_lt hw₀r
  have hw₀ : w₀ ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; linarith
  have hn : ball (0 : ℂ) 1 ∈ 𝓝 w₀ := isOpen_ball.mem_nhds hw₀
  have hds : ContinuousOn (dslope g w₀) (ball 0 1) :=
    (continuousOn_dslope hn).2 ⟨hgd.continuousOn, hgd.differentiableAt hn⟩
  have hd0 : deriv g w₀ ≠ 0 := QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hgd hgi hw₀
  set c : ℝ → ℂ := fun t => circleMap 0 r (2 * π * t) with hcdef
  have hcc : Continuous c := by rw [hcdef]; unfold circleMap; fun_prop
  have hcn : ∀ t, ‖c t‖ = r := fun t => norm_circleMap_zero' hr.le _
  have hcw : ∀ t, c t - w₀ ≠ 0 := fun t h => by
    have := hcn t; rw [sub_eq_zero.1 h] at this; linarith
  -- the segment from `w₀` to `c t` stays in the disc
  have hseg : ∀ (t : ℝ) (s : unitInterval), w₀ + (s : ℝ) • (c t - w₀) ∈ ball (0 : ℂ) 1 := fun t s => by
    have h1 := (convex_closedBall (0 : ℂ) r).add_smul_sub_mem (mem_closedBall_zero_iff.2 hw₀r.le)
      (mem_closedBall_zero_iff.2 (hcn t).le) s.2
    exact closedBall_subset_ball hr1 h1
  have hdsl : ∀ (t : ℝ) (s : unitInterval), dslope g w₀ (w₀ + (s : ℝ) • (c t - w₀)) ≠ 0 := fun t s => by
    by_cases hs : w₀ + (s : ℝ) • (c t - w₀) = w₀
    · rw [hs, dslope_same]; exact hd0
    · rw [dslope_of_ne _ hs, slope_def_field]
      refine div_ne_zero (sub_ne_zero.2 fun he => hs (hgi (hseg t s) hw₀ he)) (sub_ne_zero.2 hs)
  let Hm : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun q => (c q.1 - w₀) * dslope g w₀ (w₀ + (q.2 : ℝ) • (c q.1 - w₀)), by
      refine ((hcc.comp (continuous_subtype_val.comp continuous_fst)).sub continuous_const).mul ?_
      exact hds.comp_continuous (by fun_prop) fun q => hseg q.1 q.2⟩
  have hH0 : ∀ q, Hm q ≠ 0 := fun q => mul_ne_zero (hcw _) (hdsl _ _)
  have hHc : ∀ s, Hm (0, s) = Hm (1, s) := fun s => by
    change (c ((0 : unitInterval) : ℝ) - w₀) * dslope g w₀ (w₀ + (s : ℝ) • (c ((0 : unitInterval) : ℝ) - w₀)) =
      (c ((1 : unitInterval) : ℝ) - w₀) * dslope g w₀ (w₀ + (s : ℝ) • (c ((1 : unitInterval) : ℝ) - w₀))
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one, hcdef, circleMap_two_pi_one]
  have hhom := loopDeg_homotopy Hm hH0 hHc
  -- the end `s = 0`
  have hdeg0 : loopDeg (slice Hm 0) (fun _ => hH0 _) = 1 :=
    loopDeg_circle_sub_mul hr hw₀r hd0 _ (fun t => by
      change (c t - w₀) * dslope g w₀ (w₀ + ((0 : unitInterval) : ℝ) • (c t - w₀)) = _
      rw [Set.Icc.coe_zero, zero_smul, add_zero, dslope_same]) _
  -- the end `s = 1`
  have hγc : ContinuousOn (fun t : ℝ => g (c t)) (Icc 0 1) :=
    (hgd.continuousOn.comp_continuous hcc fun t => mem_ball_zero_iff.2 ((hcn t).trans_lt hr1)).continuousOn
  have hγw : ∀ t ∈ Icc (0 : ℝ) 1, g (c t) ≠ g w₀ := fun t _ he =>
    hcw t (sub_eq_zero.2 (hgi (mem_ball_zero_iff.2 ((hcn t).trans_lt hr1)) hw₀ he))
  have he1 : slice Hm 1 = shiftLoop (fun t : ℝ => g (c t)) hγc (g w₀) := by
    ext t
    change (c t - w₀) * dslope g w₀ (w₀ + ((1 : unitInterval) : ℝ) • (c t - w₀)) = g (c t) - g w₀
    rw [Set.Icc.coe_one, one_smul, add_sub_cancel]
    exact sub_smul_dslope g w₀ (c t)
  rw [windNum_eq_loopDeg hγc hγw, ← loopDeg_congr he1 (fun _ => hH0 _), ← hhom, hdeg0]

/-- **A univalent map of the closed disc preserves orientation.** For `g` continuous and injective on the closed unit
disc and holomorphic on the open disc, the boundary loop `t ↦ g (e^{2πit})` winds once about `g w₀`, `|w₀| < 1`. -/
theorem windNum_comp_circleMap_one_eq_one (hgc : ContinuousOn g (closedBall 0 1))
    (hgd : DifferentiableOn ℂ g (ball 0 1)) (hgi : InjOn g (closedBall 0 1)) {w₀ : ℂ} (hw₀ : w₀ ∈ ball (0 : ℂ) 1) :
    windNum (fun t : ℝ => g (circleMap 0 1 (2 * π * t))) (g w₀) = 1 := by
  have hw₀' : ‖w₀‖ < 1 := mem_ball_zero_iff.1 hw₀
  have hcm : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → ∀ t : ℝ, circleMap 0 r (2 * π * t) ∈ closedBall (0 : ℂ) 1 := fun h0 h1 t =>
    mem_closedBall_zero_iff.2 ((norm_circleMap_zero' h0 _).trans_le h1)
  have hloop : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → ContinuousOn (fun t : ℝ => g (circleMap 0 r (2 * π * t))) (Icc 0 1) :=
    fun h0 h1 => (hgc.comp_continuous (by unfold circleMap; fun_prop) (hcm h0 h1)).continuousOn
  have hcl : ∀ r : ℝ, (fun t : ℝ => g (circleMap 0 r (2 * π * t))) 0 = (fun t : ℝ => g (circleMap 0 r (2 * π * t))) 1 :=
    fun r => by simp only [circleMap_two_pi_one]
  -- the boundary loop stays at distance `≥ m > 0` from `g w₀`
  have hK := (isCompact_image_Icc (hloop zero_le_one le_rfl)).isClosed
  have hnot : g w₀ ∉ (fun t : ℝ => g (circleMap 0 1 (2 * π * t))) '' Icc 0 1 := by
    rintro ⟨t, -, ht⟩
    have := hgi (hcm zero_le_one le_rfl t) (ball_subset_closedBall hw₀) ht
    have h1 := norm_circleMap_zero' zero_le_one (2 * π * t)
    rw [this] at h1
    linarith
  obtain ⟨m, hm, hmK⟩ := exists_ball_disjoint hK hnot
  -- uniform continuity on the closed disc
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hgc) m hm
  set r := max ((‖w₀‖ + 1) / 2) (1 - δ / 2) with hrdef
  have hr1 : r < 1 := max_lt (by linarith) (by linarith)
  have hw₀r : ‖w₀‖ < r := lt_max_of_lt_left (by linarith)
  have hr0 : 0 ≤ r := (norm_nonneg w₀).trans hw₀r.le
  have h1r : 1 - r < δ := by have := le_max_right ((‖w₀‖ + 1) / 2) (1 - δ / 2); linarith
  rw [← windNum_eq_of_norm_sub_lt' (hloop hr0 hr1.le) (hloop zero_le_one le_rfl) (hcl r) (hcl 1) fun t _ => ?_]
  · exact windNum_comp_circleMap_eq_one_of_lt (hgd.mono subset_rfl)
      (hgi.mono ball_subset_closedBall) hw₀r hr1
  · have hdist : dist (circleMap 0 r (2 * π * t)) (circleMap 0 1 (2 * π * t)) < δ := by
      rw [dist_eq_norm, circleMap, circleMap, zero_add, zero_add, ← sub_mul, norm_mul, norm_exp_ofReal_mul_I,
        mul_one, show ((r : ℂ) - ((1 : ℝ) : ℂ)) = ((r - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    have h1 := hδg _ (hcm hr0 hr1.le t) _ (hcm zero_le_one le_rfl t) hdist
    rw [dist_eq_norm] at h1
    exact h1.trans_le (hmK _ (mem_image_of_mem _ ⟨‹t ∈ Icc (0 : ℝ) 1›.1, ‹t ∈ Icc (0 : ℝ) 1›.2⟩))

end InteractingSLE.Orientation
