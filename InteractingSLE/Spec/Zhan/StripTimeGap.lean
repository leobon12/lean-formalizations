/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalPath
import InteractingSLE.Foundations.Strip.SLE

/-!
# The lower left marks stay strictly right of the end mark on the strip life

Packet PROVE-ZHAN-A2. In the R36 form of a strip evolution (`Foundations/Strip/SLE.lean`) the end `−∞` of the strip
is the outermost chordal left mark `v = V^{L, last}` (started at `−1`), and a lower left strip mark `p` is the
chordal left mark started at `e^p − 1 ∈ (−1, 0)`. Its strip coordinate `t + log (V − v)` (`Strip.stripPoint`) needs
`V − v > 0`. Before the end mark meets the driver this holds: the gap `y = V − v` solves the linear equation

  `y' = 2/(V − W) − 2/(v − W) = −c y`,  `c = 2/((W − V)(W − v)) ≥ 0`,

off the null collision set of `V`, with `c` integrable (the reciprocal gap `(W − V)⁻¹` is integrable and `W − v` is
continuous and positive), so `y_t = y_0 exp(−∫₀ᵗ c) > 0` (`eq_mul_exp_neg_integral`, by the vanishing derivative of
the absolutely continuous function `y e^{∫c}`).

## Main results

* `Zhan.eq_mul_exp_neg_integral`: the linear equation `y = y₀ + ∫ f`, `f = −c y` a.e., with integrable `c`, has
  `y_r = y₀ exp(−∫₀ʳ c)`;
* `Sec2.IsForcePath.vL_lt_vL_of_lt`: for left marks `i`, `j` with `x_j < x_i`, if `V^j < W` on `[0, t]`, `t < ζ`,
  then `V^j_t < V^i_t`;
* `Strip.vL_last_lt_vL_castSucc`: on the strip life of an R36 strip path, `v < V^{L, i}` for every lower left mark.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

/-- The exponential of an absolutely continuous function is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_exp_comp {g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (g x)) a b := by
  obtain ⟨M, hM⟩ :=
    (isCompact_uIcc.image_of_continuousOn hg.continuousOn).isBounded.subset_closedBall 0
  have hlip : LipschitzOnWith (Real.exp M).toNNReal Real.exp (Icc (-M) M) := by
    refine (convex_Icc (-M) M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) fun x hx => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x),
      Real.coe_toNNReal _ (Real.exp_pos M).le]
    exact Real.exp_le_exp.2 hx.2
  refine hlip.comp_absolutelyContinuousOnInterval (fun x hx => ?_) hg
  have := hM (mem_image_of_mem g hx)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact ⟨by linarith [neg_abs_le (g x)], (le_abs_self _).trans this⟩

/-- **A linear equation with an integrable coefficient.** If `y_r = y_0 + ∫₀ʳ f` on `[0, S]` and `f = −c y` almost
everywhere on `[0, S]`, with `f` and `c` integrable, then `y_r = y_0 exp(−∫₀ʳ c)` on `[0, S]`. -/
theorem eq_mul_exp_neg_integral {y f c : ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    (hf : IntervalIntegrable f volume 0 S) (hc : IntervalIntegrable c volume 0 S)
    (hy : ∀ r ∈ Icc 0 S, y r = y 0 + ∫ u in (0 : ℝ)..r, f u)
    (hfc : ∀ᵐ u ∂volume, u ∈ Icc 0 S → f u = -(c u * y u)) :
    ∀ r ∈ Icc 0 S, y r = y 0 * Real.exp (-∫ u in (0 : ℝ)..r, c u) := by
  set F : ℝ → ℝ := fun r => ∫ u in (0 : ℝ)..r, f u with hFdef
  set C : ℝ → ℝ := fun r => ∫ u in (0 : ℝ)..r, c u with hCdef
  have hI : uIcc (0 : ℝ) S = Icc 0 S := uIcc_of_le hS
  have h0 : (0 : ℝ) ∈ uIcc 0 S := by rw [hI]; exact ⟨le_rfl, hS⟩
  have hFac : AbsolutelyContinuousOnInterval F 0 S :=
    hf.absolutelyContinuousOnInterval_intervalIntegral h0
  have hCac : AbsolutelyContinuousOnInterval C 0 S :=
    hc.absolutelyContinuousOnInterval_intervalIntegral h0
  have hYac : AbsolutelyContinuousOnInterval (fun r => y 0 + F r) 0 S :=
    ((LipschitzWith.const (y 0)).comp_absolutelyContinuousOnInterval hFac).add hFac
  have hZac : AbsolutelyContinuousOnInterval (fun r => (y 0 + F r) * Real.exp (C r)) 0 S :=
    hYac.mul (absolutelyContinuousOnInterval_exp_comp hCac)
  have hder : ∀ᵐ x, x ∈ uIcc (0 : ℝ) S →
      HasDerivAt (fun r => (y 0 + F r) * Real.exp (C r)) 0 x := by
    filter_upwards [hf.ae_hasDerivAt_integral, hc.ae_hasDerivAt_integral, hfc] with x h1 h2 h3 hx
    have hxI : x ∈ Icc 0 S := by rw [← hI]; exact hx
    refine (((h1 hx 0 h0).const_add (y 0)).mul (h2 hx 0 h0).exp).congr_deriv ?_
    rw [h3 hxI, hy x hxI]
    ring
  obtain ⟨K, hK⟩ := hZac.const_of_ae_hasDerivAt_zero hder
  have hK0 : K = y 0 := by
    have := hK 0 h0
    simp only [hFdef, hCdef, intervalIntegral.integral_same, add_zero, Real.exp_zero,
      mul_one] at this
    exact this.symm
  intro r hr
  have h1 := hK r (by rw [hI]; exact hr)
  rw [hK0, ← hy r hr] at h1
  have hpos := Real.exp_pos (C r)
  rw [Real.exp_neg]
  field_simp
  linarith [h1]

end Zhan

namespace Sec2

namespace IsForcePath

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The two-mark algebra: off a collision of `a` with `w`, `2/(a − w) − 2/(v − w) = −(2/((w − a)(w − v)))(a − v)`. -/
theorem two_div_sub_sub_two_div_sub {a v w : ℝ} (ha : a ≠ w) (hv : v ≠ w) :
    2 / (a - w) - 2 / (v - w) = -(2 / ((w - a) * (w - v)) * (a - v)) := by
  have h1 : a - w ≠ 0 := sub_ne_zero.2 ha
  have h2 : v - w ≠ 0 := sub_ne_zero.2 hv
  have h3 : w - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have h4 : w - v ≠ 0 := sub_ne_zero.2 (Ne.symm hv)
  field_simp
  ring

/-- **Left marks keep their order while the outer one is left of the driver.** For left marks `i`, `j` with
`x_j < x_i`, if `V^j < W` on `[0, t]` and `t < ζ`, then `V^j_t < V^i_t`; indeed
`V^i_t − V^j_t = (x_i − x_j) exp(−∫₀ᵗ 2/((W − V^i)(W − V^j)))`. -/
theorem vL_lt_vL_of_lt (h : IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    {i j : Fin nL} (hx : xL j < xL i) (hjw : ∀ r ≤ t, vL j r < w r) : vL j t < vL i t := by
  set y : ℝ → ℝ := fun r => vL i r.toNNReal - vL j r.toNNReal with hydef
  set f : ℝ → ℝ := fun r => 2 / (vL i r.toNNReal - w r.toNNReal) - 2 / (vL j r.toNNReal - w r.toNNReal)
    with hfdef
  set c : ℝ → ℝ := fun r => 2 / ((w r.toNNReal - vL i r.toNNReal) * (w r.toNNReal - vL j r.toNNReal))
    with hcdef
  have hf : IntervalIntegrable f volume 0 t :=
    (h.intervalIntegrable_forceL ht i).sub (h.intervalIntegrable_forceL ht j)
  have hcont : ContinuousOn (fun r : ℝ => (w r.toNNReal - vL j r.toNNReal)⁻¹) (uIcc 0 (t : ℝ)) := by
    rw [uIcc_of_le t.coe_nonneg]
    have hsub : MapsTo Real.toNNReal (Icc 0 (t : ℝ)) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := fun r hr =>
      toNNReal_lt_of_mem_Icc ht hr
    refine (((h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hsub).sub
      ((h.continuousOn_vL j).comp continuous_real_toNNReal.continuousOn hsub))).inv₀ fun r hr => ?_
    exact (sub_pos.2 (hjw _ (toNNReal_le_of_mem_Icc hr))).ne'
  have hc : IntervalIntegrable c volume 0 t := by
    have := ((h.integrable_gapL ht i).mul_continuousOn hcont).const_mul 2
    refine this.congr fun r _ => ?_
    simp only [hcdef, mul_inv, div_eq_mul_inv]
  have hy : ∀ r ∈ Icc 0 (t : ℝ), y r = y 0 + ∫ u in (0 : ℝ)..r, f u := by
    intro r hr
    have hr' := toNNReal_lt_of_mem_Icc ht hr
    have hr0 : ((0 : ℝ).toNNReal : ℝ≥0∞) < ζ := by
      simpa using lt_of_le_of_lt (zero_le (a := (t : ℝ≥0∞))) ht
    have hri : IntervalIntegrable (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) volume 0
        (r.toNNReal : ℝ) := h.intervalIntegrable_forceL hr' i
    have hrj : IntervalIntegrable (fun s : ℝ => 2 / (vL j s.toNNReal - w s.toNNReal)) volume 0
        (r.toNNReal : ℝ) := h.intervalIntegrable_forceL hr' j
    rw [Real.coe_toNNReal _ hr.1] at hri hrj
    have ei := h.vL_eq hr' i
    have ej := h.vL_eq hr' j
    rw [Real.coe_toNNReal _ hr.1] at ei ej
    simp only [hydef, hfdef, Real.toNNReal_zero, h.vL_zero]
    rw [intervalIntegral.integral_sub hri hrj, ei, ej]
    ring
  have hfc : ∀ᵐ u ∂volume, u ∈ Icc 0 (t : ℝ) → f u = -(c u * y u) := by
    have hnull := h.volume_collisionL i
    have : ∀ᵐ u ∂volume, u ∉ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
        w s.toNNReal = vL i s.toNNReal} := by
      rw [ae_iff]; simpa using hnull
    filter_upwards [this] with u hu hut
    have hne : vL i u.toNNReal ≠ w u.toNNReal := fun he =>
      hu ⟨hut.1, toNNReal_lt_of_mem_Icc ht hut, he.symm⟩
    have hjne : vL j u.toNNReal ≠ w u.toNNReal := (hjw _ (toNNReal_le_of_mem_Icc hut)).ne
    simp only [hfdef, hcdef, hydef]
    exact two_div_sub_sub_two_div_sub hne hjne
  have he := Zhan.eq_mul_exp_neg_integral t.coe_nonneg hf hc hy hfc t ⟨t.coe_nonneg, le_rfl⟩
  have hy0 : y 0 = xL i - xL j := by simp [hydef, h.vL_zero]
  have hyt : y t = vL i t - vL j t := by simp [hydef]
  rw [hyt, hy0] at he
  have : 0 < vL i t - vL j t := by rw [he]; exact mul_pos (sub_pos.2 hx) (Real.exp_pos _)
  linarith

end IsForcePath

end Sec2

namespace Strip

variable {nL nR : ℕ}

/-- **On the strip life the lower left marks stay strictly right of the end mark** (R36 form: the end mark is the
last chordal left mark, started at `−1`; a lower left mark starts at `e^p − 1 > −1`). -/
theorem vL_last_lt_vL_castSucc {a : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a (wordXL pL) xR ρL ρR w vL vR b ζ) {s : ℝ≥0}
    (hs : IsStripLife w (vL (Fin.last nL)) ζ s) (i : Fin nL) :
    vL (Fin.last nL) s < vL i.castSucc s := by
  refine hp.isForcePath.vL_lt_vL_of_lt hs.1 ?_ hs.2
  simp only [wordXL_last, wordXL_castSucc]
  linarith [Real.exp_pos (pL i)]

end Strip

end InteractingSLE
