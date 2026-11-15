/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartTrace
import InteractingSLE.WangWu.ReverseContactBdryChart

/-!
# Aux. lemma 8 for an obstacle reaching `∞`: the counterflow in the chart of the flow-line prefix

Packet PROVE-GLUECOND3 (item G3 (ii), Lemma 4.7 direction). Specification §4.2, proof of Lemma 4.7
(`source/spec/p097-144.md#lem-4.7-proof`, pp. 117–118): "The map from `𝒮 ∖ η([0, τ])` back to `𝒮` extends analytically
across the untouched upper boundary, including the counterflow starting point … Proposition 6.12 consequently applies
after a half-plane coordinate change and gives a continuous driver up to the first contact in question."

In the chart `R` (`R z = −1/z`) the counterflow is a chordal Loewner chain `K′_t` of a continuous driver `Wβ` from `0`,
and the flow-line prefix is the set `R(K_q)`, `K_q` the hull of the flow driver `Wα` at time `q` in the chart `Q`. The
chart of `ℍ ∖ R(K_q)` is `Ψ_q = R ∘ f_q ∘ R` (`WangWu.revChart Wα q`: `0` fixed, the flow tip sent to `∞`). The obstacle
`R(K_q)` is unbounded, so Aux. lemma 8 (`ConformalImageFull.exists_loewner_image`, a compact hull mapped out at `∞`)
does not apply directly. This file proves the conformal-image statement for it by a half-plane coordinate change:

  `Ψ_q = N ∘ (g_A ∘ m₁ − x₁)`, `m₁(w) = 1/(C − w)`, `A = m₁(R(K_q)) = M(K_q)`, `M(z) = z/(Cz + 1)`,

with `C > 0` so large that the pole `C` of `m₁` is far from `K′_T`; `A` is the hull of a Loewner chain by the Möbius
image theorem (`CrossRestart.exists_loewner_mobius_image`, needs `−1/C ∉ closure K_q`), `g_A` is handled by Aux. lemma 8
with arbitrary start, `x₁ = g_A(1/C)` is the start of the image chain, and `N` is the real Möbius map with
`Ψ_q = N ∘ (g_A ∘ m₁ − x₁)` (`CrossRestart.exists_realMobius_conj`). The properties of `N` that the Möbius image
theorem needs come from boundary values of `f_q`:
* `N(0) = 0`: `Ψ_q(w) → 0` and `g_A(m₁ w) → x₁` as `w → 0` (`b_eq_zero_of_tendsto`);
* `N` moves `∞`: `f_q(R w)` has a nonzero real limit as `w → C` (`CrossRestart`'s `bdryVal_ne`), while
  `g_A(m₁ w) → ∞`;
* the pole of `N` is away from the image hulls: near the pole `f_q(R w) = R(Ψ_q w) → 0`, impossible at a cluster point
  of `K′_T` (`f_q` has a nonzero limit at every nonzero point of `closure ℍ ∖ closure K_q`, and tends to `∞` at `∞`).

## Main results

* `exists_loewner_revChart_image`: if `closure K_q ∩ ℝ ⊆ {0}` and `closure K′_T ∩ closure R(K_q) = ∅`, then
  `t ↦ Ψ_q(K′_t)`, `t ∈ [0, T]`, is a chordal Loewner chain after the continuous strictly increasing capacity clock
  `τ(t) = hcap(Ψ_q(K′_t))/2`, with a continuous driver starting at `0`.
* `isFilling_image_revChart`: fillings are transported by `Ψ_q` (a homeomorphism of `ℍ ∖ R(K_q)` onto `ℍ`).
* `exists_loewner_revChart_trace`: the trace form — for a trace `β` of `K′` (in `ℍ ∪ {0}` at positive times),
  `Ψ_q(K′_t)` is the filling of `Ψ_q(β([0, t]) ∩ ℍ)` and `Ψ_q ∘ β` (with `Ψ_q(0) = 0`, `revChartZ`) is continuous
  on `[0, T]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H fwdHull fwdMap)
open QuantumZipper.CA (realMobius)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux8Inf

open WangWu hiding ratPt exists_ratPt_dist_lt
open CrossRestart ConformalImage ConformalImageFull

/-! ### Möbius algebra -/

section Algebra

theorem ne_zero_of_mem_H' {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h => by
  rw [h] at hz
  exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)

theorem add_ne_zero_of_mem_H {C : ℝ} (hC : 0 < C) {z : ℂ} (hz : z ∈ H) : (C : ℂ) * z + 1 ≠ 0 := fun h => by
  have him := congrArg Complex.im h
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, one_im, zero_im] at him
  have : (0 : ℝ) < C * z.im := mul_pos hC hz
  linarith

/-- `m₁ ∘ R = M`: `1/(C + 1/z) = z/(Cz + 1)`. -/
theorem m₁_negInv {C : ℝ} (hC : 0 < C) {z : ℂ} (hz : z ∈ H) :
    realMobius 0 1 (-1) C (negInv z) = realMobius 1 0 C 1 z := by
  have hz0 := ne_zero_of_mem_H' hz
  have hd := add_ne_zero_of_mem_H hC hz
  simp only [realMobius, negInv, Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg, zero_mul, zero_add,
    add_zero, one_mul, neg_mul, neg_neg]
  have hd' : (z⁻¹ + C : ℂ) ≠ 0 := by
    rw [show (z⁻¹ + C : ℂ) = ((C : ℂ) * z + 1) / z by field_simp; ring]
    exact div_ne_zero hd hz0
  rw [div_eq_div_iff hd' hd]
  field_simp
  ring

/-- `m₁⁻¹ ∘ M = R`: `C − (Cz + 1)/z = −1/z`. -/
theorem m₁inv_M {C : ℝ} (hC : 0 < C) {z : ℂ} (hz : z ∈ H) :
    realMobius C (-1) 1 0 (realMobius 1 0 C 1 z) = negInv z := by
  have hz0 := ne_zero_of_mem_H' hz
  have hd := add_ne_zero_of_mem_H hC hz
  simp only [realMobius, negInv, Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg, add_zero, one_mul]
  have hq : z / ((C : ℂ) * z + 1) ≠ 0 := div_ne_zero hz0 hd
  rw [div_eq_iff hq]
  field_simp
  ring

theorem m₁inv_m₁ {C : ℝ} {w : ℂ} (hw : w ∈ H) : realMobius C (-1) 1 0 (realMobius 0 1 (-1) C w) = w := by
  have h := realMobius_mobInv (a := C) (b := -1) (c := 1) (d := 0) (by norm_num) hw
  simpa only [neg_neg] using h

/-- `m₁` maps `ℍ` into `ℍ`. -/
theorem m₁_mem_H (C : ℝ) {w : ℂ} (hw : w ∈ H) : realMobius 0 1 (-1) C w ∈ H :=
  (QuantumZipper.CA.bijOn_realMobius_H (show (0 : ℝ) < 0 * C - 1 * (-1) by norm_num)).mapsTo hw

/-- `‖m₁ w‖ = 1/‖C − w‖`. -/
theorem norm_m₁ (C : ℝ) (w : ℂ) : ‖realMobius 0 1 (-1) C w‖ = 1 / ‖(C : ℂ) - w‖ := by
  simp only [realMobius, Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg, zero_mul, zero_add, neg_one_mul]
  rw [norm_div, norm_one, neg_add_eq_sub]

/-- A point of `M(K)` is at distance at least `1/(C(C‖z‖ + 1))` from `1/C`. -/
theorem norm_M_sub_le {C : ℝ} (hC : 0 < C) {z : ℂ} (hz : z ∈ H) :
    1 / (C * (C * ‖z‖ + 1)) ≤ ‖realMobius 1 0 C 1 z - ((1 / C : ℝ) : ℂ)‖ := by
  have hd := add_ne_zero_of_mem_H hC hz
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have heq : realMobius 1 0 C 1 z - ((1 / C : ℝ) : ℂ) = -1 / ((C : ℂ) * ((C : ℂ) * z + 1)) := by
    simp only [realMobius, Complex.ofReal_zero, Complex.ofReal_one, add_zero, one_mul, Complex.ofReal_div]
    rw [div_sub_div _ _ hd hC', div_eq_div_iff (mul_ne_zero hd hC') (mul_ne_zero hC' hd)]
    ring
  rw [heq, norm_div, norm_neg, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  have hn : ‖(C : ℂ) * z + 1‖ ≤ C * ‖z‖ + 1 := by
    calc ‖(C : ℂ) * z + 1‖ ≤ ‖(C : ℂ) * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = C * ‖z‖ + 1 := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC, norm_one]
  have hpos : 0 < ‖(C : ℂ) * z + 1‖ := norm_pos_iff.2 hd
  exact one_div_le_one_div_of_le (mul_pos hC hpos) (mul_le_mul_of_nonneg_left hn hC.le)

end Algebra

/-! ### Limits -/

section Limits

/-- **A real Möbius map whose values tend to `0` along points of `ℍ` tending to `0` fixes `0`**: `b = 0`. -/
theorem b_eq_zero_of_tendsto {α : Type*} {F : Filter α} [F.NeBot] {a b c d : ℝ} (hdet : 0 < a * d - b * c)
    {ξ : α → ℂ} (hξ : Tendsto ξ F (𝓝 0)) (hξH : ∀ᶠ x in F, ξ x ∈ H)
    (hN : Tendsto (fun x => realMobius a b c d (ξ x)) F (𝓝 0)) : b = 0 := by
  have hnum : Tendsto (fun x => (a : ℂ) * ξ x + b) F (𝓝 ((a : ℂ) * 0 + b)) :=
    (hξ.const_mul _).add_const _
  have hprod : Tendsto (fun x => realMobius a b c d (ξ x) * ((c : ℂ) * ξ x + d)) F
      (𝓝 (0 * ((c : ℂ) * 0 + d))) := hN.mul ((hξ.const_mul _).add_const _)
  have heq : ∀ᶠ x in F, realMobius a b c d (ξ x) * ((c : ℂ) * ξ x + d) = (a : ℂ) * ξ x + b := by
    filter_upwards [hξH] with x hx
    rw [realMobius, div_mul_cancel₀ _ (QuantumZipper.CA.realMobius_denom_ne_zero hdet hx)]
  have h := tendsto_nhds_unique (hprod.congr' heq) hnum
  rw [zero_mul, mul_zero, zero_add] at h
  exact_mod_cast h.symm

/-- **Near its pole a real Möbius map is large**: `R(N(ξ)) → 0` as `ξ → p = −d/c` through `ℍ`. -/
theorem tendsto_negInv_realMobius_of_tendsto_pole {α : Type*} {F : Filter α} {a b c d : ℝ}
    (hdet : 0 < a * d - b * c) (hc : c ≠ 0) {ξ : α → ℂ} (hξ : Tendsto ξ F (𝓝 (mobPole c d : ℂ)))
    (hξH : ∀ᶠ x in F, ξ x ∈ H) : Tendsto (fun x => negInv (realMobius a b c d (ξ x))) F (𝓝 0) := by
  set p : ℝ := mobPole c d with hp
  have hcp : c * p + d = 0 := mul_mobPole_add hc
  have hap : a * p + b ≠ 0 := by
    intro h
    have hd : d = -(c * p) := by linarith
    have hb : b = -(a * p) := by linarith
    have : a * d - b * c = 0 := by rw [hd, hb]; ring
    linarith
  have hcont : ContinuousAt (fun ζ : ℂ => -(((c : ℂ) * ζ + d) / ((a : ℂ) * ζ + b))) (p : ℂ) := by
    refine (ContinuousAt.div (by fun_prop) (by fun_prop) ?_).neg
    exact_mod_cast hap
  have hval : -(((c : ℂ) * (p : ℂ) + d) / ((a : ℂ) * (p : ℂ) + b)) = 0 := by
    have : (c : ℂ) * (p : ℂ) + d = 0 := by exact_mod_cast hcp
    rw [this, zero_div, neg_zero]
  have h := hcont.tendsto.comp hξ
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [hξH] with x hx
  simp only [Function.comp_apply, negInv, realMobius, inv_div]

/-- **`f_q` has a nonzero limit at every nonzero point of `closure ℍ` off `closure K_q`** (in `ℍ` by continuity; on
`ℝ` the boundary value differs from the driver, `ConformalImageFull.bdryVal_ne`). -/
theorem exists_ne_zero_tendsto_fwdMap {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    {y : ℂ} (hy0 : y ≠ 0) (hyim : 0 ≤ y.im) (hyK : y ∉ closure (fwdHull W q)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fwdMap W q) (𝓝[H] y) (𝓝 L) := by
  obtain ⟨r, hr, hrd⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure |>.mem_nhds hyK)
  rcases hyim.lt_or_eq with hpos | hzero
  · have hyH : y ∈ H \ fwdHull W q := ⟨hpos, fun h => hyK (subset_closure h)⟩
    refine ⟨fwdMap W q y, ne_zero_of_mem_H' (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hq hyH), ?_⟩
    exact ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hq).continuousOn.continuousAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hq).mem_nhds hyH)).tendsto.mono_left nhdsWithin_le_nhds
  · have hyre : ((y.re : ℝ) : ℂ) = y := Complex.ext rfl (by rw [Complex.ofReal_im, ← hzero])
    have hball : Disjoint (ball ((y.re : ℝ) : ℂ) r) (fwdHull W q) := by
      rw [hyre]; exact Set.disjoint_left.2 fun z hz hzK => hrd hz (subset_closure hzK)
    have hre0 : y.re ≠ 0 := fun h => hy0 (by rw [← hyre, h, Complex.ofReal_zero])
    obtain ⟨-, hlim⟩ := bdryVal_spec hW hW0 hq hr hball
    have hne := bdryVal_ne hW hW0 hr hball hre0 (t := q) ⟨hq, le_rfl⟩
    refine ⟨bdryVal W y.re q - W q, sub_ne_zero.2 hne, ?_⟩
    rw [← hyre]
    refine (hlim.sub_const (W q : ℂ)).congr fun z => ?_
    simp only [gmap, add_sub_cancel_right]

/-- `‖w‖ ≤ ‖f_q(w)‖ + K` on `ℍ ∖ K_q`. -/
theorem exists_norm_le_norm_fwdMap {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ H \ fwdHull W q, ‖w‖ ≤ ‖fwdMap W q w‖ + K := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_fwdMap_sub_le hW hW0 hq
  refine ⟨K, hK0, fun w hw => ?_⟩
  have h1 := hK w hw
  have h2 := norm_sub_norm_le w (fwdMap W q w)
  rw [norm_sub_rev] at h2
  linarith

/-- `R(Ψ_q(w)) = f_q(R w)`. -/
theorem negInv_revChart (W : ℝ → ℝ) (q : ℝ) (w : ℂ) : negInv (revChart W q w) = fwdMap W q (negInv w) := by
  rw [revChart, negInv_negInv]

/-- `R(w) ∉ K_q` for `w ∈ ℍ ∖ R(K_q)`. -/
theorem negInv_mem_H_diff {K : Set ℂ} {w : ℂ} (hw : w ∈ H) (hwK : w ∉ negInv '' K) : negInv w ∈ H \ K :=
  ⟨negInv_mem_H hw, fun h => hwK ⟨negInv w, h, negInv_negInv w⟩⟩

end Limits

/-! ### The final Möbius map -/

section Pole

variable {W : ℝ → ℝ}

/-- **The pole of `N` is away from the image hulls** (`Ψ_q = N ∘ φ₁` on a bounded set `S ⊆ ℍ` whose closure misses
that of `R(K_q)`): near the pole `f_q(R s) = R(N(φ₁ s)) → 0`, which is impossible at a cluster point `s*` of `S` —
`f_q` tends to `∞` at `∞` (`s* = 0`) and has a nonzero limit at every other point of `closure ℍ ∖ closure K_q`. -/
theorem exists_disjoint_ball_pole (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q) {S : Set ℂ}
    (hSH : S ⊆ H) (hSb : Bornology.IsBounded S) (hdis : Disjoint (closure S) (closure (negInv '' fwdHull W q)))
    {φ₁ : ℂ → ℂ} (hφH : ∀ s ∈ S, φ₁ s ∈ H) {a b c d : ℝ} (hdet : 0 < a * d - b * c) (hc : c ≠ 0)
    (hΨ : ∀ s ∈ S, revChart W q s = realMobius a b c d (φ₁ s)) :
    ∃ r > 0, Disjoint (ball (mobPole c d : ℂ) r) (φ₁ '' S) := by
  by_contra hcon
  push Not at hcon
  have hmem : (mobPole c d : ℂ) ∈ closure (φ₁ '' S) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨z, hz1, hz2⟩ := Set.not_disjoint_iff.1 (hcon ε hε)
    exact ⟨z, hz2, by rw [dist_comm]; exact hz1⟩
  obtain ⟨u, hu, hulim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose s hsS hsu using hu
  obtain ⟨R, hR⟩ := hSb.subset_closedBall 0
  obtain ⟨s₀, -, φ, hφm, hφlim⟩ := (isCompact_closedBall (0 : ℂ) R).tendsto_subseq fun n => hR (hsS n)
  have hs₀cl : s₀ ∈ closure S := mem_closure_of_tendsto hφlim (Eventually.of_forall fun n => hsS (φ n))
  have hoff : ∀ n, negInv (s n) ∈ H \ fwdHull W q := fun n =>
    negInv_mem_H_diff (hSH (hsS n)) fun h => Set.disjoint_left.1 hdis (subset_closure (hsS n)) (subset_closure h)
  -- `f_q(R s_n) → 0` along the subsequence
  have hlim0 : Tendsto (fun n => fwdMap W q (negInv (s (φ n)))) atTop (𝓝 0) := by
    have hξ : Tendsto (fun n => φ₁ (s (φ n))) atTop (𝓝 (mobPole c d : ℂ)) := by
      have := hulim.comp hφm.tendsto_atTop
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, hsu]
    have h := tendsto_negInv_realMobius_of_tendsto_pole hdet hc hξ
      (Eventually.of_forall fun n => hφH _ (hsS (φ n)))
    refine h.congr fun n => ?_
    rw [← hΨ _ (hsS (φ n)), negInv_revChart]
  by_cases hs₀ : s₀ = 0
  · obtain ⟨K, hK0, hK⟩ := exists_norm_le_norm_fwdMap hW hW0 hq
    have hev : ∀ᶠ n in atTop, 1 / (1 + K) ≤ ‖s (φ n)‖ := by
      filter_upwards [(tendsto_norm_zero.comp hlim0).eventually (gt_mem_nhds one_pos)] with n hn
      have h1 := hK _ (hoff (φ n))
      simp only [Function.comp_apply] at hn
      rw [norm_negInv] at h1
      have hpos : 0 < ‖s (φ n)‖ := norm_pos_iff.2 (ne_zero_of_mem_H' (hSH (hsS (φ n))))
      rw [div_le_iff₀ (by positivity)]
      have h2 : ‖s (φ n)‖⁻¹ ≤ 1 + K := by linarith
      calc 1 = ‖s (φ n)‖⁻¹ * ‖s (φ n)‖ := (inv_mul_cancel₀ hpos.ne').symm
        _ ≤ (1 + K) * ‖s (φ n)‖ := mul_le_mul_of_nonneg_right h2 hpos.le
        _ = ‖s (φ n)‖ * (1 + K) := mul_comm _ _
    have hge := ge_of_tendsto (hφlim.norm) hev
    rw [hs₀, norm_zero] at hge
    have : (0 : ℝ) < 1 / (1 + K) := by positivity
    linarith
  · set y := negInv s₀ with hy
    have hy0 : y ≠ 0 := by
      rw [hy, negInv]
      exact neg_ne_zero.2 (inv_ne_zero hs₀)
    have hRlim : Tendsto (fun n => negInv (s (φ n))) atTop (𝓝 y) :=
      (continuousAt_negInv hs₀).tendsto.comp hφlim
    have hyim : 0 ≤ y.im := by
      have hcl : y ∈ closure H := mem_closure_of_tendsto hRlim (Eventually.of_forall fun n => (hoff (φ n)).1)
      have hsub : closure H ⊆ {z : ℂ | 0 ≤ z.im} :=
        closure_minimal (fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz))
          (isClosed_le continuous_const Complex.continuous_im)
      exact hsub hcl
    have hyK : y ∉ closure (fwdHull W q) := by
      intro h
      have h1 := mem_closure_image (continuousAt_negInv hy0) h
      rw [hy, negInv_negInv] at h1
      exact Set.disjoint_left.1 hdis hs₀cl h1
    obtain ⟨L, hL0, hL⟩ := exists_ne_zero_tendsto_fwdMap hW hW0 hq hy0 hyim hyK
    have hlimL : Tendsto (fun n => fwdMap W q (negInv (s (φ n)))) atTop (𝓝 L) :=
      hL.comp (tendsto_nhdsWithin_iff.2 ⟨hRlim, Eventually.of_forall fun n => (hoff (φ n)).1⟩)
    exact hL0 (tendsto_nhds_unique hlimL hlim0)

/-- **`N` moves `∞`**: if `Ψ_q = N ∘ φ₁` along points `w_n ∈ ℍ` tending to a nonzero point `y` with
`R(y) ∉ closure K_q`, while `φ₁(w_n) → ∞`, then `N` is not affine (`c ≠ 0`): an affine `N` would force
`f_q(R w_n) = R(Ψ_q w_n) → 0`, but `f_q(R w_n)` tends to a nonzero limit. -/
theorem c_ne_zero_of_tendsto (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q) {w : ℕ → ℂ} {y : ℂ}
    (hw : Tendsto w atTop (𝓝 y)) (hwH : ∀ n, w n ∈ H) (hy0 : y ≠ 0) (hyK : negInv y ∉ closure (fwdHull W q))
    {φ₁ : ℂ → ℂ} (hφ : Tendsto (fun n => ‖φ₁ (w n)‖) atTop atTop) {a b c d : ℝ} (hdet : 0 < a * d - b * c)
    (hΨ : ∀ᶠ n in atTop, revChart W q (w n) = realMobius a b c d (φ₁ (w n))) : c ≠ 0 := by
  intro hc0
  rw [hc0] at hdet
  have had : 0 < a * d := by linarith
  have hd0 : d ≠ 0 := fun h => by rw [h, mul_zero] at had; exact lt_irrefl _ had
  have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at had; exact lt_irrefl _ had
  -- `‖Ψ_q(w_n)‖ → ∞`
  have hbig : Tendsto (fun n => ‖revChart W q (w n)‖) atTop atTop := by
    have hlow : Tendsto (fun n => (|a| * ‖φ₁ (w n)‖ - |b|) / |d|) atTop atTop := by
      have h1 := tendsto_atTop_add_const_right atTop (-|b|) (Tendsto.const_mul_atTop (abs_pos.2 ha0) hφ)
      exact Tendsto.atTop_div_const (abs_pos.2 hd0) (h1.congr fun n => by ring)
    refine tendsto_atTop_mono' atTop ?_ hlow
    filter_upwards [hΨ] with n hn
    rw [hn, realMobius, hc0, Complex.ofReal_zero, zero_mul, zero_add, norm_div, Complex.norm_real,
      Real.norm_eq_abs]
    refine div_le_div_of_nonneg_right ?_ (abs_nonneg d)
    have h1 := norm_sub_norm_le ((a : ℂ) * φ₁ (w n)) (-(b : ℂ))
    rw [sub_neg_eq_add, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs] at h1
    linarith
  -- so `f_q(R w_n) → 0`
  have hlim0 : Tendsto (fun n => fwdMap W q (negInv (w n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_inv_atTop_zero.comp hbig).congr fun n => ?_
    simp only [Function.comp_apply, ← negInv_revChart, norm_negInv]
  -- but it has a nonzero limit
  have hRlim : Tendsto (fun n => negInv (w n)) atTop (𝓝 (negInv y)) := (continuousAt_negInv hy0).tendsto.comp hw
  have hny0 : negInv y ≠ 0 := by rw [negInv]; exact neg_ne_zero.2 (inv_ne_zero hy0)
  have hyim : 0 ≤ (negInv y).im := by
    have hcl : negInv y ∈ closure H :=
      mem_closure_of_tendsto hRlim (Eventually.of_forall fun n => negInv_mem_H (hwH n))
    have hsub : closure H ⊆ {z : ℂ | 0 ≤ z.im} :=
      closure_minimal (fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz))
        (isClosed_le continuous_const Complex.continuous_im)
    exact hsub hcl
  obtain ⟨L, hL0, hL⟩ := exists_ne_zero_tendsto_fwdMap hW hW0 hq hny0 hyim hyK
  have hlimL : Tendsto (fun n => fwdMap W q (negInv (w n))) atTop (𝓝 L) :=
    hL.comp (tendsto_nhdsWithin_iff.2 ⟨hRlim, Eventually.of_forall fun n => negInv_mem_H (hwH n)⟩)
  exact hL0 (tendsto_nhds_unique hlimL hlim0)

end Pole

/-! ### The main theorem -/

/-- **Aux. lemma 8 for the obstacle `R(K_q)`, which reaches `∞` in the chart `R`** (proof of Lemma 4.7: the counterflow
read in the chart of the flow-line prefix). Let `Wα` (the flow line, chart `Q`) and `Wβ` (the counterflow, chart `R`) be
continuous drivers from `0`, `q, T ≥ 0`, suppose `closure K^α_q` meets `ℝ` only at `0`, and suppose the closures of the
counterflow hull `K^β_T` and of `R(K^α_q)` are disjoint. Then `t ↦ Ψ_q(K^β_t)`, `Ψ_q = revChart Wα q = R ∘ f_q ∘ R`, is
a chordal Loewner chain after a capacity time change: a continuous driver `W'` with `W'(0) = 0` and a continuous
strictly increasing clock `τ(t) = hcap(Ψ_q(K^β_t))/2`, with `K^{W'}_{τ(t)} = Ψ_q(K^β_t)` for `t ∈ [0, T]`. -/
theorem exists_loewner_revChart_image {Wα Wβ : ℝ → ℝ} (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) {q : ℝ}
    (hq : 0 ≤ q) (hKq : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα q)) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hdis : Disjoint (closure (fwdHull Wβ T)) (closure (negInv '' fwdHull Wα q))) :
    ∃ τ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 T) ∧
      ContinuousOn τ (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        τ t = hcapSet (revChart Wα q '' fwdHull Wβ t) / 2 ∧ fwdHull W' (τ t) = revChart Wα q '' fwdHull Wβ t := by
  obtain ⟨Rβ, hRβ⟩ := (InteractingSLE.isBounded_fwdHull hWβ T).subset_closedBall 0
  obtain ⟨Rα, hRα⟩ := (InteractingSLE.isBounded_fwdHull hWα q).subset_closedBall 0
  have hnβ : ∀ w ∈ fwdHull Wβ T, ‖w‖ ≤ |Rβ| := fun w hw => by
    have := hRβ hw; rw [mem_closedBall, dist_zero_right] at this; exact this.trans (le_abs_self _)
  have hnα : ∀ z ∈ fwdHull Wα q, ‖z‖ ≤ |Rα| := fun z hz => by
    have := hRα hz; rw [mem_closedBall, dist_zero_right] at this; exact this.trans (le_abs_self _)
  set C : ℝ := |Rβ| + 2 with hCdef
  have hC : 0 < C := by positivity
  set B : Set ℂ := negInv '' fwdHull Wα q with hB
  have hKβB : ∀ w ∈ fwdHull Wβ T, w ∈ H \ B := fun w hw =>
    ⟨hw.1, fun hwB => Set.disjoint_left.1 hdis (subset_closure hw) (subset_closure hwB)⟩
  -- step 1: the flow hull under `M(z) = z/(Cz + 1)`
  have hpM : mobPole C 1 = -(1 / C) := by simp only [mobPole]; ring
  have hpM0 : mobPole C 1 ≠ 0 := by rw [hpM]; exact neg_ne_zero.2 (by positivity)
  have hcl₀ : ((mobPole C 1 : ℝ) : ℂ) ∉ closure (fwdHull Wα q) := hKq _ hpM0
  obtain ⟨r₀, hr₀, hr₀d⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure |>.mem_nhds hcl₀)
  have hball₀ : Disjoint (ball ((mobPole C 1 : ℝ) : ℂ) r₀) (fwdHull Wα q) :=
    Set.disjoint_left.2 fun z hz hzK => hr₀d hz (subset_closure hzK)
  obtain ⟨σ₁, U, _, _, _, hUc, hU0, hσ₁0, hσ₁m, -, h₁⟩ :=
    exists_loewner_mobius_image hWα hWα0 hq (a := 1) (b := 0) (c := C) (d := 1) (by norm_num) hC.ne' hpM0 hr₀
      hball₀
  have hU0' : U 0 = 0 := by rw [hU0]; norm_num
  have hσq : 0 ≤ σ₁ q := by rw [← hσ₁0]; exact hσ₁m.monotoneOn ⟨le_rfl, hq⟩ ⟨hq, le_rfl⟩ hq
  set A : Set ℂ := fwdHull U (σ₁ q) with hAdef
  have hAM : A = realMobius 1 0 C 1 '' fwdHull Wα q := (h₁ q ⟨hq, le_rfl⟩).2.1
  have hA : IsHPHull A := isHPHull_fwdHull hUc hσq
  have hφ : IsMapOut A (gmap U (σ₁ q)) := isMapOut_fwdMap hUc hU0' hσq
  have hiA : realMobius C (-1) 1 0 '' A = B := by
    rw [hAM, image_image]
    exact image_congr fun z hz => m₁inv_M hC hz.1
  have hmem : ∀ w ∈ H \ B, realMobius 0 1 (-1) C w ∈ H \ A := fun w hw =>
    ⟨m₁_mem_H C hw.1, fun hA' => hw.2 (by rw [← hiA]; exact ⟨_, hA', m₁inv_m₁ hw.1⟩)⟩
  -- step 2: the counterflow hulls under `m₁(w) = 1/(C − w)`
  have hpm : mobPole (-1) C = C := by simp only [mobPole]; ring
  have hball₁ : Disjoint (ball ((mobPole (-1) C : ℝ) : ℂ) 1) (fwdHull Wβ T) := by
    rw [hpm, Set.disjoint_left]
    intro z hz hzK
    have h1 := hnβ z hzK
    rw [mem_ball, dist_eq_norm] at hz
    have h2 := norm_sub_norm_le (C : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC, norm_sub_rev] at h2
    linarith
  obtain ⟨σ₂, W₁, _, _, _, hW₁c, hW₁0, hσ₂0, hσ₂m, hσ₂c, h₂⟩ :=
    exists_loewner_mobius_image hWβ hWβ0 hT (a := 0) (b := 1) (c := -1) (d := C) (by norm_num) (by norm_num)
      (by rw [hpm]; exact hC.ne') one_pos hball₁
  have hT₁ : 0 ≤ σ₂ T := by rw [← hσ₂0]; exact hσ₂m.monotoneOn ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  have hK₁ : ∀ t ∈ Icc (0 : ℝ) T, fwdHull W₁ (σ₂ t) = realMobius 0 1 (-1) C '' fwdHull Wβ t :=
    fun t ht => (h₂ t ht).2.1
  -- step 3: Aux. lemma 8 for `g_A`
  set δ : ℝ := 1 / (C * (C * |Rα| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hballA : Disjoint (ball ((1 / C : ℝ) : ℂ) δ) A := by
    rw [hAM, Set.disjoint_left]
    rintro v hv ⟨z, hz, rfl⟩
    have h1 := norm_M_sub_le hC hz.1
    have h3 : δ ≤ 1 / (C * (C * ‖z‖ + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr; exact hnα z hz)
    rw [mem_ball, dist_eq_norm] at hv
    linarith
  have hcl1 : ((1 / C : ℝ) : ℂ) ∉ closure A := fun h => by
    obtain ⟨b, hbA, hb⟩ := Metric.mem_closure_iff.1 h δ hδpos
    exact Set.disjoint_left.1 hballA (by rw [mem_ball, dist_comm]; exact hb) hbA
  have hdisA : Disjoint (closure A) (closure (realMobius 0 1 (-1) C '' fwdHull Wβ T)) := by
    rw [Set.disjoint_left]
    intro ζ hζA hζB
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      obtain ⟨v, ⟨w, hw, rfl⟩, hv⟩ := Metric.mem_closure_iff.1 hζB (1 / (C + |Rβ|)) (by positivity)
      rw [dist_zero_left, norm_m₁] at hv
      have h2 : ‖(C : ℂ) - w‖ ≤ C + |Rβ| := by
        calc ‖(C : ℂ) - w‖ ≤ ‖(C : ℂ)‖ + ‖w‖ := norm_sub_le _ _
          _ ≤ C + |Rβ| := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]; linarith [hnβ w hw]
      have h3 : 0 < ‖(C : ℂ) - w‖ := by
        refine norm_pos_iff.2 fun h0 => ?_
        have him := congrArg Complex.im h0
        simp only [sub_im, ofReal_im, zero_sub, neg_eq_zero, zero_im] at him
        have : (0 : ℝ) < w.im := hw.1
        linarith
      have := one_div_le_one_div_of_le h3 h2
      linarith
    have hcont : ContinuousAt (realMobius C (-1) 1 0) ζ := continuousAt_realMobius (by simpa using hζ0)
    have h1 := mem_closure_image hcont hζA
    have h2 := mem_closure_image hcont hζB
    rw [hiA] at h1
    have hi2 : realMobius C (-1) 1 0 '' (realMobius 0 1 (-1) C '' fwdHull Wβ T) = fwdHull Wβ T := by
      rw [image_image]
      conv_rhs => rw [← image_id (fwdHull Wβ T)]
      exact image_congr fun w hw => m₁inv_m₁ hw.1
    rw [hi2] at h2
    exact Set.disjoint_left.1 hdis h2 h1
  have hd8 : Disjoint (closure A) (insert (W₁ 0 : ℂ) (closure (fwdHull W₁ (σ₂ T)))) := by
    rw [hK₁ T ⟨hT, le_rfl⟩, hW₁0, Set.disjoint_insert_right]
    exact ⟨hcl1, hdisA⟩
  obtain ⟨a₂, W₂, hW₂c, ha₂0, ha₂m, ha₂c, h₂'⟩ := exists_loewner_image hW₁c hT₁ hA hφ hd8
  -- step 4: the start `x₁ = g_A(1/C)` of the image chain
  obtain ⟨hx₁im, hx₁lim⟩ := bdryVal_spec hUc hU0' hσq hδpos hballA
  set x₁ : ℝ := (bdryVal U (1 / C) (σ₁ q)).re with hx₁def
  have hx₁ : (x₁ : ℂ) = bdryVal U (1 / C) (σ₁ q) :=
    Complex.ext (by simp [hx₁def]) (by rw [Complex.ofReal_im]; exact hx₁im.symm)
  have hW₂0 : W₂ 0 = x₁ := by
    obtain ⟨-, -, hR⟩ := h₂' 0 ⟨le_rfl, hT₁⟩
    have hgA0 : (fun z => fwdMap W₁ 0 z + W₁ 0) '' A = A := by
      have : ∀ z ∈ A, fwdMap W₁ 0 z + W₁ 0 = z := fun z hz => gmap_zero_apply hW₁c (hA.1 hz)
      rw [image_congr this, image_id']
    obtain ⟨-, hlim⟩ := hR (gmap U (σ₁ q)) (by rw [hgA0]; exact hφ)
    rw [ha₂0, hW₁0] at hlim
    have := MobHyp.nhdsWithin_neBot (1 / C)
    have heq := tendsto_nhds_unique hlim hx₁lim
    rw [← hx₁] at heq
    exact_mod_cast heq
  have hT₂ : 0 ≤ a₂ (σ₂ T) := by rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ ⟨hT₁, le_rfl⟩ hT₁
  have hK₂ : ∀ s ∈ Icc (0 : ℝ) (σ₂ T), fwdHull W₂ (a₂ s) = gmap U (σ₁ q) '' fwdHull W₁ s :=
    fun s hs => (h₂' s hs).2.1
  -- step 5: translate by `−x₁`
  set W₃ : ℝ → ℝ := fun s => W₂ s + -x₁ with hW₃
  have hW₃c : Continuous W₃ := by fun_prop
  have hW₃0 : W₃ 0 = 0 := by simp [hW₃, hW₂0]
  have hK₃ : ∀ s, fwdHull W₃ s = (fun z : ℂ => z + (-x₁ : ℝ)) '' fwdHull W₂ s :=
    fun s => fwdHull_add_const W₂ (-x₁) s
  -- step 6: `Ψ_q = N₀ ∘ g_A ∘ m₁` for a real Möbius map `N₀`
  have hG : IsConformalBijection (revChart Wα q) (H \ B) H := by
    refine ⟨fun z hz => ?_, fun z hz => revChart_mem_H hWα hq hz, injOn_revChart hWα hWα0 hq,
      fun ζ hζ => ⟨revChartInv Wα q ζ, revChartInv_mem hWα hWα0 hq hζ, revChart_revChartInv hWα hWα0 hq hζ⟩⟩
    have hz0 : z ≠ 0 := ne_zero_of_mem_H' hz.1
    have hw := negInv_notMem_fwdHull hz
    have h2 : DifferentiableAt ℂ (fwdMap Wα q) (negInv z) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWα hq _ hw).differentiableAt
        ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWα hq).mem_nhds hw)
    have h3 : fwdMap Wα q (negInv z) ≠ 0 :=
      ne_zero_of_mem_H' (QuantumZipper.FwdHolo.mapsTo_fwdMap hWα hq hw)
    have h1 : DifferentiableAt ℂ negInv z := (differentiableAt_inv hz0).neg
    have h4 : DifferentiableAt ℂ negInv (fwdMap Wα q (negInv z)) := (differentiableAt_inv h3).neg
    exact (h4.comp z (h2.comp z h1)).differentiableWithinAt
  have hdetI : (0 : ℝ) < C * 0 - (-1) * 1 := by norm_num
  have hφd : DifferentiableOn ℂ (realMobius C (-1) 1 0) (H \ A) :=
    (differentiableOn_realMobius hdetI).mono sdiff_subset
  have hφb : BijOn (realMobius C (-1) 1 0) (H \ A) (H \ B) := by
    have himg : realMobius C (-1) 1 0 '' (H \ A) = H \ B := by
      rw [image_H_diff hdetI hA.1, hiA]
    rw [← himg]
    exact ((QuantumZipper.CA.bijOn_realMobius_H hdetI).injOn.mono sdiff_subset).bijOn_image
  obtain ⟨a', b', c', d', hdet', hconj⟩ := exists_realMobius_conj hA hφ hφd hφb hG
  have hkey : ∀ w ∈ H \ B, revChart Wα q w = realMobius a' b' c' d' (gmap U (σ₁ q) (realMobius 0 1 (-1) C w)) := by
    intro w hw
    have h := hconj _ (hmem w hw)
    rwa [m₁inv_m₁ hw.1] at h
  -- step 7: the Möbius map `N = N₀(· + x₁)` read after the translation
  set bN : ℝ := a' * x₁ + b' with hbN
  set dN : ℝ := c' * x₁ + d' with hdN
  have hdetN : 0 < a' * dN - bN * c' := by
    have : a' * dN - bN * c' = a' * d' - b' * c' := by simp only [hbN, hdN]; ring
    linarith
  have hNeq : ∀ ξ : ℂ, realMobius a' bN c' dN (ξ + ((-x₁ : ℝ) : ℂ)) = realMobius a' b' c' d' ξ := by
    intro ξ
    simp only [realMobius, hbN, hdN]
    push_cast
    congr 1 <;> ring
  set φ₁ : ℂ → ℂ := fun w => gmap U (σ₁ q) (realMobius 0 1 (-1) C w) + ((-x₁ : ℝ) : ℂ) with hφ₁
  have hΨN : ∀ w ∈ H \ B, revChart Wα q w = realMobius a' bN c' dN (φ₁ w) := fun w hw => by
    rw [hkey w hw, hφ₁, hNeq]
  have hφ₁H : ∀ w ∈ H \ B, φ₁ w ∈ H := by
    intro w hw
    have h1 : gmap U (σ₁ q) (realMobius 0 1 (-1) C w) ∈ H := hφ.1.2.mapsTo (hmem w hw)
    show 0 < (gmap U (σ₁ q) (realMobius 0 1 (-1) C w) + ((-x₁ : ℝ) : ℂ)).im
    rw [add_im, Complex.ofReal_im, add_zero]
    exact h1
  -- step 8: `N(0) = 0`, along `w_n = i/(n+1) → 0`
  set wz : ℕ → ℂ := fun n => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hwz
  have hnwz : ∀ n : ℕ, ‖wz n‖ = 1 / ((n : ℝ) + 1) := fun n => by
    rw [hwz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hwzH : ∀ n, wz n ∈ H := fun n => by
    show 0 < (wz n).im
    simp only [hwz, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul, add_zero]
    positivity
  have hwz0 : Tendsto wz atTop (𝓝 0) := by
    have h := ((Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
    simpa [hwz] using h
  have hwzB : ∀ᶠ n in atTop, wz n ∉ B := by
    filter_upwards [eventually_gt_atTop ⌈|Rα|⌉₊] with n hn
    rintro ⟨z, hz, hzw⟩
    have h1 := hnα z hz
    have h2 : z = negInv (wz n) := by rw [← hzw, negInv_negInv]
    rw [h2, norm_negInv, hnwz, one_div, inv_inv] at h1
    have h3 : (|Rα| : ℝ) < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    linarith
  have hΨ0 : Tendsto (fun n => revChart Wα q (wz n)) atTop (𝓝 0) :=
    (tendsto_revChart_zero hWα hWα0 hq).comp
      (tendsto_nhdsWithin_iff.2 ⟨hwz0, hwzB.mono fun n hn => ⟨hwzH n, hn⟩⟩)
  have hφ₁0 : Tendsto (fun n => φ₁ (wz n)) atTop (𝓝 0) := by
    have hm1 : Tendsto (fun n => realMobius 0 1 (-1) C (wz n)) atTop (𝓝[H] ((1 / C : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => m₁_mem_H C (hwzH n)⟩
      have hc : ContinuousAt (realMobius 0 1 (-1) C) 0 :=
        continuousAt_realMobius (by simp only [ofReal_neg, ofReal_one, mul_zero, zero_add]; exact_mod_cast hC.ne')
      have hval : realMobius 0 1 (-1) C 0 = ((1 / C : ℝ) : ℂ) := by simp [realMobius]
      rw [← hval]
      exact hc.tendsto.comp hwz0
    have h := (hx₁lim.comp hm1).add_const ((-x₁ : ℝ) : ℂ)
    rw [← hx₁, Complex.ofReal_neg, add_neg_cancel] at h
    exact h.congr fun n => by simp only [hφ₁, Function.comp_apply, Complex.ofReal_neg]
  have hbN0 : bN = 0 := b_eq_zero_of_tendsto hdetN hφ₁0 (hwzB.mono fun n hn => hφ₁H _ ⟨hwzH n, hn⟩)
    (hΨ0.congr' (hwzB.mono fun n hn => hΨN _ ⟨hwzH n, hn⟩))
  have hdN0 : dN ≠ 0 := by
    intro h
    rw [h, hbN0] at hdetN
    simp at hdetN
  -- step 9: `N` moves `∞`, along `w_n = C + i/(n+1) → C`
  set wc : ℕ → ℂ := fun n => (C : ℂ) + wz n with hwc
  have hwcH : ∀ n, wc n ∈ H := fun n => by
    show 0 < (wc n).im
    rw [hwc, add_im, Complex.ofReal_im, zero_add]
    exact hwzH n
  have hwcC : Tendsto wc atTop (𝓝 (C : ℂ)) := by
    have h := hwz0.const_add (C : ℂ)
    rwa [add_zero] at h
  have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hnegC : negInv (C : ℂ) = ((mobPole C 1 : ℝ) : ℂ) := by
    rw [hpM, negInv]; push_cast; ring
  have hwcB : ∀ᶠ n in atTop, wc n ∉ B := by
    have hlim : Tendsto (fun n => negInv (wc n)) atTop (𝓝 ((mobPole C 1 : ℝ) : ℂ)) := by
      rw [← hnegC]; exact (continuousAt_negInv hC0).tendsto.comp hwcC
    filter_upwards [hlim.eventually (isOpen_ball.mem_nhds (mem_ball_self hr₀))] with n hn
    rintro ⟨z, hz, hzw⟩
    have : z = negInv (wc n) := by rw [← hzw, negInv_negInv]
    rw [this] at hz
    exact Set.disjoint_left.1 hball₀ hn hz
  obtain ⟨KA, -, hKA⟩ := exists_norm_fwdMap_sub_le hUc hU0' hσq
  have hnm : ∀ n : ℕ, ‖realMobius 0 1 (-1) C (wc n)‖ = (n : ℝ) + 1 := fun n => by
    have h1 : (C : ℂ) - wc n = -wz n := by rw [hwc]; ring
    rw [norm_m₁, h1, norm_neg, hnwz]
    field_simp
  have hφbig : Tendsto (fun n => ‖φ₁ (wc n)‖) atTop atTop := by
    have hlow : Tendsto (fun n : ℕ => (n : ℝ) + 1 - (KA + |U (σ₁ q)| + |x₁|)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    refine tendsto_atTop_mono' atTop ?_ hlow
    filter_upwards [hwcB] with n hn
    have hm := hmem _ ⟨hwcH n, hn⟩
    have h1 := hKA _ hm
    set m := realMobius 0 1 (-1) C (wc n) with hm'
    have h2 : m - φ₁ (wc n) = -(fwdMap U (σ₁ q) m - m) - ((U (σ₁ q) : ℂ) + ((-x₁ : ℝ) : ℂ)) := by
      simp only [hφ₁, gmap, ← hm']; ring
    have h3 : ‖m - φ₁ (wc n)‖ ≤ KA + (|U (σ₁ q)| + |x₁|) := by
      rw [h2]
      refine (norm_sub_le _ _).trans (add_le_add (by rw [norm_neg]; exact h1) ?_)
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    have h4 := norm_sub_norm_le m (φ₁ (wc n))
    rw [hnm n] at h4
    linarith
  have hcN : c' ≠ 0 := c_ne_zero_of_tendsto hWα hWα0 hq hwcC hwcH hC0 (by rw [hnegC]; exact hcl₀) hφbig hdetN
    (hwcB.mono fun n hn => hΨN _ ⟨hwcH n, hn⟩)
  -- step 10: the pole of `N` is away from the image hulls
  obtain ⟨r₃, hr₃, hd₃⟩ := exists_disjoint_ball_pole hWα hWα0 hq (S := fwdHull Wβ T) (fun _ hz => hz.1)
    (InteractingSLE.isBounded_fwdHull hWβ T) hdis (φ₁ := φ₁) (fun w hw => hφ₁H w (hKβB w hw)) hdetN hcN
    fun w hw => hΨN w (hKβB w hw)
  have hφ₁img : ∀ t ∈ Icc (0 : ℝ) T, fwdHull W₃ (a₂ (σ₂ t)) = φ₁ '' fwdHull Wβ t := by
    intro t ht
    have hs : σ₂ t ∈ Icc 0 (σ₂ T) :=
      ⟨by rw [← hσ₂0]; exact hσ₂m.monotoneOn ⟨le_rfl, hT⟩ ht ht.1, hσ₂m.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
    rw [hK₃, hK₂ _ hs, hK₁ t ht, image_image, image_image]
  have hd4 : Disjoint (ball (mobPole c' dN : ℂ) r₃) (fwdHull W₃ (a₂ (σ₂ T))) := by
    rw [hφ₁img T ⟨hT, le_rfl⟩]; exact hd₃
  have hpN : mobPole c' dN ≠ 0 := by
    simp only [mobPole]
    exact div_ne_zero (neg_ne_zero.2 hdN0) hcN
  obtain ⟨τ₄, W₄, _, _, _, hW₄c, hW₄0, hτ₄0, hτ₄m, hτ₄c, h₄⟩ :=
    exists_loewner_mobius_image hW₃c hW₃0 hT₂ hdetN hcN hpN hr₃ hd4
  -- step 11: assembly
  have hmaps₁ : MapsTo σ₂ (Icc 0 T) (Icc 0 (σ₂ T)) := fun t ht =>
    ⟨by rw [← hσ₂0]; exact hσ₂m.monotoneOn ⟨le_rfl, hT⟩ ht ht.1, hσ₂m.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
  have hmaps₂ : MapsTo a₂ (Icc 0 (σ₂ T)) (Icc 0 (a₂ (σ₂ T))) := fun s hs =>
    ⟨by rw [← ha₂0]; exact ha₂m.monotoneOn ⟨le_rfl, hT₁⟩ hs hs.1, ha₂m.monotoneOn hs ⟨hT₁, le_rfl⟩ hs.2⟩
  refine ⟨fun t => τ₄ (a₂ (σ₂ t)), W₄, hW₄c, by rw [hW₄0, hbN0, zero_div], by simp [hσ₂0, ha₂0, hτ₄0],
    fun t ht t' ht' htt' => hτ₄m (hmaps₂ (hmaps₁ ht)) (hmaps₂ (hmaps₁ ht'))
      (ha₂m (hmaps₁ ht) (hmaps₁ ht') (hσ₂m ht ht' htt')),
    hτ₄c.comp (ha₂c.comp hσ₂c hmaps₁) (hmaps₂.comp hmaps₁), fun t ht => ?_⟩
  have himg : realMobius a' bN c' dN '' fwdHull W₃ (a₂ (σ₂ t)) = revChart Wα q '' fwdHull Wβ t := by
    rw [hφ₁img t ht, image_image]
    exact image_congr fun w hw => (hΨN w (hKβB w (fwdHull_mono ht.2 hw))).symm
  obtain ⟨hτ, hhull, -⟩ := h₄ _ (hmaps₂ (hmaps₁ ht))
  exact ⟨by simp only; rw [hτ, himg], by simp only; rw [hhull, himg]⟩

/-! ### Traces -/

section Trace

variable {Wα : ℝ → ℝ}

/-- **Fillings under the chart `Ψ_q`**: if `K ⊆ ℍ ∖ R(K_q)` is the filling of `A'` and `Ψ_q(K)` is a hull, then
`Ψ_q(K)` is the filling of `Ψ_q(A' ∩ ℍ)`. (`Ψ_q` is a homeomorphism of `D = ℍ ∖ R(K_q)` onto `ℍ`; the component of
`ℍ ∖ A'` that is `ℍ ∖ K` meets `D` in `D ∖ K`, which is connected.) -/
theorem isFilling_image_revChart (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    {K A' : Set ℂ} (hKB : K ⊆ H \ negInv '' fwdHull Wα q) (hK' : IsHPHull (revChart Wα q '' K))
    (h : IsFilling K A') : IsFilling (revChart Wα q '' K) (revChart Wα q '' (A' ∩ H)) := by
  set D := H \ negInv '' fwdHull Wα q with hD
  have hA'K : A' ∩ H ⊆ K := inter_H_subset_of_isFilling h
  obtain ⟨⟨z, hzK, hz⟩, -⟩ := h
  have himg : ∀ S ⊆ D, H \ revChart Wα q '' S = revChart Wα q '' (D \ S) := by
    intro S hS
    ext ζ
    constructor
    · rintro ⟨hζ, hζS⟩
      refine ⟨revChartInv Wα q ζ, ⟨revChartInv_mem hWα hWα0 hq hζ, fun h => hζS ⟨_, h,
        revChart_revChartInv hWα hWα0 hq hζ⟩⟩, revChart_revChartInv hWα hWα0 hq hζ⟩
    · rintro ⟨w, ⟨hwD, hwS⟩, rfl⟩
      refine ⟨revChart_mem_H hWα hq hwD, ?_⟩
      rintro ⟨v, hv, hvw⟩
      exact hwS (injOn_revChart hWα hWα0 hq (hS hv) hwD hvw ▸ hv)
  have hA''D : A' ∩ H ⊆ D := hA'K.trans hKB
  obtain ⟨ζ₀, hζ₀⟩ := hK'.2.2.2.nonempty
  rw [himg K hKB] at hζ₀
  obtain ⟨w, hw, rfl⟩ := hζ₀
  have hwA : w ∈ D \ (A' ∩ H) := ⟨hw.1, fun h => hw.2 (hA'K h)⟩
  refine ⟨⟨revChart Wα q w, by rw [himg K hKB]; exact ⟨w, hw, rfl⟩, ?_⟩, not_isBounded_H_diff hK'.2.1⟩
  rw [himg _ hA''D, himg K hKB, ← image_connectedComponentIn (continuousOn_revChart hWα hq)
    (continuousOn_revChartInv hWα hWα0 hq) (fun v hv => revChart_mem_H hWα hq hv)
    (fun v hv => revChartInv_revChart hWα hWα0 hq hv) (fun v hv => revChart_revChartInv hWα hWα0 hq hv)
    sdiff_subset hwA]
  congr 1
  have hwK : w ∈ H \ K := ⟨hw.1.1, hw.2⟩
  have hcomp : connectedComponentIn (H \ A') w = H \ K :=
    (connectedComponentIn_eq (hz ▸ hwK)).symm.trans hz
  apply Subset.antisymm
  · intro v hv
    have h1 : v ∈ D := (connectedComponentIn_subset _ _ hv).1
    have h2 : connectedComponentIn (D \ (A' ∩ H)) w ⊆ connectedComponentIn (H \ A') w := by
      refine isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hwA) ?_
      intro x hx
      obtain ⟨hxD, hxA⟩ := connectedComponentIn_subset _ _ hx
      exact ⟨hxD.1, fun hxA' => hxA ⟨hxA', hxD.1⟩⟩
    rw [hcomp] at h2
    exact ⟨h1, (h2 hv).2⟩
  · have hpre : IsPreconnected (D \ K) := by
      have h1 := hK'.2.2.2.isPathConnected.isConnected.isPreconnected
      rw [himg K hKB] at h1
      have h2 := h1.image (revChartInv Wα q) ((continuousOn_revChartInv hWα hWα0 hq).mono
        (by rintro _ ⟨u, hu, rfl⟩; exact revChart_mem_H hWα hq hu.1))
      convert h2 using 1
      ext v
      constructor
      · intro hv
        exact ⟨revChart Wα q v, ⟨v, hv, rfl⟩, revChartInv_revChart hWα hWα0 hq hv.1⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        rwa [revChartInv_revChart hWα hWα0 hq hu.1]
    exact hpre.subset_connectedComponentIn hw fun v hv => ⟨hv.1, fun h => hv.2 (hA'K h)⟩

/-- `Ψ_q` extended by its boundary value `0` at `0` (the start of the counterflow). -/
def revChartZ (W : ℝ → ℝ) (q : ℝ) (w : ℂ) : ℂ := if w = 0 then 0 else revChart W q w

theorem revChartZ_zero (W : ℝ → ℝ) (q : ℝ) : revChartZ W q 0 = 0 := by simp [revChartZ]

theorem revChartZ_of_ne {W : ℝ → ℝ} {q : ℝ} {w : ℂ} (hw : w ≠ 0) : revChartZ W q w = revChart W q w := by
  simp [revChartZ, hw]

/-- **`Ψ_q`, extended by `0` at `0`, is continuous on `{0} ∪ (ℍ ∖ R(K_q))`** (`WangWu.tendsto_revChart_zero`). -/
theorem continuousOn_revChartZ (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) {q : ℝ} (hq : 0 ≤ q) :
    ContinuousOn (revChartZ Wα q) (insert 0 (H \ negInv '' fwdHull Wα q)) := by
  have hopen := isOpen_H_diff_negInv_fwdHull hWα hq
  have heq : ∀ w ∈ H \ negInv '' fwdHull Wα q, revChartZ Wα q w = revChart Wα q w := fun w hw =>
    revChartZ_of_ne (ne_zero_of_mem_H' hw.1)
  intro w hw
  rcases hw with rfl | hw
  · rw [continuousWithinAt_insert_self, ContinuousWithinAt, revChartZ_zero]
    exact (tendsto_revChart_zero hWα hWα0 hq).congr' (eventually_nhdsWithin_of_forall fun v hv => (heq v hv).symm)
  · have hc : ContinuousAt (revChartZ Wα q) w := by
      have h1 : ContinuousAt (revChart Wα q) w :=
        (continuousOn_revChart hWα hq).continuousAt (hopen.mem_nhds hw)
      exact h1.congr (Filter.eventuallyEq_of_mem (hopen.mem_nhds hw) fun v hv => (heq v hv).symm)
    exact hc.continuousWithinAt

/-- **Aux. lemma 8 for the obstacle `R(K_q)`, trace form**: under the hypotheses of `exists_loewner_revChart_image`,
for a trace `β` of the counterflow hulls on `(0, T]` (`K^β_t` the filling of `β([0, t])`, `β` continuous on `[0, T]`,
from `0`, in `ℍ ∪ {0}` at positive times): `Ψ_q(K^β_t)` is the filling of `Ψ_q(β([0, t]) ∩ ℍ)`, and `Ψ_q ∘ β` (with
`Ψ_q(0) = 0`, `revChartZ`) is continuous on `[0, T]`. So `Ψ_q ∘ β`, reparametrized by `τ`, is a generating trace of the
image driver `W'` on `[0, τ(T)]`. (Returns of `β` to `0` are allowed.) -/
theorem exists_loewner_revChart_trace {Wβ : ℝ → ℝ} (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) {q : ℝ}
    (hq : 0 ≤ q) (hKq : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα q)) (hWβ : Continuous Wβ)
    (hWβ0 : Wβ 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hdis : Disjoint (closure (fwdHull Wβ T)) (closure (negInv '' fwdHull Wα q))) {β : ℝ → ℂ} (hβ0 : β 0 = 0)
    (hβc : ContinuousOn β (Icc 0 T)) (hβH : ∀ t ∈ Ioc (0 : ℝ) T, β t ∈ H ∨ β t = 0)
    (hβK : ∀ t ∈ Ioc (0 : ℝ) T, IsFilling (fwdHull Wβ t) (β '' Icc 0 t)) :
    ∃ τ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 T) ∧
      ContinuousOn τ (Icc 0 T) ∧ (∀ t ∈ Icc (0 : ℝ) T,
        τ t = hcapSet (revChart Wα q '' fwdHull Wβ t) / 2 ∧ fwdHull W' (τ t) = revChart Wα q '' fwdHull Wβ t) ∧
      (∀ t ∈ Ioc (0 : ℝ) T, IsFilling (fwdHull W' (τ t)) (revChart Wα q '' (β '' Icc 0 t ∩ H))) ∧
      ContinuousOn (fun t => revChartZ Wα q (β t)) (Icc 0 T) := by
  obtain ⟨τ, W', hW'c, hW'0, hτ0, hτm, hτc, hK⟩ :=
    exists_loewner_revChart_image hWα hWα0 hq hKq hWβ hWβ0 hT hdis
  have hKB : ∀ t ∈ Icc (0 : ℝ) T, fwdHull Wβ t ⊆ H \ negInv '' fwdHull Wα q := fun t ht w hw =>
    ⟨hw.1, fun hwB => Set.disjoint_left.1 hdis (subset_closure (fwdHull_mono ht.2 hw)) (subset_closure hwB)⟩
  have hβD : ∀ t ∈ Icc (0 : ℝ) T, β t ∈ insert 0 (H \ negInv '' fwdHull Wα q) := by
    intro t ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · rw [← h0, hβ0]; exact mem_insert _ _
    · rcases hβH t ⟨hpos, ht.2⟩ with hH | h0
      · exact Or.inr (hKB t ht (inter_H_subset_of_isFilling (hβK t ⟨hpos, ht.2⟩)
          ⟨⟨t, ⟨hpos.le, le_rfl⟩, rfl⟩, hH⟩))
      · rw [h0]; exact mem_insert _ _
  refine ⟨τ, W', hW'c, hW'0, hτ0, hτm, hτc, hK, fun t ht => ?_,
    (continuousOn_revChartZ hWα hWα0 hq).comp hβc hβD⟩
  have htI : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hτt : 0 ≤ τ t := by rw [← hτ0]; exact hτm.monotoneOn ⟨le_rfl, hT⟩ htI htI.1
  rw [(hK t htI).2]
  exact isFilling_image_revChart hWα hWα0 hq (hKB t htI)
    (by rw [← (hK t htI).2]; exact isHPHull_fwdHull hW'c hτt) (hβK t ht)

end Trace

end InteractingSLE.Sec5.Aux8Inf
