import GaussianLQG.LQG.Crossing.Grid
import GaussianLQG.Probability.Gaussian
import GaussianLQG.Metric.Geodesic
import LQGMetric.Papers.GM.S1.Assembly

/-!
# Bounds for the crossing distance (blueprint Proposition `prop:crossing`)

Deterministic and Gaussian ingredients of the proof of blueprint Proposition `prop:crossing`:

* `Crossing.measure_le_abs_le_of_hasLaw_le`: the Gaussian tail `P[|Z| ≥ x] ≤ 2 e^{-x²/(2V)}` for
  a centered Gaussian `Z` of variance at most `V` (blueprint Lemma `lem:gauss`; the degenerate
  variance `0` is allowed).
* `Crossing.sq_sub_div_four_le_log_norm`: `log r(s,t) ≥ (s - t)²/4` for `s, t ∈ [0, 1]`, where
  `r(s,t) = |is - (1 + it)| = √(1 + (s - t)²)` (used for the "far" pairs).
* `Setup.measure_H_sub_tail`: `H(s,t) - H(s,s)` is a centered Gaussian of variance at most
  `6 |t - s|^{1/2}` (Lemma `lem:H-continuity`(a)), so it has the corresponding Gaussian tail.
* `Crossing.le_log_crossFn`, `Crossing.log_crossFn_le`: `log C_γ` is the infimum of
  `log D(is, 1 + it)` over `s, t ∈ [0, 1]`.
* `Crossing.log_crossFn_ge_of_grid`: the deterministic discretization step of the lower bound
  (blueprint (eq:lower-grid)): if `D(z, w) ≤ K |z - w|^{1/2}` on the unit square,
  `D(is, 1 + it) ≥ K⁻¹` and `log D ≥ L` on the grid `S_m²`, then `log C_γ ≥ L - 2 K² 2^{-m/2}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

open LQGMetric

namespace Crossing

/-! ## Gaussian tails with a variance bound -/

/-- **Lemma `lem:gauss`**, with a variance bound: if `Z ∼ N(0, v)` with `v ≤ V`, then
`P[|Z| ≥ x] ≤ 2 e^{-x²/(2V)}` for `x ≥ 0`. -/
theorem measure_le_abs_le_of_hasLaw_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    {V x : ℝ} (hvV : (v : ℝ) ≤ V) (hx : 0 ≤ x) :
    P {ω | x ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * V))) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rcases hx.lt_or_eq with hx0 | rfl
    · have hmeas : MeasurableSet {y : ℝ | x ≤ |y|} :=
        measurableSet_le measurable_const continuous_abs.measurable
      have hmap := hX.map_eq
      rw [gaussianReal_zero_var] at hmap
      have e : P {ω | x ≤ |X ω|} = P.map X {y : ℝ | x ≤ |y|} :=
        (Measure.map_apply_of_aemeasurable hX.aemeasurable hmeas).symm
      rw [e, hmap, Measure.dirac_apply' _ hmeas]
      have h0 : (0 : ℝ) ∉ {y : ℝ | x ≤ |y|} := by
        simp only [mem_ofPred_eq, abs_zero, not_le]
        exact hx0
      rw [Set.indicator_of_notMem h0]
      exact zero_le
    · calc P {ω | 0 ≤ |X ω|} ≤ 1 := prob_le_one
        _ ≤ ENNReal.ofReal (2 * Real.exp (-0 ^ 2 / (2 * V))) := by
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          simp
  · have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.coe_nonneg (by exact_mod_cast hv.symm)
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((measureReal_le_abs_le_of_hasLaw_gaussianReal hX hx).trans ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by linarith)

/-! ## `log r(s,t)` -/

/-- `log r(s,t) ≥ 0`. -/
theorem log_norm_sI_sub_nonneg (s t : ℝ) :
    0 ≤ Real.log ‖(s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I)‖ :=
  Real.log_nonneg (one_le_norm_sI_sub s t)

/-- `log r(s,t) ≥ (s - t)²/4` for `s, t ∈ [0, 1]` (blueprint proof of Proposition
`prop:crossing`, "far" pairs: `log r = ½ log(1 + (s-t)²) ≥ (s-t)²/4`). -/
theorem sq_sub_div_four_le_log_norm {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (s - t) ^ 2 / 4 ≤ Real.log ‖(s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I)‖ := by
  set r := ‖(s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I)‖ with hr
  have hr1 : 1 ≤ r := one_le_norm_sI_sub s t
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hr2 : r ^ 2 = 1 + (s - t) ^ 2 := norm_sI_sub_one_add_tI_sq s t
  have hu : (s - t) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have h2 : Real.log (r ^ 2) = 2 * Real.log r := by
    rw [Real.log_pow]
    norm_num
  have h3 : 1 - (r ^ 2)⁻¹ ≤ Real.log (r ^ 2) := Real.one_sub_inv_le_log_of_pos (by positivity)
  have h4 : (1 + (s - t) ^ 2)⁻¹ ≤ 1 - (s - t) ^ 2 / 2 := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [sq_nonneg (s - t)]
  rw [hr2] at h2 h3
  linarith

/-! ## The crossing distance as an infimum over the sides -/

theorem sI_mem_leftSide {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : (s : ℂ) * Complex.I ∈ leftSide := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hs.1, hs.2]

theorem one_add_tI_mem_rightSide {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 + (t : ℂ) * Complex.I ∈ rightSide := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ht.1, ht.2]

/-- `log C ≤ log D(is, 1 + it)` for `s, t ∈ [0, 1]`. -/
theorem log_crossFn_le (d : ContMetric) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.log (GM.crossFn d.1) ≤ Real.log (d.1 ((s : ℂ) * Complex.I, 1 + (t : ℂ) * Complex.I)) :=
  Real.log_le_log (GM.crossFn_pos_contMetric d)
    (GM.crossFn_le (GM.bddBelow_crossSet_of_nonneg fun p => contMetric_nonneg d p.1 p.2)
      (mk_mem_prod (sI_mem_leftSide hs) (one_add_tI_mem_rightSide ht)))

/-- If `c ≤ log D(is, 1 + it)` for all `s, t ∈ [0, 1]`, then `c ≤ log C`. -/
theorem le_log_crossFn (d : ContMetric) {c : ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      c ≤ Real.log (d.1 ((s : ℂ) * Complex.I, 1 + (t : ℂ) * Complex.I))) :
    c ≤ Real.log (GM.crossFn d.1) := by
  have hpos := GM.crossFn_pos_contMetric d
  rw [Real.le_log_iff_exp_le hpos]
  refine GM.le_crossFn fun p hp => ?_
  obtain ⟨⟨hu0, hu1, hu2⟩, ⟨hv0, hv1, hv2⟩⟩ := hp
  have hu : p.1 = ((p.1.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hu0]
  have hv : p.2 = 1 + ((p.2.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hv0]
  have hd : 0 < d.1 p := by
    refine contMetric_pos d fun e => ?_
    have := congrArg Complex.re e
    rw [hu0, hv0] at this
    exact zero_ne_one this
  have key := h p.1.im ⟨hu1, hu2⟩ p.2.im ⟨hv1, hv2⟩
  rw [← hu, ← hv, Prod.mk.eta, Real.le_log_iff_exp_le hd] at key
  exact key

/-! ## The deterministic discretization step -/

/-- `|a i - b i| = |a - b|`. -/
theorem norm_ofReal_mul_I_sub (a b : ℝ) :
    ‖(a : ℂ) * Complex.I - (b : ℂ) * Complex.I‖ = |a - b| := by
  rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]

/-- `|(1 + a i) - (1 + b i)| = |a - b|`. -/
theorem norm_one_add_ofReal_mul_I_sub (a b : ℝ) :
    ‖(1 + (a : ℂ) * Complex.I) - (1 + (b : ℂ) * Complex.I)‖ = |a - b| := by
  rw [add_sub_add_left_eq_sub, norm_ofReal_mul_I_sub]

theorem re_ofReal_mul_I (a : ℝ) : ((a : ℂ) * Complex.I).re = 0 := by simp

theorem re_one_add_ofReal_mul_I (a : ℝ) : (1 + (a : ℂ) * Complex.I).re = 1 := by simp

/-- Every `s ∈ [0, 1]` is within `2^{-m}` of a grid point `k 2^{-m}`, `k ≤ 2^m`. -/
theorem exists_grid_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    ∃ k : ℕ, k ≤ 2 ^ m ∧ |(k : ℝ) / 2 ^ m - s| ≤ 1 / 2 ^ m := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hs0 : 0 ≤ s * 2 ^ m := mul_nonneg hs.1 h2.le
  refine ⟨⌊s * 2 ^ m⌋₊, ?_, ?_⟩
  · have h : s * 2 ^ m ≤ ((2 ^ m : ℕ) : ℝ) := by
      push_cast
      nlinarith [hs.2]
    exact Nat.floor_le_of_le h
  · have h1 := Nat.floor_le hs0
    have h2' := Nat.lt_floor_add_one (s * 2 ^ m)
    have hk1 : (⌊s * 2 ^ m⌋₊ : ℝ) / 2 ^ m ≤ s := by
      rw [div_le_iff₀ h2]
      exact h1
    have hk2 : s < ((⌊s * 2 ^ m⌋₊ : ℝ) + 1) / 2 ^ m := by
      rw [lt_div_iff₀ h2]
      exact h2'
    have hk3 : ((⌊s * 2 ^ m⌋₊ : ℝ) + 1) / 2 ^ m =
        (⌊s * 2 ^ m⌋₊ : ℝ) / 2 ^ m + 1 / 2 ^ m := add_div _ _ _
    have hpos : 0 < 1 / (2 : ℝ) ^ m := one_div_pos.2 h2
    rw [abs_le]
    constructor <;> linarith

/-- **The discretization step of the lower bound** (blueprint proof of Proposition `prop:crossing`,
(eq:lower-grid)). Let `d` be a continuous metric, `K > 0` and `m : ℕ`, such that
`d(z, w) ≤ K |z - w|^{1/2}` on the unit square, `d(is, 1 + it) ≥ K⁻¹` for `s, t ∈ [0, 1]`, and
`log d(i k 2^{-m}, 1 + i l 2^{-m}) ≥ L` for all `k, l ≤ 2^m`. Then
`log C ≥ L - 2 K² (2^{-m})^{1/2}`, where `C` is the left–right crossing distance of the square.
(For grid neighbours, `|log D(is, 1+it) - log D(is', 1+it')| ≤ (D(is, is') + D(1+it, 1+it'))/I`.) -/
theorem log_crossFn_ge_of_grid (d : ContMetric) {K L : ℝ} (hK : 0 < K) (m : ℕ)
    (hA : ∀ z ∈ unitSquare, ∀ w ∈ unitSquare, d.1 (z, w) ≤ K * ‖z - w‖ ^ (1 / 2 : ℝ))
    (hI : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      K⁻¹ ≤ d.1 ((s : ℂ) * Complex.I, 1 + (t : ℂ) * Complex.I))
    (hgrid : ∀ k : ℕ, k ≤ 2 ^ m → ∀ l : ℕ, l ≤ 2 ^ m →
      L ≤ Real.log (d.1 ((((k : ℝ) / 2 ^ m : ℝ) : ℂ) * Complex.I,
        1 + (((l : ℝ) / 2 ^ m : ℝ) : ℂ) * Complex.I))) :
    L - 2 * K ^ 2 * (1 / (2 : ℝ) ^ m) ^ (1 / 2 : ℝ) ≤ Real.log (GM.crossFn d.1) := by
  refine le_log_crossFn d fun s hs t ht => ?_
  set δ₀ : ℝ := (1 / (2 : ℝ) ^ m) ^ (1 / 2 : ℝ) with hδ₀
  have hδ₀0 : 0 ≤ δ₀ := by positivity
  obtain ⟨k, hk, hks⟩ := exists_grid_le hs m
  obtain ⟨l, hl, hlt⟩ := exists_grid_le ht m
  set zk : ℂ := (((k : ℝ) / 2 ^ m : ℝ) : ℂ) * Complex.I with hzk
  set wl : ℂ := 1 + (((l : ℝ) / 2 ^ m : ℝ) : ℂ) * Complex.I with hwl
  have hzkS : zk ∈ unitSquare := sI_mem_unitSquare (div_two_pow_mem_Icc hk)
  have hwlS : wl ∈ unitSquare := one_add_tI_mem_unitSquare (div_two_pow_mem_Icc hl)
  set D := d.1 ((s : ℂ) * Complex.I, 1 + (t : ℂ) * Complex.I) with hDdef
  set Dg := d.1 (zk, wl) with hDg
  have hD : K⁻¹ ≤ D := hI s hs t ht
  have hDpos : 0 < D := lt_of_lt_of_le (inv_pos.2 hK) hD
  -- the two short segments
  have h1 : d.1 (zk, (s : ℂ) * Complex.I) ≤ K * δ₀ := by
    refine (hA zk hzkS _ (sI_mem_unitSquare hs)).trans (mul_le_mul_of_nonneg_left ?_ hK.le)
    rw [hzk, norm_ofReal_mul_I_sub]
    exact Real.rpow_le_rpow (abs_nonneg _) hks (by norm_num)
  have h2 : d.1 (1 + (t : ℂ) * Complex.I, wl) ≤ K * δ₀ := by
    refine (hA _ (one_add_tI_mem_unitSquare ht) wl hwlS).trans
      (mul_le_mul_of_nonneg_left ?_ hK.le)
    rw [hwl, norm_one_add_ofReal_mul_I_sub, abs_sub_comm]
    exact Real.rpow_le_rpow (abs_nonneg _) hlt (by norm_num)
  have htri : Dg ≤ d.1 (zk, (s : ℂ) * Complex.I) + D + d.1 (1 + (t : ℂ) * Complex.I, wl) := by
    have e1 := d.2.triangle zk ((s : ℂ) * Complex.I) wl
    have e2 := d.2.triangle ((s : ℂ) * Complex.I) (1 + (t : ℂ) * Complex.I) wl
    linarith
  have hKD : 2 * K * δ₀ ≤ 2 * K ^ 2 * δ₀ * D := by
    have h3 : 1 ≤ K * D := by
      rw [← inv_mul_cancel₀ hK.ne', mul_comm K⁻¹ K]
      exact mul_le_mul_of_nonneg_left hD hK.le
    calc 2 * K * δ₀ = 2 * K * δ₀ * 1 := by ring
      _ ≤ 2 * K * δ₀ * (K * D) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * K ^ 2 * δ₀ * D := by ring
  have hDgle : Dg ≤ D * (1 + 2 * K ^ 2 * δ₀) := by nlinarith
  have hDgpos : 0 < Dg := by
    refine contMetric_pos d fun e => ?_
    have h := congrArg Complex.re e
    rw [hzk, hwl, re_ofReal_mul_I, re_one_add_ofReal_mul_I] at h
    exact zero_ne_one h
  have hL := hgrid k hk l hl
  have hpos : 0 < 1 + 2 * K ^ 2 * δ₀ := by positivity
  have hlog : Real.log Dg ≤ Real.log D + 2 * K ^ 2 * δ₀ := by
    calc Real.log Dg ≤ Real.log (D * (1 + 2 * K ^ 2 * δ₀)) := Real.log_le_log hDgpos hDgle
      _ = Real.log D + Real.log (1 + 2 * K ^ 2 * δ₀) := Real.log_mul hDpos.ne' hpos.ne'
      _ ≤ Real.log D + 2 * K ^ 2 * δ₀ := by
          have := Real.log_le_sub_one_of_pos hpos
          linarith
  linarith

end Crossing

namespace Setup

variable (S : Setup)

/-! ## Gaussian tails of `H(s,t) - H(s,s)` -/

/-- **Lemma `lem:H-continuity`(a)** with Lemma `lem:gauss`: `H(s,t) - H(s,s)` is a centered
Gaussian of variance at most `6 |t - s|^{1/2}`, so `P[|H(s,t) - H(s,s)| ≥ x] ≤ 2 e^{-x²/(2V)}`
for every `V ≥ 6 |t - s|^{1/2}`. -/
theorem measure_H_sub_tail {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {V x : ℝ} (hvV : 6 * |t - s| ^ (1 / 2 : ℝ) ≤ V) (hx : 0 ≤ x) :
    stdP {ω | x ≤ |S.H s t ω - S.H s s ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-x ^ 2 / (2 * V))) := by
  refine Crossing.measure_le_abs_le_of_hasLaw_le (S.hasLaw_H_sub s t s s) ?_ hx
  rw [Real.coe_toNNReal']
  refine max_le ?_ ((by positivity : (0 : ℝ) ≤ 6 * |t - s| ^ (1 / 2 : ℝ)).trans hvV)
  have h := energy_segMeasure_sub_le hs ht hs hs
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h
  exact h.trans hvV

end Setup

end GaussianLQG
