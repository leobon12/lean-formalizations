import SmallGammaGeodesics.Core.PathFunctionals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UnitInterval

/-!
# Approximate geodesics and the clock geometry (source (4.1); packet P-A4)

Source: `source/small-parameter-lqg-geodesics.pdf`, §3 (proof of Lemma 3.1) and §4.1, display (4.1).
Mathematics: planning audit GA2 (`planning/audits/GA2-sections-3-4.md`), "Details for later use",
D1 (steps (i)–(v) of the proof of Lemma 3.1′) and D3 (clock geometry).

Standing hypotheses (`ApproxGeod d η Δ`): `d : ℂ × ℂ → ℝ` is **any** function (no metric axiom is
used) with `|d(z,w) - |z-w|| ≤ Δ` for `|z|, |w| ≤ 3`, where `0 ≤ Δ ≤ 1/100`, and
`η : [0,1] → ℂ` is continuous with `η 0 = 0`, `η 1 = 1` and the constant-speed identity
`d(η s, η t) = |t - s| d(0,1)`. Write `η = x + iy` and `M = maxDev η`.

* `ApproxGeod.norm_lt_two`: `|η| < 2` (a first exit from `B₂` would cost more than `d(0,1)`).
* `ApproxGeod.abs_norm_sub_le`, `ApproxGeod.abs_norm_sub_one_sub_le`:
  `||η t| - t| ≤ 2Δ`, `||η t - 1| - (1-t)| ≤ 2Δ`.
* `ApproxGeod.norm_add_norm_sub_one_le`: `|η t| + |η t - 1| ≤ 1 + 3Δ`; hence
  `ApproxGeod.maxDev_le_sqrt`: `M ≤ √(3Δ)`.
* `ApproxGeod.abs_re_sub_le`: `|x(t) - t| ≤ 3Δ`.
* `ApproxGeod.abs_im_sub_le`: `|y(t) - y(s)| ≤ 5 √(|t-s| Δ) + 8Δ`.
* `ApproxGeod.maxDev_le_iSup_abs_im`: `M ≤ sup |y| + 3Δ`.
* `ApproxGeod.norm_sub_le_two_mul`: `|η t - t| ≤ 2(M + Δ)`.
* `clock_geometry`: the statement of GA2 Details (c), with the frozen `maxDev` for `heightDev`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SmallGammaGeodesics

/-- The standing hypotheses of Lemma 3.1′ and of the clock geometry (4.1) (planning audit GA2,
Details D1 and D3): `d : ℂ × ℂ → ℝ` is any function (no metric axiom is used) with additive
Euclidean error at most `Δ ∈ [0, 1/100]` on `B̄₃(0)`, and `η` is a constant-speed `d`-geodesic
from `0` to `1`. -/
structure ApproxGeod (d : ℂ × ℂ → ℝ) (η : C(unitInterval, ℂ)) (Δ : ℝ) : Prop where
  nonneg : 0 ≤ Δ
  le : Δ ≤ 1 / 100
  err : ∀ z w : ℂ, ‖z‖ ≤ 3 → ‖w‖ ≤ 3 → |d (z, w) - ‖z - w‖| ≤ Δ
  zero : η 0 = 0
  one : η 1 = 1
  geod : ∀ s t : unitInterval, d (η s, η t) = |(t : ℝ) - s| * d (0, 1)

/-! ## The unit segment `[0,1] ⊆ ℂ` -/

theorem mem_segment_zero_one_iff {w : ℂ} :
    w ∈ segment ℝ (0 : ℂ) 1 ↔ ∃ a ∈ Icc (0 : ℝ) 1, (a : ℂ) = w := by
  rw [segment_eq_image]
  simp only [mem_image, smul_zero, zero_add, Complex.real_smul, mul_one]

theorem ofReal_mem_segment {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    (a : ℂ) ∈ segment ℝ (0 : ℂ) 1 :=
  mem_segment_zero_one_iff.2 ⟨a, ha, rfl⟩

/-- `|z| + |z - 1| ≥ √(1 + 4 (Im z)²)`, in squared form. -/
theorem one_add_four_mul_im_sq_le (z : ℂ) : 1 + 4 * z.im ^ 2 ≤ (‖z‖ + ‖z - 1‖) ^ 2 := by
  have h1 : ‖z - 1‖ = ‖1 - (starRingEnd ℂ) z‖ := by
    rw [← Complex.norm_conj (z - 1), map_sub, map_one, norm_sub_rev]
  have h2 : ‖z + (1 - (starRingEnd ℂ) z)‖ ≤ ‖z‖ + ‖z - 1‖ := by
    rw [h1]
    exact norm_add_le _ _
  have h3 : ‖z + (1 - (starRingEnd ℂ) z)‖ ^ 2 = 1 + 4 * z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.add_im,
      Complex.sub_im, Complex.one_im, Complex.conj_im]
    ring
  rw [← h3]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-- A point `z` of the ellipse `|z| + |z - 1| ≤ 1 + ε` (`0 ≤ ε ≤ 1`) is within `√ε` of `[0,1]`
(GA2 D1 (iv)). -/
theorem infDist_segment_le_sqrt {z : ℂ} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hz : ‖z‖ + ‖z - 1‖ ≤ 1 + ε) : infDist z (segment ℝ (0 : ℂ) 1) ≤ Real.sqrt ε := by
  have hεs : ε ≤ Real.sqrt ε := by
    rw [Real.le_sqrt hε hε]
    nlinarith
  rcases lt_or_ge z.re 0 with hre | hre
  · -- left of the segment: the nearest point is `0`
    have h1 : 1 ≤ ‖z - 1‖ := by
      have := Complex.abs_re_le_norm (z - 1)
      rw [Complex.sub_re, Complex.one_re, abs_of_neg (by linarith)] at this
      linarith
    calc infDist z (segment ℝ (0 : ℂ) 1) ≤ dist z 0 :=
          infDist_le_dist_of_mem (left_mem_segment ℝ 0 1)
      _ = ‖z‖ := by rw [dist_zero_right]
      _ ≤ ε := by linarith
      _ ≤ Real.sqrt ε := hεs
  rcases le_or_gt z.re 1 with hre1 | hre1
  · -- above or below the segment: the nearest point is `Re z`
    have hmem : ((z.re : ℝ) : ℂ) ∈ segment ℝ (0 : ℂ) 1 := ofReal_mem_segment ⟨hre, hre1⟩
    have hd : dist z (z.re : ℂ) = |z.im| := by
      rw [Complex.dist_eq]
      have e : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hsq : z.im ^ 2 ≤ ε := by
      have h1 := one_add_four_mul_im_sq_le z
      have h2 : (‖z‖ + ‖z - 1‖) ^ 2 ≤ (1 + ε) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hz 2
      nlinarith
    calc infDist z (segment ℝ (0 : ℂ) 1) ≤ dist z (z.re : ℂ) := infDist_le_dist_of_mem hmem
      _ = |z.im| := hd
      _ = Real.sqrt (z.im ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ε := Real.sqrt_le_sqrt hsq
  · -- right of the segment: the nearest point is `1`
    have h1 : 1 < ‖z‖ := lt_of_lt_of_le hre1 ((le_abs_self _).trans (Complex.abs_re_le_norm z))
    calc infDist z (segment ℝ (0 : ℂ) 1) ≤ dist z 1 :=
          infDist_le_dist_of_mem (right_mem_segment ℝ 0 1)
      _ = ‖z - 1‖ := Complex.dist_eq z 1
      _ ≤ ε := by linarith
      _ ≤ Real.sqrt ε := hεs

namespace ApproxGeod

variable {d : ℂ × ℂ → ℝ} {η : C(unitInterval, ℂ)} {Δ : ℝ}

/-! ## D1 (ii)–(iv): the clock -/

/-- `|d(0,1) - 1| ≤ Δ` (GA2 D1 (ii)). -/
theorem abs_d01_sub_one_le (h : ApproxGeod d η Δ) : |d (0, 1) - 1| ≤ Δ := by
  have h1 := h.err 0 1 (by norm_num) (by norm_num)
  rwa [show ‖(0 : ℂ) - 1‖ = 1 by norm_num] at h1

theorem d01_le (h : ApproxGeod d η Δ) : d (0, 1) ≤ 1 + Δ := by
  have := (abs_le.1 h.abs_d01_sub_one_le).2
  linarith

theorem le_d01 (h : ApproxGeod d η Δ) : 1 - Δ ≤ d (0, 1) := by
  have := (abs_le.1 h.abs_d01_sub_one_le).1
  linarith

/-- `d(0, η t) = t d(0,1)`. -/
theorem d_zero_eq (h : ApproxGeod d η Δ) (t : unitInterval) : d (0, η t) = t * d (0, 1) := by
  have h1 := h.geod 0 t
  rwa [h.zero, Set.Icc.coe_zero, sub_zero, abs_of_nonneg t.2.1] at h1

/-- `d(η t, 1) = (1 - t) d(0,1)`. -/
theorem d_one_eq (h : ApproxGeod d η Δ) (t : unitInterval) : d (η t, 1) = (1 - t) * d (0, 1) := by
  have h1 := h.geod t 1
  rwa [h.one, Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.2 t.2.2)] at h1

/-- **GA2 D1 (i)**: `|η t| < 2`. If `|η τ| = 2` for some `τ` (intermediate value theorem), then
`d(0,1) = d(0, η τ) + d(η τ, 1) ≥ (2 - Δ) + (1 - Δ) > 1 + Δ`. -/
theorem norm_lt_two (h : ApproxGeod d η Δ) (t : unitInterval) : ‖η t‖ < 2 := by
  by_contra hcon
  have hcon : 2 ≤ ‖η t‖ := le_of_not_gt hcon
  have hcont : Continuous fun s : unitInterval => ‖η s‖ := continuous_norm.comp η.continuous
  have h2mem : (2 : ℝ) ∈ Icc ‖η 0‖ ‖η t‖ := ⟨by rw [h.zero, norm_zero]; norm_num, hcon⟩
  obtain ⟨τ, hτ⟩ := intermediate_value_univ 0 t hcont h2mem
  simp only at hτ
  have hτ3 : ‖η τ‖ ≤ 3 := by rw [hτ]; norm_num
  have e1 := h.err 0 (η τ) (by norm_num) hτ3
  have e2 := h.err (η τ) 1 hτ3 (by norm_num)
  have n1 : ‖(0 : ℂ) - η τ‖ = 2 := by rw [zero_sub, norm_neg, hτ]
  have n2 : 1 ≤ ‖η τ - 1‖ := by
    have := norm_sub_norm_le (η τ) 1
    rw [hτ, norm_one] at this
    linarith
  rw [n1] at e1
  have hsum : d (0, η τ) + d (η τ, 1) = d (0, 1) := by
    rw [h.d_zero_eq τ, h.d_one_eq τ]
    ring
  linarith [(abs_le.1 e1).1, (abs_le.1 e2).1, h.d01_le, h.le]

theorem norm_le_three (h : ApproxGeod d η Δ) (t : unitInterval) : ‖η t‖ ≤ 3 :=
  (h.norm_lt_two t).le.trans (by norm_num)

/-- `|t d(0,1) - t| ≤ Δ` for `t ∈ [0,1]`. -/
theorem abs_mul_d01_sub_le (h : ApproxGeod d η Δ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |t * d (0, 1) - t| ≤ Δ := by
  rw [show t * d (0, 1) - t = t * (d (0, 1) - 1) by ring, abs_mul, abs_of_nonneg ht0]
  calc t * |d (0, 1) - 1| ≤ 1 * Δ :=
        mul_le_mul ht1 h.abs_d01_sub_one_le (abs_nonneg _) zero_le_one
    _ = Δ := one_mul Δ

/-- **GA2 D1 (iii)**: `||η t| - t| ≤ 2Δ`. -/
theorem abs_norm_sub_le (h : ApproxGeod d η Δ) (t : unitInterval) : |‖η t‖ - t| ≤ 2 * Δ := by
  have e := h.err 0 (η t) (by norm_num) (h.norm_le_three t)
  rw [zero_sub, norm_neg, h.d_zero_eq t] at e
  have e2 := h.abs_mul_d01_sub_le t.2.1 t.2.2
  calc |‖η t‖ - t| = |(‖η t‖ - t * d (0, 1)) + (t * d (0, 1) - t)| := by ring_nf
    _ ≤ |‖η t‖ - t * d (0, 1)| + |t * d (0, 1) - t| := abs_add_le _ _
    _ ≤ Δ + Δ := by rw [abs_sub_comm]; exact add_le_add e e2
    _ = 2 * Δ := by ring

/-- **GA2 D1 (iii)**: `||η t - 1| - (1 - t)| ≤ 2Δ`. -/
theorem abs_norm_sub_one_sub_le (h : ApproxGeod d η Δ) (t : unitInterval) :
    |‖η t - 1‖ - (1 - t)| ≤ 2 * Δ := by
  have e := h.err (η t) 1 (h.norm_le_three t) (by norm_num)
  rw [h.d_one_eq t] at e
  have e2 := h.abs_mul_d01_sub_le (sub_nonneg.2 t.2.2) (by linarith [t.2.1] : 1 - (t : ℝ) ≤ 1)
  calc |‖η t - 1‖ - (1 - t)|
      = |(‖η t - 1‖ - (1 - t) * d (0, 1)) + ((1 - t) * d (0, 1) - (1 - t))| := by ring_nf
    _ ≤ |‖η t - 1‖ - (1 - t) * d (0, 1)| + |(1 - t) * d (0, 1) - (1 - t)| := abs_add_le _ _
    _ ≤ Δ + Δ := by rw [abs_sub_comm]; exact add_le_add e e2
    _ = 2 * Δ := by ring

/-- **GA2 D1 (iv)**: `|η t| + |η t - 1| ≤ d(0,1) + 2Δ ≤ 1 + 3Δ`. -/
theorem norm_add_norm_sub_one_le (h : ApproxGeod d η Δ) (t : unitInterval) :
    ‖η t‖ + ‖η t - 1‖ ≤ 1 + 3 * Δ := by
  have e1 := h.err 0 (η t) (by norm_num) (h.norm_le_three t)
  have e2 := h.err (η t) 1 (h.norm_le_three t) (by norm_num)
  rw [zero_sub, norm_neg, h.d_zero_eq t] at e1
  rw [h.d_one_eq t] at e2
  linarith [(abs_le.1 e1).1, (abs_le.1 e2).1, h.d01_le]

/-- **GA2 D1 (iv)**: `M ≤ √(3Δ)`. -/
theorem maxDev_le_sqrt (h : ApproxGeod d η Δ) : maxDev η ≤ Real.sqrt (3 * Δ) := by
  refine ciSup_le fun t => ?_
  exact infDist_segment_le_sqrt (by linarith [h.nonneg]) (by linarith [h.le])
    (h.norm_add_norm_sub_one_le t)

/-- `M ≤ 2/5` (from `M ≤ √(3Δ)` and `Δ ≤ 1/100`). -/
theorem maxDev_le_two_fifths (h : ApproxGeod d η Δ) : maxDev η ≤ 2 / 5 := by
  refine h.maxDev_le_sqrt.trans ?_
  rw [Real.sqrt_le_left (by norm_num)]
  linarith [h.le]

/-! ## D3: the clock geometry -/

/-- **GA2 D3, step 1**: `|x(t) - t| ≤ 2Δ + 2Δ² ≤ 3Δ`, from `2x - 1 = |η|² - |η - 1|²`. -/
theorem abs_re_sub_le (h : ApproxGeod d η Δ) (t : unitInterval) : |(η t).re - t| ≤ 3 * Δ := by
  set x := (η t).re
  set y := (η t).im
  set a := ‖η t‖
  set b := ‖η t - 1‖
  have ha2 : a ^ 2 = x * x + y * y := by rw [Complex.sq_norm, Complex.normSq_apply]
  have hb2 : b ^ 2 = (x - 1) * (x - 1) + y * y := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, sub_zero]
  have hx : 2 * x - 1 = a ^ 2 - b ^ 2 := by rw [ha2, hb2]; ring
  set e₁ := a - t with he₁
  set e₂ := b - (1 - t) with he₂
  have h1 : |e₁| ≤ 2 * Δ := h.abs_norm_sub_le t
  have h2 : |e₂| ≤ 2 * Δ := h.abs_norm_sub_one_sub_le t
  have key : 2 * (x - t) = 2 * t * e₁ - 2 * (1 - t) * e₂ + e₁ ^ 2 - e₂ ^ 2 := by
    have ea : a = t + e₁ := by rw [he₁]; ring
    have eb : b = 1 - t + e₂ := by rw [he₂]; ring
    have : 2 * x - 1 = (t + e₁) ^ 2 - (1 - t + e₂) ^ 2 := by rw [hx, ea, eb]
    linear_combination this
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hΔ0 := h.nonneg
  have hΔ1 := h.le
  obtain ⟨h1l, h1u⟩ := abs_le.1 h1
  obtain ⟨h2l, h2u⟩ := abs_le.1 h2
  have p1 : t * e₁ ≤ t * (2 * Δ) := mul_le_mul_of_nonneg_left h1u ht0
  have p2 : t * (-(2 * Δ)) ≤ t * e₁ := mul_le_mul_of_nonneg_left h1l ht0
  have p3 : (1 - t) * e₂ ≤ (1 - t) * (2 * Δ) := mul_le_mul_of_nonneg_left h2u (by linarith)
  have p4 : (1 - t) * (-(2 * Δ)) ≤ (1 - t) * e₂ := mul_le_mul_of_nonneg_left h2l (by linarith)
  have q1 : e₁ ^ 2 ≤ (2 * Δ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have q2 : e₂ ^ 2 ≤ (2 * Δ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have q3 : 0 ≤ e₁ ^ 2 := sq_nonneg _
  have q4 : 0 ≤ e₂ ^ 2 := sq_nonneg _
  have q5 : (2 * Δ) ^ 2 ≤ 2 * Δ / 25 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- `|η t - η s| ≤ |t - s| (1 + Δ) + Δ`. -/
theorem norm_sub_le (h : ApproxGeod d η Δ) (s t : unitInterval) :
    ‖η t - η s‖ ≤ |(t : ℝ) - s| * (1 + Δ) + Δ := by
  have e := h.err (η s) (η t) (h.norm_le_three s) (h.norm_le_three t)
  rw [h.geod s t, norm_sub_rev] at e
  have h1 := (abs_le.1 e).1
  have h2 : |(t : ℝ) - s| * d (0, 1) ≤ |(t : ℝ) - s| * (1 + Δ) :=
    mul_le_mul_of_nonneg_left h.d01_le (abs_nonneg _)
  linarith

/-- **GA2 D3, step 2**: `|y(t) - y(s)| ≤ 5 √(|t-s| Δ) + 8Δ`. -/
theorem abs_im_sub_le (h : ApproxGeod d η Δ) (s t : unitInterval) :
    |(η t).im - (η s).im| ≤ 5 * Real.sqrt (|(t : ℝ) - s| * Δ) + 8 * Δ := by
  have hΔ0 := h.nonneg
  have hΔ1 := h.le
  set D := |(t : ℝ) - s| with hD
  have hD0 : 0 ≤ D := abs_nonneg _
  have hD1 : D ≤ 1 := by
    rw [hD, abs_le]
    constructor <;> linarith [s.2.1, s.2.2, t.2.1, t.2.2]
  set X := |(η t).re - (η s).re|
  set Y := |(η t).im - (η s).im|
  have hX0 : 0 ≤ X := abs_nonneg _
  have hY0 : 0 ≤ Y := abs_nonneg _
  -- `X² + Y² = |η t - η s|²`
  have hXY : X ^ 2 + Y ^ 2 = ‖η t - η s‖ ^ 2 := by
    rw [sq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hN := h.norm_sub_le s t
  have hN0 : 0 ≤ ‖η t - η s‖ := norm_nonneg _
  have hsq : ‖η t - η s‖ ^ 2 ≤ (D * (1 + Δ) + Δ) ^ 2 := pow_le_pow_left₀ hN0 hN 2
  -- `X ≥ D - 6Δ`
  have hX : D - 6 * Δ ≤ X := by
    have r1 := h.abs_re_sub_le t
    have r2 := h.abs_re_sub_le s
    have tri : |(t : ℝ) - s| ≤ |(η t).re - t| + |(η t).re - (η s).re| + |(η s).re - s| := by
      calc |(t : ℝ) - s| = |-((η t).re - t) + ((η t).re - (η s).re) + ((η s).re - s)| := by
            ring_nf
        _ ≤ |-((η t).re - t) + ((η t).re - (η s).re)| + |(η s).re - s| := abs_add_le _ _
        _ ≤ |-((η t).re - t)| + |(η t).re - (η s).re| + |(η s).re - s| := by
            gcongr; exact abs_add_le _ _
        _ = |(η t).re - t| + |(η t).re - (η s).re| + |(η s).re - s| := by rw [abs_neg]
    linarith
  have hY_le_N : Y ≤ ‖η t - η s‖ := by
    have := Complex.abs_im_le_norm (η t - η s)
    rwa [Complex.sub_im] at this
  have hs0 : 0 ≤ Real.sqrt (D * Δ) := Real.sqrt_nonneg _
  rcases le_or_gt (6 * Δ) D with hcase | hcase
  · -- `|t - s| ≥ 6Δ`: `Y² ≤ a² - b² = (a - b)(a + b) ≤ 8Δ (2 + Δ) |t - s| ≤ 25 |t - s| Δ`
    have hb0 : 0 ≤ D - 6 * Δ := by linarith
    have hXb : (D - 6 * Δ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hb0 hX 2
    have hab : (D * (1 + Δ) + Δ) ^ 2 - (D - 6 * Δ) ^ 2 =
        Δ * (D + 7) * (D * (2 + Δ) - 5 * Δ) := by ring
    have hpos : 0 ≤ D * (2 + Δ) - 5 * Δ := by nlinarith
    have hle2 : D * (2 + Δ) - 5 * Δ ≤ 3 * D := by nlinarith
    have hprod : Δ * (D + 7) * (D * (2 + Δ) - 5 * Δ) ≤ Δ * 8 * (3 * D) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hΔ0) hle2 hpos (by positivity)
    have hDΔ : 0 ≤ D * Δ := mul_nonneg hD0 hΔ0
    have hY2 : Y ^ 2 ≤ 25 * (D * Δ) := by nlinarith
    have hYs : Y ≤ Real.sqrt (25 * (D * Δ)) :=
      (Real.le_sqrt hY0 (by positivity)).2 hY2
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 25),
      show Real.sqrt 25 = 5 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      at hYs
    linarith
  · -- `|t - s| < 6Δ`: `Y ≤ |η t - η s| ≤ 6Δ(1 + Δ) + Δ ≤ 8Δ`
    have : D * (1 + Δ) ≤ 6 * Δ * (1 + Δ) := mul_le_mul_of_nonneg_right hcase.le (by linarith)
    nlinarith

/-- **GA2 D3, step 3**: `M ≤ sup_t |y(t)| + 3Δ`. -/
theorem maxDev_le_iSup_abs_im (h : ApproxGeod d η Δ) :
    maxDev η ≤ (⨆ t : unitInterval, |(η t).im|) + 3 * Δ := by
  have hbdd : BddAbove (range fun t : unitInterval => |(η t).im|) :=
    (isCompact_range ((continuous_abs.comp Complex.continuous_im).comp η.continuous)).bddAbove
  refine ciSup_le fun t => ?_
  have hmem : ((t : ℝ) : ℂ) ∈ segment ℝ (0 : ℂ) 1 := ofReal_mem_segment ⟨t.2.1, t.2.2⟩
  calc infDist (η t) (segment ℝ (0 : ℂ) 1) ≤ dist (η t) ((t : ℝ) : ℂ) := infDist_le_dist_of_mem hmem
    _ = ‖η t - ((t : ℝ) : ℂ)‖ := Complex.dist_eq _ _
    _ ≤ |(η t - ((t : ℝ) : ℂ)).re| + |(η t - ((t : ℝ) : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |(η t).re - t| + |(η t).im| := by
        rw [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    _ ≤ 3 * Δ + ⨆ t : unitInterval, |(η t).im| :=
        add_le_add (h.abs_re_sub_le t) (le_ciSup hbdd t)
    _ = (⨆ t : unitInterval, |(η t).im|) + 3 * Δ := add_comm _ _

/-- **GA2 D1 (v)**: `|η t - t| ≤ 2(M + Δ)`. For `w ∈ [0,1]`,
`|η t - t| ≤ |η t - w| + ||w| - |η t|| + ||η t| - t| ≤ 2|η t - w| + 2Δ`; take `w` almost nearest. -/
theorem norm_sub_le_two_mul (h : ApproxGeod d η Δ) (t : unitInterval) :
    ‖η t - ((t : ℝ) : ℂ)‖ ≤ 2 * (maxDev η + Δ) := by
  have key : ∀ w ∈ segment ℝ (0 : ℂ) 1, ‖η t - ((t : ℝ) : ℂ)‖ ≤ 2 * dist (η t) w + 2 * Δ := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := mem_segment_zero_one_iff.1 hw
    have h1 : ‖η t - ((t : ℝ) : ℂ)‖ ≤ ‖η t - (a : ℂ)‖ + |a - t| := by
      calc ‖η t - ((t : ℝ) : ℂ)‖ = ‖(η t - (a : ℂ)) + ((a : ℂ) - ((t : ℝ) : ℂ))‖ := by ring_nf
        _ ≤ ‖η t - (a : ℂ)‖ + ‖(a : ℂ) - ((t : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = ‖η t - (a : ℂ)‖ + |a - t| := by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h2 : |a - t| ≤ ‖η t - (a : ℂ)‖ + 2 * Δ := by
      have e1 : |a - ‖η t‖| ≤ ‖η t - (a : ℂ)‖ := by
        have := abs_norm_sub_norm_le (a : ℂ) (η t)
        rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.1, norm_sub_rev] at this
      have e2 := h.abs_norm_sub_le t
      calc |a - t| = |(a - ‖η t‖) + (‖η t‖ - t)| := by ring_nf
        _ ≤ |a - ‖η t‖| + |‖η t‖ - t| := abs_add_le _ _
        _ ≤ ‖η t - (a : ℂ)‖ + 2 * Δ := add_le_add e1 e2
    rw [Complex.dist_eq]
    linarith
  -- pass to the infimum
  by_contra hcon
  have hcon : 2 * (maxDev η + Δ) < ‖η t - ((t : ℝ) : ℂ)‖ := lt_of_not_ge hcon
  have hlt : infDist (η t) (segment ℝ (0 : ℂ) 1) < (‖η t - ((t : ℝ) : ℂ)‖ - 2 * Δ) / 2 := by
    have := le_maxDev η t
    linarith
  obtain ⟨w, hw, hwd⟩ :=
    (infDist_lt_iff ⟨0, left_mem_segment ℝ 0 1⟩).1 hlt
  have := key w hw
  linarith

end ApproxGeod

/-! ## The clock geometry (4.1) -/

/-- **Clock geometry (4.1)** (deterministic; planning audit GA2, Details D3 and (c), with the frozen
`maxDev` for `heightDev`). For any function `d` with additive Euclidean error `Δ ≤ 1/100` on
`B̄₃(0)` and any constant-speed `d`-geodesic `η = x + iy` from `0` to `1`:
`|η| < 2`, `|x(t) - t| ≤ 3Δ`, `|y(t) - y(s)| ≤ 5√(|t-s|Δ) + 8Δ`, `M ≤ sup|y| + 3Δ` and
`M ≤ √(3Δ)`. -/
theorem clock_geometry :
    ∀ (d : ℂ × ℂ → ℝ) (η : C(unitInterval, ℂ)) (Δ : ℝ), 0 ≤ Δ → Δ ≤ 1 / 100 →
      (∀ z w : ℂ, ‖z‖ ≤ 3 → ‖w‖ ≤ 3 → |d (z, w) - ‖z - w‖| ≤ Δ) →
      η 0 = 0 → η 1 = 1 → (∀ s t : unitInterval, d (η s, η t) = |(t : ℝ) - s| * d (0, 1)) →
      (∀ t : unitInterval, ‖η t‖ < 2) ∧
      (∀ t : unitInterval, |(η t).re - t| ≤ 3 * Δ) ∧
      (∀ s t : unitInterval, |(η t).im - (η s).im| ≤ 5 * Real.sqrt (|(t : ℝ) - s| * Δ) + 8 * Δ) ∧
      maxDev η ≤ (⨆ t : unitInterval, |(η t).im|) + 3 * Δ ∧
      maxDev η ≤ Real.sqrt (3 * Δ) := by
  intro d η Δ hΔ0 hΔ hd h0 h1 hgeo
  have h : ApproxGeod d η Δ := ⟨hΔ0, hΔ, hd, h0, h1, hgeo⟩
  exact ⟨h.norm_lt_two, h.abs_re_sub_le, h.abs_im_sub_le, h.maxDev_le_iSup_abs_im,
    h.maxDev_le_sqrt⟩

end SmallGammaGeodesics
