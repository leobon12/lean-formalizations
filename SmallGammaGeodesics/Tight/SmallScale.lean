import GaussianLQG.LQG.Scaling.LogMoments
import GaussianLQG.LQG.Exponents

/-!
# Lemma 6.0: the uniform small-scale lower bound for `e^{-b_γ} D` (packet P-T0, target T1)

Source: `source/small-parameter-lqg-geodesics.pdf`, §6.3 and Theorem 1.2, as corrected by planning
audit GA3 (`planning/audits/GA3-sections-5-6.md`, Details A11; table rows X14, X15; rulings G8,
G12). The metric is normalized by `e^{-b_γ}` with `b_γ = E log D(0,1)` (`Setup.b`, ruling G8).

**Lemma 6.0** (`smallScale_lower`). For every GaussianLQG coordinate `Setup` and every `ε > 0` there
are `n ∈ ℕ` and `γs > 0` such that for `γ ∈ (0, γs]`,
`P[∃ z, w ∈ B̄₂ : 0 < |z-w| ≤ 2^{-n}, e^{-b_γ} D(z,w) < |z-w|^{5/4}] ≤ ε`.

## Proof (GA3 A11, with the internal choices recorded)

Fix `γ ∈ (0, γs]`. Then `0 < ξ ≤ 1/64`, `p := ξQ ≤ 17/16` (`Setup.exists_exponents`),
`|b_γ| ≤ C_b` (`Setup.abs_b_le`) and `E[I^{-32}] ≤ C₆` for `I := I_D(B̄₂, 1/2)` (`Setup.S6` with
`p = 32`). Put `C_* = e^{C_b}`, so `e^{-b_γ} C_* ≥ 1`.

For a scale `n` put `r = 2^{-n}`, `L = n log 2 = log(1/r)`, `N = 2·2^n` and let the grid be
`{r(j + k i) : |j|, |k| ≤ N}` (`gridPt`, `gridBox`). It has `(2N+1)² ≤ 25·4^n` points, each of
norm `≤ 4`, and every point of `B̄₂` lies within `r` of one of them (`exists_gridPt_near`). For a
grid point `z`:

* (Gaussian event, `gaussBad`) `{L/(16ξ) ≤ -h_r(z)}`, where `h_r(z)` is the circle average
  (`pairing` with `circleMeasure z r`), of law `N(0, ℰ)` with
  `ℰ ≤ log(1/r) + 2 log⁺(|z| + r) ≤ L + 10` (`energy_circleMeasure_le`). If `L ≥ 10`, Chernoff
  with the variance majorant `L + 10 ≤ 2L` and `x = L/(16ξ) ≥ 4L` gives probability
  `≤ e^{-x²/(2(L+10))} ≤ e^{-4L} = r⁴` (`measure_gaussBad_le`).
* (Metric event, `sepBad`) `{I'_{z,r} ≤ C_* r^{1/8}}`, where `I'_{z,r} = I(B̄₂, 1/2)` of the
  rescaled metric `D'(u,v) = r^{-p} e^{-ξ h_r(z)} D(z + ru, z + rv)` of (S4) (`Setup.rescaled`),
  which has the law of `D`. Markov with the 32nd inverse moment gives probability
  `≤ C₆ (C_* r^{1/8})^{32} = C₆ C_*^{32} r⁴` (`measure_sepBad_le`).

So the union over the grid at scale `n` has probability `≤ 25 (1/4)^n (1 + C_*^{32} C₆)`
(`measure_scaleBad_le`), and the union over `n ≥ n₀` is at most
`(100/3)(1/4)^{n₀}(1 + C_*^{32} C₆) ≤ ε` for `n₀` large.

Deterministic inclusion (`subset_iUnion_scaleBad`): let `z', w' ∈ B̄₂` with
`0 < ρ := |z'-w'| ≤ 2^{-n₀}` and `e^{-b} D(z',w') < ρ^{5/4}`. Take `m ≥ n₀` with `r/2 < ρ ≤ r`,
`r = 2^{-m}`, and a grid point `z` with `|z' - z| ≤ r`. With `u = (z'-z)/r`, `v = (w'-z)/r` we get
`u, v ∈ B̄₂`, `|u - v| > 1/2` and `D(z',w') = r^p e^{ξ h_r(z)} D'(u,v)`. Off both events,
`e^{ξ h_r(z)} > r^{1/16}` and `D'(u,v) ≥ I'_{z,r} > C_* r^{1/8}`, so
`e^{-b} D(z',w') > r^{p + 3/16} ≥ r^{5/4} ≥ ρ^{5/4}` because `p + 3/16 ≤ 5/4` (`key_real`); a
contradiction.

## Adjustments to the internal argument of GA3 A11 (allowed by the packet)

* Grid: mesh `r` (not `r/8`) on the box `[-N, N]²`, `N = 2·2^n`, instead of `(r/8)(ℤ + iℤ) ∩ B̄₃`.
  Then `|u| ≤ 1`, `|v| ≤ 2`, and the grid points have `|z| ≤ 4`.
* Variance bound: `ℰ(σ_{z,r}, σ_{z,r}) ≤ log(1/r) + 10` for `|z| ≤ 4`, `r ≤ 1` (instead of `+3` on
  `B̄₃`); the Gaussian bound needs `n log 2 ≥ 10` (instead of `log(1/r) ≥ 3`), which only enlarges
  `n_ε`.
* The normalizing constant: `C_* = e^{C_b}` with `|b_γ| ≤ C_b`.
* `γs = min(γ_e, γ_b, γ₆, 1/64, 1/(16(|C₁|+1)))`, which gives `ξ ≤ 1/64` and `ξQ ≤ 17/16`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace SmallGammaGeodesics

open GaussianLQG

namespace SmallScale

/-! ## A Gaussian lower tail with a variance majorant -/

/-- Chernoff lower tail with a variance majorant: if `X ∼ N(0, v)` and `v ≤ V` with `V > 0`, then
`P[X ≤ -x] ≤ e^{-x²/(2V)}` for `x ≥ 0`. -/
theorem measure_le_neg_le_of_hasLaw_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) {V x : ℝ} (hV : (v : ℝ) ≤ V) (hV0 : 0 < V)
    (hx : 0 ≤ x) : P {ω | x ≤ -X ω} ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * V))) := by
  have hX' := hasLaw_neg_of_hasLaw_gaussianReal hX
  have h := measure_ge_le_exp_mul_mgf (X := fun ω => -X ω) (μ := P) x (t := x / V)
    (div_nonneg hx hV0.le) (integrable_exp_mul_of_hasLaw_gaussianReal hX' _)
  rw [mgf_gaussianReal hX', ← Real.exp_add] at h
  have hexp : -(x / V) * x + (0 * (x / V) + (v : ℝ) * (x / V) ^ 2 / 2) ≤ -x ^ 2 / (2 * V) := by
    have key : (v : ℝ) * (x / V) ^ 2 / 2 ≤ V * (x / V) ^ 2 / 2 := by gcongr
    have e1 : -(x / V) * x + V * (x / V) ^ 2 / 2 = -x ^ 2 / (2 * V) := by
      field_simp
      ring
    linarith
  calc P {ω | x ≤ -X ω} = ENNReal.ofReal (P.real {ω | x ≤ -X ω}) :=
        (ofReal_measureReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * V))) :=
        ENNReal.ofReal_le_ofReal (h.trans (Real.exp_le_exp.2 hexp))

/-! ## Dyadic scales -/

theorem log_inv_two_pow (n : ℕ) : Real.log ((2 : ℝ)⁻¹ ^ n) = -(n * Real.log 2) := by
  rw [Real.log_pow, Real.log_inv]
  ring

theorem inv_two_pow_pos (n : ℕ) : 0 < (2 : ℝ)⁻¹ ^ n := pow_pos (by norm_num) n

theorem inv_two_pow_le_one (n : ℕ) : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

/-- `2^{-n} · 2^n = 1`. -/
theorem inv_two_pow_mul_two_pow (n : ℕ) : (2 : ℝ)⁻¹ ^ n * 2 ^ n = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]

/-- `(2^{-n})^a = e^{-a n log 2}`. -/
theorem inv_two_pow_rpow (n : ℕ) (a : ℝ) :
    ((2 : ℝ)⁻¹ ^ n) ^ a = Real.exp (-(n * Real.log 2) * a) := by
  rw [Real.rpow_def_of_pos (inv_two_pow_pos n), log_inv_two_pow]

/-- `(2^{-n})⁴ = e^{-4 n log 2}`. -/
theorem inv_two_pow_pow_four (n : ℕ) :
    ((2 : ℝ)⁻¹ ^ n) ^ 4 = Real.exp (-(4 * (n * Real.log 2))) := by
  rw [← Real.rpow_natCast, inv_two_pow_rpow]
  congr 1
  push_cast
  ring

/-! ## The grid -/

/-- The grid point `r (j + k i)` of the index `p = (j, k)`. -/
def gridPt (r : ℝ) (p : ℤ × ℤ) : ℂ := ⟨r * p.1, r * p.2⟩

/-- The index box `[-N, N]²`. -/
def gridBox (N : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N

theorem card_gridBox (N : ℕ) : (gridBox N).card = (2 * N + 1) ^ 2 := by
  have h : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    omega
  rw [gridBox, Finset.card_product, h, sq]

theorem abs_le_of_mem_Icc_int {N : ℕ} {j : ℤ} (hj : j ∈ Finset.Icc (-(N : ℤ)) N) :
    |(j : ℝ)| ≤ N := by
  rw [Finset.mem_Icc] at hj
  rw [abs_le]
  constructor
  · exact_mod_cast hj.1
  · exact_mod_cast hj.2

/-- Grid points of `gridBox N` have norm at most `2 r N`. -/
theorem norm_gridPt_le {r : ℝ} (hr : 0 ≤ r) {N : ℕ} {p : ℤ × ℤ} (hp : p ∈ gridBox N) :
    ‖gridPt r p‖ ≤ 2 * r * N := by
  rw [gridBox, Finset.mem_product] at hp
  have h1 := abs_le_of_mem_Icc_int hp.1
  have h2 := abs_le_of_mem_Icc_int hp.2
  calc ‖gridPt r p‖ ≤ |(gridPt r p).re| + |(gridPt r p).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = r * |(p.1 : ℝ)| + r * |(p.2 : ℝ)| := by
        simp only [gridPt, abs_mul, abs_of_nonneg hr]
    _ ≤ r * N + r * N := by gcongr
    _ = 2 * r * N := by ring

/-- Rounding: an integer within `1/2` of a real number of modulus `≤ N` lies in `[-N, N]`. -/
theorem round_mem_Icc {x : ℝ} {N : ℕ} (hx : |x| ≤ N) : round x ∈ Finset.Icc (-(N : ℤ)) N := by
  have h1 : |((round x : ℤ) : ℝ)| < N + 1 := by
    have h := abs_sub_round x
    have h' := abs_sub_abs_le_abs_sub ((round x : ℤ) : ℝ) x
    rw [abs_sub_comm] at h'
    linarith
  have h2 : |round x| < (N : ℤ) + 1 := by
    have : ((|round x| : ℤ) : ℝ) < ((N : ℤ) : ℝ) + 1 := by
      push_cast
      exact h1
    exact_mod_cast this
  rw [Finset.mem_Icc, ← abs_le]
  exact Int.lt_add_one_iff.mp h2

/-- `|x - r j| = r |x/r - j|`. -/
theorem abs_sub_mul_eq {r : ℝ} (hr : 0 < r) (x : ℝ) (j : ℝ) : |x - r * j| = r * |x / r - j| := by
  rw [← abs_of_pos hr, ← abs_mul, abs_of_pos hr]
  congr 1
  field_simp

/-- Every point of `B̄_{rN}(0)` lies within `r` of a grid point of `gridBox N`. -/
theorem exists_gridPt_near {r : ℝ} (hr : 0 < r) {N : ℕ} {z : ℂ} (hz : ‖z‖ ≤ r * N) :
    ∃ p ∈ gridBox N, ‖z - gridPt r p‖ ≤ r := by
  have hre : |z.re / r| ≤ N := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    calc |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      _ ≤ r * N := hz
      _ = N * r := mul_comm _ _
  have him : |z.im / r| ≤ N := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    calc |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      _ ≤ r * N := hz
      _ = N * r := mul_comm _ _
  refine ⟨(round (z.re / r), round (z.im / r)), ?_, ?_⟩
  · rw [gridBox, Finset.mem_product]
    exact ⟨round_mem_Icc hre, round_mem_Icc him⟩
  · have h1 := abs_sub_round (z.re / r)
    have h2 := abs_sub_round (z.im / r)
    calc ‖z - gridPt r (round (z.re / r), round (z.im / r))‖
        ≤ |(z - gridPt r (round (z.re / r), round (z.im / r))).re| +
          |(z - gridPt r (round (z.re / r), round (z.im / r))).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = r * |z.re / r - (round (z.re / r) : ℝ)| + r * |z.im / r - (round (z.im / r) : ℝ)| := by
          simp only [Complex.sub_re, Complex.sub_im, gridPt]
          rw [abs_sub_mul_eq hr, abs_sub_mul_eq hr]
      _ ≤ r * (1 / 2) + r * (1 / 2) := by gcongr
      _ = r := by ring

/-! ## The energy of circle measures at grid points -/

/-- `ℰ(σ_{z,r}, σ_{z,r}) ≤ log(1/r) + 10` for `|z| ≤ 4` and `0 < r ≤ 1`. -/
theorem energy_circleMeasure_le_of_norm_le {z : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hz : ‖z‖ ≤ 4) :
    energy (circleMeasure z r) (circleMeasure z r) ≤ Real.log r⁻¹ + 10 := by
  have h := energy_circleMeasure_le z hr
  have h1 : Real.posLog r⁻¹ = Real.log r⁻¹ := by
    refine Real.posLog_eq_log ?_
    rw [abs_of_pos (inv_pos.2 hr)]
    exact (one_le_inv₀ hr).2 hr1
  have h2 : Real.posLog (‖z‖ + r) ≤ 5 := by
    refine (Real.posLog_le_abs _).trans ?_
    rw [abs_of_nonneg (by positivity)]
    linarith
  linarith

/-! ## The bad events -/

/-- The Gaussian bad event at scale `r = 2^{-n}` and centre `z`: `n log 2 / (16 ξ) ≤ -h_r(z)`, i.e.
`ξ h_r(z) ≤ -(1/16) log(1/r)`. -/
def gaussBad (S : Setup) (γ : ℝ) (n : ℕ) (z : ℂ) : Set Coord :=
  {ω | (n * Real.log 2) / (16 * S.ξ γ) ≤ -pairing S.e (circleMeasure z ((2 : ℝ)⁻¹ ^ n)) ω}

/-- The metric bad event at scale `r = 2^{-n}` and centre `z`: the rescaled metric of (S4),
`D'(u,v) = r^{-ξQ} e^{-ξ h_r(z)} D(z + r u, z + r v)`, has `I_{D'}(B̄₂, 1/2) ≤ C r^{1/8}`. -/
def sepBad (S : Setup) (γ C : ℝ) (n : ℕ) (z : ℂ) : Set Coord :=
  {ω | sepInf (S.rescaled γ z (((2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) ω) (Metric.closedBall 0 2) (1 / 2) ≤
    ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ n) ^ (1 / 8 : ℝ))}

/-- All bad events at scale `n`, over the grid `gridBox (2·2^n)` of mesh `2^{-n}`. -/
def scaleBad (S : Setup) (γ C : ℝ) (n : ℕ) : Set Coord :=
  ⋃ p ∈ gridBox (2 * 2 ^ n),
    (gaussBad S γ n (gridPt ((2 : ℝ)⁻¹ ^ n) p) ∪ sepBad S γ C n (gridPt ((2 : ℝ)⁻¹ ^ n) p))

/-! ## Probability of the bad events -/

/-- The Gaussian event has probability at most `r⁴` once `ξ ≤ 1/64`, `n log 2 ≥ 10` and
`|z| ≤ 4`. -/
theorem measure_gaussBad_le (S : Setup) {γ : ℝ} (hξ0 : 0 < S.ξ γ) (hξ : S.ξ γ ≤ 1 / 64) {n : ℕ}
    (hn : 10 ≤ n * Real.log 2) {z : ℂ} (hz : ‖z‖ ≤ 4) :
    stdP (gaussBad S γ n z) ≤ ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n) ^ 4) := by
  set r : ℝ := (2 : ℝ)⁻¹ ^ n with hr_def
  set L : ℝ := n * Real.log 2 with hL_def
  have hr0 : 0 < r := inv_two_pow_pos n
  have hr1 : r ≤ 1 := inv_two_pow_le_one n
  have hL0 : 0 ≤ L := by linarith
  have hX := hasLaw_pairing_circleMeasure S.frame z hr0
  have hE : energy (circleMeasure z r) (circleMeasure z r) ≤ L + 10 := by
    have h := energy_circleMeasure_le_of_norm_le hr0 hr1 hz
    rwa [Real.log_inv, hr_def, log_inv_two_pow, neg_neg] at h
  have hV : ((energy (circleMeasure z r) (circleMeasure z r)).toNNReal : ℝ) ≤ L + 10 := by
    rw [Real.coe_toNNReal']
    exact max_le hE (by linarith)
  have hx0 : 0 ≤ L / (16 * S.ξ γ) := by positivity
  have h := measure_le_neg_le_of_hasLaw_gaussianReal hX hV (by linarith) hx0
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hr_def, inv_two_pow_pow_four, ← hL_def]
  refine Real.exp_le_exp.2 ?_
  have hx4 : 4 * L ≤ L / (16 * S.ξ γ) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hξ hL0
    linarith
  have hsq : (4 * L) ^ 2 ≤ (L / (16 * S.ξ γ)) ^ 2 := pow_le_pow_left₀ (by positivity) hx4 2
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  nlinarith

/-- The metric event: Markov with the 32nd inverse moment of `I(B̄₂, 1/2)`, transported by (S4). -/
theorem measure_sepBad_le (S : Setup) {γ C : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hC : 0 < C)
    {C₆ : ℝ≥0∞}
    (hI : ∫⁻ ω, (sepInf (S.D γ ω).1 (Metric.closedBall 0 2) (1 / 2))⁻¹ ^ (32 : ℝ) ∂stdP ≤ C₆)
    (n : ℕ) (z : ℂ) :
    stdP (sepBad S γ C n z) ≤
      C₆ * ENNReal.ofReal ((C * ((2 : ℝ)⁻¹ ^ n) ^ (1 / 8 : ℝ)) ^ (32 : ℝ)) := by
  set r : ℝ := (2 : ℝ)⁻¹ ^ n with hr_def
  set c : ℝ := C * r ^ (1 / 8 : ℝ) with hc_def
  have hr0 : 0 < r := inv_two_pow_pos n
  have hc : 0 < c := mul_pos hC (Real.rpow_pos_of_pos hr0 _)
  set F : C(ℂ × ℂ, ℝ) → ℝ≥0∞ :=
    fun d => (sepInf d (Metric.closedBall 0 2) (1 / 2))⁻¹ ^ (32 : ℝ) with hF_def
  have hF : Measurable F := ((measurable_sepInf_cont _ _).inv).pow_const _
  have ha : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hint : ∫⁻ ω, F (S.rescaled γ z (r : ℂ) ω) ∂stdP ≤ C₆ := by
    rw [S.lintegral_comp_rescaled hγ hγ2 z ha hF]
    exact hI
  set t : ℝ≥0∞ := (ENNReal.ofReal c)⁻¹ ^ (32 : ℝ) with ht_def
  have ht0 : t ≠ 0 := by
    rw [ht_def, ENNReal.inv_rpow]
    exact ENNReal.inv_ne_zero.2 (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have httop : t ≠ ⊤ := by
    rw [ht_def]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')
  have hsub : sepBad S γ C n z ⊆ {ω | t ≤ F (S.rescaled γ z (r : ℂ) ω)} := by
    intro ω hω
    exact ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.2 hω) (by norm_num)
  calc stdP (sepBad S γ C n z) ≤ stdP {ω | t ≤ F (S.rescaled γ z (r : ℂ) ω)} := measure_mono hsub
    _ ≤ (∫⁻ ω, F (S.rescaled γ z (r : ℂ) ω) ∂stdP) / t :=
        meas_ge_le_lintegral_div (hF.comp (S.measurable_rescaled γ z _)).aemeasurable ht0 httop
    _ ≤ C₆ / t := by gcongr
    _ = C₆ * ENNReal.ofReal (c ^ (32 : ℝ)) := by
        rw [ht_def, div_eq_mul_inv, ENNReal.inv_rpow, inv_inv, ENNReal.ofReal_rpow_of_pos hc]

/-- `(C r^{1/8})^{32} = C^{32} r^4`. -/
theorem mul_rpow_one_eighth_rpow_32 {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) :
    (C * r ^ (1 / 8 : ℝ)) ^ (32 : ℝ) = C ^ 32 * r ^ 4 := by
  rw [Real.mul_rpow hC (Real.rpow_nonneg hr _), ← Real.rpow_mul hr]
  norm_num

/-- `(4·2^n + 1)² 2^{-4n} ≤ 25 · 4^{-n}`. -/
theorem card_mul_le (n : ℕ) :
    ((4 * 2 ^ n + 1 : ℕ) : ℝ) ^ 2 * ((2 : ℝ)⁻¹ ^ n) ^ 4 ≤ 25 * (1 / 4 : ℝ) ^ n := by
  set x : ℝ := (2 : ℝ)⁻¹ ^ n with hx_def
  have hx0 : 0 < x := inv_two_pow_pos n
  have hx1 : x ≤ 1 := inv_two_pow_le_one n
  have hx2 : x * 2 ^ n = 1 := inv_two_pow_mul_two_pow n
  have h4 : (1 / 4 : ℝ) ^ n = x ^ 2 := by
    rw [hx_def, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4]
  push_cast
  calc ((4 : ℝ) * 2 ^ n + 1) ^ 2 * x ^ 4 = ((4 * 2 ^ n + 1) * x) ^ 2 * x ^ 2 := by ring
    _ = (4 + x) ^ 2 * x ^ 2 := by
        congr 2
        linear_combination 4 * hx2
    _ ≤ 25 * x ^ 2 := by
        have h5 : (4 + x) ^ 2 ≤ 5 ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
        have h25 : (4 + x) ^ 2 ≤ 25 := by norm_num at h5; exact h5
        exact mul_le_mul_of_nonneg_right h25 (sq_nonneg x)

/-- **One scale.** For admissible `γ` and `n log 2 ≥ 10`, the bad events at scale `n` have
probability at most `25 (1/4)^n (1 + C^{32} C₆)`. -/
theorem measure_scaleBad_le (S : Setup) {γ C : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hξ0 : 0 < S.ξ γ) (hξ : S.ξ γ ≤ 1 / 64) (hC : 0 < C) {C₆ : ℝ≥0∞} (hC₆ : C₆ ≠ ⊤)
    (hI : ∫⁻ ω, (sepInf (S.D γ ω).1 (Metric.closedBall 0 2) (1 / 2))⁻¹ ^ (32 : ℝ) ∂stdP ≤ C₆)
    {n : ℕ} (hn : 10 ≤ n * Real.log 2) :
    stdP (scaleBad S γ C n) ≤ ENNReal.ofReal (25 * (1 / 4 : ℝ) ^ n * (1 + C ^ 32 * C₆.toReal)) := by
  set r : ℝ := (2 : ℝ)⁻¹ ^ n with hr_def
  set M : ℝ := 1 + C ^ 32 * C₆.toReal with hM_def
  have hr0 : 0 < r := inv_two_pow_pos n
  have hM : 0 ≤ M := by positivity
  have hrN : 2 * r * ((2 * 2 ^ n : ℕ) : ℝ) = 4 := by
    push_cast
    have := inv_two_pow_mul_two_pow n
    rw [← hr_def] at this
    linear_combination 4 * this
  have hpt : ∀ p ∈ gridBox (2 * 2 ^ n),
      stdP (gaussBad S γ n (gridPt r p) ∪ sepBad S γ C n (gridPt r p)) ≤
        ENNReal.ofReal (r ^ 4 * M) := by
    intro p hp
    have hz : ‖gridPt r p‖ ≤ 4 := (norm_gridPt_le hr0.le hp).trans hrN.le
    calc stdP (gaussBad S γ n (gridPt r p) ∪ sepBad S γ C n (gridPt r p))
        ≤ stdP (gaussBad S γ n (gridPt r p)) + stdP (sepBad S γ C n (gridPt r p)) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (r ^ 4) +
            C₆ * ENNReal.ofReal ((C * r ^ (1 / 8 : ℝ)) ^ (32 : ℝ)) :=
          add_le_add (measure_gaussBad_le S hξ0 hξ hn hz)
            (measure_sepBad_le S hγ hγ2 hC hI n (gridPt r p))
      _ = ENNReal.ofReal (r ^ 4 * M) := by
          rw [mul_rpow_one_eighth_rpow_32 hC.le hr0.le, ← ENNReal.ofReal_toReal hC₆,
            ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_add (by positivity)
            (by positivity), hM_def]
          congr 1
          ring
  have hcard : ((gridBox (2 * 2 ^ n)).card : ℝ) = ((4 * 2 ^ n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [card_gridBox]
    push_cast
    ring
  calc stdP (scaleBad S γ C n)
      ≤ ∑ p ∈ gridBox (2 * 2 ^ n),
          stdP (gaussBad S γ n (gridPt r p) ∪ sepBad S γ C n (gridPt r p)) :=
        measure_biUnion_finset_le _ _
    _ ≤ (gridBox (2 * 2 ^ n)).card • ENNReal.ofReal (r ^ 4 * M) :=
        Finset.sum_le_card_nsmul _ _ _ hpt
    _ = ENNReal.ofReal ((gridBox (2 * 2 ^ n)).card * (r ^ 4 * M)) := by
        rw [← ENNReal.ofReal_nsmul, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (25 * (1 / 4 : ℝ) ^ n * M) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hcard, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (card_mul_le n) hM

/-! ## The deterministic inclusion -/

/-- The real-variable core of the contradiction: if `D = r^p e R` with `e > r^{1/16}`,
`R > e^{C_b} r^{1/8}`, `p ≤ 17/16`, `|b| ≤ C_b` and `0 < r ≤ 1`, then `e^{-b} D > r^{5/4}`. -/
theorem key_real {r p e R D b Cb : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hp : p ≤ 17 / 16)
    (hb : |b| ≤ Cb) (he : r ^ (1 / 16 : ℝ) < e) (hR : Real.exp Cb * r ^ (1 / 8 : ℝ) < R)
    (hD : D = r ^ p * e * R) : r ^ (5 / 4 : ℝ) < Real.exp (-b) * D := by
  have hbc : 1 ≤ Real.exp (-b) * Real.exp Cb := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith [le_abs_self b])
  have h16 : 0 < r ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have h8 : 0 < r ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr0 _
  have h1 : Real.exp (-b) * Real.exp Cb * r ^ (1 / 8 : ℝ) < Real.exp (-b) * R := by
    rw [mul_assoc]
    exact mul_lt_mul_of_pos_left hR (Real.exp_pos _)
  have h2 : r ^ (1 / 16 : ℝ) * (Real.exp (-b) * Real.exp Cb * r ^ (1 / 8 : ℝ)) <
      e * (Real.exp (-b) * R) :=
    mul_lt_mul'' he h1 h16.le (by positivity)
  calc r ^ (5 / 4 : ℝ) ≤ r ^ (p + 3 / 16) :=
        Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
    _ = r ^ p * (r ^ (1 / 16 : ℝ) * r ^ (1 / 8 : ℝ)) := by
        rw [show p + 3 / 16 = p + (1 / 16 + 1 / 8) by norm_num, Real.rpow_add hr0,
          Real.rpow_add hr0]
    _ ≤ r ^ p * (r ^ (1 / 16 : ℝ) * (Real.exp (-b) * Real.exp Cb * r ^ (1 / 8 : ℝ))) := by
        gcongr
        exact le_mul_of_one_le_left h8.le hbc
    _ < r ^ p * (e * (Real.exp (-b) * R)) := mul_lt_mul_of_pos_left h2 hrp
    _ = Real.exp (-b) * D := by
        rw [hD]
        ring

/-- **The deterministic inclusion.** Every bad pair at a scale `≤ 2^{-n₀}` produces a bad grid event
at some scale `n ≥ n₀`. -/
theorem subset_iUnion_scaleBad (S : Setup) {γ Cb : ℝ} (hξ0 : 0 < S.ξ γ)
    (hp : S.ξ γ * LQGMetric.Q γ ≤ 17 / 16) (hb : |S.b γ| ≤ Cb) (n₀ : ℕ) :
    {ω | ∃ z ∈ Metric.closedBall (0 : ℂ) 2, ∃ w ∈ Metric.closedBall (0 : ℂ) 2,
        0 < ‖z - w‖ ∧ ‖z - w‖ ≤ (2 : ℝ)⁻¹ ^ n₀ ∧
          Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) < ‖z - w‖ ^ (5 / 4 : ℝ)} ⊆
      ⋃ k : ℕ, scaleBad S γ (Real.exp Cb) (n₀ + k) := by
  rintro ω ⟨z', hz', w', hw', hpos, hle, hlt⟩
  -- the dyadic shell of `ρ = |z' - w'|`
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near_of_lt_one hpos (hle.trans (inv_two_pow_le_one n₀))
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hmn : n₀ ≤ m := by
    by_contra h
    have h' : m + 1 ≤ n₀ := by omega
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) h'
    linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine mem_iUnion.2 ⟨k, ?_⟩
  set n : ℕ := n₀ + k with hn_def
  set r : ℝ := (2 : ℝ)⁻¹ ^ n with hr_def
  have hr0 : 0 < r := inv_two_pow_pos n
  have hr1 : r ≤ 1 := inv_two_pow_le_one n
  have hrhalf : r / 2 < ‖z' - w'‖ := by
    rw [pow_succ] at hm1
    linarith
  -- a grid point near `z'`
  have hrN : r * ((2 * 2 ^ n : ℕ) : ℝ) = 2 := by
    push_cast
    have := inv_two_pow_mul_two_pow n
    rw [← hr_def] at this
    linear_combination 2 * this
  have hz'N : ‖z'‖ ≤ r * ((2 * 2 ^ n : ℕ) : ℝ) := by
    rw [hrN]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz'
  obtain ⟨p, hpbox, hzp⟩ := exists_gridPt_near hr0 hz'N
  set z : ℂ := gridPt r p with hz_def
  refine mem_iUnion₂.2 ⟨p, hpbox, ?_⟩
  by_contra hcon
  rw [mem_union, not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  -- rescaled coordinates
  set u : ℂ := (z' - z) / (r : ℂ) with hu_def
  set v : ℂ := (w' - z) / (r : ℂ) with hv_def
  have hzu : z + (r : ℂ) * u = z' := by
    rw [hu_def, ofReal_mul_div_ofReal hr0]
    ring
  have hzv : z + (r : ℂ) * v = w' := by
    rw [hv_def, ofReal_mul_div_ofReal hr0]
    ring
  have hu : u ∈ Metric.closedBall (0 : ℂ) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, hu_def, norm_div_ofReal hr0, div_le_iff₀ hr0]
    linarith
  have hv : v ∈ Metric.closedBall (0 : ℂ) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, hv_def, norm_div_ofReal hr0, div_le_iff₀ hr0]
    have h1 : ‖w' - z‖ ≤ ‖w' - z'‖ + ‖z' - z‖ := norm_sub_le_norm_sub_add_norm_sub w' z' z
    have h2 : ‖w' - z'‖ = ‖z' - w'‖ := norm_sub_rev _ _
    linarith
  have huv : 1 / 2 ≤ ‖u - v‖ := by
    rw [hu_def, hv_def, ← sub_div, show z' - z - (w' - z) = z' - w' by ring, norm_div_ofReal hr0,
      le_div_iff₀ hr0]
    linarith
  -- the field and the rescaled metric
  set h : ℝ := pairing S.e (circleMeasure z r) ω with h_def
  set R : ℝ := S.rescaled γ z (r : ℂ) ω (u, v) with hR_def
  have hRdef : R = r ^ (-(S.ξ γ * LQGMetric.Q γ)) * Real.exp (-(S.ξ γ) * h) *
      (S.D γ ω).1 (z', w') := by
    rw [hR_def, Setup.rescaled_apply, Setup.rescaleFactor, Complex.norm_of_nonneg hr0.le, hzu, hzv]
  have hD : (S.D γ ω).1 (z', w') = r ^ (S.ξ γ * LQGMetric.Q γ) * Real.exp (S.ξ γ * h) * R := by
    have e1 : r ^ (S.ξ γ * LQGMetric.Q γ) * r ^ (-(S.ξ γ * LQGMetric.Q γ)) = 1 := by
      rw [← Real.rpow_add hr0, add_neg_cancel, Real.rpow_zero]
    have e2 : Real.exp (S.ξ γ * h) * Real.exp (-(S.ξ γ) * h) = 1 := by
      rw [← Real.exp_add, show S.ξ γ * h + -S.ξ γ * h = 0 by ring, Real.exp_zero]
    rw [hRdef]
    calc (S.D γ ω).1 (z', w') = 1 * 1 * (S.D γ ω).1 (z', w') := by ring
      _ = (r ^ (S.ξ γ * LQGMetric.Q γ) * r ^ (-(S.ξ γ * LQGMetric.Q γ))) *
            (Real.exp (S.ξ γ * h) * Real.exp (-(S.ξ γ) * h)) * (S.D γ ω).1 (z', w') := by
          rw [e1, e2]
      _ = _ := by ring
  -- off the Gaussian event: `e^{ξ h} > r^{1/16}`
  have he : r ^ (1 / 16 : ℝ) < Real.exp (S.ξ γ * h) := by
    have hA' : -h < (n * Real.log 2) / (16 * S.ξ γ) := by
      simpa only [gaussBad, mem_ofPred_eq, not_le] using hA
    rw [lt_div_iff₀ (by positivity)] at hA'
    rw [hr_def, inv_two_pow_rpow]
    exact Real.exp_lt_exp.2 (by linarith)
  -- off the metric event: `R > e^{C_b} r^{1/8}`
  have hRlt : Real.exp Cb * r ^ (1 / 8 : ℝ) < R := by
    have h1 : sepInf (S.rescaled γ z (r : ℂ) ω) (Metric.closedBall 0 2) (1 / 2) ≤
        ENNReal.ofReal R := sepInf_le_ofReal _ hu hv huv
    have h2 : ENNReal.ofReal (Real.exp Cb * r ^ (1 / 8 : ℝ)) <
        sepInf (S.rescaled γ z (r : ℂ) ω) (Metric.closedBall 0 2) (1 / 2) := by
      simpa only [sepBad, mem_ofPred_eq, not_le] using hB
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 (h2.trans_le h1)).1
  have hkey := key_real hr0 hr1 hp hb he hRlt hD
  have hρ : ‖z' - w'‖ ^ (5 / 4 : ℝ) ≤ r ^ (5 / 4 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hm2 (by norm_num)
  linarith

end SmallScale

open SmallScale

/-! ## Lemma 6.0 -/

/-- **Lemma 6.0 (coordinate form; GA3 A11).** For every GaussianLQG coordinate `Setup` and every
`ε > 0` there are `n` and `γs > 0` such that for `γ ∈ (0, γs]`, with probability at least `1 - ε`,
every pair `z, w ∈ B̄₂` with `0 < |z - w| ≤ 2^{-n}` has `e^{-b_γ} D(z,w) ≥ |z - w|^{5/4}`. -/
theorem smallScale_lower (S : Setup) : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ γs : ℝ, 0 < γs ∧
    ∀ γ ∈ Ioc (0 : ℝ) γs,
      stdP {ω | ∃ z ∈ Metric.closedBall (0 : ℂ) 2, ∃ w ∈ Metric.closedBall (0 : ℂ) 2,
        0 < ‖z - w‖ ∧ ‖z - w‖ ≤ (2 : ℝ)⁻¹ ^ n ∧
          Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) < ‖z - w‖ ^ (5 / 4 : ℝ)} ≤ ENNReal.ofReal ε := by
  intro ε hε
  -- the thresholds in `γ`
  obtain ⟨γe, C₁, hγe, hγe2, hexp⟩ := S.exists_exponents
  obtain ⟨γb, Cb, hγb, hb⟩ := S.abs_b_le
  obtain ⟨γ₆, hγ₆, h6⟩ := S.S6 32 (by norm_num)
  obtain ⟨C₆, hC₆, hC₆b⟩ := h6 (Metric.closedBall 0 2) (isCompact_closedBall 0 2) (1 / 2)
    (by norm_num)
  set C : ℝ := Real.exp Cb with hC_def
  have hC : 0 < C := Real.exp_pos _
  set M : ℝ := 1 + C ^ 32 * C₆.toReal with hM_def
  have hM : 0 < M := by positivity
  -- the threshold in `n`
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (10 / Real.log 2)
  obtain ⟨n₂, hn₂⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / (34 * M) by positivity)
    (show (1 / 4 : ℝ) < 1 by norm_num)
  set n₀ : ℕ := max n₁ n₂ with hn₀_def
  refine ⟨n₀, min (min (min γe γb) γ₆) (min (1 / 64) (1 / (16 * (|C₁| + 1)))), by positivity, ?_⟩
  rintro γ ⟨hγ0, hγs⟩
  have hγe' : γ ≤ γe :=
    hγs.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hγb' : γ ≤ γb :=
    hγs.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hγ₆' : γ ≤ γ₆ := hγs.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγ64 : γ ≤ 1 / 64 := hγs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγC : γ ≤ 1 / (16 * (|C₁| + 1)) := hγs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγ2 : γ < 2 := hγe'.trans_lt hγe2
  obtain ⟨hξ3, hξγ, -, hQ⟩ := hexp γ ⟨hγ0, hγe'⟩
  have hξ0 : 0 < S.ξ γ := by linarith
  have hξ64 : S.ξ γ ≤ 1 / 64 := hξγ.trans hγ64
  have hp : S.ξ γ * LQGMetric.Q γ ≤ 17 / 16 := by
    have h1 : S.ξ γ * LQGMetric.Q γ - 1 ≤ C₁ * S.ξ γ := (abs_le.1 hQ).2
    have h2 : C₁ * S.ξ γ ≤ |C₁| * γ :=
      (mul_le_mul_of_nonneg_right (le_abs_self C₁) hξ0.le).trans
        (mul_le_mul_of_nonneg_left hξγ (abs_nonneg C₁))
    have h3 : |C₁| * γ ≤ 1 / 16 := by
      have hpos : 0 < 16 * (|C₁| + 1) := by positivity
      rw [le_div_iff₀ hpos] at hγC
      nlinarith [abs_nonneg C₁]
    linarith
  have hbγ := hb γ ⟨hγ0, hγb'⟩
  have hI := (hC₆b γ ⟨hγ0, hγ₆'⟩).2
  -- every scale `n₀ + k` satisfies `10 ≤ (n₀ + k) log 2`
  have hscale : ∀ k : ℕ, 10 ≤ ((n₀ + k : ℕ) : ℝ) * Real.log 2 := by
    intro k
    have h1 : 10 < (n₁ : ℝ) * Real.log 2 := by
      rwa [div_lt_iff₀ hlog2] at hn₁
    have h2 : (n₁ : ℝ) ≤ ((n₀ + k : ℕ) : ℝ) := by
      exact_mod_cast (le_max_left n₁ n₂).trans (Nat.le_add_right n₀ k)
    nlinarith
  -- the geometric series
  have hsum : Summable fun k : ℕ => 25 * (1 / 4 : ℝ) ^ (n₀ + k) * M := by
    have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (25 * (1 / 4 : ℝ) ^ n₀ * M)
    refine h.congr fun k => ?_
    rw [pow_add]
    ring
  have htsum : ∑' k : ℕ, 25 * (1 / 4 : ℝ) ^ (n₀ + k) * M = 25 * (1 / 4 : ℝ) ^ n₀ * M * (4 / 3) := by
    have h : ∑' k : ℕ, 25 * (1 / 4 : ℝ) ^ (n₀ + k) * M =
        ∑' k : ℕ, 25 * (1 / 4 : ℝ) ^ n₀ * M * (1 / 4 : ℝ) ^ k := by
      congr 1
      ext k
      rw [pow_add]
      ring
    rw [h, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hn₀ : (1 / 4 : ℝ) ^ n₀ ≤ (1 / 4 : ℝ) ^ n₂ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right n₁ n₂)
  calc stdP {ω | ∃ z ∈ Metric.closedBall (0 : ℂ) 2, ∃ w ∈ Metric.closedBall (0 : ℂ) 2,
        0 < ‖z - w‖ ∧ ‖z - w‖ ≤ (2 : ℝ)⁻¹ ^ n₀ ∧
          Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) < ‖z - w‖ ^ (5 / 4 : ℝ)}
      ≤ stdP (⋃ k : ℕ, scaleBad S γ C (n₀ + k)) :=
        measure_mono (subset_iUnion_scaleBad S hξ0 hp hbγ n₀)
    _ ≤ ∑' k : ℕ, stdP (scaleBad S γ C (n₀ + k)) := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (25 * (1 / 4 : ℝ) ^ (n₀ + k) * M) :=
        ENNReal.tsum_le_tsum fun k =>
          measure_scaleBad_le S hγ0 hγ2 hξ0 hξ64 hC hC₆ hI (hscale k)
    _ = ENNReal.ofReal (∑' k : ℕ, 25 * (1 / 4 : ℝ) ^ (n₀ + k) * M) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [htsum]
        have h1 : 25 * (1 / 4 : ℝ) ^ n₀ * M * (4 / 3) ≤ 34 * M * (1 / 4 : ℝ) ^ n₂ := by
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n₀]
        have h2 : 34 * M * (1 / 4 : ℝ) ^ n₂ ≤ ε := by
          rw [lt_div_iff₀ (by positivity)] at hn₂
          linarith
        linarith

end SmallGammaGeodesics
