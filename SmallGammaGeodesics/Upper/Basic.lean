import SmallGammaGeodesics.Upper.Defs
import SmallGammaGeodesics.Probes.Sampling
import SmallGammaGeodesics.Probes.LowPass

/-!
# §5 infrastructure: the probe grid, the top level and the band reconstruction (packet P-U0)

Blueprint `blueprint/sections/s5-upper.tex`, deterministic part; statements of
`planning/packets/BP2-planned-statements.md` (§5 block), ruling G27.

* `probeGrid_spec` (Lemma `lem:probe-grid`): the grid `𝒜_j = {i/(3·2^j) : 0 ≤ i ≤ 3·2^j}` lies in
  `[0,1]`, has at most `4/ℓ_j` points, and samples every band up to the factor `2`
  (a repackaging of P-B1's `lemma41_sampling`, whose proof uses exactly this grid).
* `ell_Jxi_bounds`, `log_inv_ell_le` (Lemma `lem:top-level`): `ξ^{3/8}/2 < ℓ_{J(ξ)} ≤ ξ^{3/8}` for
  `0 < ξ ≤ 1`, and for `0 < ξ ≤ 1/10`, `j ≤ J(ξ)`: `L ≥ 1` and `1 + log(1/ℓ_j) ≤ 2L`.
* `maxDev_le_of_bands` (Lemma `lem:band-reconstruction`, source (5.2)): if `η` is a `Δ`-Euclidean
  geodesic and every band at the grid points of the levels `j ≤ J` is at most `c_β R ℓ_j^{1/8}`, then
  `M(η) ≤ R/4 + C_r (√(ℓ_J Δ) + Δ)`.
* `exists_band_gt_of_lt_maxDev`: the deterministic core of Corollary `cor:band-inclusion`
  (`bandEv_of_lt_maxDev` in `Upper/Good.lean`).

Reusable helpers: `ell_rpow_one_eighth`, `sum_ell_rpow_one_eighth_le`, `two_mul_cBeta_mul_sum_le`,
`yPath_coe`, `continuous_yPath`, `yPath_zero`, `yPath_one`, `ApproxGeod.modulus_yPath_le`,
`abs_lowPass_le_of_bands`, `Jxi_spec`, `ell_eq_two_rpow`, `sqrt_ell_Jxi_mul_add_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## The probe grid -/

/-- The probe grid with its denominator written as the cast of the natural number `3·2^j`. -/
theorem probeGrid_eq_image (j : ℕ) :
    probeGrid j = (Finset.range (3 * 2 ^ j + 1)).image
      fun i : ℕ => (i : ℝ) / ((3 * 2 ^ j : ℕ) : ℝ) := by
  simp only [probeGrid, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- **Lemma `lem:probe-grid`**: `𝒜_j ⊆ [0,1]`, `#𝒜_j ≤ 4/ℓ_j`, and for every `y` continuous on `[0,1]` and
every real `a` there is `a' ∈ 𝒜_j` with `|B_j(a)| ≤ 2|B_j(a')|`. The proof is that of P-B1's
`lemma41_sampling` (sampling at `2i/(3·2^{j+1})`, `i < 3·2^{j+1}`, and the reflection
`B_j(2 - u) = -B_j(u)`), specialized to the grid `probeGrid j`. -/
theorem probeGrid_spec (j : ℕ) : (↑(probeGrid j) : Set ℝ) ⊆ Icc 0 1 ∧
    ((probeGrid j).card : ℝ) ≤ 4 / ell j ∧
    ∀ y : ℝ → ℝ, ContinuousOn y (Icc 0 1) → ∀ a, ∃ a' ∈ probeGrid j,
      |band y j a| ≤ 2 * |band y j a'| := by
  set L : ℕ := 3 * 2 ^ j with hL
  have hLpos : 0 < L := by positivity
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  rw [probeGrid_eq_image, ← hL]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hLr]
    exact_mod_cast (show i ≤ L by omega)
  · calc (((Finset.range (L + 1)).image (fun i : ℕ => (i : ℝ) / L)).card : ℝ)
        ≤ ((Finset.range (L + 1)).card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = L + 1 := by rw [Finset.card_range]; push_cast; ring
      _ ≤ 4 / ell j := by
          rw [div_eq_mul_inv, inv_ell, hL]
          have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
          push_cast
          linarith
  · intro y _ a
    have hN : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    obtain ⟨i, hi, hle⟩ :=
      sinePoly_le_grid hN (fun k => rho ((k : ℝ) * ell j) * sineCoef y k) a
    rw [← band_eq_sinePoly] at hle
    have hgrid : gridPt (2 ^ (j + 1)) i = (i : ℝ) / L := by
      unfold gridPt
      rw [hL]
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity), pow_succ]
      ring
    have hi' : i < 2 * L := by
      rw [Finset.mem_range] at hi
      rw [hL]
      calc i < 3 * 2 ^ (j + 1) := hi
        _ = 2 * (3 * 2 ^ j) := by rw [pow_succ]; ring
    have habs := abs_nonneg (sinePoly (2 ^ (j + 1))
      (fun k => rho ((k : ℝ) * ell j) * sineCoef y k) (gridPt (2 ^ (j + 1)) i))
    by_cases hiL : i ≤ L
    · refine ⟨(i : ℝ) / L, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
      rw [band_eq_sinePoly y j ((i : ℝ) / L), ← hgrid]
      linarith
    · refine ⟨((2 * L - i : ℕ) : ℝ) / L,
        Finset.mem_image.mpr ⟨2 * L - i, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
      have hrefl : ((2 * L - i : ℕ) : ℝ) / L = 2 - gridPt (2 ^ (j + 1)) i := by
        rw [hgrid, Nat.cast_sub (by omega)]
        have hLr' : (L : ℝ) ≠ 0 := hLr.ne'
        field_simp
        push_cast
        ring
      rw [hrefl, band_eq_sinePoly y j (2 - gridPt (2 ^ (j + 1)) i), sinePoly_two_sub, abs_neg]
      linarith

/-! ## The top level `J(ξ)` -/

/-- `J(ξ) = ⌈x⌉₊` with `x = (3/8) log₂(1/ξ) ≥ 0`, so `x ≤ J(ξ) < x + 1` (for `0 < ξ ≤ 1`). -/
theorem Jxi_spec {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ ≤ 1) :
    0 ≤ (3 / 8 : ℝ) * Real.logb 2 ξ⁻¹ ∧ (3 / 8 : ℝ) * Real.logb 2 ξ⁻¹ ≤ Jxi ξ ∧
      (Jxi ξ : ℝ) < (3 / 8 : ℝ) * Real.logb 2 ξ⁻¹ + 1 := by
  have hlog : 0 ≤ Real.logb 2 ξ⁻¹ := Real.logb_nonneg one_lt_two ((one_le_inv₀ h0).2 h1)
  have hx0 : 0 ≤ (3 / 8 : ℝ) * Real.logb 2 ξ⁻¹ := mul_nonneg (by norm_num) hlog
  exact ⟨hx0, Nat.le_ceil _, Nat.ceil_lt_add_one hx0⟩

/-- `2^{-(3/8) log₂(1/ξ)} = ξ^{3/8}`. -/
theorem two_rpow_neg_three_eighths_logb {ξ : ℝ} (h0 : 0 < ξ) :
    (2 : ℝ) ^ (-((3 / 8 : ℝ) * Real.logb 2 ξ⁻¹)) = ξ ^ (3 / 8 : ℝ) := by
  rw [show -((3 / 8 : ℝ) * Real.logb 2 ξ⁻¹) = Real.logb 2 ξ⁻¹ * (-(3 / 8 : ℝ)) by ring,
    Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.2 h0),
    Real.rpow_neg (inv_nonneg.2 h0.le), Real.inv_rpow h0.le, inv_inv]

/-- `ℓ_j = 2^{-j}` as a real power. -/
theorem ell_eq_two_rpow (j : ℕ) : ell j = (2 : ℝ) ^ (-(j : ℝ)) := by
  rw [ell, Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- **Lemma `lem:top-level` (a)**: `ξ^{3/8}/2 < ℓ_{J(ξ)} ≤ ξ^{3/8}` for `0 < ξ ≤ 1`. -/
theorem ell_Jxi_bounds {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ ≤ 1) :
    ξ ^ (3/8 : ℝ) / 2 < ell (Jxi ξ) ∧ ell (Jxi ξ) ≤ ξ ^ (3/8 : ℝ) := by
  obtain ⟨-, hJ1, hJ2⟩ := Jxi_spec h0 h1
  rw [ell_eq_two_rpow, ← two_rpow_neg_three_eighths_logb h0]
  constructor
  · rw [div_eq_mul_inv, ← Real.rpow_neg_one 2, ← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- `e² < 10`. -/
theorem exp_two_lt_ten : Real.exp 2 < 10 := by
  have h := Real.exp_one_lt_d9
  have hp := Real.exp_pos 1
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

/-- **Lemma `lem:top-level` (b)**: for `0 < ξ ≤ 1/10` and `j ≤ J(ξ)`, `L = log(1/ξ) ≥ 1` and
`1 + log(1/ℓ_j) ≤ 2L`. In fact `L ≥ 2` (since `e² < 10`), `log(1/ℓ_j) = j log 2 ≤ J log 2 < (3/8) L + log 2`,
and `1 + log 2 + (3/8) L ≤ 2L` because `log 2 < 1`. -/
theorem log_inv_ell_le {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ ≤ 1/10) {j : ℕ} (hj : j ≤ Jxi ξ) :
    1 ≤ Real.log ξ⁻¹ ∧ 1 + Real.log (ell j)⁻¹ ≤ 2 * Real.log ξ⁻¹ := by
  have h10 : (10 : ℝ) ≤ ξ⁻¹ := by
    have := inv_anti₀ h0 h1
    norm_num at this
    exact this
  have hL2 : 2 ≤ Real.log ξ⁻¹ := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [exp_two_lt_ten]
  refine ⟨by linarith, ?_⟩
  obtain ⟨-, -, hJ2⟩ := Jxi_spec h0 (h1.trans (by norm_num))
  have hjJ : (j : ℝ) ≤ Jxi ξ := by exact_mod_cast hj
  have hl : Real.log (ell j)⁻¹ = j * Real.log 2 := by rw [inv_ell, Real.log_pow]
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith [show (0.6931471808 : ℝ) < 1 by norm_num]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlb : Real.logb 2 ξ⁻¹ * Real.log 2 = Real.log ξ⁻¹ := by
    rw [Real.logb, div_mul_cancel₀ _ hlog2pos.ne']
  calc 1 + Real.log (ell j)⁻¹ = 1 + j * Real.log 2 := by rw [hl]
    _ ≤ 1 + ((3 / 8 : ℝ) * Real.logb 2 ξ⁻¹ + 1) * Real.log 2 := by
        gcongr
        linarith
    _ = 1 + (3 / 8 : ℝ) * Real.log ξ⁻¹ + Real.log 2 := by rw [← hlb]; ring
    _ ≤ 2 * Real.log ξ⁻¹ := by linarith

/-! ## Geometric sums of `ℓ_j^{1/8}` and the constant `c_β` -/

/-- `ℓ_j^{1/8} = (2^{-1/8})^j`. -/
theorem ell_rpow_one_eighth (j : ℕ) :
    ell j ^ (1 / 8 : ℝ) = ((2 : ℝ) ^ (-(1 / 8 : ℝ))) ^ j := by
  rw [ell, Real.inv_rpow (by positivity), Real.rpow_neg (by norm_num), inv_pow,
    ← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num),
    mul_comm (j : ℝ)]

/-- `2^{-1/8} < 1`. -/
theorem two_rpow_neg_one_eighth_lt_one : (2 : ℝ) ^ (-(1 / 8 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- `∑_{j ≤ J} ℓ_j^{1/8} ≤ (1 - 2^{-1/8})⁻¹`. -/
theorem sum_ell_rpow_one_eighth_le (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ell j ^ (1 / 8 : ℝ) ≤ (1 - (2 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-(1 / 8 : ℝ)) := by positivity
  simp_rw [ell_rpow_one_eighth]
  rw [Finset.range_eq_Ico]
  refine (geom_sum_Ico_le_of_lt_one (m := 0) (n := J + 1) hr0
    two_rpow_neg_one_eighth_lt_one).trans (le_of_eq ?_)
  rw [pow_zero]
  exact one_div (1 - (2 : ℝ) ^ (-(1 / 8 : ℝ)))

/-- `c_β = (1 - 2^{-1/8})/8 > 0`. -/
theorem cBeta_pos : 0 < cBeta := by
  unfold cBeta
  have := two_rpow_neg_one_eighth_lt_one
  exact div_pos (by linarith) (by norm_num)

/-- `2 c_β ∑_{j ≤ J} ℓ_j^{1/8} ≤ 1/4` (Convention `conv:upper`). -/
theorem two_mul_cBeta_mul_sum_le (J : ℕ) :
    2 * cBeta * ∑ j ∈ Finset.range (J + 1), ell j ^ (1 / 8 : ℝ) ≤ 1 / 4 := by
  have hpos : 0 < 1 - (2 : ℝ) ^ (-(1 / 8 : ℝ)) := by
    linarith [two_rpow_neg_one_eighth_lt_one]
  calc 2 * cBeta * ∑ j ∈ Finset.range (J + 1), ell j ^ (1 / 8 : ℝ)
      ≤ 2 * cBeta * (1 - (2 : ℝ) ^ (-(1 / 8 : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left (sum_ell_rpow_one_eighth_le J) (by linarith [cBeta_pos])
    _ = 1 / 4 := by
        unfold cBeta
        field_simp
        ring

/-! ## The imaginary part of a path -/

/-- On `[0,1]`, `y_η(t) = Im η(t)`. -/
theorem yPath_coe (η : C(unitInterval, ℂ)) (t : unitInterval) : yPath η t = (η t).im := by
  rw [yPath, Set.projIcc_val]

/-- `y_η` is continuous on `ℝ` (it is constant outside `[0,1]`). -/
theorem continuous_yPath (η : C(unitInterval, ℂ)) : Continuous (yPath η) :=
  Complex.continuous_im.comp (η.continuous.comp continuous_projIcc)

/-- `y_η(0) = 0` when `η(0) = 0`. -/
theorem yPath_zero {η : C(unitInterval, ℂ)} (h0 : η 0 = 0) : yPath η 0 = 0 := by
  have h := yPath_coe η 0
  rw [Set.Icc.coe_zero] at h
  rw [h, h0, Complex.zero_im]

/-- `y_η(1) = 0` when `η(1) = 1`. -/
theorem yPath_one {η : C(unitInterval, ℂ)} (h1 : η 1 = 1) : yPath η 1 = 0 := by
  have h := yPath_coe η 1
  rw [Set.Icc.coe_one] at h
  rw [h, h1, Complex.one_im]

/-- The modulus of continuity of `y_η` on `[0,1]` for a `Δ`-Euclidean geodesic `η`:
`ω_y(r) ≤ 5√(rΔ) + 8Δ` (from the clock geometry (4.1), `ApproxGeod.abs_im_sub_le`). -/
theorem ApproxGeod.modulus_yPath_le {d : ℂ × ℂ → ℝ} {η : C(unitInterval, ℂ)} {Δ : ℝ}
    (h : ApproxGeod d η Δ) (r : ℝ) :
    modulus (yPath η) r ≤ 5 * Real.sqrt (r * Δ) + 8 * Δ := by
  have hΔ := h.nonneg
  have hb : 0 ≤ 5 * Real.sqrt (r * Δ) + 8 * Δ := by positivity
  unfold modulus
  refine Real.iSup_le (fun s => Real.iSup_le (fun t => Real.iSup_le (fun hst => ?_) hb) hb) hb
  rw [yPath_coe η s, yPath_coe η t, abs_sub_comm]
  refine (h.abs_im_sub_le s t).trans ?_
  have hle : |(t : ℝ) - s| * Δ ≤ r * Δ := by
    refine mul_le_mul_of_nonneg_right ?_ hΔ
    rw [abs_sub_comm]
    exact hst
  have := Real.sqrt_le_sqrt hle
  linarith

/-! ## Band reconstruction (5.2) -/

/-- If every band of `y` at the grid points of the levels `j ≤ J` is at most `c_β R ℓ_j^{1/8}`, then
`|S_J(t)| ≤ R/4` for every real `t`: `S_J = ∑_{j ≤ J} B_j`, `|B_j(t)| ≤ 2 c_β R ℓ_j^{1/8}` by the grid
lemma, and `2 c_β ∑_j ℓ_j^{1/8} ≤ 1/4`. -/
theorem abs_lowPass_le_of_bands {y : ℝ → ℝ} (hy : ContinuousOn y (Icc 0 1)) {J : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hb : ∀ j ≤ J, ∀ a ∈ probeGrid j, |band y j a| ≤ cBeta * R * ell j ^ (1 / 8 : ℝ))
    (t : ℝ) : |lowPass y J t| ≤ R / 4 := by
  rw [← sum_band_eq_lowPass]
  have hbt : ∀ j ∈ Finset.range (J + 1),
      |band y j t| ≤ 2 * cBeta * R * ell j ^ (1 / 8 : ℝ) := by
    intro j hj
    have hjJ : j ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    obtain ⟨a', ha', hle⟩ := (probeGrid_spec j).2.2 y hy t
    calc |band y j t| ≤ 2 * |band y j a'| := hle
      _ ≤ 2 * (cBeta * R * ell j ^ (1 / 8 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hb j hjJ a' ha') (by norm_num)
      _ = 2 * cBeta * R * ell j ^ (1 / 8 : ℝ) := by ring
  calc |∑ j ∈ Finset.range (J + 1), band y j t|
      ≤ ∑ j ∈ Finset.range (J + 1), |band y j t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (J + 1), 2 * cBeta * R * ell j ^ (1 / 8 : ℝ) := Finset.sum_le_sum hbt
    _ = (2 * cBeta * ∑ j ∈ Finset.range (J + 1), ell j ^ (1 / 8 : ℝ)) * R := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ 1 / 4 * R := mul_le_mul_of_nonneg_right (two_mul_cBeta_mul_sum_le J) hR
    _ = R / 4 := by ring

/-- **Lemma `lem:band-reconstruction`** (source (5.2)): there is `C_r ≥ 0` such that for every
`Δ`-Euclidean geodesic `η` (`ApproxGeod d η Δ`), every `J` and every `R ≥ 0`, if
`|B_{j,a}(y_η)| ≤ c_β R ℓ_j^{1/8}` for all `j ≤ J` and `a ∈ 𝒜_j`, then
`M(η) ≤ R/4 + C_r (√(ℓ_J Δ) + Δ)`. Here `C_r = 13 max(C₄, 0) + 3` with `C₄` the constant of
`lemma41_lowPass`. -/
theorem maxDev_le_of_bands : ∃ Cr, 0 ≤ Cr ∧ ∀ (d : ℂ × ℂ → ℝ) (η : C(unitInterval, ℂ)) (Δ : ℝ),
    ApproxGeod d η Δ → ∀ (J : ℕ) (R : ℝ), 0 ≤ R →
    (∀ j ≤ J, ∀ a ∈ probeGrid j, |band (yPath η) j a| ≤ cBeta * R * ell j ^ (1/8 : ℝ)) →
    maxDev η ≤ R / 4 + Cr * (Real.sqrt (ell J * Δ) + Δ) := by
  obtain ⟨C₄, hC₄⟩ := lemma41_lowPass
  set C : ℝ := max C₄ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨13 * C + 3, by positivity, fun d η Δ h J R hR hb => ?_⟩
  have hyc : ContinuousOn (yPath η) (Icc 0 1) := (continuous_yPath η).continuousOn
  have hy0 : yPath η 0 = 0 := yPath_zero h.zero
  have hy1 : yPath η 1 = 0 := yPath_one h.one
  have hΔ := h.nonneg
  set s := Real.sqrt (ell J * Δ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hmod : modulus (yPath η) (ell J) ≤ 5 * s + 8 * Δ := h.modulus_yPath_le (ell J)
  have hmod0 : 0 ≤ modulus (yPath η) (ell J) := modulus_nonneg hyc (ell_pos J).le
  have hpt : ∀ t : unitInterval, |(η t).im| ≤ R / 4 + C * (5 * s + 8 * Δ) := by
    intro t
    have hrem := hC₄ (yPath η) hyc hy0 hy1 J t t.2
    have hlow := abs_lowPass_le_of_bands hyc hR hb t
    rw [← yPath_coe]
    calc |yPath η t| = |lowPass (yPath η) J t + (yPath η t - lowPass (yPath η) J t)| := by
          congr 1
          ring
      _ ≤ |lowPass (yPath η) J t| + |yPath η t - lowPass (yPath η) J t| := abs_add_le _ _
      _ ≤ R / 4 + C₄ * modulus (yPath η) (ell J) := add_le_add hlow hrem
      _ ≤ R / 4 + C * (5 * s + 8 * Δ) := by
          have h1 : C₄ * modulus (yPath η) (ell J) ≤ C * modulus (yPath η) (ell J) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hmod0
          have h2 : C * modulus (yPath η) (ell J) ≤ C * (5 * s + 8 * Δ) :=
            mul_le_mul_of_nonneg_left hmod hC0
          linarith
  have hsup : (⨆ t : unitInterval, |(η t).im|) ≤ R / 4 + C * (5 * s + 8 * Δ) := ciSup_le hpt
  calc maxDev η ≤ (⨆ t : unitInterval, |(η t).im|) + 3 * Δ := h.maxDev_le_iSup_abs_im
    _ ≤ R / 4 + C * (5 * s + 8 * Δ) + 3 * Δ := by linarith
    _ ≤ R / 4 + (13 * C + 3) * (s + Δ) := by
        nlinarith [mul_nonneg hC0 hs0, mul_nonneg hC0 hΔ]

/-! ## The deterministic core of the band inclusion (5.12) -/

/-- (X5) at the top level: for `0 < ξ ≤ 1` and `0 ≤ Δ ≤ ξ^{99/100}`,
`√(ℓ_{J(ξ)} Δ) + Δ ≤ 2 ξ^{19/1200} ξ^{2/3}` (since `3/16 + 99/200 = 819/1200 ≤ 99/100` and
`819/1200 - 2/3 = 19/1200`). -/
theorem sqrt_ell_Jxi_mul_add_le {ξ Δ : ℝ} (h0 : 0 < ξ) (h1 : ξ ≤ 1) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ ξ ^ (99 / 100 : ℝ)) :
    Real.sqrt (ell (Jxi ξ) * Δ) + Δ ≤ 2 * ξ ^ (19 / 1200 : ℝ) * ξ ^ (2 / 3 : ℝ) := by
  have hℓ := (ell_Jxi_bounds h0 h1).2
  have key : ξ ^ (19 / 1200 : ℝ) * ξ ^ (2 / 3 : ℝ) = ξ ^ (819 / 1200 : ℝ) := by
    rw [← Real.rpow_add h0]
    norm_num
  have hs : Real.sqrt (ell (Jxi ξ) * Δ) ≤ ξ ^ (819 / 1200 : ℝ) := by
    calc Real.sqrt (ell (Jxi ξ) * Δ) ≤ Real.sqrt (ξ ^ (3 / 8 : ℝ) * ξ ^ (99 / 100 : ℝ)) :=
          Real.sqrt_le_sqrt (mul_le_mul hℓ hΔ hΔ0 (by positivity))
      _ = ξ ^ (819 / 1200 : ℝ) := by
          rw [← Real.rpow_add h0, Real.sqrt_eq_rpow, ← Real.rpow_mul h0.le]
          norm_num
  have hΔ' : Δ ≤ ξ ^ (819 / 1200 : ℝ) :=
    hΔ.trans (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by norm_num))
  rw [mul_assoc, key]
  linarith

/-- The deterministic core of Corollary `cor:band-inclusion`: there is `ξ_b ∈ (0, 1]` such that for
`0 < ξ ≤ ξ_b`, every `Δ`-Euclidean geodesic `η` with `Δ ≤ ξ^{99/100}` and every `R ≥ ξ^{2/3}` with
`M(η) > R`, some band at a grid point of a level `j ≤ J(ξ)` exceeds `c_β R ℓ_j^{1/8}`. -/
theorem exists_band_gt_of_lt_maxDev : ∃ ξb : ℝ, 0 < ξb ∧ ξb ≤ 1 ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξb →
    ∀ (d : ℂ × ℂ → ℝ) (η : C(unitInterval, ℂ)) (Δ : ℝ), ApproxGeod d η Δ → Δ ≤ ξ ^ (99 / 100 : ℝ) →
    ∀ R : ℝ, ξ ^ (2 / 3 : ℝ) ≤ R → R < maxDev η →
      ∃ j ≤ Jxi ξ, ∃ a ∈ probeGrid j, cBeta * R * ell j ^ (1 / 8 : ℝ) < |band (yPath η) j a| := by
  obtain ⟨Cr, hCr, hrec⟩ := maxDev_le_of_bands
  set c : ℝ := 3 / (8 * (Cr + 1)) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    linarith
  set ξb : ℝ := c ^ (1200 / 19 : ℝ) with hξb
  have hξb0 : 0 < ξb := Real.rpow_pos_of_pos hc0 _
  have hξb1 : ξb ≤ 1 := Real.rpow_le_one hc0.le hc1 (by norm_num)
  have hξbc : ξb ^ (19 / 1200 : ℝ) = c := by
    rw [hξb, ← Real.rpow_mul hc0.le]
    norm_num
  refine ⟨ξb, hξb0, hξb1, fun ξ h0 hξ d η Δ h hΔ R hR hRM => ?_⟩
  have h1 : ξ ≤ 1 := hξ.trans hξb1
  by_contra hnot
  simp only [not_exists, not_and, not_lt] at hnot
  have hR0 : 0 ≤ R := le_trans (Real.rpow_nonneg h0.le _) hR
  have hM := hrec d η Δ h (Jxi ξ) R hR0 hnot
  have hrem := sqrt_ell_Jxi_mul_add_le h0 h1 h.nonneg hΔ
  have hsmall : ξ ^ (19 / 1200 : ℝ) ≤ c := by
    rw [← hξbc]
    exact Real.rpow_le_rpow h0.le hξ (by norm_num)
  have hcCr : 2 * Cr * c ≤ 3 / 4 := by
    rw [hc, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hδ0 : 0 ≤ ξ ^ (2 / 3 : ℝ) := Real.rpow_nonneg h0.le _
  have hξ0' : 0 ≤ ξ ^ (19 / 1200 : ℝ) := Real.rpow_nonneg h0.le _
  have hfin : Cr * (Real.sqrt (ell (Jxi ξ) * Δ) + Δ) ≤ 3 / 4 * ξ ^ (2 / 3 : ℝ) := by
    calc Cr * (Real.sqrt (ell (Jxi ξ) * Δ) + Δ)
        ≤ Cr * (2 * ξ ^ (19 / 1200 : ℝ) * ξ ^ (2 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hrem hCr
      _ = (2 * Cr * ξ ^ (19 / 1200 : ℝ)) * ξ ^ (2 / 3 : ℝ) := by ring
      _ ≤ (2 * Cr * c) * ξ ^ (2 / 3 : ℝ) := by gcongr
      _ ≤ 3 / 4 * ξ ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_right hcCr hδ0
  linarith

end SmallGammaGeodesics
