import HigherDimLQGContinuity.UnifBase.Hyp
import HigherDimLQGMetric.DGZ.SelfDiam
import HigherDimLFPP.Exist.CrudeBounds
import HigherDimLFPP.Exist.Concentration

/-!
# Equi-Lipschitz mean exponents of the unit functional (packet U0)

Blueprint Part D, `d:lem-equilip` (a)–(d) ([C] (A.5)–(A.6); NA3 R2(a)–(d), ROUTE-3; ruling N8: part (e), the Lipschitz
property of `ϕ`, is PAR's `phiXi_lipschitz` and is not proved again). For a dyadic realization `(P, W, H)` put
`X^ξ_n = lfppDistance d ξ (H n · ω)` (the unit functional `D_n(0, e₁; Q₂(0))`), `S_n = sup_{[-2,2]^d} |h_n|` and

`f_n(ξ) = expMean P H ξ n = E[log X^ξ_n]/(n log 2)` (junk value `0` at `n = 0`).

* (a) `expMean_zero_left`: `f_n(0) = 0` (`X^0_n = 1`, PAR's `log_lfppDistance_zero`); pathwise
  `|log X^ξ_n - log X^η_n| ≤ |ξ - η| S_n` (PAR's `abs_log_lfppDistance_param_sub_le`); `log X^ξ_n ∈ L¹`
  (`IsBandVersion.integrable_log_lfppDistance`).
* (b) `exists_integral_bandSup_le`: `E S_n ≤ A₁ n` for `n ≥ 1` (`exists_bandSup_bounds` and `Crude.supMean_band_le`
  with `m = n`), with `A₁ = 2 · bandConst + 1` depending only on `(d, κ)`; hence `expMean_lipschitz`: every `f_n` is
  `L`-Lipschitz on `ℝ` with `L = A₁/log 2`, uniformly in `n` and in the realization.
* (c) `abs_log_aQ_sub_integral_le`: `|log a^ξ_n(p) - E log X^ξ_n| ≤ q(p) ξ √(n log 2)` for `ξ > 0`, `n ≥ 1`,
  `p ∈ (0, 1)` (`IsBandVersion.abs_log_lowerQuantile_lfppDistance_sub_le`, `q = quantileConst`); in normalized form
  `abs_log_aQ_div_sub_expMean_le`: `|log a^ξ_n(p)/(n log 2) - f_n(ξ)| ≤ q(p) ξ/√(n log 2)`.
* (d) `tendsto_expMean`: `f_n(ξ) → ϕ(ξ) - 1` for every `ξ ≥ 0` (for `ξ > 0`: `DGZ.IsDGZExponent` at `Q(ξ)` from
  `l10a_isDGZExponent_of_isKernelExponent ∘ l10a_distExp_isKernelExponent`, no subcriticality, and (c) at `p = 1/2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd WN IsLFPPKernel IsWhiteNoise IsBandVersion lfppDistance)

variable {d : ℕ}

/-- The mean exponent `f_n(ξ) = E[log X^ξ_n]/(n log 2)` of the unit functional `X^ξ_n = D_n(0, e₁; Q₂(0))` of a dyadic
realization (`d:lem-equilip`; junk value `0` at `n = 0`). It depends only on the law of `h_n`. -/
def expMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ) (ξ : ℝ) (n : ℕ) : ℝ :=
  (∫ ω, Real.log (lfppDistance d ξ (fun z => H n z ω)) ∂P) / (n * Real.log 2)

section Basic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `f_0 = 0` (the junk value at depth `0`). -/
@[simp] theorem expMean_zero_right (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ) (ξ : ℝ) :
    expMean P H ξ 0 = 0 := by
  simp only [expMean, Nat.cast_zero, zero_mul, div_zero]

/-- **`d:lem-equilip`(a)**: `f_n(0) = 0`, since `X^0_n = 1` (`d ≥ 1`). -/
theorem expMean_zero_left (hd : 0 < d) (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ) (n : ℕ) :
    expMean P H 0 n = 0 := by
  simp only [expMean, log_lfppDistance_zero hd, integral_zero, zero_div]

/-- `f_n(ξ)` depends only on the law (`d:lem-equilip`: "this depends only on the law, hence on no choice"): it is the
same for every dyadic realization (`IsBandVersion.map_lfppDistance_eq`, as `DGZ.aQ_eq_of_isDyadicRealization`). -/
theorem expMean_eq_of_isDyadicRealization {κ : Rd d → ℝ} {Ω' : Type*} [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} {H' : ℕ → Rd d → Ω' → ℝ} (hH : DGZ.IsDyadicRealization κ P W H)
    (hH' : DGZ.IsDyadicRealization κ P' W' H') (ξ : ℝ) (n : ℕ) :
    expMean P H ξ n = expMean P' H' ξ n := by
  unfold expMean
  have hm := (hH.band n).map_lfppDistance_eq (hH'.band n) hH.whiteNoise hH'.whiteNoise ξ
    (HigherDimLFPP.DGZ.measurable_lfppDistance_continuousMap ξ)
  have h1 : ∫ ω, Real.log (lfppDistance d ξ fun z => H n z ω) ∂P =
      ∫ x, Real.log x ∂(P.map fun ω => lfppDistance d ξ fun z => H n z ω) :=
    (integral_map ((hH.band n).measurable_lfppDistance ξ).aemeasurable
      Real.measurable_log.aestronglyMeasurable).symm
  have h2 : ∫ ω, Real.log (lfppDistance d ξ fun z => H' n z ω) ∂P' =
      ∫ x, Real.log x ∂(P'.map fun ω => lfppDistance d ξ fun z => H' n z ω) :=
    (integral_map ((hH'.band n).measurable_lfppDistance ξ).aemeasurable
      Real.measurable_log.aestronglyMeasurable).symm
  rw [h1, h2, hm]

/-- `|φ z| ≤ sup_{[-2,2]^d} |φ|` on the cube `Q₂(0)` (`closure U ⊆ [-2,2]^d`). -/
theorem u0_abs_le_iSup_box {φ : Rd d → ℝ} (hφ : Continuous φ) {z : Rd d}
    (hz : z ∈ HigherDimLFPP.cube d) :
    |φ z| ≤ ⨆ w : HigherDimLFPP.Osc.box (0 : Rd d) 2, |φ w| :=
  HigherDimLFPP.Conc.abs_le_iSup_abs_of_isCompact (HigherDimLFPP.Osc.isCompact_box 0 2) hφ
    (HigherDimLFPP.Osc.closure_cube_subset_box (subset_closure hz))

/-- **`d:lem-equilip`(a)**, pathwise comparison: `|log X^ξ - log X^η| ≤ |ξ - η| sup_{[-2,2]^d} |φ|`. -/
theorem abs_log_lfppDistance_sub_le_iSup_box {φ : Rd d → ℝ} (hφ : Continuous φ) (ξ η : ℝ) :
    |Real.log (lfppDistance d ξ φ) - Real.log (lfppDistance d η φ)| ≤
      |ξ - η| * ⨆ w : HigherDimLFPP.Osc.box (0 : Rd d) 2, |φ w| :=
  abs_log_lfppDistance_param_sub_le hφ (fun _ hz => u0_abs_le_iSup_box hφ hz) ξ η

end Basic

/-! ### (b) The expected supremum and the equi-Lipschitz bound -/

/-- **`d:lem-equilip`(b)**: `E sup_{[-2,2]^d} |h_n| ≤ A₁ n` for `n ≥ 1`, with `A₁` depending only on `(d, κ)`
(`exists_bandSup_bounds`: `E sup |h_n| ≤ 2 supMean + √(n log 2)`; `Crude.supMean_band_le` with `m = n`:
`supMean ≤ bandConst · n`; `√(n log 2) ≤ n`). -/
theorem exists_integral_bandSup_le (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ A₁ : ℝ, 0 < A₁ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
      {H : ℕ → Rd d → Ω → ℝ}, DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ, 1 ≤ n →
        Integrable (fun ω => ⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) 2, |H n z ω|) P ∧
        ∫ ω, (⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) 2, |H n z ω|) ∂P ≤ A₁ * n := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨L, -, hL⟩ := HigherDimLFPP.exists_bandSup_bounds hκ
  have hK := HigherDimLFPP.Crude.bandConst_pos d L
  refine ⟨2 * HigherDimLFPP.Crude.bandConst d L + 1, by linarith, ?_⟩
  intro Ω _ P W H hH n hn
  have hband : IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 (H n) :=
    (hH.band n).congr_band (inv_pow 2 n) rfl
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hV : 0 < (n : ℝ) * Real.log 2 := by positivity
  have hbV : Real.log (1 / ((2 : ℝ) ^ n)⁻¹) ≤ n * Real.log 2 := by
    rw [one_div, inv_inv, Real.log_pow]
  have ha1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨-, -, ⟨hint, hle⟩, -⟩ := hL hH.whiteNoise (by positivity) ha1 hband hV hbV (0 : Rd d)
    (R := 2) (by norm_num)
  refine ⟨hint, hle.trans ?_⟩
  have hsm := HigherDimLFPP.Crude.supMean_band_le d L hn le_rfl
  rw [Real.sqrt_mul_self (Nat.cast_nonneg n)] at hsm
  have hsq : √((n : ℝ) * Real.log 2) ≤ n := by
    rw [Real.sqrt_le_left]
    · have hl1 : Real.log 2 ≤ 1 := HigherDimLFPP.Crude.log_two_le_one
      nlinarith
    · positivity
  linarith

/-- **`d:lem-equilip`(b)**: the mean exponents are equi-Lipschitz: there is `L ≥ 0`, depending only on `(d, κ)`, with
`|f_n(ξ) - f_n(η)| ≤ L |ξ - η|` for every dyadic realization, every `n` and all `ξ, η ∈ ℝ`. -/
theorem expMean_lipschitz (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
      {H : ℕ → Rd d → Ω → ℝ}, DGZ.IsDyadicRealization κ P W H → ∀ (n : ℕ) (ξ η : ℝ),
        |expMean P H ξ n - expMean P H η n| ≤ L * |ξ - η| := by
  obtain ⟨A₁, hA₁, hA⟩ := exists_integral_bandSup_le hd hκ
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨A₁ / Real.log 2, by positivity, ?_⟩
  intro Ω _ P W H hH n ξ η
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [expMean_zero_right, sub_self, abs_zero]
    positivity
  obtain ⟨hint, hle⟩ := hA hH n hn
  have hband := hH.band n
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hiξ := hband.integrable_log_lfppDistance hκ hH.whiteNoise ha ξ
  have hiη := hband.integrable_log_lfppDistance hκ hH.whiteNoise ha η
  have hpt : ∀ ω, |Real.log (lfppDistance d ξ (fun z => H n z ω)) -
      Real.log (lfppDistance d η (fun z => H n z ω))| ≤
        |ξ - η| * ⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) 2, |H n z ω| := fun ω =>
    abs_log_lfppDistance_sub_le_iSup_box (hband.continuous ω) ξ η
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n * Real.log 2 := by positivity
  unfold expMean
  rw [← sub_div, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos, ← integral_sub hiξ hiη]
  calc |∫ ω, (Real.log (lfppDistance d ξ (fun z => H n z ω)) -
          Real.log (lfppDistance d η (fun z => H n z ω))) ∂P|
      ≤ ∫ ω, |Real.log (lfppDistance d ξ (fun z => H n z ω)) -
          Real.log (lfppDistance d η (fun z => H n z ω))| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, |ξ - η| * ⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) 2, |H n z ω| ∂P :=
        integral_mono (hiξ.sub hiη).abs (hint.const_mul _) hpt
    _ = |ξ - η| * ∫ ω, (⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) 2, |H n z ω|) ∂P :=
        integral_const_mul _ _
    _ ≤ |ξ - η| * (A₁ * n) := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ = A₁ / Real.log 2 * |ξ - η| * (n * Real.log 2) := by
        field_simp

/-! ### (c) Quantiles against the mean -/

section Quantile

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}

/-- **`d:lem-equilip`(c)** ([8]-bp `r2:cor:quant`(c)): for `ξ > 0`, `n ≥ 1` and `p ∈ (0, 1)`,
`|log a^ξ_n(p) - E log X^ξ_n| ≤ q(p) ξ √(n log 2)` (`q = quantileConst`). -/
theorem abs_log_aQ_sub_integral_le (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hH : DGZ.IsDyadicRealization κ P W H) {ξ : ℝ} (hξ : 0 < ξ) {n : ℕ} (hn : 1 ≤ n)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    |Real.log (DGZ.aQ P H ξ n p) - ∫ ω, Real.log (lfppDistance d ξ (fun z => H n z ω)) ∂P| ≤
      HigherDimLFPP.Conc.quantileConst p.toReal * ξ * √(n * Real.log 2) := by
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hab : (2 : ℝ)⁻¹ ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have h := (hH.band n).abs_log_lowerQuantile_lfppDistance_sub_le hd hκ hH.whiteNoise ha hab hξ
    hp0 hp1
  rw [DGZ.log_one_div_inv_two_pow] at h
  exact h

/-- **`d:lem-equilip`(c)**, normalized: `|log a^ξ_n(p)/(n log 2) - f_n(ξ)| ≤ q(p) ξ / √(n log 2)`. -/
theorem abs_log_aQ_div_sub_expMean_le (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hH : DGZ.IsDyadicRealization κ P W H) {ξ : ℝ} (hξ : 0 < ξ) {n : ℕ} (hn : 1 ≤ n)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    |Real.log (DGZ.aQ P H ξ n p) / (n * Real.log 2) - expMean P H ξ n| ≤
      HigherDimLFPP.Conc.quantileConst p.toReal * ξ / √(n * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) < n * Real.log 2 := by positivity
  have h := abs_log_aQ_sub_integral_le hd hκ hH hξ hn hp0 hp1
  unfold expMean
  rw [← sub_div, abs_div, abs_of_pos hx]
  calc |Real.log (DGZ.aQ P H ξ n p) -
          ∫ ω, Real.log (lfppDistance d ξ (fun z => H n z ω)) ∂P| / (n * Real.log 2)
      ≤ HigherDimLFPP.Conc.quantileConst p.toReal * ξ * √(n * Real.log 2) / (n * Real.log 2) :=
        div_le_div_of_nonneg_right h hx.le
    _ = HigherDimLFPP.Conc.quantileConst p.toReal * ξ / √(n * Real.log 2) := by
        rw [mul_div_assoc, Real.sqrt_div_self', mul_one_div]

end Quantile

/-- `c / √(n log 2) → 0`. -/
theorem u0_tendsto_const_div_sqrt (c : ℝ) :
    Tendsto (fun n : ℕ => c / √((n : ℝ) * Real.log 2)) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hlog2
  exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp h1)

/-! ### (d) The pointwise limit -/

/-- **`d:lem-equilip`(d)**: `f_n(ξ) → ϕ(ξ) - 1` for every `ξ ≥ 0` and every dyadic realization (`d ≥ 2`). For
`ξ > 0`: `log λ^ξ_n/(n log 2) → ξQ(ξ) - 1` (`DGZ.IsDGZExponent` at `Q(ξ)`, no subcriticality needed) and
`|f_n(ξ) - log λ^ξ_n/(n log 2)| ≤ q(1/2) ξ/√(n log 2)` (c); for `ξ = 0` both sides vanish. -/
theorem tendsto_expMean (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : DGZ.IsDyadicRealization κ P W H) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    Tendsto (fun n : ℕ => expMean P H ξ n) atTop (𝓝 (phiXi d ξ - 1)) := by
  have hd0 : 0 < d := by omega
  rcases hξ.lt_or_eq with hξ | rfl
  swap
  · simp only [expMean_zero_left hd0, phiXi_zero, sub_self]
    exact tendsto_const_nhds
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp := l10a_isDGZExponent_of_isKernelExponent hd hκ
    (l10a_distExp_isKernelExponent hd hκ hξ) Ω P W H hH
  have hm : Tendsto (fun n : ℕ => Real.log (DGZ.aQ P H ξ n 2⁻¹) / (n * Real.log 2)) atTop
      (𝓝 (phiXi d ξ - 1)) := by
    have h := hexp.div_const (Real.log 2)
    have e1 : (fun n : ℕ => Real.log (DGZ.aQ P H ξ n 2⁻¹) / (n * Real.log 2)) =
        fun n : ℕ => Real.log (DGZ.aQ P H ξ n 2⁻¹) / n / Real.log 2 := by
      funext n
      rw [div_div]
    have e2 : phiXi d ξ - 1 = -(1 - ξ * distExp d ξ) * Real.log 2 / Real.log 2 := by
      rw [phiXi_of_pos hξ, mul_div_assoc, div_self hlog2.ne']
      ring
    rw [e1, e2]
    exact h
  have hp0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hp1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  refine tendsto_of_tendsto_of_dist hm ?_
  refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_
    (u0_tendsto_const_div_sqrt (HigherDimLFPP.Conc.quantileConst (2⁻¹ : ℝ≥0∞).toReal * ξ))
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.dist_eq]
  exact abs_log_aQ_div_sub_expMean_le hd0 hκ hH hξ hn hp0 hp1

end HigherDimLQGContinuity
