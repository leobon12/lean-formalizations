import HigherDimLFPP.Upper.UpperProb
import HigherDimLFPP.Frozen.Kappa
import HigherDimLFPP.Frozen.IsLFPPExponent

/-!
# The existence-free upper comparison: HA3 D10, (4.1′) and (4.25′)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (4.1) and (4.25), in the existence-free form
of the planning audit HA3 (`planning/audits/HA3-section-4.md`), §5 ("What §4 proves without
assuming that `λ_d` exists"), Details D10 and the Lean statements of "(c)" (`UpperComparisonBlock`,
`UpperComparison`, `UpperComparisonExponent`), stated with the frozen white-noise model (ruling
H10): `IsWhiteNoise P W` and continuous versions `H ε` of `H_{ε,1}` for `ε ∈ (0,1)`.

* `UpperComparisonBlock d` — **(4.1′)**: for every admissible kernel there is `C = C(d, κ)` such
  that for every model and every `n ≥ 3` there is `ζ_n > 0` with
  `P*[log D^ζ_{ε,d}/log ε > ζ^{4/3} (α_n A_{n,d} + C n^{3/4})/((n-1) log 2) + θ] → 0` as `ε ↓ 0`,
  for all `ζ ∈ (0, ζ_n)` and `θ > 0`.
* `UpperComparison d` — **(4.25′)**: for every `η > 0` and all small `ζ`,
  `P*[log D^ζ_{ε,d}/log ε > (κ_d + η) ζ^{4/3}] → 0`.
* `UpperComparisonExponent d` — the exponent form (the paper's (4.25) when `λ_d` exists):
  every LFPP exponent satisfies `λ ≤ (κ_d + η) ζ^{4/3}` for all small `ζ`; and
  `upperComparison_limsup`: `lim sup_{ζ↓0} λ(ζ)/ζ^{4/3} ≤ κ_d` for every exponent function.

All three are proved here **conditional on `GoodRecordMeanBound d κ`** (HA3 D6 (iv), the conclusion
of Lemma 4.3 for records), the only hypothesis beyond the frozen model; the Lemma 4.3 packet
completes the upper comparison by supplying it (`upperComparisonBlock_of_goodRecordMeanBound`,
`upperComparison_of_goodRecordMeanBound`, `upperComparisonExponent_of_goodRecordMeanBound`).

**Proof** (HA3 D10).  (4.1′): `τ = u = n^{-1/4}`, `t = n^{1/4}`; for `ζ < ζ_n = δ_*^{3/2}` put
`δ = ζ^{2/3}`, so `δ^{3/2} = ζ`, `δ² = ζ^{4/3}`; D8 (`upperProb_tendsto`) with the exceptional
events of `chainUnionBound`, D9 (`exists_Psi_le`, `Z_b ≤ 1` by `exists_Nb_wBad_le_one`) and
`log(2K/3) ≥ (n-1) log 2`.  (4.25′): `α_n → 1`, `A_{n,d}/(n log 2) → κ_d` (Fekete,
`Var.tendsto_A_div`), `n/(n-1) → 1`, `n^{3/4}/(n-1) → 0`, so the rate tends to `κ_d`; choose `n` with
rate `≤ κ_d + η/2` and `θ = η ζ^{4/3}/2`.  Exponent form: a limit in probability cannot exceed a
level that is exceeded only with probability `→ 0`.

2D source: `LQGDimension/LFPP/UpperAssembly.lean` (`lam_le_at_delta`, `upperAssembly`) and
`LQGDimension/LFPP/ExponentFromProb.lean` (`exponentFromProb`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

/-! ## The statements -/

/-- The rate in (4.1′) (inside the `ζ^{4/3}`): `(α_n A_{n,d} + C n^{3/4}) / ((n - 1) log 2)`. -/
def upperRate (d : ℕ) (C : ℝ) (n : ℕ) : ℝ :=
  (alphaN n * (A n d).toReal + C * (n : ℝ) ^ (3 / 4 : ℝ)) / (((n : ℝ) - 1) * Real.log 2)

/-- **(4.1′), existence-free** (HA3 §5).  For every admissible kernel there is `C` such that for
every white-noise model and every block size `n ≥ 3` there is `ζ_n > 0` with
`P[log D^ζ_{ε,d}/log ε > ζ^{4/3} (α_n A_{n,d} + C n^{3/4})/((n-1) log 2) + θ] → 0` as `ε ↓ 0`, for
all `ζ ∈ (0, ζ_n)` and `θ > 0`.  (`P` of a possibly non-measurable set is its outer measure.) -/
def UpperComparisonBlock (d : ℕ) : Prop :=
  ∀ κ : Rd d → ℝ, IsLFPPKernel κ → ∃ C : ℝ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      ∀ n : ℕ, 3 ≤ n → ∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, ∀ θ > 0,
        Tendsto (fun ε => P {ω | ζ ^ (4 / 3 : ℝ) * upperRate d C n + θ <
            Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε}) (𝓝[>] 0) (𝓝 0)

/-- **(4.25′), existence-free** (HA3 §5).  For every `η > 0` and all small `ζ`,
`P[log D^ζ_{ε,d}/log ε > (κ_d + η) ζ^{4/3}] → 0` as `ε ↓ 0`. -/
def UpperComparison (d : ℕ) : Prop :=
  ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      ∀ η > 0, ∀ᶠ ζ in 𝓝[>] 0,
        Tendsto (fun ε => P {ω | ζ ^ (4 / 3 : ℝ) * (kappa d + η) <
            Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε}) (𝓝[>] 0) (𝓝 0)

/-- Consequence for exponents (the paper's (4.25) when `λ_d` exists): every LFPP exponent at a
small `ζ` is at most `(κ_d + η) ζ^{4/3}`. -/
def UpperComparisonExponent (d : ℕ) : Prop :=
  ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      ∀ η > 0, ∀ᶠ ζ in 𝓝[>] 0, ∀ lam : ℝ, IsLFPPExponent H P ζ lam →
        lam ≤ ζ ^ (4 / 3 : ℝ) * (kappa d + η)

/-! ## (4.1′) -/

section Block

variable {d : ℕ}

/-- `(ζ^{2/3})^{3/2} = ζ` and `(ζ^{2/3})² = ζ^{4/3}` for `ζ ≥ 0`. -/
theorem rpow_two_thirds_facts {ζ : ℝ} (hζ : 0 ≤ ζ) :
    (ζ ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = ζ ∧ (ζ ^ (2 / 3 : ℝ)) ^ 2 = ζ ^ (4 / 3 : ℝ) := by
  constructor
  · rw [← Real.rpow_mul hζ]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hζ]
    norm_num

/-- **(4.1′) for one kernel**, conditional on the good-record mean bound. -/
theorem upperComparisonBlock_kernel [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hG : GoodRecordMeanBound d κ) :
    ∃ C : ℝ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
      ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
        ∀ n : ℕ, 3 ≤ n → ∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, ∀ θ > 0,
          Tendsto (fun ε => P {ω | ζ ^ (4 / 3 : ℝ) * upperRate d C n + θ <
              Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Cstar, CV, hCstar, hCV, hmain⟩ := chainUnionBound hκ hG
  obtain ⟨C, hC0, hPsi⟩ := exists_Psi_le d (CV := CV) hCstar
  refine ⟨C, fun Ω _ P W hW H hH n hn => ?_⟩
  obtain ⟨Cbad, CV', -, hCV', hn'⟩ := hmain n hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set τ := (n : ℝ) ^ (-(1 / 4 : ℝ)) with hτdef
  set t := (n : ℝ) ^ (1 / 4 : ℝ) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos hn0 _
  have hτ : τ ∈ Ioo (0 : ℝ) 1 :=
    ⟨rpow_neg_quarter_pos hn1, rpow_neg_quarter_lt_one (by omega)⟩
  obtain ⟨δ₀, hδ₀, hexc⟩ := hn' Ω P W hW H hH τ hτ τ hτ
  obtain ⟨δ₁, hδ₁, hZb⟩ := exists_Nb_wBad_le_one d n ht Cbad hCV'
  set δs := min δ₀ δ₁ with hδs
  have hδs0 : 0 < δs := lt_min hδ₀ hδ₁
  refine ⟨δs ^ (3 / 2 : ℝ), Real.rpow_pos_of_pos hδs0 _, fun ζ hζ θ hθ => ?_⟩
  have hζ0 : 0 < ζ := hζ.1
  obtain ⟨hζδ, hδ2⟩ := rpow_two_thirds_facts hζ0.le
  set δ := ζ ^ (2 / 3 : ℝ) with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos hζ0 _
  have hδlt : δ < δs := by
    have h := Real.rpow_lt_rpow hζ0.le hζ.2 (by norm_num : (0 : ℝ) < 2 / 3)
    rwa [← Real.rpow_mul hδs0.le, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num,
      Real.rpow_one] at h
  have hδ₀' : δ ∈ Ioo (0 : ℝ) δ₀ := ⟨hδ, hδlt.trans_le (min_le_left _ _)⟩
  have hδ₁' : δ ∈ Ioo (0 : ℝ) δ₁ := ⟨hδ, hδlt.trans_le (min_le_right _ _)⟩
  set Z := Zsum d n δ t τ (bStar d n τ τ Cstar) Cbad CV CV' with hZdef
  have hZ0 : 0 ≤ Z :=
    add_nonneg (tsum_nonneg fun k => mul_nonneg (Ng_nonneg d n k) (wGood_pos _ _ _ _ _).le)
      (mul_nonneg (Nb_nonneg d n hδ) (wBad_pos _ _ _ _ _).le)
  -- D8
  have h8 := upperProb_tendsto hκ hW hH hn hδ ht hZ0 (fun ε hε => by
    obtain ⟨𝒜, h𝒜, hω⟩ := hexc δ hδ₀' t ht ε hε
    exact ⟨𝒜, h𝒜, fun ω h => (hω ω h).2⟩) hθ
  rw [hζδ] at h8
  -- D9 and the comparison of rates
  have hΨ := hPsi n hn hδ (hZb δ hδ₁')
  have hL₀ := sub_one_mul_log_two_le hn1
  have hn2 : (0 : ℝ) < ((n : ℝ) - 1) * Real.log 2 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact mul_pos (by linarith) (Real.log_pos one_lt_two)
  have hnum0 : 0 ≤ alphaN n * (A n d).toReal + C * (n : ℝ) ^ (3 / 4 : ℝ) := by
    have := alphaN_pos (n := n) (by omega)
    have := Var.A_toReal_nonneg n d
    have := Real.rpow_nonneg hn0.le (3 / 4 : ℝ)
    positivity
  have hrate : δ ^ 2 * ((Real.log (1 + Z) + 2) / t) / Real.log (2 * (2 : ℝ) ^ n / 3) ≤
      ζ ^ (4 / 3 : ℝ) * upperRate d C n := by
    rw [← hδ2, upperRate, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg δ)
    calc (Real.log (1 + Z) + 2) / t / Real.log (2 * (2 : ℝ) ^ n / 3)
        ≤ (alphaN n * (A n d).toReal + C * (n : ℝ) ^ (3 / 4 : ℝ)) /
            Real.log (2 * (2 : ℝ) ^ n / 3) :=
          div_le_div_of_nonneg_right hΨ (log_two_mul_div_three_pos hn).le
      _ ≤ (alphaN n * (A n d).toReal + C * (n : ℝ) ^ (3 / 4 : ℝ)) /
            (((n : ℝ) - 1) * Real.log 2) :=
          div_le_div_of_nonneg_left hnum0 hn2 hL₀
  refine ENNReal.tendsto_nhds_zero.2 fun e he =>
    (ENNReal.tendsto_nhds_zero.1 h8 e he).mono fun ε hε => (measure_mono fun ω hω => ?_).trans hε
  simp only [mem_ofPred_eq] at hω ⊢
  linarith

/-- **(4.1′)** (`UpperComparisonBlock`), conditional on the good-record mean bound (HA3 D6 (iv))
for every admissible kernel. -/
theorem upperComparisonBlock_of_goodRecordMeanBound (hd : 1 ≤ d)
    (hG : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → GoodRecordMeanBound d κ) :
    UpperComparisonBlock d := by
  have : NeZero d := ⟨by omega⟩
  intro κ hκ
  exact upperComparisonBlock_kernel hκ (hG κ hκ)

end Block

/-! ## (4.25′) -/

section Limit

variable {d : ℕ}

/-- `α_n → 1`. -/
theorem tendsto_alphaN : Tendsto alphaN atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => 1 + (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 1) := by
    simpa using h0.const_add 1
  have h2 : Tendsto (fun n : ℕ => 1 - (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 1) := by
    simpa using h0.const_sub 1
  have c1 : Tendsto (fun x : ℝ => x ^ (2 / 3 : ℝ)) (𝓝 1) (𝓝 1) := by
    simpa using (Real.continuousAt_rpow_const 1 (2 / 3) (Or.inl one_ne_zero)).tendsto
  have c2 : Tendsto (fun x : ℝ => x ^ (-(1 / 3 : ℝ))) (𝓝 1) (𝓝 1) := by
    simpa using (Real.continuousAt_rpow_const 1 (-(1 / 3)) (Or.inl one_ne_zero)).tendsto
  have h := (c1.comp h1).mul (c2.comp h2)
  rw [mul_one] at h
  exact h

/-- `n/(n - 1) → 1`. -/
theorem tendsto_nat_div_sub_one : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1)) atTop (𝓝 1) := by
  have h := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (-1)
  simpa [sub_eq_add_neg] using h

/-- **The rate of (4.1′) tends to `κ_d`** (HA3 D10): `c_n → κ_d` for every `C`. -/
theorem tendsto_upperRate (hd : 2 ≤ d) (C : ℝ) :
    Tendsto (fun n => upperRate d C n) atTop (𝓝 (kappa d)) := by
  have hA := Var.tendsto_A_div hd
  have hq : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => alphaN n * ((A n d).toReal / ((n : ℝ) * Real.log 2)) *
      ((n : ℝ) / ((n : ℝ) - 1)) + C / Real.log 2 * ((n : ℝ) ^ (-(1 / 4 : ℝ)) *
        ((n : ℝ) / ((n : ℝ) - 1)))) atTop (𝓝 (kappa d)) := by
    have := ((tendsto_alphaN.mul hA).mul tendsto_nat_div_sub_one).add
      (tendsto_const_nhds (x := C / Real.log 2) |>.mul (hq.mul tendsto_nat_div_sub_one))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq34 : (n : ℝ) ^ (-(1 / 4 : ℝ)) * n = (n : ℝ) ^ (3 / 4 : ℝ) := by
    have h := Real.rpow_add hn0 (-(1 / 4 : ℝ)) 1
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  rw [upperRate]
  have e : (n : ℝ) ^ (-(1 / 4 : ℝ)) * ((n : ℝ) / ((n : ℝ) - 1)) =
      (n : ℝ) ^ (3 / 4 : ℝ) / ((n : ℝ) - 1) := by
    rw [← hq34, mul_div_assoc]
  rw [e]
  field_simp

/-- **(4.25′) for one kernel**, from (4.1′) and `c_n → κ_d`. -/
theorem upperComparison_kernel (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hG : GoodRecordMeanBound d κ) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      ∀ η > 0, ∀ᶠ ζ in 𝓝[>] 0,
        Tendsto (fun ε => P {ω | ζ ^ (4 / 3 : ℝ) * (kappa d + η) <
            Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε}) (𝓝[>] 0) (𝓝 0) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC⟩ := upperComparisonBlock_kernel hκ hG
  intro Ω _ P W hW H hH η hη
  obtain ⟨n, hn3, hnrate⟩ := ((eventually_ge_atTop 3).and ((tendsto_upperRate hd C).eventually
    (eventually_le_nhds (show kappa d < kappa d + η / 2 by linarith)))).exists
  obtain ⟨ζ₀, hζ₀, hblock⟩ := hC Ω P W hW H hH n hn3
  filter_upwards [Ioo_mem_nhdsGT hζ₀] with ζ hζ
  have hζ43 : 0 < ζ ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hζ.1 _
  have h := hblock ζ hζ (ζ ^ (4 / 3 : ℝ) * (η / 2)) (by positivity)
  refine ENNReal.tendsto_nhds_zero.2 fun e he =>
    (ENNReal.tendsto_nhds_zero.1 h e he).mono fun ε hε => (measure_mono fun ω hω => ?_).trans hε
  simp only [mem_ofPred_eq] at hω ⊢
  have : ζ ^ (4 / 3 : ℝ) * upperRate d C n ≤ ζ ^ (4 / 3 : ℝ) * (kappa d + η / 2) :=
    mul_le_mul_of_nonneg_left hnrate hζ43.le
  nlinarith

/-- **(4.25′)** (`UpperComparison`), conditional on the good-record mean bound (HA3 D6 (iv)) for
every admissible kernel. -/
theorem upperComparison_of_goodRecordMeanBound (hd : 2 ≤ d)
    (hG : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → GoodRecordMeanBound d κ) : UpperComparison d :=
  fun κ hκ => upperComparison_kernel hd hκ (hG κ hκ)

end Limit

/-! ## The exponent form -/

section Exponent

variable {d : ℕ}

/-- **A limit in probability cannot exceed a level that is exceeded only with probability `→ 0`**
(HA3 D10, "Exponent form"; 2D `exponentFromProb`).  If `X_ε → λ` in probability as `ε ↓ 0` and
`P*(c < X_ε) → 0`, then `λ ≤ c`. -/
theorem le_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ} {lam c : ℝ}
    (hX : TendstoInMeasure P X (𝓝[>] 0) (fun _ => lam))
    (hc : Tendsto (fun ε => P {ω | c < X ε ω}) (𝓝[>] 0) (𝓝 0)) : lam ≤ c := by
  by_contra hlt
  push Not at hlt
  set θ := (lam - c) / 2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have h1 := hX (ENNReal.ofReal θ) (ENNReal.ofReal_pos.2 hθ0)
  have hsub : ∀ ε, {ω | X ε ω ≤ c} ⊆ {ω | ENNReal.ofReal θ ≤ edist (X ε ω) lam} := by
    intro ε ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have h2 : Tendsto (fun ε => P {ω | X ε ω ≤ c}) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
      fun ε => measure_mono (hsub ε)
  have hsum := h2.add hc
  rw [add_zero] at hsum
  have hge : ∀ ε, (1 : ENNReal) ≤ P {ω | X ε ω ≤ c} + P {ω | c < X ε ω} := by
    intro ε
    calc (1 : ENNReal) = P univ := measure_univ.symm
      _ ≤ P ({ω | X ε ω ≤ c} ∪ {ω | c < X ε ω}) := by
          refine measure_mono fun ω _ => ?_
          rcases le_or_gt (X ε ω) c with h | h
          · exact Or.inl h
          · exact Or.inr h
      _ ≤ _ := measure_union_le _ _
  have := ge_of_tendsto' hsum hge
  simp at this

/-- **The exponent form** (`UpperComparisonExponent`), conditional on the good-record mean bound
(HA3 D6 (iv)) for every admissible kernel. -/
theorem upperComparisonExponent_of_goodRecordMeanBound (hd : 2 ≤ d)
    (hG : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → GoodRecordMeanBound d κ) :
    UpperComparisonExponent d := by
  intro κ hκ Ω _ P W hW H hH η hη
  have := hW.isProbabilityMeasure
  filter_upwards [upperComparison_of_goodRecordMeanBound hd hG κ hκ Ω P W hW H hH η hη] with ζ hζ
  intro lam hlam
  exact le_of_tendstoInMeasure hlam hζ

/-- **The paper's (4.25)** in `lim sup` form: for every exponent function `λ(ζ)` (an LFPP exponent
for all small `ζ`) and every `η > 0`, eventually `λ(ζ)/ζ^{4/3} ≤ κ_d + η` as `ζ ↓ 0`; conditional
on the good-record mean bound. -/
theorem upperComparison_limsup (hd : 2 ≤ d)
    (hG : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → GoodRecordMeanBound d κ)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) {H : ℝ → Rd d → Ω → ℝ}
    (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) {lam : ℝ → ℝ}
    (hlam : ∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, IsLFPPExponent H P ζ (lam ζ)) {η : ℝ}
    (hη : 0 < η) : ∀ᶠ ζ in 𝓝[>] 0, lam ζ / ζ ^ (4 / 3 : ℝ) ≤ kappa d + η := by
  obtain ⟨ζ₀, hζ₀, hlam⟩ := hlam
  filter_upwards [upperComparisonExponent_of_goodRecordMeanBound hd hG κ hκ Ω P W hW H hH η hη,
    Ioo_mem_nhdsGT hζ₀] with ζ h1 h2
  have hζ43 : 0 < ζ ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos h2.1 _
  rw [div_le_iff₀ hζ43, mul_comm]
  exact h1 (lam ζ) (hlam ζ h2)

end Exponent

end HigherDimLFPP.Upper
