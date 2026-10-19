import HigherDimLFPP.Lower.LowerFixed
import HigherDimLFPP.Var.Lemma22

/-!
# The existence-free lower comparison: HA4 D9–D10, (5.1) and (5.29)

Packet P-L4, targets T3 and T4 (ruling H6; audit HA4, §4 items 3–4 and "Consequences",
"Details for later use" D9–D10, Lean block (c)).  The field is the frozen white-noise model
(ruling H10): `IsWhiteNoise P W` and continuous versions `H ε` of `H_{ε,1}` for `ε ∈ (0,1)`.

* `LowerComparisonBlock d` — **(5.1), existence-free** (HA4 §4 item 3): for `n ≥ N₀`, every
  `η > 0` and all small `ζ`,
  `P*(log D^ζ_{ε,d} / log ε < ζ^{4/3}((β_{n,d} - 7)/((n + g_n) log 2) - η)) → 0` as `ε ↓ 0`.
  From item 2 (`LowerComparisonFixed`) with `δ = ζ^{2/3}`, `θ = δ²η/2`, and
  `log(1/q_δ) → (n + g_n) log 2` (`tendsto_log_inv_qStep`).
* `LowerComparison d` — **(5.29), existence-free** (HA4 §4 item 4): for every `η > 0` and all
  small `ζ`, `P*(log D^ζ_{ε,d} / log ε < (κ_d - η) ζ^{4/3}) → 0` as `ε ↓ 0` through all values.
  From the block form and `(β_{n,d} - 7)/((n + g_n) log 2) → κ_d` (`tendsto_blockRate`: P-V2's
  `betaRateLimit` and `g_n/n → 0`).
* `LowerBoundOfExponent d` — **the exponent form** (HA4 D10, the paper's (5.29) under (1.3)):
  every LFPP exponent at a small `ζ` is at least `(κ_d - η) ζ^{4/3}`; and `lowerComparison_liminf`:
  for every exponent function `λ(ζ)` and every `η > 0`, eventually `λ(ζ)/ζ^{4/3} ≥ κ_d - η`
  (`lim inf_{ζ↓0} λ(ζ)/ζ^{4/3} ≥ κ_d`).

All statements are proved conditional only on Lemma 5.3 (`Lemma53Holds d κ` for every admissible
kernel; P-L3), through the iteration `IterD` (`iterD_of_lemma53`).  The quantifier order is
HA4's: `∀ κ, ∀ η, ∀ᶠ ζ, ∀ model` (the threshold for `ζ` does not depend on the model).

2D source: `LQGDimension/LFPP/LowerAssembly.lean` (`lowerAssembly`) and
`LQGDimension/LFPP/ExponentFromProb.lean` (`exponentFromProb`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-! ## Real analysis -/

/-- `log(1/q_δ) → (n + g_n) log 2` as `δ ↓ 0` (source after (5.28)). -/
theorem tendsto_log_inv_qStep (d n : ℕ) :
    Tendsto (fun δ => Real.log (qStep d n δ)⁻¹) (𝓝[>] 0)
      (𝓝 (((n : ℝ) + gPad n) * Real.log 2)) := by
  have hK : (0 : ℝ) < blockK n := by exact_mod_cast blockK_pos n
  have h1 : Tendsto (qStep d n) (𝓝[>] 0) (𝓝 (1 / (blockK n : ℝ))) := by
    rw [← qStep_zero]
    exact ((continuous_qStep d n).tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun δ => (qStep d n δ)⁻¹) (𝓝[>] 0) (𝓝 (blockK n : ℝ)) := by
    have := h1.inv₀ (by positivity : (1 / (blockK n : ℝ)) ≠ 0)
    rwa [one_div, inv_inv] at this
  have h3 := (Real.continuousAt_log hK.ne').tendsto.comp h2
  have hlog : Real.log (blockK n : ℝ) = ((n : ℝ) + gPad n) * Real.log 2 := by
    rw [blockK, Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  rw [hlog] at h3
  exact h3

/-- For all small `δ`, `(β_{n,d} - 7)/log(1/q_δ) > (β_{n,d} - 7)/((n + g_n) log 2) - η`. -/
theorem eventually_rate_lt (d n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ δ in 𝓝[>] 0, (betaN n d - 7) / (((n : ℝ) + gPad n) * Real.log 2) - η <
      (betaN n d - 7) / Real.log (qStep d n δ)⁻¹ := by
  have hpos : 0 < ((n : ℝ) + gPad n) * Real.log 2 := by
    have := gPad_pos n
    have : (0 : ℝ) < gPad n := by exact_mod_cast this
    have := Real.log_pos one_lt_two
    positivity
  have h := (tendsto_const_nhds (x := betaN n d - 7)).div (tendsto_log_inv_qStep d n) hpos.ne'
  exact h.eventually (lt_mem_nhds (sub_lt_self _ hη))

/-- `ζ ↦ ζ^{2/3}` maps `𝓝[>] 0` to itself. -/
theorem tendsto_rpow_two_thirds :
    Tendsto (fun ζ : ℝ => ζ ^ (2 / 3 : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h := (Real.continuousAt_rpow_const 0 (2 / 3) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ζ hζ
    exact Real.rpow_pos_of_pos hζ _

/-- `(ζ^{2/3})^{3/2} = ζ` and `(ζ^{2/3})² = ζ^{4/3}` for `ζ ≥ 0` (`ζ = δ^{3/2}`, `δ² = ζ^{4/3}`). -/
theorem rpow_two_thirds_rpow {ζ : ℝ} (hζ : 0 ≤ ζ) :
    (ζ ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = ζ ∧ (ζ ^ (2 / 3 : ℝ)) ^ 2 = ζ ^ (4 / 3 : ℝ) := by
  constructor
  · rw [← Real.rpow_mul hζ]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hζ]
    norm_num

/-- `g_n / n → 0` (`g_n = ⌈20 log₂(n + 2)⌉`). -/
theorem tendsto_gPad_div : Tendsto (fun n : ℕ => (gPad n : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2) / n) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    refine h.congr fun n => ?_
    simp only [Function.comp, pow_one, one_mul, add_neg_cancel_right]
  have hup : Tendsto (fun n : ℕ => 20 / Real.log 2 * (Real.log ((n : ℝ) + 2) / n) +
      1 / (n : ℝ)) atTop (𝓝 0) := by
    have := (hlog.const_mul (20 / Real.log 2)).add tendsto_one_div_atTop_nhds_zero_nat
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hlb : 0 ≤ 20 * Real.logb 2 ((n : ℝ) + 2) := by
    have := Real.logb_nonneg one_lt_two hn2
    positivity
  have hg : (gPad n : ℝ) < 20 * Real.logb 2 ((n : ℝ) + 2) + 1 := Nat.ceil_lt_add_one hlb
  have hg' : (gPad n : ℝ) ≤ 20 / Real.log 2 * Real.log ((n : ℝ) + 2) + 1 := by
    have e : 20 * Real.logb 2 ((n : ℝ) + 2) = 20 / Real.log 2 * Real.log ((n : ℝ) + 2) := by
      rw [Real.logb]
      ring
    linarith
  calc (gPad n : ℝ) / n ≤ (20 / Real.log 2 * Real.log ((n : ℝ) + 2) + 1) / n :=
        div_le_div_of_nonneg_right hg' hn0.le
    _ = 20 / Real.log 2 * (Real.log ((n : ℝ) + 2) / n) + 1 / (n : ℝ) := by ring

/-- **The block rate tends to `κ_d`** (HA4 D9): `(β_{n,d} - 7)/((n + g_n) log 2) → κ_d`, from
`β_{n,d}/(n log 2) → κ_d` (Lemma 2.2, P-V2's `betaRateLimit`) and `g_n/n → 0`. -/
theorem tendsto_blockRate (hd : 2 ≤ d) :
    Tendsto (fun n : ℕ => (betaN n d - 7) / (((n : ℝ) + gPad n) * Real.log 2)) atTop
      (𝓝 (kappa d)) := by
  have hβ : Tendsto (fun n : ℕ => betaN n d / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d)) :=
    betaRateLimit d hd
  have h7 : Tendsto (fun n : ℕ => 7 / ((n : ℝ) * Real.log 2)) atTop (𝓝 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat (7 / Real.log 2)).congr fun n => ?_
    rw [div_div, mul_comm]
  have hg : Tendsto (fun n : ℕ => (1 + (gPad n : ℝ) / n)⁻¹) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)).add tendsto_gPad_div).inv₀ (by norm_num)
    simpa using this
  have hlim := (hβ.sub h7).mul hg
  rw [sub_zero, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hg0 : (0 : ℝ) ≤ gPad n := Nat.cast_nonneg _
  have hng : (0 : ℝ) < n + gPad n := by linarith
  field_simp

/-! ## The block form (5.1) -/

/-- **(5.1), existence-free** (HA4 §4 item 3): for every admissible kernel there is `N₀` such
that for every block level `n ≥ N₀`, every `η > 0`, all sufficiently small `ζ > 0` and every
white-noise model, `P*(log D^ζ_{ε,d} / log ε < ζ^{4/3}((β_{n,d} - 7)/((n + g_n) log 2) - η)) → 0`
as `ε ↓ 0` through all values. -/
def LowerComparisonBlock (d : ℕ) : Prop :=
  ∀ κ : Rd d → ℝ, IsLFPPKernel κ → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ η > 0, ∀ᶠ ζ in 𝓝[>] 0,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      Tendsto (fun ε => P {ω | Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε <
          ζ ^ (4 / 3 : ℝ) * ((betaN n d - 7) / (((n : ℝ) + gPad n) * Real.log 2) - η)})
        (𝓝[>] 0) (𝓝 0)

/-- **(5.1)** for one kernel, from the iteration `IterD` (HA4 D9, "Block form"). -/
theorem lowerComparisonBlock_kernel (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hI : IterD d κ) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ η > 0, ∀ᶠ ζ in 𝓝[>] 0,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
      ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
        Tendsto (fun ε => P {ω | Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε <
            ζ ^ (4 / 3 : ℝ) * ((betaN n d - 7) / (((n : ℝ) + gPad n) * Real.log 2) - η)})
          (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨N₀, hN₀⟩ := lowerComparisonFixed_kernel hd hκ hI
  refine ⟨N₀, fun n hn η hη => ?_⟩
  obtain ⟨δ₀, hδ₀, hfix⟩ := hN₀ n hn
  have hδ : ∀ᶠ δ in 𝓝[>] 0, δ ∈ Ioo (0 : ℝ) δ₀ ∧
      (betaN n d - 7) / (((n : ℝ) + gPad n) * Real.log 2) - η / 2 <
        (betaN n d - 7) / Real.log (qStep d n δ)⁻¹ :=
    Filter.Eventually.and (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) δ₀ from
      Ioo_mem_nhdsGT hδ₀) (eventually_rate_lt d n (half_pos hη))
  filter_upwards [tendsto_rpow_two_thirds.eventually hδ, self_mem_nhdsWithin] with ζ hζ hζ0
  intro Ω _ P W hW H hH
  have hζ0' : 0 < ζ := hζ0
  obtain ⟨hδ1, hrate⟩ := hζ
  obtain ⟨h32, h2⟩ := rpow_two_thirds_rpow hζ0'.le
  have hδpos : 0 < ζ ^ (2 / 3 : ℝ) := hδ1.1
  have hθ : 0 < (ζ ^ (2 / 3 : ℝ)) ^ 2 * η / 2 := by positivity
  have hT := hfix (ζ ^ (2 / 3 : ℝ)) hδ1 _ hθ Ω P W hW H hH
  rw [h32] at hT
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => zero_le)
    fun ε => measure_mono fun ω hω => ?_
  have hω' : Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε <
      ζ ^ (4 / 3 : ℝ) * ((betaN n d - 7) / (((n : ℝ) + gPad n) * Real.log 2) - η) := hω
  show Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε <
    (ζ ^ (2 / 3 : ℝ)) ^ 2 * (betaN n d - 7) / Real.log (qStep d n (ζ ^ (2 / 3 : ℝ)))⁻¹ -
      (ζ ^ (2 / 3 : ℝ)) ^ 2 * η / 2
  rw [h2] at hθ ⊢
  have hζ43 : 0 < ζ ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hζ0' _
  have hmul := mul_le_mul_of_nonneg_left hrate.le hζ43.le
  rw [mul_div_assoc]
  nlinarith

/-- **(5.1)** (`LowerComparisonBlock`) from the iteration `IterD`. -/
theorem lowerComparisonBlock_of_iterD (hd : 0 < d)
    (hI : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → IterD d κ) : LowerComparisonBlock d :=
  fun _ hκ => lowerComparisonBlock_kernel hd hκ (hI _ hκ)

/-- **(5.1)** (`LowerComparisonBlock`), conditional only on Lemma 5.3. -/
theorem lowerComparisonBlock_of_lemma53 (hd : 0 < d)
    (h53 : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → Lemma53Holds d κ) : LowerComparisonBlock d :=
  lowerComparisonBlock_of_iterD hd fun _ hκ => iterD_of_lemma53 hd hκ (h53 _ hκ)

/-! ## The rate form (5.29) -/

/-- **(5.29), existence-free** (HA4 §4 item 4, `LowerComparison`): for every admissible kernel,
every `η > 0`, all sufficiently small `ζ > 0` and every white-noise model,
`P*(log D^ζ_{ε,d} / log ε < (κ_d - η) ζ^{4/3}) → 0` as `ε ↓ 0` through all values. -/
def LowerComparison (d : ℕ) : Prop :=
  ∀ κ : Rd d → ℝ, IsLFPPKernel κ → ∀ η > 0, ∀ᶠ ζ in 𝓝[>] 0,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      Tendsto (fun ε => P {ω | Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε <
          (kappa d - η) * ζ ^ (4 / 3 : ℝ)}) (𝓝[>] 0) (𝓝 0)

/-- **(5.29)** for one kernel, from the iteration `IterD` (HA4 D9, "Rate form"). -/
theorem lowerComparison_kernel (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hI : IterD d κ) :
    ∀ η > 0, ∀ᶠ ζ in 𝓝[>] 0,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
      ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
        Tendsto (fun ε => P {ω | Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε <
            (kappa d - η) * ζ ^ (4 / 3 : ℝ)}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨N₀, hN₀⟩ := lowerComparisonBlock_kernel (by omega) hκ hI
  intro η hη
  obtain ⟨n, hnN₀, hn⟩ := ((eventually_ge_atTop N₀).and ((tendsto_blockRate hd).eventually
    (lt_mem_nhds (show kappa d - η / 2 < kappa d by linarith)))).exists
  filter_upwards [hN₀ n hnN₀ (η / 2) (half_pos hη), self_mem_nhdsWithin] with ζ hζ hζ0
  intro Ω _ P W hW H hH
  have hζ43 : 0 < ζ ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hζ0 _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hζ Ω P W hW H hH)
    (fun _ => zero_le) fun ε => measure_mono fun ω hω => ?_
  have hω' : Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε <
      (kappa d - η) * ζ ^ (4 / 3 : ℝ) := hω
  show Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε <
    ζ ^ (4 / 3 : ℝ) * ((betaN n d - 7) / (((n : ℝ) + gPad n) * Real.log 2) - η / 2)
  have hmul := mul_le_mul_of_nonneg_left hn.le hζ43.le
  nlinarith

/-- **(5.29)** (`LowerComparison`) from the iteration `IterD`. -/
theorem lowerComparison_of_iterD (hd : 2 ≤ d)
    (hI : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → IterD d κ) : LowerComparison d :=
  fun _ hκ => lowerComparison_kernel hd hκ (hI _ hκ)

/-- **(5.29)** (`LowerComparison`), conditional only on Lemma 5.3 (HA4 D9). -/
theorem lowerComparison_of_lemma53 (hd : 2 ≤ d)
    (h53 : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → Lemma53Holds d κ) : LowerComparison d :=
  lowerComparison_of_iterD hd fun _ hκ => iterD_of_lemma53 (by omega) hκ (h53 _ hκ)

/-! ## The exponent form (HA4 D10) -/

/-- **A limit in probability is not below a level undershot only with probability `→ 0`**
(HA4 D10; 2D `exponentFromProb`).  If `X_ε → λ` in probability as `ε ↓ 0` and
`P*(X_ε < c) → 0`, then `c ≤ λ`. -/
theorem ge_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ} {lam c : ℝ}
    (hX : TendstoInMeasure P X (𝓝[>] 0) (fun _ => lam))
    (hc : Tendsto (fun ε => P {ω | X ε ω < c}) (𝓝[>] 0) (𝓝 0)) : c ≤ lam := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨θ, hθ_def⟩ : ∃ θ, θ = (c - lam) / 2 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by
    rw [hθ_def]
    linarith
  have h1 := hX (ENNReal.ofReal θ) (ENNReal.ofReal_pos.2 hθ0)
  have hsub : ∀ ε, {ω | c ≤ X ε ω} ⊆ {ω | ENNReal.ofReal θ ≤ edist (X ε ω) lam} := by
    intro ε ω hω
    have hω' : c ≤ X ε ω := hω
    show ENNReal.ofReal θ ≤ edist (X ε ω) lam
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h2 : Tendsto (fun ε => P {ω | c ≤ X ε ω}) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
      fun ε => measure_mono (hsub ε)
  have hsum := hc.add h2
  rw [add_zero] at hsum
  have hge : ∀ ε, (1 : ENNReal) ≤ P {ω | X ε ω < c} + P {ω | c ≤ X ε ω} := by
    intro ε
    calc (1 : ENNReal) = P univ := measure_univ.symm
      _ ≤ P ({ω | X ε ω < c} ∪ {ω | c ≤ X ε ω}) := by
          refine measure_mono fun ω _ => ?_
          rcases lt_or_ge (X ε ω) c with h | h
          · exact Or.inl h
          · exact Or.inr h
      _ ≤ _ := measure_union_le _ _
  have := ge_of_tendsto' hsum hge
  simp at this

/-- **The exponent form** (HA4 D10, `LowerBoundOfExponent`; the paper's (5.29) when the exponent
exists): for every admissible kernel and every `η > 0`, for all sufficiently small `ζ > 0`, every
LFPP exponent `λ` (1.3) of every white-noise model satisfies `λ ≥ (κ_d - η) ζ^{4/3}`. -/
def LowerBoundOfExponent (d : ℕ) : Prop :=
  ∀ κ : Rd d → ℝ, IsLFPPKernel κ → ∀ η > 0, ∀ᶠ ζ in 𝓝[>] 0,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      ∀ lam : ℝ, IsLFPPExponent H P ζ lam → (kappa d - η) * ζ ^ (4 / 3 : ℝ) ≤ lam

/-- The exponent form for one kernel, from the rate form. -/
theorem lowerBoundOfExponent_kernel (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hI : IterD d κ) :
    ∀ η > 0, ∀ᶠ ζ in 𝓝[>] 0,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
      ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
        ∀ lam : ℝ, IsLFPPExponent H P ζ lam → (kappa d - η) * ζ ^ (4 / 3 : ℝ) ≤ lam := by
  intro η hη
  filter_upwards [lowerComparison_kernel hd hκ hI η hη] with ζ hζ
  intro Ω _ P W hW H hH lam hlam
  have := hW.isProbabilityMeasure
  exact ge_of_tendstoInMeasure hlam (hζ Ω P W hW H hH)

/-- **The exponent form** (`LowerBoundOfExponent`) from the iteration `IterD`. -/
theorem lowerBoundOfExponent_of_iterD (hd : 2 ≤ d)
    (hI : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → IterD d κ) : LowerBoundOfExponent d :=
  fun _ hκ => lowerBoundOfExponent_kernel hd hκ (hI _ hκ)

/-- **The exponent form** (`LowerBoundOfExponent`), conditional only on Lemma 5.3. -/
theorem lowerBoundOfExponent_of_lemma53 (hd : 2 ≤ d)
    (h53 : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → Lemma53Holds d κ) : LowerBoundOfExponent d :=
  lowerBoundOfExponent_of_iterD hd fun _ hκ => iterD_of_lemma53 (by omega) hκ (h53 _ hκ)

/-- The `lim inf` form for one kernel, from the iteration `IterD`. -/
theorem lowerComparison_liminf_of_iterD (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hI : IterD d κ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) {H : ℝ → Rd d → Ω → ℝ}
    (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) {lam : ℝ → ℝ}
    (hlam : ∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, IsLFPPExponent H P ζ (lam ζ)) {η : ℝ}
    (hη : 0 < η) : ∀ᶠ ζ in 𝓝[>] 0, kappa d - η ≤ lam ζ / ζ ^ (4 / 3 : ℝ) := by
  obtain ⟨ζ₀, hζ₀, hlam⟩ := hlam
  filter_upwards [lowerBoundOfExponent_kernel hd hκ hI η hη, Ioo_mem_nhdsGT hζ₀] with ζ h1 h2
  have hζ43 : 0 < ζ ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos h2.1 _
  rw [le_div_iff₀ hζ43]
  exact h1 Ω P W hW H hH (lam ζ) (hlam ζ h2)

/-- **The paper's (5.29) in `lim inf` form**, for one kernel: for every exponent function `λ(ζ)`
(an LFPP exponent for all small `ζ`) and every `η > 0`, eventually `λ(ζ)/ζ^{4/3} ≥ κ_d - η` as
`ζ ↓ 0`; conditional only on Lemma 5.3 for this kernel. -/
theorem lowerComparison_liminf (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (h53 : Lemma53Holds d κ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) {H : ℝ → Rd d → Ω → ℝ}
    (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) {lam : ℝ → ℝ}
    (hlam : ∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, IsLFPPExponent H P ζ (lam ζ)) {η : ℝ}
    (hη : 0 < η) : ∀ᶠ ζ in 𝓝[>] 0, kappa d - η ≤ lam ζ / ζ ^ (4 / 3 : ℝ) :=
  lowerComparison_liminf_of_iterD hd hκ (iterD_of_lemma53 (by omega) hκ h53) hW hH hlam hη

end HigherDimLFPP.Lower
