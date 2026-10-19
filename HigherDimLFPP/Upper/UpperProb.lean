import HigherDimLFPP.Upper.ChainSimultaneity
import HigherDimLFPP.Field.Oscillation
import HigherDimLFPP.Var.Theorem11

/-!
# The fixed-`δ` probability bound and the parameter choice: HA3 D8, D9

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.4, (4.20)–(4.24) (before "Let `N → ∞` and
use (1.3)", which is the only place where the existence of `λ_d` enters, HA3 F10), as corrected by
the planning audit HA3 (`planning/audits/HA3-section-4.md`), Details D8 and D9.

* **D8** (`upperProb_tendsto`): for fixed `n ≥ 3`, `δ > 0`, `t > 0` and a family of exceptional
  events as produced by `chainUnionBound` (with `T₀ = (M_ε/t)(log(1 + Z) + 2)`),
  `P*[log D^{δ^{3/2}}_{ε,d}/log ε > δ² Ψ / log(2K/3) + θ] → 0` as `ε ↓ 0` for every `θ > 0`,
  where `Ψ = (log(1 + Z) + 2)/t`.  The three bad events are `𝒜_ε` (`P ≤ e^{-2M_ε}`), a large
  oscillation (`osc_tendsto`) and a large root average (`segAvg_cutoff_bounded`); outer measures
  throughout (HA3 F8).
* **D9** (`exists_Psi_le`, `exists_Nb_wBad_le_one`): with `τ = u = n^{-1/4}` and `t = n^{1/4}`
  (so `tτ = 1`), `(π²/8) C_V t² √(k+1) ≤ (k+1)/2 + C₆ n` bounds `log Z_g` by
  `(2d+1) n log 2 + C₆ n + t(b*_n + 1) + O_d(1)`; `Z_b ≤ 1` for small `δ`; hence
  `Ψ ≤ α_n A_{n,d} + C n^{3/4}` with `C = C(d, κ, C_*)` independent of `n`.

2D source: `LQGDimension/LFPP/UpperAssembly.lean` (`prob_tendsto`) and
`LQGDimension/LFPP/ZLimit.lean`, `UpperAssemblyAux2.lean` (real analysis).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

/-! ## D8: the fixed-`δ` probability bound -/

section D8

variable {d : ℕ} [NeZero d] {κ : Rd d → ℝ}

theorem log_two_mul_div_three_pos {n : ℕ} (hn : 3 ≤ n) : 0 < Real.log (2 * (2 : ℝ) ^ n / 3) := by
  have h8 : (8 : ℝ) ≤ 2 ^ n := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  exact Real.log_pos (by linarith)

/-- `log(2K/3) ≥ (n - 1) log 2`, `K = 2ⁿ`. -/
theorem sub_one_mul_log_two_le {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) - 1) * Real.log 2 ≤ Real.log (2 * (2 : ℝ) ^ n / 3) := by
  have h1 : ((n : ℝ) - 1) * Real.log 2 = Real.log ((2 : ℝ) ^ (n - 1)) := by
    rw [Real.log_pow, Nat.cast_sub hn, Nat.cast_one]
  rw [h1]
  refine Real.log_le_log (by positivity) ?_
  have e : (2 : ℝ) ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [e]
  have : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  linarith

/-- `M_ε ≤ log(1/ε)/log(2K/3) + 1` and `M_ε ≥ log(1/ε)/log(2K/3)`. -/
theorem Mchain_bounds {n : ℕ} (hn : 3 ≤ n) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    Real.log (1 / ε) / Real.log (2 * (2 : ℝ) ^ n / 3) ≤ (Mchain n ε : ℝ) ∧
      (Mchain n ε : ℝ) ≤ Real.log (1 / ε) / Real.log (2 * (2 : ℝ) ^ n / 3) + 1 := by
  have hL : 0 ≤ Real.log (1 / ε) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos hε.1.le hε.2.le)
  have hx : 0 ≤ Real.log (1 / ε) / Real.log (2 * (2 : ℝ) ^ n / 3) :=
    div_nonneg hL (log_two_mul_div_three_pos hn).le
  unfold Mchain
  push_cast
  exact ⟨(Nat.lt_floor_add_one _).le, by linarith [Nat.floor_le hx]⟩

/-- **HA3 D8, the fixed-`δ` probability bound** (existence-free form of (4.24); 2D
`prob_tendsto`).  Let `n ≥ 3`, `δ > 0`, `t > 0`, `Z ≥ 0`, and suppose that for every cutoff
`ε ∈ (0,1)` there is an exceptional event of outer probability at most `e^{-2M_ε}` off which
`log D^ζ_{ε,d} ≥ ζ H_root - ζ ω(5ε) - δ² T₀` with `T₀ = (M_ε/t)(log(1 + Z) + 2)`, `ζ = δ^{3/2}`
(as provided by `chainUnionBound`).  Then for every `θ > 0`,
`P*[log D^ζ_{ε,d}/log ε > δ² Ψ/log(2K/3) + θ] → 0` as `ε ↓ 0`, `Ψ = (log(1 + Z) + 2)/t`. -/
theorem upperProb_tendsto (hκ : IsLFPPKernel κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) {H : ℝ → Rd d → Ω → ℝ}
    (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) {n : ℕ} (hn : 3 ≤ n)
    {δ t Z : ℝ} (hδ : 0 < δ) (ht : 0 < t) (hZ : 0 ≤ Z)
    (hexc : ∀ ε ∈ Ioo (0 : ℝ) 1, ∃ 𝒜 : Set Ω,
      P 𝒜 ≤ ENNReal.ofReal (Real.exp (-2 * (Mchain n ε : ℝ))) ∧ ∀ ω ∉ 𝒜,
        δ ^ (3 / 2 : ℝ) * segAvg (fun z => H ε z ω) 0 (e₁ d) -
            δ ^ (3 / 2 : ℝ) * osc (fun z => H ε z ω) (5 * ε) - δ ^ 2 * Tzero (Mchain n ε) t Z ≤
          Real.log (lfppDistance d (δ ^ (3 / 2 : ℝ)) (fun z => H ε z ω)))
    {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun ε => P {ω | δ ^ 2 * ((Real.log (1 + Z) + 2) / t) /
        Real.log (2 * (2 : ℝ) ^ n / 3) + θ <
          Real.log (lfppDistance d (δ ^ (3 / 2 : ℝ)) (fun z => H ε z ω)) / Real.log ε})
      (𝓝[>] 0) (𝓝 0) := by
  set ζ := δ ^ (3 / 2 : ℝ) with hζ
  have hξ0 : 0 < ζ := Real.rpow_pos_of_pos hδ _
  set Ψ := (Real.log (1 + Z) + 2) / t with hΨ
  have hΨ0 : 0 ≤ Ψ := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + Z)
    positivity
  set L₀ := Real.log (2 * (2 : ℝ) ^ n / 3) with hL₀
  have hL₀0 : 0 < L₀ := log_two_mul_div_three_pos hn
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨ρ', -, hρ'pos, hρ'e⟩ := ENNReal.lt_iff_exists_real_btwn.1 he
  have hρ' : 0 < ρ' := ENNReal.ofReal_pos.1 hρ'pos
  have hρ : 0 < ρ' / 3 := by positivity
  obtain ⟨K', hK'⟩ := segAvg_cutoff_bounded hκ hW hH hρ
  have hκ' : 0 < θ / (2 * ζ) := by positivity
  have hosc' := (ENNReal.tendsto_nhds_zero.1 (osc_tendsto hκ hW hH hκ')) (ENNReal.ofReal (ρ' / 3))
    (ENNReal.ofReal_pos.2 hρ)
  have hlog : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      max (2 * (ζ * max K' 0 + δ ^ 2 * Ψ) / θ) (L₀ * Real.log (3 / ρ') / 2) ≤
        Real.log (1 / ε) := by
    have := (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).eventually
      (eventually_ge_atTop (max (2 * (ζ * max K' 0 + δ ^ 2 * Ψ) / θ)
        (L₀ * Real.log (3 / ρ') / 2)))
    filter_upwards [this] with ε hε
    rw [one_div, Real.log_inv]
    exact hε
  filter_upwards [hosc', hlog, Ioo_mem_nhdsGT one_pos] with ε hεosc hεlog hε
  obtain ⟨𝒜, h𝒜, hgood⟩ := hexc ε hε
  obtain ⟨hM1, hM2⟩ := Mchain_bounds hn hε
  have hℓ : 0 < Real.log (1 / ε) := by
    apply Real.log_pos
    rw [one_div]
    exact one_lt_inv_iff₀.2 ⟨hε.1, hε.2⟩
  have hlogε : Real.log ε = -Real.log (1 / ε) := by rw [one_div, Real.log_inv, neg_neg]
  -- the three bad events
  have hsub : {ω | δ ^ 2 * Ψ / L₀ + θ <
        Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε} ⊆
      (𝒜 ∪ {ω | θ / (2 * ζ) * Real.log (1 / ε) < osc (fun z => H ε z ω) (5 * ε)}) ∪
        {ω | K' < |segAvg (fun z => H ε z ω) 0 (e₁ d)|} := by
    intro ω hω
    by_contra hnot
    have h1 : ω ∉ 𝒜 := fun h => hnot (Or.inl (Or.inl h))
    have h2 : osc (fun z => H ε z ω) (5 * ε) ≤ θ / (2 * ζ) * Real.log (1 / ε) :=
      not_lt.1 fun hh => hnot (Or.inl (Or.inr hh))
    have h3 : |segAvg (fun z => H ε z ω) 0 (e₁ d)| ≤ K' := not_lt.1 fun hh => hnot (Or.inr hh)
    have hdet := hgood ω h1
    have hHK := (abs_le.1 (h3.trans (le_max_left K' 0))).1
    have ha : ζ * osc (fun z => H ε z ω) (5 * ε) ≤ θ / 2 * Real.log (1 / ε) := by
      calc ζ * osc (fun z => H ε z ω) (5 * ε) ≤ ζ * (θ / (2 * ζ) * Real.log (1 / ε)) :=
            mul_le_mul_of_nonneg_left h2 hξ0.le
        _ = θ / 2 * Real.log (1 / ε) := by field_simp
    have hb : -(ζ * segAvg (fun z => H ε z ω) 0 (e₁ d)) ≤ ζ * max K' 0 := by
      have := mul_le_mul_of_nonneg_left hHK hξ0.le
      linarith
    have hT : δ ^ 2 * Tzero (Mchain n ε) t Z ≤ δ ^ 2 * Ψ * (Real.log (1 / ε) / L₀) + δ ^ 2 * Ψ := by
      have e : Tzero (Mchain n ε) t Z = (Mchain n ε : ℝ) * Ψ := by
        rw [Tzero, hΨ]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hM2 (mul_nonneg (sq_nonneg δ) hΨ0)
      nlinarith
    have hc : ζ * max K' 0 + δ ^ 2 * Ψ ≤ θ / 2 * Real.log (1 / ε) := by
      have h4 := (div_le_iff₀ hθ).1 ((le_max_left _ _).trans hεlog)
      linarith
    simp only [mem_ofPred_eq] at hω
    rw [hlogε, lt_div_iff_of_neg (by linarith)] at hω
    have e2 : (δ ^ 2 * Ψ / L₀ + θ) * -Real.log (1 / ε) =
        -(δ ^ 2 * Ψ * (Real.log (1 / ε) / L₀)) - θ * Real.log (1 / ε) := by ring
    rw [e2] at hω
    linarith
  -- probability bounds
  have hP1 : P 𝒜 ≤ ENNReal.ofReal (ρ' / 3) := by
    refine h𝒜.trans (ENNReal.ofReal_le_ofReal ?_)
    have hT : Real.log (3 / ρ') ≤ 2 * (Mchain n ε : ℝ) := by
      have h5 : L₀ * Real.log (3 / ρ') / 2 ≤ Real.log (1 / ε) := (le_max_right _ _).trans hεlog
      have h6 : Real.log (1 / ε) / L₀ ≤ (Mchain n ε : ℝ) := hM1
      rw [div_le_iff₀ hL₀0] at h6
      nlinarith
    have hexp : Real.exp (-2 * (Mchain n ε : ℝ)) ≤ Real.exp (-Real.log (3 / ρ')) :=
      Real.exp_le_exp.2 (by linarith)
    have hexp2 : Real.exp (-Real.log (3 / ρ')) = ρ' / 3 := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    linarith
  calc P {ω | δ ^ 2 * Ψ / L₀ + θ < Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add_left (measure_union_le _ _) _
    _ ≤ ENNReal.ofReal (ρ' / 3) + ENNReal.ofReal (ρ' / 3) + ENNReal.ofReal (ρ' / 3) :=
        add_le_add (add_le_add hP1 hεosc) (hK' ε hε)
    _ = ENNReal.ofReal ρ' := by
        rw [← ENNReal.ofReal_add hρ.le hρ.le, ← ENNReal.ofReal_add (by positivity) hρ.le]
        congr 1
        ring
    _ ≤ e := hρ'e.le

/-- **HA3 D8, conditional on the good-record mean bound** (the fixed-`δ` probability bound in
HA3's form): with the constants of `chainUnionBound`, for every model, `n ≥ 3`, `τ, u ∈ (0,1)`
there is `δ₀ > 0` such that for all `δ ∈ (0, δ₀)`, `t > 0` and `θ > 0`,
`P*[log D^{δ^{3/2}}_{ε,d}/log ε > δ² (log(1 + Z_g + Z_b) + 2)/(t (n-1) log 2) + θ] → 0` as
`ε ↓ 0`. -/
theorem fixedDelta_prob_tendsto (hκ : IsLFPPKernel κ) (hG : GoodRecordMeanBound d κ) :
    ∃ Cstar CV : ℝ, 0 ≤ Cstar ∧ 0 ≤ CV ∧ ∀ n : ℕ, 3 ≤ n → ∃ Cbad CV' : ℝ, 0 ≤ Cbad ∧ 0 ≤ CV' ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
      ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      ∀ τ ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ t > 0,
      ∀ θ > 0,
        Tendsto (fun ε => P {ω | δ ^ 2 * (Real.log (1 + Zsum d n δ t τ (bStar d n τ u Cstar) Cbad
            CV CV') + 2) / (t * (((n : ℝ) - 1) * Real.log 2)) + θ <
          Real.log (lfppDistance d (δ ^ (3 / 2 : ℝ)) (fun z => H ε z ω)) / Real.log ε})
          (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Cstar, CV, hCstar, hCV, hmain⟩ := chainUnionBound hκ hG
  refine ⟨Cstar, CV, hCstar, hCV, fun n hn => ?_⟩
  obtain ⟨Cbad, CV', hCbad, hCV', hn'⟩ := hmain n hn
  refine ⟨Cbad, CV', hCbad, hCV', fun Ω _ P W hW H hH τ hτ u hu => ?_⟩
  obtain ⟨δ₀, hδ₀, hexc⟩ := hn' Ω P W hW H hH τ hτ u hu
  refine ⟨δ₀, hδ₀, fun δ hδ t ht θ hθ => ?_⟩
  set Z := Zsum d n δ t τ (bStar d n τ u Cstar) Cbad CV CV' with hZdef
  have hZ0 : 0 ≤ Z :=
    add_nonneg (tsum_nonneg fun k => mul_nonneg (Ng_nonneg d n k) (wGood_pos _ _ _ _ _).le)
      (mul_nonneg (Nb_nonneg d n hδ.1) (wBad_pos _ _ _ _ _).le)
  have h8 := upperProb_tendsto hκ hW hH hn hδ.1 ht hZ0 (fun ε hε => by
    obtain ⟨𝒜, h𝒜, hω⟩ := hexc δ hδ t ht ε hε
    exact ⟨𝒜, h𝒜, fun ω h => (hω ω h).2⟩) hθ
  have hn1 : 1 ≤ n := by omega
  have hn2 : (0 : ℝ) < ((n : ℝ) - 1) * Real.log 2 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact mul_pos (by linarith) (Real.log_pos one_lt_two)
  have hnum : 0 ≤ δ ^ 2 * ((Real.log (1 + Z) + 2) / t) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + Z)
    positivity
  have hrate : δ ^ 2 * ((Real.log (1 + Z) + 2) / t) / Real.log (2 * (2 : ℝ) ^ n / 3) ≤
      δ ^ 2 * (Real.log (1 + Z) + 2) / (t * (((n : ℝ) - 1) * Real.log 2)) := by
    have e : δ ^ 2 * (Real.log (1 + Z) + 2) / (t * (((n : ℝ) - 1) * Real.log 2)) =
        δ ^ 2 * ((Real.log (1 + Z) + 2) / t) / (((n : ℝ) - 1) * Real.log 2) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left hnum hn2 (sub_one_mul_log_two_le hn1)
  refine ENNReal.tendsto_nhds_zero.2 fun e he =>
    (ENNReal.tendsto_nhds_zero.1 h8 e he).mono fun ε hε => (measure_mono fun ω hω => ?_).trans hε
  simp only [mem_ofPred_eq] at hω ⊢
  linarith

end D8

/-! ## D9: the parameter choice and the `O_d(n^{3/4})` error -/

section D9

/-- `α_n = (1 + n^{-1/4})^{2/3} (1 - n^{-1/4})^{-1/3}` (HA3 §5). -/
def alphaN (n : ℕ) : ℝ :=
  (1 + (n : ℝ) ^ (-(1 / 4 : ℝ))) ^ (2 / 3 : ℝ) * (1 - (n : ℝ) ^ (-(1 / 4 : ℝ))) ^ (-(1 / 3 : ℝ))

theorem rpow_neg_quarter_lt_one {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) ^ (-(1 / 4 : ℝ)) < 1 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  exact Real.rpow_lt_one_of_one_lt_of_neg hn1 (by norm_num)

theorem rpow_neg_quarter_pos {n : ℕ} (hn : 1 ≤ n) : 0 < (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
  Real.rpow_pos_of_pos (Nat.cast_pos.2 (by omega)) _

theorem alphaN_pos {n : ℕ} (hn : 2 ≤ n) : 0 < alphaN n := by
  have h1 := rpow_neg_quarter_lt_one hn
  have h0 := rpow_neg_quarter_pos (n := n) (by omega)
  unfold alphaN
  have : 0 < 1 - (n : ℝ) ^ (-(1 / 4 : ℝ)) := by linarith
  positivity

/-- `t τ = n^{1/4} n^{-1/4} = 1`. -/
theorem rpow_quarter_mul_rpow_neg_quarter {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) = 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_add hn0]
  norm_num

/-- `b*_n` at `τ = u = n^{-1/4}`: `b*_n = α_n A_{n,d} + C_* n^{1/8} + 1`. -/
theorem bStar_quarter (d n : ℕ) (Cstar : ℝ) :
    bStar d n ((n : ℝ) ^ (-(1 / 4 : ℝ))) ((n : ℝ) ^ (-(1 / 4 : ℝ))) Cstar =
      alphaN n * (A n d).toReal + Cstar * (n : ℝ) ^ (1 / 8 : ℝ) + 1 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold bStar alphaN
  rw [← Real.rpow_mul hn0]
  norm_num

/-- `Σ_k (k+1)^d e^{-k/2}`, a constant depending only on `d`. -/
def sumPolyExp (d : ℕ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) ^ d * Real.exp (-(1 / 2 : ℝ)) ^ k

theorem summable_polyExp (d : ℕ) :
    Summable fun k : ℕ => ((k : ℝ) + 1) ^ d * Real.exp (-(1 / 2 : ℝ)) ^ k :=
  summable_succ_pow_mul_geometric d (Real.exp_pos _) (Real.exp_lt_one_iff.2 (by norm_num))

theorem one_le_sumPolyExp (d : ℕ) : 1 ≤ sumPolyExp d := by
  have h := (summable_polyExp d).le_tsum 0 fun j _ => by positivity
  unfold sumPolyExp
  refine le_trans (le_of_eq ?_) h
  simp

/-- `N_g(k) = 3 c_d^{2d} K^{2d+1} (k+1)^d`, `K = 2ⁿ`. -/
theorem Ng_eq (d n k : ℕ) :
    Ng d n k = 3 * cGood d ^ (2 * d) * ((2 : ℝ) ^ n) ^ (2 * d + 1) * ((k : ℝ) + 1) ^ d := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  rw [Ng, mul_pow, mul_pow, pow_mul (Real.sqrt ((k : ℝ) + 1)) 2 d, Real.sq_sqrt hk, pow_succ]
  ring

/-- With `tτ = 1`: `w_g(k) ≤ exp(t(b+1) + y²/2 + 1/2) e^{-k/2}`, `y = (π²/8) t² C_V`
(from `y√(k+1) ≤ (k+1)/2 + y²/2`). -/
theorem wGood_le_of_mul_eq_one {t τ bs CV : ℝ} (htτ : t * τ = 1) (k : ℕ) :
    wGood t τ bs CV k ≤ Real.exp (t * (bs + 1) + (Real.pi ^ 2 / 8 * t ^ 2 * CV) ^ 2 / 2 + 1 / 2) *
      Real.exp (-(1 / 2 : ℝ)) ^ k := by
  rw [wGood, ← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  set y := Real.pi ^ 2 / 8 * t ^ 2 * CV with hy
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hs := Real.sq_sqrt hk
  have h := sq_nonneg (y - Real.sqrt ((k : ℝ) + 1))
  rw [sub_sq] at h
  have e1 : Real.pi ^ 2 / 8 * t ^ 2 * (CV * Real.sqrt ((k : ℝ) + 1)) =
      y * Real.sqrt ((k : ℝ) + 1) := by rw [hy]; ring
  have e2 : t * (bs + 1 - τ * k) = t * (bs + 1) - (t * τ) * k := by ring
  rw [e1, e2, htτ]
  linarith

/-- `Z_g ≤ G S` with `G = 3 c_d^{2d} K^{2d+1} exp(t(b+1) + y²/2 + 1/2)`, `S = Σ (k+1)^d e^{-k/2}`. -/
theorem tsum_Ng_wGood_le (d n : ℕ) {t τ bs CV : ℝ} (ht : 0 < t) (hτ : 0 < τ) (htτ : t * τ = 1) :
    ∑' k, Ng d n k * wGood t τ bs CV k ≤
      3 * cGood d ^ (2 * d) * ((2 : ℝ) ^ n) ^ (2 * d + 1) *
        Real.exp (t * (bs + 1) + (Real.pi ^ 2 / 8 * t ^ 2 * CV) ^ 2 / 2 + 1 / 2) * sumPolyExp d := by
  rw [sumPolyExp, ← tsum_mul_left]
  have hc := cGood_pos d
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_Ng_wGood d n ht hτ bs CV)
    ((summable_polyExp d).mul_left _)
  rw [Ng_eq]
  have hpos : 0 ≤ 3 * cGood d ^ (2 * d) * ((2 : ℝ) ^ n) ^ (2 * d + 1) * ((k : ℝ) + 1) ^ d := by
    positivity
  calc 3 * cGood d ^ (2 * d) * ((2 : ℝ) ^ n) ^ (2 * d + 1) * ((k : ℝ) + 1) ^ d * wGood t τ bs CV k
      ≤ 3 * cGood d ^ (2 * d) * ((2 : ℝ) ^ n) ^ (2 * d + 1) * ((k : ℝ) + 1) ^ d *
          (Real.exp (t * (bs + 1) + (Real.pi ^ 2 / 8 * t ^ 2 * CV) ^ 2 / 2 + 1 / 2) *
            Real.exp (-(1 / 2 : ℝ)) ^ k) :=
        mul_le_mul_of_nonneg_left (wGood_le_of_mul_eq_one htτ k) hpos
    _ = _ := by ring

/-- `log(1 + Z_g + Z_b) ≤ log 3 + log G + log S` when `Z_b ≤ 1` and `1 ≤ G S`. -/
theorem log_one_add_Zsum_le {d n : ℕ} {δ t τ bs Cbad CV CV' G : ℝ} (hδ : 0 < δ) (hG : 0 < G)
    (hZg : ∑' k, Ng d n k * wGood t τ bs CV k ≤ G * sumPolyExp d)
    (hZb : Nb d n δ * wBad n t δ Cbad CV' ≤ 1) (hGS : 1 ≤ G * sumPolyExp d) :
    Real.log (1 + Zsum d n δ t τ bs Cbad CV CV') ≤
      Real.log 3 + Real.log G + Real.log (sumPolyExp d) := by
  have hS : 0 < sumPolyExp d := lt_of_lt_of_le one_pos (one_le_sumPolyExp d)
  have hZb0 : 0 ≤ Nb d n δ * wBad n t δ Cbad CV' :=
    mul_nonneg (Nb_nonneg d n hδ) (wBad_pos _ _ _ _ _).le
  have hZg0 : 0 ≤ ∑' k, Ng d n k * wGood t τ bs CV k :=
    tsum_nonneg fun k => mul_nonneg (Ng_nonneg d n k) (wGood_pos _ _ _ _ _).le
  rw [← Real.log_mul (by norm_num) hG.ne', ← Real.log_mul (by positivity) hS.ne']
  refine Real.log_le_log (by unfold Zsum; linarith) ?_
  unfold Zsum
  have e : 3 * G * sumPolyExp d = 3 * (G * sumPolyExp d) := by ring
  rw [e]
  linarith

/-- **HA3 D9**: with `τ = u = n^{-1/4}` and `t = n^{1/4}`, for every `n ≥ 3`, `δ > 0` and
constants with `Z_b ≤ 1`, `Ψ = (log(1 + Z_g + Z_b) + 2)/t ≤ α_n A_{n,d} + C n^{3/4}`, where
`C = C(d, C_V, C_*)` does not depend on `n`. -/
theorem exists_Psi_le (d : ℕ) {CV Cstar : ℝ} (hCstar : 0 ≤ Cstar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 3 ≤ n → ∀ {δ Cbad CV' : ℝ}, 0 < δ →
      Nb d n δ * wBad n ((n : ℝ) ^ (1 / 4 : ℝ)) δ Cbad CV' ≤ 1 →
      (Real.log (1 + Zsum d n δ ((n : ℝ) ^ (1 / 4 : ℝ)) ((n : ℝ) ^ (-(1 / 4 : ℝ)))
          (bStar d n ((n : ℝ) ^ (-(1 / 4 : ℝ))) ((n : ℝ) ^ (-(1 / 4 : ℝ))) Cstar) Cbad CV CV') + 2) /
          (n : ℝ) ^ (1 / 4 : ℝ) ≤
        alphaN n * (A n d).toReal + C * (n : ℝ) ^ (3 / 4 : ℝ) := by
  set c := cGood d with hc
  have hc1 : 1 ≤ c := by
    rw [hc, cGood]
    have := Real.sqrt_nonneg (d : ℝ)
    linarith
  set S := sumPolyExp d with hS
  have hS1 : 1 ≤ S := one_le_sumPolyExp d
  set Y₀ : ℝ := (Real.pi ^ 2 / 8) ^ 2 * CV ^ 2 / 2 with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  set C₈ : ℝ := 2 * Real.log 3 + 2 * d * Real.log c + Real.log S + 5 / 2 with hC₈
  have hC₈0 : 0 ≤ C₈ := by
    have h1 := Real.log_nonneg hc1
    have h2 := Real.log_nonneg hS1
    have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  set C₉ : ℝ := (2 * d + 1) * Real.log 2 + Y₀ with hC₉
  have hC₉0 : 0 ≤ C₉ := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  refine ⟨C₈ + C₉ + Cstar + 2, by positivity, fun n hn {δ Cbad CV'} hδ hZb => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set t := (n : ℝ) ^ (1 / 4 : ℝ) with ht
  set τ := (n : ℝ) ^ (-(1 / 4 : ℝ)) with hτ
  have ht0 : 0 < t := Real.rpow_pos_of_pos hn0 _
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hn0 _
  have htτ : t * τ = 1 := rpow_quarter_mul_rpow_neg_quarter hn1
  have ht4 : t ^ 4 = n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hA0 : 0 ≤ (A n d).toReal := Var.A_toReal_nonneg n d
  have hα0 : 0 < alphaN n := alphaN_pos (by omega)
  set bs := bStar d n τ τ Cstar with hbs
  have hbs_eq : bs = alphaN n * (A n d).toReal + Cstar * (n : ℝ) ^ (1 / 8 : ℝ) + 1 :=
    bStar_quarter d n Cstar
  have hbs0 : 0 ≤ bs := by
    rw [hbs_eq]
    have := Real.rpow_nonneg hn0.le (1 / 8 : ℝ)
    positivity
  set K : ℝ := (2 : ℝ) ^ n with hK
  have hK1 : 1 ≤ K := one_le_pow₀ (by norm_num)
  have hy2 : (Real.pi ^ 2 / 8 * t ^ 2 * CV) ^ 2 / 2 = Y₀ * n := by
    rw [hY₀, ← ht4]; ring
  set G : ℝ := 3 * c ^ (2 * d) * K ^ (2 * d + 1) * Real.exp (t * (bs + 1) + Y₀ * n + 1 / 2)
    with hG
  have hG0 : 0 < G := by positivity
  have hZg : ∑' k, Ng d n k * wGood t τ bs CV k ≤ G * S := by
    have h := tsum_Ng_wGood_le d n (bs := bs) (CV := CV) ht0 hτ0 htτ
    rw [hy2] at h
    exact h
  have hG1 : 1 ≤ G := by
    have h2 : 1 ≤ Real.exp (t * (bs + 1) + Y₀ * n + 1 / 2) := Real.one_le_exp (by positivity)
    have h4 : 1 ≤ c ^ (2 * d) := one_le_pow₀ hc1
    have h5 : 1 ≤ K ^ (2 * d + 1) := one_le_pow₀ hK1
    have h3 : 1 ≤ 3 * c ^ (2 * d) * K ^ (2 * d + 1) := by
      have h6 : 1 ≤ c ^ (2 * d) * K ^ (2 * d + 1) := one_le_mul_of_one_le_of_one_le h4 h5
      have e : 3 * c ^ (2 * d) * K ^ (2 * d + 1) = 3 * (c ^ (2 * d) * K ^ (2 * d + 1)) := by ring
      rw [e]
      linarith
    exact one_le_mul_of_one_le_of_one_le h3 h2
  have hGS1 : 1 ≤ G * S := one_le_mul_of_one_le_of_one_le hG1 hS1
  have hlogZ := log_one_add_Zsum_le hδ hG0 hZg hZb hGS1
  have hlogG : Real.log G = Real.log 3 + 2 * d * Real.log c + (2 * d + 1) * n * Real.log 2 +
      (t * (bs + 1) + Y₀ * n + 1 / 2) := by
    rw [hG, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow, hK, Real.log_pow]
    push_cast
    ring
  rw [hlogG] at hlogZ
  -- `Ψ ≤ b* + 1 + (C₈ + C₉ n) τ`
  have hΨ : (Real.log (1 + Zsum d n δ t τ bs Cbad CV CV') + 2) / t ≤
      bs + 1 + (C₈ + C₉ * n) * τ := by
    rw [div_le_iff₀ ht0]
    have e : (bs + 1 + (C₈ + C₉ * n) * τ) * t = t * (bs + 1) + (C₈ + C₉ * n) * (t * τ) := by
      ring
    rw [e, htτ, hC₈, hC₉]
    linarith
  -- `(C₈ + C₉ n) n^{-1/4} ≤ (C₈ + C₉) n^{3/4}` and `C_* n^{1/8} + 2 ≤ (C_* + 2) n^{3/4}`
  have hτ1 : τ ≤ 1 := (rpow_neg_quarter_lt_one (by omega)).le
  have h34 : 1 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hn1' (by norm_num)
  have hnτ : (n : ℝ) * τ = (n : ℝ) ^ (3 / 4 : ℝ) := by
    have h := Real.rpow_add hn0 1 (-(1 / 4 : ℝ))
    rw [Real.rpow_one] at h
    rw [hτ, ← h]
    norm_num
  have h18 : (n : ℝ) ^ (1 / 8 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1' (by norm_num)
  have hfin : (C₈ + C₉ * n) * τ ≤ (C₈ + C₉) * (n : ℝ) ^ (3 / 4 : ℝ) := by
    have e : (C₈ + C₉ * n) * τ = C₈ * τ + C₉ * ((n : ℝ) * τ) := by ring
    rw [e, hnτ]
    have := mul_le_mul_of_nonneg_left (hτ1.trans h34) hC₈0
    linarith
  have h1 : Cstar * (n : ℝ) ^ (1 / 8 : ℝ) ≤ Cstar * (n : ℝ) ^ (3 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_left h18 hCstar
  have e : (C₈ + C₉ + Cstar + 2) * (n : ℝ) ^ (3 / 4 : ℝ) =
      (C₈ + C₉) * (n : ℝ) ^ (3 / 4 : ℝ) + Cstar * (n : ℝ) ^ (3 / 4 : ℝ) +
        2 * (n : ℝ) ^ (3 / 4 : ℝ) := by ring
  rw [e]
  linarith [hΨ, hbs_eq, hfin, h1, h34]

/-- `Z_b → 0`: for fixed `n` and `t > 0` there is `δ₁ > 0` with `N_b w_b ≤ 1` for all
`δ ∈ (0, δ₁)` (HA3 D9: `log Z_b = O_{n,d}(log(1/δ) + 1/δ) - c₀ t/(Kδ²)`). -/
theorem exists_Nb_wBad_le_one (d n : ℕ) {t : ℝ} (ht : 0 < t) (Cbad : ℝ) {CV' : ℝ}
    (hCV' : 0 ≤ CV') : ∃ δ₁ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₁, Nb d n δ * wBad n t δ Cbad CV' ≤ 1 := by
  set cB := cBad d with hcB
  have hcB0 : 0 < cB := cBad_pos d
  set K : ℝ := (2 : ℝ) ^ n with hK
  have hK0 : 0 < K := by positivity
  set P₀ : ℝ := 3 * cB ^ (4 * d) * K ^ (2 * d) * ((4 * d).factorial : ℝ) * Real.exp (t * Cbad)
    with hP₀
  have hP₀0 : 0 < P₀ := by positivity
  set B₀ : ℝ := 1 + Real.pi ^ 2 / 8 * t ^ 2 * CV' with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  set A₀ : ℝ := t * a0 n with hA₀
  have hA₀0 : 0 < A₀ := mul_pos ht (a0_pos n)
  set x₀ : ℝ := max 1 ((B₀ + |Real.log P₀|) / A₀) with hx₀
  have hx₀1 : 1 ≤ x₀ := le_max_left _ _
  refine ⟨1 / x₀, by positivity, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  set x := 1 / δ with hxdef
  have hx0 : 0 < x := by positivity
  have hxx₀ : x₀ < x := by
    rw [hxdef, lt_div_iff₀ hδ0]
    have := hδ.2
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hx1 : 1 ≤ x := hx₀1.trans hxx₀.le
  -- `N_b = 3 c^{4d} K^{2d} x^{4d}` and `x^{4d} ≤ (4d)! e^x`
  have hNb : Nb d n δ = 3 * cB ^ (4 * d) * K ^ (2 * d) * x ^ (4 * d) := by
    rw [Nb, hxdef, hcB, hK]
    field_simp
    ring
  have hpow : x ^ (4 * d) ≤ ((4 * d).factorial : ℝ) * Real.exp x := by
    have h := Real.pow_div_factorial_le_exp x hx0.le (4 * d)
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have hw : wBad n t δ Cbad CV' = Real.exp (t * Cbad + Real.pi ^ 2 / 8 * t ^ 2 * CV' * x -
      A₀ * x ^ 2) := by
    rw [wBad, hxdef, hA₀]
    congr 1
    field_simp
    ring
  have hquad : B₀ * x - A₀ * x ^ 2 ≤ -Real.log P₀ := by
    have h1 : (B₀ + |Real.log P₀|) / A₀ ≤ x := (le_max_right _ _).trans hxx₀.le
    rw [div_le_iff₀ hA₀0] at h1
    have h2 : (B₀ + |Real.log P₀|) * x ≤ A₀ * x ^ 2 := by nlinarith
    have h3 : -Real.log P₀ ≥ -|Real.log P₀| := neg_le_neg (le_abs_self _)
    nlinarith [abs_nonneg (Real.log P₀)]
  rw [hNb, hw]
  calc 3 * cB ^ (4 * d) * K ^ (2 * d) * x ^ (4 * d) *
        Real.exp (t * Cbad + Real.pi ^ 2 / 8 * t ^ 2 * CV' * x - A₀ * x ^ 2)
      ≤ 3 * cB ^ (4 * d) * K ^ (2 * d) * (((4 * d).factorial : ℝ) * Real.exp x) *
          Real.exp (t * Cbad + Real.pi ^ 2 / 8 * t ^ 2 * CV' * x - A₀ * x ^ 2) := by
        gcongr
    _ = P₀ * Real.exp (B₀ * x - A₀ * x ^ 2) := by
        have e : Real.exp x * Real.exp (t * Cbad + Real.pi ^ 2 / 8 * t ^ 2 * CV' * x - A₀ * x ^ 2) =
            Real.exp (t * Cbad) * Real.exp (B₀ * x - A₀ * x ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add, hB₀]
          congr 1
          ring
        rw [hP₀]
        calc 3 * cB ^ (4 * d) * K ^ (2 * d) * (((4 * d).factorial : ℝ) * Real.exp x) *
              Real.exp (t * Cbad + Real.pi ^ 2 / 8 * t ^ 2 * CV' * x - A₀ * x ^ 2)
            = 3 * cB ^ (4 * d) * K ^ (2 * d) * ((4 * d).factorial : ℝ) * (Real.exp x *
              Real.exp (t * Cbad + Real.pi ^ 2 / 8 * t ^ 2 * CV' * x - A₀ * x ^ 2)) := by ring
          _ = _ := by rw [e]; ring
    _ ≤ P₀ * Real.exp (-Real.log P₀) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hquad) hP₀0.le
    _ = 1 := by rw [Real.exp_neg, Real.exp_log hP₀0, mul_inv_cancel₀ hP₀0.ne']

end D9

end HigherDimLFPP.Upper
