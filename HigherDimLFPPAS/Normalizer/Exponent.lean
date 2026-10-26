import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.Basic

/-!
# Consequences of the uniform ratio limit: (2.10) and `𝔞_ε = ε^{1−ξQ+o(1)}` (packet N1; MA1 A7.4–A7.5)

Elementary real analysis replacing the Bingham–Goldie–Teugels theorems cited in Lemma 2.5 of
`source/higher-dimensional-lfpp-almost-sure.pdf` (l. 304–310). For a function `A : ℝ → ℝ` (in the
application `A = aEps κ ξ`) and an exponent `θ` (in the application `θ = ξ Q`) write
`c(ε, r) = r A(ε/r) / (r^θ A(ε))` (the ratio (1.8)). If `c(ε, r) → 1` as `ε ↓ 0` uniformly for `r` in every
compact subinterval of `(0, ∞)` then:

* `n1_window_of_unif` ((2.10)): for every `a > 0`, `sup_{ε ∈ [(n+1)^{−a}, n^{−a}]} |A(ε)/A(n^{−a}) − 1| → 0`;
* `n1_exponent_of_unif`: if moreover `A > 0` near `0`, then `log A(ε) / log ε → 1 − θ`;
* `n1_rpow_bounds_of_unif`: equivalently, for every `η > 0`, `ε^{1−θ+η} ≤ A(ε) ≤ ε^{1−θ−η}` for small `ε`.

The exponent statement goes through the additive form `n1_tendsto_div_of_increments`: a function `φ`
whose increments over `[t, t + s]`, `s ∈ [0, 1]`, are eventually `λ s + O(η)` satisfies `φ(t)/t → λ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLFPPAS.Normalizer

/-- The ratio identity behind (2.10) and the exponent: `A(t/ρ)/A(t) = c(t, ρ) ρ^{θ−1}` for `ρ > 0`,
with `c(t, ρ) = ρ A(t/ρ)/(ρ^θ A(t))` (no positivity of `A` needed: both sides vanish if `A(t) = 0`). -/
theorem n1_ratio_mul_rpow (A : ℝ → ℝ) (θ t : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    A (t / ρ) / A t = ρ * A (t / ρ) / (ρ ^ θ * A t) * ρ ^ (θ - 1) := by
  have hρθ : ρ ^ θ = ρ ^ (θ - 1) * ρ := by
    rw [← Real.rpow_add_one hρ.ne', sub_add_cancel]
  have hpos : 0 < ρ ^ (θ - 1) := Real.rpow_pos_of_pos hρ _
  rw [hρθ]
  by_cases hA : A t = 0
  · simp [hA]
  · field_simp

/-- **Increments determine the growth rate.** If for every `η > 0` there is `T` with
`|φ(t + s) − φ(t) − λ s| ≤ η` for all `t ≥ T` and `s ∈ [0, 1]`, then `φ(t)/t → λ` as `t → ∞`. -/
theorem n1_tendsto_div_of_increments {φ : ℝ → ℝ} {lam : ℝ}
    (hφ : ∀ η : ℝ, 0 < η → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ s ∈ Icc (0 : ℝ) 1,
      |φ (t + s) - φ t - lam * s| ≤ η) :
    Tendsto (fun t => φ t / t) atTop (𝓝 lam) := by
  rw [Metric.tendsto_atTop]
  intro e he
  obtain ⟨T, hT⟩ := hφ (e / 4) (by positivity)
  -- telescoping along integer steps
  have hstep : ∀ k : ℕ, ∀ s ∈ Icc (0 : ℝ) 1,
      |φ (T + k + s) - φ T - lam * (k + s)| ≤ e / 4 * (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro s hs
      have := hT T le_rfl s hs
      simpa only [Nat.cast_zero, add_zero, zero_add, one_mul, mul_one] using this
    | succ k ih =>
      intro s hs
      have h1 := hT (T + (k + 1 : ℕ)) (by
        have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith) s hs
      have h2 := ih 1 ⟨zero_le_one, le_rfl⟩
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast] at h1 ⊢
      have heq : φ (T + ((k : ℝ) + 1) + s) - φ T - lam * ((k : ℝ) + 1 + s) =
          (φ (T + ((k : ℝ) + 1) + s) - φ (T + ((k : ℝ) + 1)) - lam * s) +
          (φ (T + (k : ℝ) + 1) - φ T - lam * ((k : ℝ) + 1)) := by
        rw [show T + ((k : ℝ) + 1) = T + (k : ℝ) + 1 by ring]
        ring
      rw [heq]
      calc |(φ (T + ((k : ℝ) + 1) + s) - φ (T + ((k : ℝ) + 1)) - lam * s) +
            (φ (T + (k : ℝ) + 1) - φ T - lam * ((k : ℝ) + 1))|
          ≤ |φ (T + ((k : ℝ) + 1) + s) - φ (T + ((k : ℝ) + 1)) - lam * s| +
            |φ (T + (k : ℝ) + 1) - φ T - lam * ((k : ℝ) + 1)| := abs_add_le _ _
        _ ≤ e / 4 + e / 4 * ((k : ℝ) + 1) := add_le_add h1 h2
        _ = e / 4 * ((k : ℝ) + 1 + 1) := by ring
  -- the bound `|φ t - lam t| ≤ C + (e/4) (t - T + 1)` for `t ≥ T`
  set C : ℝ := |φ T| + |lam * T| with hC
  have hbound : ∀ t : ℝ, T ≤ t → |φ t - lam * t| ≤ C + e / 4 * (t - T + 1) := by
    intro t ht
    set k : ℕ := ⌊t - T⌋₊ with hk
    have hk1 : (k : ℝ) ≤ t - T := Nat.floor_le (by linarith)
    have hk2 : t - T < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    set s : ℝ := t - T - k with hs
    have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have h := hstep k s hs01
    have ht' : T + (k : ℝ) + s = t := by rw [hs]; ring
    rw [ht'] at h
    have hks : (k : ℝ) + s = t - T := by rw [hs]; ring
    rw [hks] at h
    have heq : φ t - lam * t = (φ t - φ T - lam * (t - T)) + (φ T - lam * T) := by ring
    rw [heq]
    calc |(φ t - φ T - lam * (t - T)) + (φ T - lam * T)|
        ≤ |φ t - φ T - lam * (t - T)| + |φ T - lam * T| := abs_add_le _ _
      _ ≤ e / 4 * ((k : ℝ) + 1) + (|φ T| + |lam * T|) := add_le_add h (abs_sub _ _)
      _ ≤ C + e / 4 * (t - T + 1) := by
          rw [hC]
          have : e / 4 * ((k : ℝ) + 1) ≤ e / 4 * (t - T + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
          linarith
  -- conclusion for large `t`
  refine ⟨max (max T 1) ((4 * (C + e / 4 * (1 - T)) + 1) / e + 1), fun t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht1 : 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htC : (4 * (C + e / 4 * (1 - T)) + 1) / e + 1 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
  rw [Real.dist_eq]
  have hdiv : φ t / t - lam = (φ t - lam * t) / t := by field_simp
  rw [hdiv, abs_div, abs_of_pos htpos, div_lt_iff₀ htpos]
  have hb := hbound t htT
  -- `C + (e/4)(t - T + 1) < e t` for `t` beyond the threshold
  have het : 0 < t * e := mul_pos htpos he
  have hkey : C + e / 4 * (1 - T) < 3 * e / 4 * t := by
    have h1 : (4 * (C + e / 4 * (1 - T)) + 1) / e < t := by linarith
    rw [div_lt_iff₀ he] at h1
    linarith
  linarith

/-- **(2.10) from the uniform ratio limit** (MA1 A7.4). If `c(ε, r) = r A(ε/r)/(r^θ A(ε)) → 1`
uniformly on `[1, 2]` as `ε ↓ 0`, then for every `a > 0`, eventually in `n`, for all
`ε ∈ [(n+1)^{−a}, n^{−a}]`, `|A(ε)/A(n^{−a}) − 1| ≤ η`. -/
theorem n1_window_of_unif {A : ℝ → ℝ} {θ : ℝ}
    (hunif : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc (1 : ℝ) 2,
      |r * A (ε / r) / (r ^ θ * A ε) - 1| ≤ η)
    {a : ℝ} (ha : 0 < a) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      |A ε / A ((n : ℝ) ^ (-a)) - 1| ≤ η := by
  intro η hη
  -- continuity of `x ↦ x^{θ-1}` at `1`
  have hcont : ContinuousAt (fun x : ℝ => x ^ (θ - 1)) 1 :=
    Real.continuousAt_rpow_const 1 (θ - 1) (Or.inl one_ne_zero)
  have hlev : 0 < min (η / 3) 1 := lt_min (by positivity) one_pos
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont _ hlev
  simp only [Real.one_rpow, Real.dist_eq] at hδc
  -- `t_n = n^{-a} → 0⁺`
  have ht0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
    · filter_upwards [eventually_gt_atTop 0] with n hn
      exact Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) _
  -- the endpoint ratio `n^{-a}/(n+1)^{-a} = (1 + 1/n)^a → 1`
  have hend : Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ a) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h2 := (Real.continuousAt_rpow_const 1 a (Or.inl one_ne_zero)).tendsto.comp h1
    simpa only [Function.comp_def, Real.one_rpow] using h2
  have hmin : (1 : ℝ) < 1 + min δ 1 := by
    have := lt_min hδ one_pos
    linarith
  filter_upwards [ht0.eventually (hunif (η / 3) (by positivity)), eventually_gt_atTop 0,
    hend.eventually (gt_mem_nhds hmin)] with n hn hn0 hn1 ε hε
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hεpos : 0 < ε := lt_of_lt_of_le (Real.rpow_pos_of_pos hn1pos _) hε.1
  set t : ℝ := (n : ℝ) ^ (-a) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hnpos _
  set ρ : ℝ := t / ε with hρ
  have hρpos : 0 < ρ := div_pos htpos hεpos
  have hρ1 : 1 ≤ ρ := by rw [hρ, le_div_iff₀ hεpos, one_mul]; exact hε.2
  -- `ρ ≤ (1 + 1/n)^a`
  have hρup : ρ ≤ (1 + 1 / (n : ℝ)) ^ a := by
    have hq : t / ((n : ℝ) + 1) ^ (-a) = (1 + 1 / (n : ℝ)) ^ a := by
      rw [ht, Real.rpow_neg hnpos.le, Real.rpow_neg hn1pos.le, div_inv_eq_mul,
        inv_mul_eq_div, ← Real.div_rpow hn1pos.le hnpos.le]
      congr 1
      field_simp
    rw [hρ, ← hq]
    exact div_le_div_of_nonneg_left htpos.le (Real.rpow_pos_of_pos hn1pos _) hε.1
  have hρδ : ρ < 1 + min δ 1 := lt_of_le_of_lt hρup hn1
  have hρ2 : ρ ∈ Icc (1 : ℝ) 2 := ⟨hρ1, by have := min_le_right δ 1; linarith⟩
  have hc := hn ρ hρ2
  have hεeq : t / ρ = ε := by rw [hρ]; field_simp
  have hid := n1_ratio_mul_rpow A θ t hρpos
  rw [hεeq] at hid hc
  rw [hid]
  set c : ℝ := ρ * A ε / (ρ ^ θ * A t) with hcdef
  have hpow : |ρ ^ (θ - 1) - 1| < min (η / 3) 1 := hδc (by
    rw [abs_lt]
    constructor
    · linarith
    · have := min_le_left δ 1
      linarith)
  have hpow1 : |ρ ^ (θ - 1) - 1| < η / 3 := lt_of_lt_of_le hpow (min_le_left _ _)
  have hpow2 : ρ ^ (θ - 1) ≤ 2 := by
    have := (abs_lt.1 (lt_of_lt_of_le hpow (min_le_right _ _))).2
    linarith
  have hpow0 : 0 < ρ ^ (θ - 1) := Real.rpow_pos_of_pos hρpos _
  have heq : c * ρ ^ (θ - 1) - 1 = (c - 1) * ρ ^ (θ - 1) + (ρ ^ (θ - 1) - 1) := by ring
  rw [heq]
  calc |(c - 1) * ρ ^ (θ - 1) + (ρ ^ (θ - 1) - 1)|
      ≤ |(c - 1) * ρ ^ (θ - 1)| + |ρ ^ (θ - 1) - 1| := abs_add_le _ _
    _ = |c - 1| * ρ ^ (θ - 1) + |ρ ^ (θ - 1) - 1| := by
        rw [abs_mul, abs_of_pos hpow0]
    _ ≤ η / 3 * 2 + η / 3 := by
        refine add_le_add ?_ hpow1.le
        exact mul_le_mul hc hpow2 hpow0.le (by positivity)
    _ = η := by ring

/-- `|log c| ≤ 2 |c - 1|` for `|c - 1| ≤ 1/2`. -/
theorem n1_abs_log_le {c : ℝ} (hc : |c - 1| ≤ 1 / 2) : |Real.log c| ≤ 2 * |c - 1| := by
  have hc0 : 1 / 2 ≤ c := by have := (abs_le.1 hc).1; linarith
  have hcpos : 0 < c := by linarith
  have hup : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hcpos
  have hlow : 1 - c⁻¹ ≤ Real.log c := Real.one_sub_inv_le_log_of_pos hcpos
  have hinv : 1 - c⁻¹ = (c - 1) / c := by field_simp
  rw [hinv] at hlow
  have hlow' : -(2 * |c - 1|) ≤ (c - 1) / c := by
    rw [le_div_iff₀ hcpos]
    have h1 : -(2 * |c - 1|) * c ≤ -|c - 1| := by
      have : |c - 1| ≤ 2 * |c - 1| * c := by nlinarith [abs_nonneg (c - 1)]
      linarith
    have h2 : -|c - 1| ≤ c - 1 := neg_abs_le _
    linarith
  rw [abs_le]
  constructor
  · linarith
  · have := le_abs_self (c - 1)
    linarith

/-- **The exponent from the uniform ratio limit** (MA1 A7.5). If `A > 0` near `0` and
`c(ε, r) = r A(ε/r)/(r^θ A(ε)) → 1` uniformly on `[1, e]` as `ε ↓ 0`, then
`log A(ε) / log ε → 1 − θ`. -/
theorem n1_exponent_of_unif {A : ℝ → ℝ} {θ : ℝ} (hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < A ε)
    (hunif : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc (1 : ℝ) (Real.exp 1),
      |r * A (ε / r) / (r ^ θ * A ε) - 1| ≤ η) :
    Tendsto (fun ε => Real.log (A ε) / Real.log ε) (𝓝[>] 0) (𝓝 (1 - θ)) := by
  set φ : ℝ → ℝ := fun t => Real.log (A (Real.exp (-t))) with hφdef
  have hφ : ∀ η : ℝ, 0 < η → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ s ∈ Icc (0 : ℝ) 1,
      |φ (t + s) - φ t - (θ - 1) * s| ≤ η := by
    intro η hη
    have hη' : 0 < min (η / 2) (1 / 2) := lt_min (by positivity) (by norm_num)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hpos.and (hunif _ hη'))
    refine ⟨-Real.log u + 1, fun t ht s hs => ?_⟩
    have hupos : 0 < u := hu
    -- the scales `ε = e^{-t}` and `ε / r = e^{-(t+s)}` with `r = e^s ∈ [1, e]`
    have hεlt : Real.exp (-t) < u := by
      calc Real.exp (-t) ≤ Real.exp (Real.log u - 1) := Real.exp_le_exp.2 (by linarith)
        _ < Real.exp (Real.log u) := Real.exp_lt_exp.2 (by linarith)
        _ = u := Real.exp_log hupos
    have hε : Real.exp (-t) ∈ Ioo (0 : ℝ) u := ⟨Real.exp_pos _, hεlt⟩
    have hε' : Real.exp (-(t + s)) ∈ Ioo (0 : ℝ) u :=
      ⟨Real.exp_pos _, lt_of_le_of_lt (Real.exp_le_exp.2 (by linarith [hs.1])) hεlt⟩
    have hr : Real.exp s ∈ Icc (1 : ℝ) (Real.exp 1) :=
      ⟨Real.one_le_exp hs.1, Real.exp_le_exp.2 hs.2⟩
    have hrpos : 0 < Real.exp s := Real.exp_pos s
    obtain ⟨hA, hc⟩ := hsub hε
    have hA' := (hsub hε').1
    have hdiv : Real.exp (-t) / Real.exp s = Real.exp (-(t + s)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    have hc' := hc (Real.exp s) hr
    rw [hdiv] at hc'
    set c : ℝ := Real.exp s * A (Real.exp (-(t + s))) / (Real.exp s ^ θ * A (Real.exp (-t)))
      with hcdef
    have hc2 : |c - 1| ≤ 1 / 2 := le_trans hc' (min_le_right _ _)
    have hcpos : 0 < c := by have := (abs_le.1 hc2).1; linarith
    have hid := n1_ratio_mul_rpow A θ (Real.exp (-t)) hrpos
    rw [hdiv] at hid
    -- `φ(t + s) − φ(t) = log c + (θ − 1) s`
    have hlog : φ (t + s) - φ t = Real.log c + (θ - 1) * s := by
      simp only [hφdef]
      rw [← Real.log_div hA'.ne' hA.ne', hid, ← hcdef,
        Real.log_mul hcpos.ne' (Real.rpow_pos_of_pos hrpos _).ne', Real.log_rpow hrpos,
        Real.log_exp]
    rw [hlog, add_sub_cancel_right]
    calc |Real.log c| ≤ 2 * |c - 1| := n1_abs_log_le hc2
      _ ≤ 2 * min (η / 2) (1 / 2) := by linarith
      _ ≤ 2 * (η / 2) := by
          have := min_le_left (η / 2) (1 / 2)
          linarith
      _ = η := by ring
  have hlim := n1_tendsto_div_of_increments hφ
  have hcomp : Tendsto (fun ε => φ (-Real.log ε) / (-Real.log ε)) (𝓝[>] 0) (𝓝 (θ - 1)) :=
    hlim.comp (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  have hneg := hcomp.neg
  rw [neg_sub] at hneg
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  simp only [hφdef, neg_neg, Real.exp_log hεpos]
  rw [div_neg, neg_neg]

/-- **`A(ε) = ε^{1−θ+o(1)}`** in the two-sided form: under the hypotheses of `n1_exponent_of_unif`,
for every `η > 0`, `ε^{1−θ+η} ≤ A(ε) ≤ ε^{1−θ−η}` for all small `ε > 0`. -/
theorem n1_rpow_bounds_of_unif {A : ℝ → ℝ} {θ : ℝ} (hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < A ε)
    (hunif : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc (1 : ℝ) (Real.exp 1),
      |r * A (ε / r) / (r ^ θ * A ε) - 1| ≤ η) :
    ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ε ^ (1 - θ + η) ≤ A ε ∧ A ε ≤ ε ^ (1 - θ - η) := by
  intro η hη
  have hlim := n1_exponent_of_unif hpos hunif
  have hclose : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |Real.log (A ε) / Real.log ε - (1 - θ)| < η := by
    have := (Metric.tendsto_nhds.1 hlim) η hη
    filter_upwards [this] with ε hε
    rwa [Real.dist_eq] at hε
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  filter_upwards [hclose, hsmall, hpos, self_mem_nhdsWithin] with ε hε hε1 hA hε0
  have hε0' : (0 : ℝ) < ε := hε0
  have hlogneg : Real.log ε < 0 := Real.log_neg hε0' hε1
  rw [abs_lt] at hε
  have hq1 : Real.log (A ε) / Real.log ε < 1 - θ + η := by linarith
  have hq2 : 1 - θ - η < Real.log (A ε) / Real.log ε := by linarith
  rw [div_lt_iff_of_neg hlogneg] at hq1
  rw [lt_div_iff_of_neg hlogneg] at hq2
  constructor
  · rw [Real.rpow_def_of_pos hε0', ← Real.exp_log hA]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [Real.rpow_def_of_pos hε0', ← Real.exp_log hA]
    exact Real.exp_le_exp.2 (by linarith)

end HigherDimLFPPAS.Normalizer
