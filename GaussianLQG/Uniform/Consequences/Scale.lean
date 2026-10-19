import GaussianLQG.Uniform.Consequences.Basic
import LQGMetric.Papers.DDDF.S6Eq698
import LQGMetric.Papers.DDDF.S6P28Sup
import LQGMetric.Papers.DDDF.S6P26Up
import LQGMetric.Papers.DDDF.P18Zero
import LQGMetric.Papers.DDDF.P18Straight

/-!
# Consequences of the uniform DDDF core, helper lemmas: scale relations (Route U, U11)

Phase B, packet PB-U10 (ledger packet B-7). Mathematical source: the uniform-constants ledger
`blueprint/phaseB/uniform-ledger.tex`, statement U11 (a)–(d) and the constant ledger
§`subsec:ledger-cons`. Every lemma holds at one white noise and one `ξ`, with explicit constants;
the uniform statement `scale_unif` is assembled in `GaussianLQG/Uniform/Consequences.lean`.

* (a) `lambdaN_sub_le`: `λ_{n-k} ≤ B 2^{2ξk} e^{C₃√k} λ_n` from the a-priori scale bound
  (P18 Step 3, `IfaceStep3U`) and `Λ ≤ B`: `λ_{n-k} ≤ ℓ̄_{n-k} ≤ B ℓ_{n-k}
  ≤ B 2^{2ξk} e^{C₃√k} ℓ_n ≤ B 2^{2ξk} e^{C₃√k} λ_n`.
* (b) `lambdaN_succ_le`: DDDF (6.98) at `r = 1`, upper half, following
  `s6_eq6_98_of_Lambda` (`S6Eq698Main.lean`): `φ_{0,n+1} = φ_{0,1} + φ_{1,n+1}`
  (`ae_phiMN_add`), the crossing of `[0,1]²` for `φ_{1,n+1}` has the law of `L_n(R_{2,2})/2`
  (`S6.law_hi`), `L_n(R_{2,2}) ≤ L_n(R_{3,1})`, Prop 18 with `Λ ≤ B`, and the sup bound
  `prob_sup_phiMN01_le` for `φ_{0,1}` (`phiVer_sup_tail_unif`, explicit constant). The lower half
  of (b) is (a) at `k = 1` (`exp_neg_mul_lambdaN_le_succ`).
* (c) `lambdaN_ge_inf_field` (`n ≥ 1`; a copy of `S6XiQ.lambdaN_ge_inf_field`, whose file imports
  `γ`-specific modules) and `one_le_lambdaN_zero` (`λ_0 ≥ 1`, since `φ_{0,0} = 0`).
* (d) `lintegral_lenN_le`, `lambdaN_le_three_exp`: `E L_n(R_{1,1}) ≤ e^{ξ² n log 2/2}` along the
  straight crossing, then Markov (`S6U.lowerMedian_le_three`): `λ_n ≤ 3 e^{ξ² n log 2/2}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform
namespace Cons

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail LQGMetric.DDDF.S6P28

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-! ### (a) from the a-priori scale bound -/

/-- **U11 (a)** at one noise (ledger row U11(a)): from P18 Step 3 at level `p`
(`2^{-2ξk} ℓ_{n-k}(p) e^{-C₃√k} ≤ ℓ_n(p)`) and `Λ_k(p) ≤ B`,
`λ_{n-k} ≤ B 2^{2ξk} e^{C₃√k} λ_n`. -/
lemma lambdaN_sub_le (hW : IsWhiteNoise P W) {p B C₃ : ℝ} (hp : 0 < p) (hph : p ≤ 1 / 2)
    (hB1 : 1 ≤ B) (hB : ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B)
    (h3 : ∀ n k : ℕ, k ≤ n → (2 : ℝ) ^ (-(2 * ξ * k)) * ellN ξ W P (n - k) (ENNReal.ofReal p) *
      Real.exp (-(C₃ * Real.sqrt k)) ≤ ellN ξ W P n (ENNReal.ofReal p))
    {n k : ℕ} (hk : k ≤ n) :
    lambdaN ξ W P (n - k) ≤
      B * (2 : ℝ) ^ (2 * ξ * k) * Real.exp (C₃ * Real.sqrt k) * lambdaN ξ W P n := by
  obtain ⟨-, hℓlam, -, -⟩ := S6AB.quantile_facts hW hp hph hB1 hB n
  obtain ⟨-, -, hlamB, -⟩ := S6AB.quantile_facts hW hp hph hB1 hB (n - k)
  have h := h3 n k hk
  have hA : 0 < (2 : ℝ) ^ (2 * ξ * k) := Real.rpow_pos_of_pos two_pos _
  have hE : 0 < Real.exp (C₃ * Real.sqrt k) := Real.exp_pos _
  rw [Real.rpow_neg zero_le_two, Real.exp_neg] at h
  have hℓ' : ellN ξ W P (n - k) (ENNReal.ofReal p) ≤
      (2 : ℝ) ^ (2 * ξ * k) * Real.exp (C₃ * Real.sqrt k) * ellN ξ W P n (ENNReal.ofReal p) := by
    have e : ellN ξ W P (n - k) (ENNReal.ofReal p) =
        (2 : ℝ) ^ (2 * ξ * k) * Real.exp (C₃ * Real.sqrt k) *
          (((2 : ℝ) ^ (2 * ξ * k))⁻¹ * ellN ξ W P (n - k) (ENNReal.ofReal p) *
            (Real.exp (C₃ * Real.sqrt k))⁻¹) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h (mul_pos hA hE).le
  calc lambdaN ξ W P (n - k) ≤ B * ellN ξ W P (n - k) (ENNReal.ofReal p) := hlamB
    _ ≤ B * ((2 : ℝ) ^ (2 * ξ * k) * Real.exp (C₃ * Real.sqrt k) *
          ellN ξ W P n (ENNReal.ofReal p)) := mul_le_mul_of_nonneg_left hℓ' (by linarith)
    _ ≤ B * ((2 : ℝ) ^ (2 * ξ * k) * Real.exp (C₃ * Real.sqrt k) * lambdaN ξ W P n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hℓlam (mul_pos hA hE).le)
          (by linarith)
    _ = B * (2 : ℝ) ^ (2 * ξ * k) * Real.exp (C₃ * Real.sqrt k) * lambdaN ξ W P n := by ring

/-- **U11 (b), lower half** from (a) at `k = 1`: for `0 ≤ ξ ≤ 1/2`,
`e^{-(B + 1 + C₃)} λ_n ≤ λ_{n+1}`. -/
lemma exp_neg_mul_lambdaN_le_succ (hW : IsWhiteNoise P W) {p B C₃ : ℝ} (hp : 0 < p)
    (hph : p ≤ 1 / 2) (hB1 : 1 ≤ B) (hB : ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B)
    (h3 : ∀ n k : ℕ, k ≤ n → (2 : ℝ) ^ (-(2 * ξ * k)) * ellN ξ W P (n - k) (ENNReal.ofReal p) *
      Real.exp (-(C₃ * Real.sqrt k)) ≤ ellN ξ W P n (ENNReal.ofReal p))
    (hξ : ξ ≤ 1 / 2) (n : ℕ) :
    Real.exp (-(B + 1 + C₃)) * lambdaN ξ W P n ≤ lambdaN ξ W P (n + 1) := by
  have h := lambdaN_sub_le hW hp hph hB1 hB h3 (n := n + 1) (k := 1) (by omega)
  rw [Nat.add_sub_cancel, Nat.cast_one, Real.sqrt_one, mul_one, mul_one] at h
  have h0 : 0 ≤ lambdaN ξ W P (n + 1) := (lambdaN_pos (ξ := ξ) hW (n + 1)).le
  have h2 : (2 : ℝ) ^ (2 * ξ) ≤ Real.exp 1 := by
    calc (2 : ℝ) ^ (2 * ξ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
      _ ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hBe : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
  have hK : B * (2 : ℝ) ^ (2 * ξ) * Real.exp C₃ ≤ Real.exp (B + 1 + C₃) := by
    rw [Real.exp_add, Real.exp_add]
    have hA : 0 ≤ (2 : ℝ) ^ (2 * ξ) := (Real.rpow_pos_of_pos two_pos _).le
    gcongr
  have h4 : lambdaN ξ W P n ≤ Real.exp (B + 1 + C₃) * lambdaN ξ W P (n + 1) :=
    h.trans (mul_le_mul_of_nonneg_right hK h0)
  calc Real.exp (-(B + 1 + C₃)) * lambdaN ξ W P n
      ≤ Real.exp (-(B + 1 + C₃)) * (Real.exp (B + 1 + C₃) * lambdaN ξ W P (n + 1)) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = lambdaN ξ W P (n + 1) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-! ### (b) DDDF (6.98) at `r = 1`, upper half -/

/-- `sup_{[0,1]²} |φ_{0,1}|` is at most `M₁ = C_F √6 + 4 log 2 + 2` with probability at least
`7/8` (`phiVer_sup_tail_unif` with `n = 1`, `δ = 1/2`, `m = 2`; DDDF (2.11)). -/
lemma prob_sup_phiMN01_le (hW : IsWhiteNoise P W) :
    P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiMN W P 0 1 x ω| ≤
        ferniqueCF * Real.sqrt 6 + (2 * (((1 : ℕ) : ℝ) + 1) * Real.log 2 + 2)} ≤
      ENNReal.ofReal (1 / 8) := by
  have hP := hW.isProbabilityMeasure
  set M := ferniqueCF * Real.sqrt 6 + (2 * (((1 : ℕ) : ℝ) + 1) * Real.log 2 + 2) with hM_def
  have hY : phiMN W P 0 1 = phiVer W P 2⁻¹ 1 := by simp only [phiMN, pow_one, pow_zero]
  have hφ := isPhiVersion_phiVer hW (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ ≤ 1)
  have htail := phiVer_sup_tail_unif hW 1 (δ := 2⁻¹) (by norm_num) (by norm_num) (by norm_num)
    (m := 2) (by norm_num)
  rw [hY]
  have hsub : {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiVer W P 2⁻¹ 1 x ω| ≤ M} ⊆
      {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P 2⁻¹ 1 z ω|} := by
    intro ω hω
    simp only [not_forall, not_le, mem_ofPred_eq] at hω ⊢
    obtain ⟨x, hx, hlt⟩ := hω
    have hbdd : BddAbove (range fun v : ferniqueBox 0 1 => |phiVer W P 2⁻¹ 1 v ω|) := by
      have := (isCompact_ferniqueBox 0 1).bddAbove_image
        (continuous_abs.comp (hφ.cont ω)).continuousOn
      rwa [Set.image_eq_range] at this
    have hx' : x ∈ ferniqueBox 0 1 := by
      simpa [MarkedRect.toSet, rectAB, ferniqueBox] using hx
    exact hlt.le.trans (le_ciSup hbdd ⟨x, hx'⟩)
  have h8 : Real.exp (-(2 * 2)) ≤ 1 / 8 := by
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h4 : (8 : ℝ) ≤ Real.exp 4 := by
      have e : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith
    rw [show -(2 * 2 : ℝ) = -4 by norm_num, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h4
  calc P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiVer W P 2⁻¹ 1 x ω| ≤ M}
      ≤ P {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P 2⁻¹ 1 z ω|} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P 2⁻¹ 1 z ω|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (1 / 8) := ENNReal.ofReal_le_ofReal (htail.trans h8)

/-- **U11 (b), upper half: DDDF (6.98) at `r = 1`** (template `s6_eq6_98_of_Lambda`,
DDDF l. 1608–1613), at one noise: if `Λ_k(p) ≤ B` (`p ≤ 1/2`, `B ≥ 1`), if Prop 18 gives
`P(e^s Λ_k ℓ_k ≤ L_k(R_{3,1})) ≤ 1/8` for every `k`, and if `sup_{[0,1]²}|φ_{0,1}| ≤ M` with
probability at least `7/8`, then `λ_{n+1} ≤ e^{|ξ|M} (e^s B λ_n)/2`. -/
lemma lambdaN_succ_le (hW : IsWhiteNoise P W) {p B s M : ℝ} (hp : 0 < p) (hph : p ≤ 1 / 2)
    (hB1 : 1 ≤ B) (hB : ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B)
    (h18 : ∀ n : ℕ, P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) *
        ellN ξ W P n (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
      ENNReal.ofReal (1 / 8))
    (hM : P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiMN W P 0 1 x ω| ≤ M} ≤ ENNReal.ofReal (1 / 8))
    (n : ℕ) :
    lambdaN ξ W P (n + 1) ≤ Real.exp (|ξ| * M) * (2⁻¹ * (Real.exp s * B * lambdaN ξ W P n)) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨-, -, -, hΛℓ⟩ := S6AB.quantile_facts hW hp hph hB1 hB n
  have hn1 : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have hY := isPhiVersion_phiMN hW (Nat.zero_le (n + 1))
  have hHi := isPhiVersion_phiMN hW hn1
  have hZ := isPhiVersion_phiMN hW (Nat.zero_le n)
  -- `φ_{0,n+1} = φ_{0,1} + φ_{1,n+1}` a.s. (DDDF l. 1613)
  have hGc : P {ω | ¬ ∀ x, phiMN W P 0 (n + 1) x ω =
      phiMN W P 0 1 x ω + phiMN W P 1 (n + 1) x ω} = 0 := ae_iff.1 (ae_phiMN_add hW hn1)
  -- the crossing of `[0,1]²` for `φ_{1,n+1}` has the law of `L_n(R_{2,2})/2` (scaling)
  have hHi_eq : phiMN W P 1 (n + 1) = phiVer W P (2⁻¹ * (2 : ℝ)⁻¹ ^ n) 2⁻¹ := by
    rw [phiMN, pow_one, ← pow_succ']
  have hlaw : ∀ S : Set ℝ, MeasurableSet S →
      P {ω | lenObs ξ (phiMN W P 1 (n + 1)) (rectAB 1 1) ω ∈ S} =
        P {ω | 2⁻¹ * lenObs ξ (phiMN W P 0 n) (rectAB 2 2) ω ∈ S} := by
    intro S hS
    have h := S6.law_hi (ξ := ξ) hW n (a := 2⁻¹) (by norm_num) hS
    rw [inv_inv] at h
    rw [hHi_eq]
    exact h
  -- Prop 18 and `Λ ≤ B`: `P(e^s B λ_n < L_n(R_{2,2})) ≤ 1/8`
  have hup : P {ω | Real.exp s * B * lambdaN ξ W P n <
      lenObs ξ (phiMN W P 0 n) (rectAB 2 2) ω} ≤ ENNReal.ofReal (1 / 8) := by
    refine (measure_mono fun ω hω => ?_).trans (h18 n)
    simp only [mem_ofPred_eq] at hω ⊢
    have h1 := lenObs_rectAB_mono (ξ := ξ) hZ.cont (x := 2) (X := 3) (y := 1) (y' := 2)
      (by norm_num) (by norm_num) zero_le_one (by norm_num) ω
    have h2 : Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
        Real.exp s * B * lambdaN ξ W P n := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left hΛℓ (Real.exp_pos _).le
    linarith
  have hupH : P {ω | 2⁻¹ * (Real.exp s * B * lambdaN ξ W P n) <
      lenObs ξ (phiMN W P 1 (n + 1)) (rectAB 1 1) ω} ≤ ENNReal.ofReal (1 / 8) := by
    have h := hlaw (Ioi (2⁻¹ * (Real.exp s * B * lambdaN ξ W P n))) measurableSet_Ioi
    simp only [mem_Ioi] at h
    rw [h]
    refine le_of_eq_of_le (congrArg P (Set.ext fun ω => ?_)) hup
    exact ⟨fun h => lt_of_mul_lt_mul_left h (by norm_num : (0 : ℝ) ≤ 2⁻¹),
      fun h => mul_lt_mul_of_pos_left h (by norm_num : (0 : ℝ) < 2⁻¹)⟩
  set t := 2⁻¹ * (Real.exp s * B * lambdaN ξ W P n) with ht_def
  have hYm : Measurable (lenObs ξ (phiMN W P 0 (n + 1)) (rectAB 1 1)) :=
    measurable_lenObs hY.cont hY.meas _
  refine S6.lowerMedian_le_of hYm ?_
  set E1 := {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiMN W P 0 1 x ω| ≤ M}
  have hsub : {ω | Real.exp (|ξ| * M) * t < lenObs ξ (phiMN W P 0 (n + 1)) (rectAB 1 1) ω} ⊆
      {ω | ¬ ∀ x, phiMN W P 0 (n + 1) x ω = phiMN W P 0 1 x ω + phiMN W P 1 (n + 1) x ω} ∪
        E1 ∪ {ω | t < lenObs ξ (phiMN W P 1 (n + 1)) (rectAB 1 1) ω} := by
    intro ω hω
    by_contra hn
    simp only [mem_union, not_or] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    simp only [E1, mem_ofPred_eq, not_not] at h1 h2 h3
    have hcmp := (S6.len_cmp (ξ := ξ) (hY.cont ω) (hHi.cont ω) h1 h2).2
    have hω' : Real.exp (|ξ| * M) * t < lenObs ξ (phiMN W P 0 (n + 1)) (rectAB 1 1) ω := hω
    have h3' : lenObs ξ (phiMN W P 1 (n + 1)) (rectAB 1 1) ω ≤ t := not_lt.1 h3
    have := mul_le_mul_of_nonneg_left h3' (Real.exp_pos (|ξ| * M)).le
    linarith
  calc P {ω | Real.exp (|ξ| * M) * t < lenObs ξ (phiMN W P 0 (n + 1)) (rectAB 1 1) ω}
      ≤ P {ω | ¬ ∀ x, phiMN W P 0 (n + 1) x ω = phiMN W P 0 1 x ω + phiMN W P 1 (n + 1) x ω} +
          P E1 + P {ω | t < lenObs ξ (phiMN W P 1 (n + 1)) (rectAB 1 1) ω} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl))
    _ ≤ 0 + ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := by
        rw [hGc]; gcongr
    _ < 2⁻¹ := three_eighths_lt_half

/-! ### (c) lower bound by the infimum of the field -/

/-- **U11 (c), `n ≥ 1`** (DDDF l. 1480; a copy of `S6XiQ.lambdaN_ge_inf_field`, whose file
imports `γ`-specific modules): `λ_n ≥ e^{-ξ (C_F √6 + 2(n+1) log 2 + 1)}`, from
`L_n(R_{1,1}) ≥ e^{-ξ sup|φ_{0,n}|}` and the sup tail (2.11) (`phiVer_sup_tail_unif`). -/
lemma lambdaN_ge_inf_field (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(ξ * (ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + 1)))) ≤
      lambdaN ξ W P n := by
  have hP := hW.isProbabilityMeasure
  set δ : ℝ := (2 : ℝ)⁻¹ ^ n with hδ_def
  set M := ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + 1) with hM_def
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hδ3 : δ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hY : phiMN W P 0 n = phiVer W P δ 1 := by simp [phiMN, hδ_def]
  have hφ := isPhiVersion_phiVer hW hδ0 hδ1
  have hδa : ((2 : ℝ) ^ n)⁻¹ ≤ 2 * δ := by
    have : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
    rw [hδ_def, inv_pow]; linarith
  have hδb : δ ≤ ((2 : ℝ) ^ n)⁻¹ := by rw [hδ_def, inv_pow]
  have htail := phiVer_sup_tail_unif hW n hδa hδb hδ3 (m := 1) zero_le_one
  have hM : P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiVer W P δ 1 x ω| ≤ M} < 2⁻¹ := by
    have hsub : {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiVer W P δ 1 x ω| ≤ M} ⊆
        {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} := by
      intro ω hω
      simp only [not_forall, not_le, mem_ofPred_eq] at hω ⊢
      obtain ⟨x, hx, hlt⟩ := hω
      have hbdd : BddAbove (range fun v : ferniqueBox 0 1 => |phiVer W P δ 1 v ω|) := by
        have := (isCompact_ferniqueBox 0 1).bddAbove_image
          (continuous_abs.comp (hφ.cont ω)).continuousOn
        rwa [Set.image_eq_range] at this
      have hx' : x ∈ ferniqueBox 0 1 := by
        simpa [MarkedRect.toSet, rectAB, ferniqueBox] using hx
      exact hlt.le.trans (le_ciSup hbdd ⟨x, hx'⟩)
    have he : Real.exp (-(2 * 1)) < 2⁻¹ := by
      have h3 := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
      rw [Real.exp_neg, mul_one]
      exact inv_strictAnti₀ two_pos (by linarith)
    calc P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiVer W P δ 1 x ω| ≤ M}
        ≤ P {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * 1))) := ENNReal.ofReal_le_ofReal htail
      _ < ENNReal.ofReal 2⁻¹ := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 he
      _ = 2⁻¹ := by rw [ENNReal.ofReal_inv_of_pos two_pos]; simp
  have h := le_lowerMedian_lenObs (ξ := ξ) (P := P) hφ.cont hφ.meas (rectAB 1 1)
    (by simp [rectAB]) (by simp [rectAB]) hM
  rw [abs_of_nonneg hξ, show (rectAB 1 1).crossWidth = 1 by simp [MarkedRect.crossWidth, rectAB],
    mul_one] at h
  have e : lambdaN ξ W P n =
      lowerMedianLaw (P.map (lenObs ξ (phiVer W P δ 1) (rectAB 1 1))) := by
    rw [lambdaN, lenN, lenMN, hY]
  rw [e]
  exact h

/-- **U11 (c), `n = 0`**: `λ_0 ≥ 1`, since `φ_{0,0} = 0` a.s. (`ae_phiMN_zero_zero`), so
`L_0(R_{1,1}) ≥ 1`. -/
lemma one_le_lambdaN_zero (hW : IsWhiteNoise P W) : 1 ≤ lambdaN ξ W P 0 := by
  have hP := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (le_refl 0)
  have hnull : P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiMN W P 0 0 x ω| ≤ 0} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_phiMN_zero_zero hW] with ω hω hmem
    exact hmem fun x _ => by rw [hω x, abs_zero]
  have h := le_lowerMedian_lenObs (ξ := ξ) (P := P) hφ.cont hφ.meas (rectAB 1 1)
    (by simp [rectAB]) (by simp [rectAB]) (M := 0) (by rw [hnull]; norm_num)
  rw [mul_zero, neg_zero, Real.exp_zero, one_mul,
    show (rectAB 1 1).crossWidth = 1 by simp [MarkedRect.crossWidth, rectAB]] at h
  exact h

/-! ### (d) Markov on the straight crossing -/

/-- **Mean of `L_n(R_{1,1})`** (ledger U11(d), "Markov on a straight crossing"):
`E L_n(R_{1,1}) ≤ e^{ξ² n log 2/2}`, since `L_n(R_{1,1}) ≤ ∫₀¹ e^{ξ φ_{0,n}(t)} dt` along the
straight segment and `φ_{0,n}(x) ~ N(0, n log 2)` (`hasLaw_phiMN`, `lintegral_exp_gauss_le`;
Tonelli). -/
lemma lintegral_lenN_le (hW : IsWhiteNoise P W) (ξ : ℝ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (lenN ξ W P 1 1 n ω) ∂P ≤
      ENNReal.ofReal (Real.exp (ξ ^ 2 * n * Real.log 2 / 2)) := by
  have hP := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  set R : MarkedRect := rectAB 1 1 with hRdef
  have hw : (0 : ℝ) ≤ R.w := by simp [hRdef, rectAB]
  have hh : (0 : ℝ) ≤ R.h := by simp [hRdef, rectAB]
  have hA := R.admPath_seg hw hh
  have hnorm : ∀ t, ‖deriv R.seg t‖ = 1 := fun t => by
    rw [(R.hasDerivAt_seg t).deriv, R.norm_p₂_sub_p₁ hw hh]
    simp [hRdef, rectAB, MarkedRect.crossWidth]
  set F : ℝ → Ω → ℝ≥0∞ := fun t ω =>
    ENNReal.ofReal (Real.exp (ξ * phiMN W P 0 n (R.seg t) ω) * (fun _ : ℝ => (1 : ℝ)) t)
    with hFdef
  have hF : Measurable (Function.uncurry F) :=
    measurable_expWeight hφ.cont hφ.meas R.continuous_seg measurable_const ξ
  have hpt : ∀ ω, ENNReal.ofReal (lenN ξ W P 1 1 n ω) ≤ ∫⁻ t in Icc (0 : ℝ) 1, F t ω := by
    intro ω
    have e1 : ENNReal.ofReal (lenN ξ W P 1 1 n ω) =
        rectLen ξ (fun x => phiMN W P 0 n x ω) R := ofReal_lenObs hφ.cont R hw hh ω
    rw [e1]
    refine (crossLenIn_le_lfppLen hA).trans (le_of_eq ?_)
    unfold lfppLen
    simp only [hFdef, hnorm]
  have hmom : ∀ t, ∫⁻ ω, F t ω ∂P ≤ ENNReal.ofReal (Real.exp (ξ ^ 2 * n * Real.log 2 / 2)) := by
    intro t
    obtain ⟨v, hv, hL⟩ := hasLaw_phiMN hW n (R.seg t)
    have hσ : (v : ℝ) ≤ Real.sqrt (n * Real.log 2) ^ 2 := by
      rw [Real.sq_sqrt (by positivity), hv]
    have h := lintegral_exp_gauss_le hL hσ ξ
    rw [Real.sq_sqrt (by positivity)] at h
    simp only [hFdef, mul_one]
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    congr 1
    ring
  calc ∫⁻ ω, ENNReal.ofReal (lenN ξ W P 1 1 n ω) ∂P
      ≤ ∫⁻ ω, (∫⁻ t in Icc (0 : ℝ) 1, F t ω) ∂P := lintegral_mono hpt
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ ω, F t ω ∂P :=
        lintegral_lintegral_swap ((hF.comp measurable_swap).aemeasurable)
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (ξ ^ 2 * n * Real.log 2 / 2)) :=
        lintegral_mono hmom
    _ = ENNReal.ofReal (Real.exp (ξ ^ 2 * n * Real.log 2 / 2)) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **U11 (d)** (ledger row U11(d)): `λ_n ≤ 3 e^{ξ² n log 2/2}` (Markov,
`S6U.lowerMedian_le_three`, with `lintegral_lenN_le`). -/
lemma lambdaN_le_three_exp (hW : IsWhiteNoise P W) (ξ : ℝ) (n : ℕ) :
    lambdaN ξ W P n ≤ 3 * Real.exp (ξ ^ 2 * n * Real.log 2 / 2) := by
  have hP := hW.isProbabilityMeasure
  exact S6U.lowerMedian_le_three (measurable_lenMN hW 1 1 (Nat.zero_le n)) (Real.exp_pos _).le
    (lintegral_lenN_le hW ξ n)

end Cons
end Uniform
end GaussianLQG
