import HigherDimLQGContinuity.MomentsW1.LocalChainMain
import Mathlib.Analysis.SumIntegralExpDecay

/-! Analytic estimates for the starting scale of the confined chain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric.DGZ

private theorem chainDelta_tendsto_zero :
    Filter.Tendsto chainDelta Filter.atTop (nhds (0 : ℝ)) := by
  have h := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have h' := h.const_mul 1000
  change Filter.Tendsto (fun x : ℕ => 1000 * (x : ℝ)^2 * (2 : ℝ)⁻¹ ^ x)
    Filter.atTop (nhds (0 : ℝ))
  simpa only [mul_zero, mul_assoc] using h'

private theorem wnStartScale_exists (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ j : ℕ, 110 ≤ j ∧ chainDelta j ≤ ρ / 100 := by
  have h : ∀ᶠ j : ℕ in Filter.atTop, chainDelta j < ρ / 100 :=
    (chainDelta_tendsto_zero.eventually_lt_const (by positivity))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  exact ⟨max 110 N, le_max_left _ _, (hN _ (le_max_right _ _)).le⟩

/-- First scale where the contraction drift fits within a box of radius `ρ`. -/
def wnStartScale (ρ : ℝ) (hρ : 0 < ρ) : ℕ :=
  Nat.find (wnStartScale_exists ρ hρ)

theorem wnStartScale_spec (ρ : ℝ) (hρ : 0 < ρ) :
    110 ≤ wnStartScale ρ hρ ∧ chainDelta (wnStartScale ρ hρ) ≤ ρ / 100 :=
  Nat.find_spec (wnStartScale_exists ρ hρ)

theorem wnStartScale_minimal (ρ : ℝ) (hρ : 0 < ρ) {j : ℕ}
    (hj : 110 ≤ j) (hδ : chainDelta j ≤ ρ / 100) : wnStartScale ρ hρ ≤ j :=
  Nat.find_min' (wnStartScale_exists ρ hρ) (And.intro hj hδ)

theorem wnStartScale_pred_gt (ρ : ℝ) (hρ : 0 < ρ)
    (hj : 110 < wnStartScale ρ hρ) :
    ρ / 100 < chainDelta (wnStartScale ρ hρ - 1) := by
  by_contra h
  have hle : chainDelta (wnStartScale ρ hρ - 1) ≤ ρ / 100 := le_of_not_gt h
  have hmin := wnStartScale_minimal ρ hρ (j := wnStartScale ρ hρ - 1)
    (by omega) hle
  omega

theorem wnStartScale_delta_le (ρ : ℝ) (hρ : 0 < ρ) {j : ℕ}
    (hj : wnStartScale ρ hρ ≤ j) : chainDelta j ≤ ρ/100 := by
  have hj₀ : 110 ≤ wnStartScale ρ hρ := (wnStartScale_spec ρ hρ).1
  have hbase := (wnStartScale_spec ρ hρ).2
  have hmono : chainDelta j ≤ chainDelta (wnStartScale ρ hρ) := by
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih =>
      exact (chainDelta_succ_le (by omega : 3 ≤ j)).trans ih
  exact hmono.trans hbase

theorem wnStartScale_mesh_le (ρ : ℝ) (hρ : 0 < ρ) :
    (2 : ℝ)⁻¹ ^ wnStartScale ρ hρ ≤ ρ := by
  let j := wnStartScale ρ hρ
  have hj : 110 ≤ j := (wnStartScale_spec ρ hρ).1
  have hδ : chainDelta j ≤ ρ / 100 := (wnStartScale_spec ρ hρ).2
  have hj1 : (1 : ℝ) ≤ (j : ℝ)^2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
    nlinarith
  have hpow : 0 ≤ (2 : ℝ)⁻¹ ^ j := by positivity
  unfold chainDelta at hδ
  dsimp only [j] at *
  nlinarith [mul_nonneg (sub_nonneg.mpr hj1) hpow]

theorem wnStartScale_radius_mul_pow_le (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) :
    ρ * (2 : ℝ) ^ wnStartScale ρ hρ ≤
      ((2 : ℝ)^110 + 200000) * (wnStartScale ρ hρ : ℝ)^2 := by
  let j := wnStartScale ρ hρ
  have hj : 110 ≤ j := (wnStartScale_spec ρ hρ).1
  have hj1 : (1 : ℝ) ≤ (j : ℝ)^2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
    nlinarith
  by_cases hj0 : j = 110
  · change ρ * (2 : ℝ)^j ≤ ((2 : ℝ)^110 + 200000) * (j : ℝ)^2
    rw [hj0]
    have hpow : 0 ≤ (2 : ℝ)^110 := by positivity
    norm_num at hj1 ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ1) hpow]
  · have hjgt : 110 < j := by omega
    let k := j - 1
    have hkj : j = k + 1 := by dsimp [k]; omega
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hkj' : (k : ℝ) ≤ j := by exact_mod_cast (by dsimp [k]; omega : k ≤ j)
    have hδ : ρ / 100 < chainDelta k := by
      simpa only [k] using wnStartScale_pred_gt ρ hρ hjgt
    have hpow : (2 : ℝ)⁻¹ ^ k = 2 * (2 : ℝ)⁻¹ ^ j := by
      rw [hkj, pow_succ]
      norm_num
      ring
    have hbound : ρ ≤ 200000 * (k : ℝ)^2 * (2 : ℝ)⁻¹ ^ j := by
      unfold chainDelta at hδ
      rw [hpow] at hδ
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hbound (by positivity : 0 ≤ (2 : ℝ)^j)
    have hcancel : (2 : ℝ)⁻¹ ^ j * (2 : ℝ)^j = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (by positivity : (2 : ℝ)^j ≠ 0)]
    have hmain : ρ * (2 : ℝ)^j ≤ 200000 * (k : ℝ)^2 := by
      calc
        ρ * (2 : ℝ)^j ≤ (200000 * (k : ℝ)^2 * (2 : ℝ)⁻¹ ^ j) * (2 : ℝ)^j := hmul
        _ = 200000 * (k : ℝ)^2 := by rw [mul_assoc, hcancel, mul_one]
    have hk2 : (k : ℝ)^2 ≤ (j : ℝ)^2 := pow_le_pow_left₀ hk0 hkj' _
    dsimp only [j] at *
    nlinarith [sq_nonneg (j : ℝ)]

private theorem wnTwoRpow_split (a b : ℝ) (k : ℕ) :
    (2 : ℝ) ^ (-(a * k)) =
      (2 : ℝ) ^ (-((a-b) * k)) * (2 : ℝ) ^ (-(b*k)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- A polynomial times a decaying dyadic power has a uniform finite tail bound. -/
theorem wnWeightedSum (m j n : ℕ) {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    ∑ k ∈ Finset.Ico j n, (k : ℝ)^m * (2 : ℝ)^(-(a*k)) ≤
      (2^(a-b) * (m.factorial : ℝ) / (Real.log 2 * (a-b))^(m+1)) *
        (2 : ℝ)^(-(b*j)) := by
  let f (k : ℕ) : ℝ := (k : ℝ)^m * (2 : ℝ)^(-((a-b)*k))
  let t (k : ℕ) : ℝ := (2 : ℝ)^(-(b*k))
  have ht : ∀ k, j ≤ k → t k ≤ t j := by
    intro k hk
    dsimp [t]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hcast : (j : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hf : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    positivity
  have hmain :
      ∑ k ∈ Finset.Ico j n, f k * t k ≤
        (∑ k ∈ Finset.Ico j n, f k) * t j := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (ht k (Finset.mem_Ico.mp hk).1) (hf k)
  have hsubset : Finset.Ico j n ⊆ Finset.Iic n := by
    intro k hk
    exact Finset.mem_Iic.mpr (Finset.mem_Ico.mp hk).2.le
  have hsum : ∑ k ∈ Finset.Ico j n, f k ≤ ∑ k ∈ Finset.Iic n, f k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro k _ _
    exact hf k
  have htotal := sum_Iic_pow_mul_two_pow_neg_le (k := m) (M := n) (sub_pos.mpr hab)
  have hsum' : ∑ k ∈ Finset.Iic n, f k ≤
      2^(a-b) * (m.factorial : ℝ) / (Real.log 2 * (a-b))^(m+1) := by
    simpa only [f] using htotal
  have ht0 : 0 ≤ t j := by dsimp [t]; positivity
  calc
    ∑ k ∈ Finset.Ico j n, (k : ℝ)^m * (2 : ℝ)^(-(a*k)) =
        ∑ k ∈ Finset.Ico j n, f k * t k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [wnTwoRpow_split a b k]
          dsimp only [f, t]
          ring
    _ ≤ (∑ k ∈ Finset.Ico j n, f k) * t j := hmain
    _ ≤ (∑ k ∈ Finset.Iic n, f k) * t j := mul_le_mul_of_nonneg_right hsum ht0
    _ ≤ (2^(a-b) * (m.factorial : ℝ) / (Real.log 2 * (a-b))^(m+1)) * t j :=
      mul_le_mul_of_nonneg_right hsum' ht0
    _ = _ := rfl

/-- The terminal polynomial term obeys the same decaying bound. -/
theorem wnWeightedTerm (m j n : ℕ) {a b : ℝ} (hb : 0 < b) (hab : b < a)
    (hjn : j ≤ n) :
    (n : ℝ)^m * (2 : ℝ)^(-(a*n)) ≤
      (2^(a-b) * (m.factorial : ℝ) / (Real.log 2 * (a-b))^(m+1)) *
        (2 : ℝ)^(-(b*j)) := by
  have hterm : (n : ℝ)^m * (2 : ℝ)^(-((a-b)*n)) ≤
      ∑ k ∈ Finset.Iic n, (k : ℝ)^m * (2 : ℝ)^(-((a-b)*k)) := by
    exact Finset.single_le_sum (s := Finset.Iic n)
      (f := fun k : ℕ => (k : ℝ)^m * (2 : ℝ)^(-((a-b)*k)))
      (by intro k _; positivity) (by simp)
  have htotal := sum_Iic_pow_mul_two_pow_neg_le (k := m) (M := n) (sub_pos.mpr hab)
  have hdec : (2 : ℝ)^(-(b*n)) ≤ (2 : ℝ)^(-(b*j)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have : (j : ℝ) ≤ n := by exact_mod_cast hjn
    nlinarith
  have hnonneg : 0 ≤ (n : ℝ)^m * (2 : ℝ)^(-((a-b)*n)) := by positivity
  have hnonneg' : 0 ≤ (2 : ℝ)^(-(b*j)) := by positivity
  calc
    (n : ℝ)^m * (2 : ℝ)^(-(a*n)) =
        ((n : ℝ)^m * (2 : ℝ)^(-((a-b)*n))) * (2 : ℝ)^(-(b*n)) := by
          rw [wnTwoRpow_split a b n]
          ring
    _ ≤ ((n : ℝ)^m * (2 : ℝ)^(-((a-b)*n))) * (2 : ℝ)^(-(b*j)) :=
      mul_le_mul_of_nonneg_left hdec hnonneg
    _ ≤ (∑ k ∈ Finset.Iic n, (k : ℝ)^m * (2 : ℝ)^(-((a-b)*k))) *
        (2 : ℝ)^(-(b*j)) := mul_le_mul_of_nonneg_right hterm hnonneg'
    _ ≤ (2^(a-b) * (m.factorial : ℝ) / (Real.log 2 * (a-b))^(m+1)) *
        (2 : ℝ)^(-(b*j)) := mul_le_mul_of_nonneg_right htotal hnonneg'

theorem wnPolyDecay (m : ℕ) {a : ℝ} (ha : 0 < a) (j : ℕ) :
    (j : ℝ)^m * (2 : ℝ)^(-(a*j)) ≤
      2^a * (m.factorial : ℝ) / (Real.log 2 * a)^(m+1) := by
  have hterm : (j : ℝ)^m * (2 : ℝ)^(-(a*j)) ≤
      ∑ k ∈ Finset.Iic j, (k : ℝ)^m * (2 : ℝ)^(-(a*k)) :=
    Finset.single_le_sum (s := Finset.Iic j)
      (f := fun k : ℕ => (k : ℝ)^m * (2 : ℝ)^(-(a*k)))
      (by intro k _; positivity) (by simp)
  exact hterm.trans (sum_Iic_pow_mul_two_pow_neg_le (k := m) (M := j) ha)

/-- A normalized chain sum decays uniformly from its initial scale. -/
theorem wnLocalChain_sum_bound {d j n : ℕ} {a b B e : ℝ} {c : ℕ → ℝ}
    (hb : 0 < b) (hab : b < a) (hB : 0 ≤ B) (hjn : j ≤ n)
    (hc : ∀ k, j ≤ k → k < n → c k ≤ B * (2 : ℝ)^(-(a*k)))
    (he : (n : ℝ)^2 * (2 : ℝ)⁻¹ ^ n * e ≤
      B * ((n : ℝ)^2 * (2 : ℝ)^(-(a*n)))) :
    wnLocalChain_sum d j n c e ≤
      B * ((2^(a-b) * ((2*d).factorial : ℝ) /
        (Real.log 2 * (a-b))^(2*d+1)) +
        (2^(a-b) * (2 : ℕ).factorial /
        (Real.log 2 * (a-b))^3)) * (2 : ℝ)^(-(b*j)) := by
  let K₁ : ℝ := 2^(a-b) * ((2*d).factorial : ℝ) /
    (Real.log 2 * (a-b))^(2*d+1)
  let K₂ : ℝ := 2^(a-b) * ((2 : ℕ).factorial : ℝ) /
    (Real.log 2 * (a-b))^3
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico j n) :
      (k : ℝ)^(2*d) * c k ≤
        B * ((k : ℝ)^(2*d) * (2 : ℝ)^(-(a*k))) := by
    have hck := hc k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2
    have hm : 0 ≤ (k : ℝ)^(2*d) := by positivity
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hck)]
  have hsum : ∑ k ∈ Finset.Ico j n, (k : ℝ)^(2*d) * c k ≤
      B * (∑ k ∈ Finset.Ico j n, (k : ℝ)^(2*d) * (2 : ℝ)^(-(a*k))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsum' := wnWeightedSum (2*d) j n hb hab
  have hterm' := wnWeightedTerm 2 j n hb hab hjn
  have hpow : (2 : ℕ) + 1 = 3 := by omega
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  have hdec : 0 ≤ (2 : ℝ)^(-(b*j)) := by positivity
  have hsum'' : ∑ k ∈ Finset.Ico j n, (k : ℝ)^(2*d) * c k ≤
      B * K₁ * (2 : ℝ)^(-(b*j)) := by
    calc
      _ ≤ B * (∑ k ∈ Finset.Ico j n, (k : ℝ)^(2*d) * (2 : ℝ)^(-(a*k))) := hsum
      _ ≤ B * (K₁ * (2 : ℝ)^(-(b*j))) := mul_le_mul_of_nonneg_left (by simpa [K₁] using hsum') hB
      _ = _ := by ring
  have hterm'' : (n : ℝ)^2 * (2 : ℝ)⁻¹ ^ n * e ≤
      B * K₂ * (2 : ℝ)^(-(b*j)) := by
    calc
      _ ≤ B * ((n : ℝ)^2 * (2 : ℝ)^(-(a*n))) := he
      _ ≤ B * (K₂ * (2 : ℝ)^(-(b*j))) :=
        mul_le_mul_of_nonneg_left (by simpa [K₂, hpow] using hterm') hB
      _ = _ := by ring
  dsimp [wnLocalChain_sum]
  calc
    _ ≤ B*K₁*(2 : ℝ)^(-(b*j)) + B*K₂*(2 : ℝ)^(-(b*j)) := add_le_add hsum'' hterm''
    _ = B*(K₁+K₂)*(2 : ℝ)^(-(b*j)) := by ring
    _ = _ := rfl

theorem wnStartScale_chain_factor {ρ σ b : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hσ : 0 < σ) (hσb : σ < b) :
    (2*ρ*(2 : ℝ)^wnStartScale ρ hρ+2) *
      (2 : ℝ)^(-(b*(wnStartScale ρ hρ:ℝ))) ≤
      (2*((2 : ℝ)^110+200000)+2) *
        (2^(b-σ) * ((2 : ℕ).factorial : ℝ) /
          (Real.log 2 * (b-σ))^3) * ρ^σ := by
  let j := wnStartScale ρ hρ
  let C : ℝ := (2 : ℝ)^110+200000
  let K : ℝ := 2^(b-σ) * ((2 : ℕ).factorial : ℝ) /
    (Real.log 2 * (b-σ))^3
  have hj1 : 1 ≤ (j : ℝ)^2 := by
    have hj := (wnStartScale_spec ρ hρ).1
    have : (1:ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
    nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfac : 2*ρ*(2 : ℝ)^j+2 ≤ (2*C+2)*(j:ℝ)^2 := by
    have h := wnStartScale_radius_mul_pow_le ρ hρ hρ1
    dsimp only [C, j] at *
    nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ)^110+200000 by positivity)
      (show 0 ≤ (j:ℝ)^2-1 by linarith)]
  have hmesh : (2 : ℝ)^(-(j:ℝ)) ≤ ρ := by
    have h := wnStartScale_mesh_le ρ hρ
    dsimp only [j] at *
    simpa only [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast] using h
  have hmeshσ : (2 : ℝ)^(-(σ*(j:ℝ))) ≤ ρ^σ := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ)^(-(j:ℝ))) hmesh hσ.le
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at h
    convert h using 1
    ring_nf
  have hpoly : (j:ℝ)^2*(2 : ℝ)^(-((b-σ)*(j:ℝ))) ≤ K := by
    simpa only [K] using wnPolyDecay 2 (sub_pos.mpr hσb) j
  have hsplit : (2 : ℝ)^(-(b*(j:ℝ))) =
      (2 : ℝ)^(-((b-σ)*(j:ℝ))) * (2 : ℝ)^(-(σ*(j:ℝ))) :=
    wnTwoRpow_split b σ j
  have hdec0 : 0 ≤ (2 : ℝ)^(-((b-σ)*(j:ℝ))) := by positivity
  have hdec1 : 0 ≤ (2 : ℝ)^(-(σ*(j:ℝ))) := by positivity
  change (2*ρ*(2 : ℝ)^j+2)*(2 : ℝ)^(-(b*(j:ℝ))) ≤ (2*C+2)*K*ρ^σ
  rw [hsplit]
  calc
    (2*ρ*(2 : ℝ)^j+2)*
      ((2 : ℝ)^(-((b-σ)*(j:ℝ))) * (2 : ℝ)^(-(σ*(j:ℝ)))) ≤
        ((2*C+2)*(j:ℝ)^2)*
          ((2 : ℝ)^(-((b-σ)*(j:ℝ))) * (2 : ℝ)^(-(σ*(j:ℝ)))) :=
      mul_le_mul_of_nonneg_right hfac (mul_nonneg hdec0 hdec1)
    _ = (2*C+2)*((j:ℝ)^2*(2 : ℝ)^(-((b-σ)*(j:ℝ))))*
        (2 : ℝ)^(-(σ*(j:ℝ))) := by ring
    _ ≤ (2*C+2)*K*(2 : ℝ)^(-(σ*(j:ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (by positivity)) hdec1
    _ ≤ (2*C+2)*K*ρ^σ :=
      mul_le_mul_of_nonneg_left hmeshσ (by positivity)

theorem wnBadScale_chain_factor {ρ σ b : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hb : 0 < b) {M : ℕ}
    (hM : wnStartScale ρ hρ ≤ M) :
    (2*ρ*(2 : ℝ)^M+2) * (2 : ℝ)^(-(b*(M:ℝ))) ≤
      4*((2 : ℝ)^M)^4 * ρ^σ := by
  let T : ℝ := (2 : ℝ)^M
  have hT1 : 1 ≤ T := by dsimp [T]; exact one_le_pow₀ (by norm_num)
  have hmesh : (2 : ℝ)^(-(wnStartScale ρ hρ:ℝ)) ≤ ρ := by
    simpa only [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast] using
      wnStartScale_mesh_le ρ hρ
  have hmeshσ : (2 : ℝ)^(-(σ*(wnStartScale ρ hρ:ℝ))) ≤ ρ^σ := by
    have h := Real.rpow_le_rpow
      (by positivity : 0 ≤ (2 : ℝ)^(-(wnStartScale ρ hρ:ℝ))) hmesh hσ.le
    rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)] at h
    convert h using 1
    ring_nf
  have hMcast : (wnStartScale ρ hρ:ℝ) ≤ M := by exact_mod_cast hM
  have hpowLe : (2 : ℝ)^(-(M:ℝ)) ≤
      (2 : ℝ)^(-(σ*(wnStartScale ρ hρ:ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    have hj0 : (0:ℝ) ≤ wnStartScale ρ hρ := Nat.cast_nonneg _
    nlinarith
  have hrho : T⁻¹ ≤ ρ^σ := by
    have hpow : (2 : ℝ)^(-(M:ℝ)) = T⁻¹ := by
      dsimp [T]
      rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2), Real.rpow_natCast]
    rw [← hpow]
    exact hpowLe.trans hmeshσ
  have hdec : (2 : ℝ)^(-(b*(M:ℝ))) ≤ 1 := by
    calc
      _ ≤ (2 : ℝ)^(0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by
          have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
          nlinarith)
      _ = 1 := by simp
  have hdec0 : 0 ≤ (2 : ℝ)^(-(b*(M:ℝ))) := by positivity
  have hfac : 2*ρ*T+2 ≤ 4*T := by
    nlinarith [mul_nonneg (show 0 ≤ 1-ρ by linarith) (show 0 ≤ T by linarith)]
  have hsmall : (2*ρ*T+2)*(2 : ℝ)^(-(b*(M:ℝ))) ≤ 4*T := by
    have hfac0 : 0 ≤ 2*ρ*T+2 := by positivity
    nlinarith [mul_nonneg hfac0 (sub_nonneg.mpr hdec)]
  have hTinv : T*T⁻¹ = 1 := mul_inv_cancel₀ (by linarith : T ≠ 0)
  have hlarge : T ≤ T^4*ρ^σ := by
    have hm := mul_le_mul_of_nonneg_left hrho (by positivity : 0 ≤ T^4)
    have hcalc : T^4*T⁻¹ = T^3 := by
      calc
        T^4*T⁻¹ = T^3*(T*T⁻¹) := by ring
        _ = T^3 := by rw [hTinv, mul_one]
    rw [hcalc] at hm
    nlinarith [sq_nonneg (T-1), mul_nonneg (show 0 ≤ T-1 by linarith)
      (show 0 ≤ T^2+T+1 by positivity)]
  change (2*ρ*T+2)*(2 : ℝ)^(-(b*(M:ℝ))) ≤ 4*T^4*ρ^σ
  nlinarith [mul_nonneg (by norm_num : (0:ℝ)≤4) (sub_nonneg.mpr hlarge)]

theorem wnStartScale_terminal_factor {ρ σ a : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hσ : 0 < σ) (hσa : σ < a) (ha1 : a ≤ 1) {n : ℕ}
    (hn : n < wnStartScale ρ hρ) :
    ρ * (2 : ℝ)^((1-a)*(n:ℝ)) ≤
      ((2 : ℝ)^110+200000) *
        (2^(a-σ) * ((2 : ℕ).factorial : ℝ) /
          (Real.log 2 * (a-σ))^3) * ρ^σ := by
  let j := wnStartScale ρ hρ
  let C : ℝ := (2 : ℝ)^110+200000
  let K : ℝ := 2^(a-σ) * ((2 : ℕ).factorial : ℝ) /
    (Real.log 2 * (a-σ))^3
  have hnj : (n:ℝ) ≤ j := by exact_mod_cast (by omega : n ≤ j)
  have hmono : (2 : ℝ)^((1-a)*(n:ℝ)) ≤ (2 : ℝ)^((1-a)*(j:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    nlinarith
  have hsplit : (2 : ℝ)^((1-a)*(j:ℝ)) =
      (2 : ℝ)^j * (2 : ℝ)^(-(a*(j:ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoly : (j:ℝ)^2*(2 : ℝ)^(-((a-σ)*(j:ℝ))) ≤ K := by
    simpa only [K] using wnPolyDecay 2 (sub_pos.mpr hσa) j
  have hmesh : (2 : ℝ)^(-(j:ℝ)) ≤ ρ := by
    have h := wnStartScale_mesh_le ρ hρ
    dsimp only [j] at *
    simpa only [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast] using h
  have hmeshσ : (2 : ℝ)^(-(σ*(j:ℝ))) ≤ ρ^σ := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ)^(-(j:ℝ))) hmesh hσ.le
    rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)] at h
    convert h using 1
    ring_nf
  have hδ := wnStartScale_radius_mul_pow_le ρ hρ hρ1
  have hpow0 : 0 ≤ (2 : ℝ)^(-(a*(j:ℝ))) := by positivity
  have hρ0 : 0 ≤ ρ := hρ.le
  have hsplit2 : (2 : ℝ)^(-(a*(j:ℝ))) =
      (2 : ℝ)^(-((a-σ)*(j:ℝ))) * (2 : ℝ)^(-(σ*(j:ℝ))) :=
    wnTwoRpow_split a σ j
  change ρ * (2 : ℝ)^((1-a)*(n:ℝ)) ≤ C*K*ρ^σ
  calc
    ρ * (2 : ℝ)^((1-a)*(n:ℝ)) ≤ ρ * (2 : ℝ)^((1-a)*(j:ℝ)) :=
      mul_le_mul_of_nonneg_left hmono hρ0
    _ = (ρ*(2 : ℝ)^j)*(2 : ℝ)^(-(a*(j:ℝ))) := by rw [hsplit]; ring
    _ ≤ (C*(j:ℝ)^2)*(2 : ℝ)^(-(a*(j:ℝ))) := by
      exact mul_le_mul_of_nonneg_right (by simpa only [C, j] using hδ) hpow0
    _ = C*((j:ℝ)^2*(2 : ℝ)^(-((a-σ)*(j:ℝ))))*
        (2 : ℝ)^(-(σ*(j:ℝ))) := by rw [hsplit2]; ring
    _ ≤ C*K*(2 : ℝ)^(-(σ*(j:ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly hC) (by positivity)
    _ ≤ C*K*ρ^σ := mul_le_mul_of_nonneg_left hmeshσ (mul_nonneg hC hK)

theorem wnBadScale_power_dom {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) {M : ℕ} (hM : wnStartScale ρ hρ ≤ M) :
    (2 : ℝ)^M ≤ ((2 : ℝ)^M)^4 * ρ^σ := by
  let T : ℝ := (2 : ℝ)^M
  have hT1 : 1 ≤ T := by dsimp [T]; exact one_le_pow₀ (by norm_num)
  have hmesh : (2 : ℝ)^(-(wnStartScale ρ hρ:ℝ)) ≤ ρ := by
    simpa only [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast] using
      wnStartScale_mesh_le ρ hρ
  have hmeshσ : (2 : ℝ)^(-(σ*(wnStartScale ρ hρ:ℝ))) ≤ ρ^σ := by
    have h := Real.rpow_le_rpow
      (by positivity : 0 ≤ (2 : ℝ)^(-(wnStartScale ρ hρ:ℝ))) hmesh hσ.le
    rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)] at h
    convert h using 1
    ring_nf
  have hMcast : (wnStartScale ρ hρ:ℝ) ≤ M := by exact_mod_cast hM
  have hpowLe : (2 : ℝ)^(-(M:ℝ)) ≤
      (2 : ℝ)^(-(σ*(wnStartScale ρ hρ:ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    have hj0 : (0:ℝ) ≤ wnStartScale ρ hρ := Nat.cast_nonneg _
    nlinarith
  have hrho : T⁻¹ ≤ ρ^σ := by
    have hpow : (2 : ℝ)^(-(M:ℝ)) = T⁻¹ := by
      dsimp [T]
      rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2), Real.rpow_natCast]
    rw [← hpow]
    exact hpowLe.trans hmeshσ
  have hm := mul_le_mul_of_nonneg_left hrho (by positivity : 0 ≤ T^4)
  have hcalc : T^4*T⁻¹ = T^3 := by
    calc
      T^4*T⁻¹ = T^3*(T*T⁻¹) := by ring
      _ = T^3 := by rw [mul_inv_cancel₀ (by linarith : T ≠ 0), mul_one]
  rw [hcalc] at hm
  change T ≤ T^4*ρ^σ
  nlinarith [sq_nonneg (T-1), mul_nonneg (show 0 ≤ T-1 by linarith)
    (show 0 ≤ T^2+T+1 by positivity)]

theorem wnBadScale_terminal_factor {ρ σ a : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : 0 ≤ a) {M n : ℕ}
    (hM : wnStartScale ρ hρ ≤ M) (hn : n < M) :
    ρ * (2 : ℝ)^((1-a)*(n:ℝ)) ≤ ((2 : ℝ)^M)^4 * ρ^σ := by
  have hcast : (n:ℝ) ≤ M := by exact_mod_cast (by omega : n ≤ M)
  have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hpow : (2 : ℝ)^((1-a)*(n:ℝ)) ≤ (2 : ℝ)^M := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    nlinarith
  have hρT : ρ*(2 : ℝ)^((1-a)*(n:ℝ)) ≤ (2 : ℝ)^M := by
    have ht0 : 0 ≤ (2 : ℝ)^((1-a)*(n:ℝ)) := by positivity
    nlinarith [mul_nonneg (show 0 ≤ 1-ρ by linarith) ht0]
  exact hρT.trans (wnBadScale_power_dom hρ hσ hσ1 hM)

end HigherDimLQGContinuity
