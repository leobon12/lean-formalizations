import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

 











set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.Polylog

 



theorem bounded_additive_real_slope (x : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ n m : ℕ, x n + x m - c ≤ x (n + m) ∧
      x (n + m) ≤ x n + x m + c) :
    ∃ β : ℝ, ∀ n : ℕ, 0 < n → |x n / n - β| ≤ c / n := by
  have hLower : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * (x 1 - c) + c ≤ x (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := (h (n + 1) 1).1
      push_cast at ih ⊢
      nlinarith
  have hUpper : ∀ n : ℕ, x (n + 1) ≤ ((n + 1 : ℕ) : ℝ) * (x 1 + c) - c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := (h (n + 1) 1).2
      push_cast at ih ⊢
      nlinarith
  let u : ℕ → ℝ := fun n => x n + c
  let v : ℕ → ℝ := fun n => -x n + c
  have hu : Subadditive u := by
    intro n m
    dsimp [u]
    linarith [(h n m).2]
  have hv : Subadditive v := by
    intro n m
    dsimp [v]
    linarith [(h n m).1]
  have huBdd : BddBelow (Set.range fun n : ℕ => u n / n) := by
    refine ⟨min 0 (x 1 - c), ?_⟩
    rintro z ⟨n, rfl⟩
    rcases n with _ | n
    · simpa only [Nat.cast_zero, div_zero] using (min_le_left (0 : ℝ) (x 1 - c))
    · have hn : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      have hh := hLower n
      push_cast at hh
      apply le_trans (min_le_right _ _)
      dsimp [u]
      apply (le_div_iff₀ hn).2
      push_cast
      nlinarith [hh, hc]
  have hvBdd : BddBelow (Set.range fun n : ℕ => v n / n) := by
    refine ⟨min 0 (-(x 1 + c)), ?_⟩
    rintro z ⟨n, rfl⟩
    rcases n with _ | n
    · simpa only [Nat.cast_zero, div_zero] using (min_le_left (0 : ℝ) (-(x 1 + c)))
    · have hn : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      have hh := hUpper n
      push_cast at hh
      apply le_trans (min_le_right _ _)
      dsimp [v]
      apply (le_div_iff₀ hn).2
      push_cast
      nlinarith [hh, hc]
  let β := hu.lim
  have huLim : Tendsto (fun n => u n / n) atTop (𝓝 β) := hu.tendsto_lim huBdd
  have hvLim : Tendsto (fun n => v n / n) atTop (𝓝 hv.lim) := hv.tendsto_lim hvBdd
  have hSum : Tendsto (fun n : ℕ => u n / n + v n / n) atTop (𝓝 (β + hv.lim)) :=
    huLim.add hvLim
  have hSumZero : Tendsto (fun n : ℕ => u n / n + v n / n) atTop (𝓝 (0 : ℝ)) := by
    have hcdiv : Tendsto (fun n : ℕ => (2 * c) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    convert hcdiv using 1
    ext n
    dsimp [u, v]
    ring
  have hβv : β + hv.lim = 0 := tendsto_nhds_unique hSum hSumZero
  refine ⟨β, ?_⟩
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hle := hu.lim_le_div huBdd (Nat.ne_of_gt hn)
  have hge := hv.lim_le_div hvBdd (Nat.ne_of_gt hn)
  dsimp [u] at hle
  dsimp [v] at hge
  change β ≤ (x n + c) / n at hle
  rw [add_div] at hle
  rw [add_div, neg_div] at hge
  rw [abs_le]
  constructor <;> nlinarith [hβv]

 


theorem bounded_additive_dyadic_rate (x : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ n m : ℕ, x n + x m - c ≤ x (n + m) ∧
      x (n + m) ≤ x n + x m + c) :
    ∃ α : ℝ, ∀ n : ℕ, 0 < n →
      Real.exp (-c) * (2 : ℝ) ^ (-α * n) ≤ Real.exp (x n) ∧
      Real.exp (x n) ≤ Real.exp c * (2 : ℝ) ^ (-α * n) := by
  obtain ⟨β, hβ⟩ := bounded_additive_real_slope x c hc h
  let α : ℝ := -β / Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPow (n : ℕ) : Real.exp (β * n) = (2 : ℝ) ^ (-α * n) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [α]
    field_simp
  refine ⟨α, ?_⟩
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hrate := hβ n hn
  rw [abs_le] at hrate
  have hExpr : x n / n - β = (x n - β * n) / n := by
    field_simp
  rw [hExpr] at hrate
  have hLower : -c ≤ x n - β * n := by
    have hh := mul_le_mul_of_nonneg_right hrate.1 hnR.le
    field_simp [hn0] at hh
    linarith
  have hUpper : x n - β * n ≤ c := by
    have hh := mul_le_mul_of_nonneg_right hrate.2 hnR.le
    field_simp [hn0] at hh
    linarith
  constructor
  · rw [← hPow n, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [← hPow n, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

end SupercriticalLQGUniqueness.B2.Polylog
