import HigherDimLQGContinuity.Windows.Basic

/-!
# Rational exhaustion of the subcritical interval

Nested rational windows cover every positive subcritical parameter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open HigherDimLQGMetric

namespace HigherDimLQGContinuity

/-- The positive subcritical interval is exhausted by nested rational windows.
The lower endpoints strictly decrease to zero and the upper endpoints strictly
increase to the critical parameter. -/
theorem exists_window_exhaustion {d : ℕ} (hd : 2 ≤ d) :
    ∃ lo hi : ℕ → ℚ,
      (∀ n, 0 < (lo n : ℝ) ∧ (lo n : ℝ) < (hi n : ℝ) ∧ (hi n : ℝ) ∈ subcritSet d) ∧
      StrictAnti lo ∧ StrictMono hi ∧
      Tendsto (fun n => (lo n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n => (hi n : ℝ)) atTop (𝓝 (xiCrit d)) ∧
      (∀ n, Icc (lo n : ℝ) (hi n : ℝ) ⊆ subcritSet d) ∧
      (∀ n, Icc (lo n : ℝ) (hi n : ℝ) ⊆ Icc (lo (n + 1) : ℝ) (hi (n + 1) : ℝ)) ∧
      subcritSet d = ⋃ n, Ioo (lo n : ℝ) (hi n : ℝ) := by
  have hc : 0 < xiCrit d := xiCrit_pos hd
  obtain ⟨u, huMono, huBound, huTendsto⟩ := Real.exists_seq_rat_strictMono_tendsto (xiCrit d)
  obtain ⟨q, hq0, hqc⟩ := exists_rat_btwn hc
  have hevent : ∀ᶠ n in atTop, (q : ℝ) < (u n : ℝ) :=
    huTendsto.eventually (lt_mem_nhds hqc)
  obtain ⟨N, hN⟩ := hevent.exists
  have huN0 : (0 : ℝ) < (u N : ℝ) := hq0.trans hN
  let lo : ℕ → ℚ := fun n => u N / ((n : ℚ) + 2)
  let hi : ℕ → ℚ := fun n => u (n + N)
  have hhiMono : StrictMono hi := fun _ _ h => huMono (Nat.add_lt_add_right h N)
  have hhiBound (n : ℕ) : (hi n : ℝ) < xiCrit d := huBound _
  have hhi0 (n : ℕ) : (0 : ℝ) < (hi n : ℝ) := by
    have hle : u N ≤ hi n := huMono.monotone (Nat.le_add_left N n)
    exact huN0.trans_le (by exact_mod_cast hle)
  have hlo0 (n : ℕ) : (0 : ℝ) < (lo n : ℝ) := by
    have hNrat : 0 < u N := by exact_mod_cast huN0
    have h : (0 : ℚ) < u N / ((n : ℚ) + 2) := div_pos hNrat (by positivity)
    have h' : (0 : ℝ) < ((u N / ((n : ℚ) + 2) : ℚ) : ℝ) := by exact_mod_cast h
    exact h'
  have hlohi (n : ℕ) : (lo n : ℝ) < (hi n : ℝ) := by
    have hle : u N ≤ hi n := huMono.monotone (Nat.le_add_left N n)
    have hdiv : (lo n : ℝ) < (u N : ℝ) := by
      have hNrat : 0 < u N := by exact_mod_cast huN0
      have h : u N / ((n : ℚ) + 2) < u N :=
        div_lt_self hNrat (by have : 0 ≤ (n : ℚ) := Nat.cast_nonneg _; linarith)
      have h' : ((u N / ((n : ℚ) + 2) : ℚ) : ℝ) < (u N : ℝ) := by exact_mod_cast h
      exact h'
    exact hdiv.trans_le (by exact_mod_cast hle)
  have hloAnti : StrictAnti lo := by
    apply strictAnti_nat_of_succ_lt
    intro n
    dsimp [lo]
    apply div_lt_div_of_pos_left (by exact_mod_cast huN0)
    · positivity
    · exact_mod_cast Nat.lt_succ_self (n + 2)
  have hloTendsto : Tendsto (fun n => (lo n : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (u N : ℝ)).comp
      (tendsto_add_atTop_nat 2)
    convert h using 1
    ext n
    simp only [lo, Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat,
      Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
  have hhiTendsto : Tendsto (fun n => (hi n : ℝ)) atTop (𝓝 (xiCrit d)) :=
    huTendsto.comp (tendsto_add_atTop_nat N)
  have hhiSub (n : ℕ) : (hi n : ℝ) ∈ subcritSet d := by
    rw [subcritSet_eq_Ioo hd]
    exact ⟨hhi0 n, hhiBound n⟩
  refine ⟨lo, hi, fun n => ⟨hlo0 n, hlohi n, hhiSub n⟩, hloAnti, hhiMono,
    hloTendsto, hhiTendsto, ?_, ?_, ?_⟩
  · intro n x hx
    rw [subcritSet_eq_Ioo hd]
    exact ⟨(hlo0 n).trans_le hx.1, hx.2.trans_lt (hhiBound n)⟩
  · intro n x hx
    have hlow : (lo (n + 1) : ℝ) ≤ (lo n : ℝ) := by
      exact_mod_cast (le_of_lt (hloAnti (Nat.lt_succ_self n)) : lo (n + 1) ≤ lo n)
    have hhigh : (hi n : ℝ) ≤ (hi (n + 1) : ℝ) := by
      exact_mod_cast (le_of_lt (hhiMono (Nat.lt_succ_self n)) : hi n ≤ hi (n + 1))
    exact ⟨hlow.trans hx.1, hx.2.trans hhigh⟩
  · ext ξ
    rw [subcritSet_eq_Ioo hd]
    constructor
    · intro hξ
      have hloEv : ∀ᶠ n in atTop, (lo n : ℝ) < ξ :=
        hloTendsto.eventually (gt_mem_nhds hξ.1)
      have hhiEv : ∀ᶠ n in atTop, ξ < (hi n : ℝ) :=
        hhiTendsto.eventually (lt_mem_nhds hξ.2)
      obtain ⟨n, hnlo, hnhi⟩ := (hloEv.and hhiEv).exists
      exact mem_iUnion.2 ⟨n, ⟨hnlo, hnhi⟩⟩
    · intro hξ
      obtain ⟨n, hn⟩ := mem_iUnion.1 hξ
      exact ⟨(hlo0 n).trans hn.1, hn.2.trans (hhiBound n)⟩

end HigherDimLQGContinuity
