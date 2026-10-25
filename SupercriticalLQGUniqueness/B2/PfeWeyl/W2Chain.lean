import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem exists_dedup_chain {α : Type*} (v : ℕ → α) (N : ℕ) :
    ∃ (N' : ℕ) (v' : ℕ → α), N' ≤ N ∧ v' 0 = v 0 ∧ v' N' = v N ∧
      (∀ j < N', v' j ≠ v' (j + 1)) ∧
      (∀ j < N', ∃ i < N, v' j = v i ∧ v' (j + 1) = v (i + 1)) ∧
      ∀ c : α → α → ℝ≥0∞,
        (∑ j ∈ Finset.range N', c (v' j) (v' (j + 1))) ≤
          ∑ i ∈ Finset.range N, c (v i) (v (i + 1)) := by
  induction N with
  | zero =>
    exact ⟨0, v, le_rfl, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j hj => absurd hj (Nat.not_lt_zero _), fun c => le_rfl⟩
  | succ N ih =>
    obtain ⟨N', v', hN', h0, hlast, hdist, hpair, hsum⟩ := ih
    by_cases heq : v (N + 1) = v N
    · refine ⟨N', v', hN'.trans (Nat.le_succ N), h0, hlast.trans heq.symm, hdist,
        fun j hj => ?_, fun c => ?_⟩
      · obtain ⟨i, hi, h1, h2⟩ := hpair j hj
        exact ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩
      · rw [Finset.sum_range_succ]
        exact (hsum c).trans le_self_add
    · let w : ℕ → α := fun j => if j = N' + 1 then v (N + 1) else v' j
      have hw : ∀ j ≤ N', w j = v' j := fun j hj => by
        simp [w, show j ≠ N' + 1 by omega]
      have hwlast : w (N' + 1) = v (N + 1) := by simp [w]
      refine ⟨N' + 1, w, Nat.succ_le_succ hN', ?_, hwlast, ?_, ?_, fun c => ?_⟩
      · rw [hw 0 (Nat.zero_le _), h0]
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · rw [hw j hj.le, hw (j + 1) hj]
          exact hdist j hj
        · subst hj
          rw [hw j le_rfl, hwlast, hlast]
          exact fun h => heq h.symm
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · obtain ⟨i, hi, h1, h2⟩ := hpair j hj
          refine ⟨i, Nat.lt_succ_of_lt hi, ?_, ?_⟩
          · rw [hw j hj.le, h1]
          · rw [hw (j + 1) hj, h2]
        · subst hj
          exact ⟨N, Nat.lt_succ_self N, by rw [hw j le_rfl, hlast], hwlast⟩
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hrest : (∑ j ∈ Finset.range N', c (w j) (w (j + 1))) =
            ∑ j ∈ Finset.range N', c (v' j) (v' (j + 1)) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          rw [hw j hj'.le, hw (j + 1) hj']
        rw [hrest, hw N' le_rfl, hwlast, hlast]
        exact add_le_add (hsum c) le_rfl

 


theorem exists_diagonal_upper {β : Type*} [PseudoMetricSpace β]
    (F : ℕ → β → ℝ≥0∞) (q : β) (e : ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → ∃ p : ℕ → β, Tendsto p atTop (𝓝 q) ∧
      ∀ᶠ n in atTop, F n (p n) ≤ e + ENNReal.ofReal ε) :
    ∃ p : ℕ → β, Tendsto p atTop (𝓝 q) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, F n (p n) ≤ e + ENNReal.ofReal ε := by
  have hk : ∀ k : ℕ, ∃ p : ℕ → β, Tendsto p atTop (𝓝 q) ∧
      ∀ᶠ n in atTop, F n (p n) ≤ e + ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
    fun k => h _ (by positivity)
  choose P hPq hPF using hk
  let Good : ℕ → ℕ → Prop := fun n k =>
    F n (P k n) ≤ e + ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∧
      dist (P k n) q < 1 / ((k : ℝ) + 1)
  have hGood : ∀ k, ∀ᶠ n in atTop, Good n k := by
    intro k
    refine (hPF k).and ?_
    exact (Metric.tendsto_nhds.1 (hPq k)) _ (by positivity)
  let κ : ℕ → ℕ := fun n => Nat.findGreatest (Good n) n
  have hκ : Tendsto κ atTop atTop := by
    refine tendsto_atTop.2 fun k => ?_
    filter_upwards [hGood k, eventually_ge_atTop k] with n hn hkn
    exact Nat.le_findGreatest hkn hn
  have hκGood : ∀ᶠ n in atTop, Good n (κ n) := by
    filter_upwards [hGood 0] with n hn
    exact Nat.findGreatest_spec (Nat.zero_le n) hn
  have hsmall : Tendsto (fun n => 1 / ((κ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hκ
  refine ⟨fun n => P (κ n) n, ?_, ?_⟩
  · refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [hκGood, (tendsto_order.1 hsmall).2 ε hε] with n hn hεn
    exact hn.2.trans hεn
  · intro ε hε
    filter_upwards [hκGood, (tendsto_order.1 hsmall).2 ε hε] with n hn hεn
    exact hn.1.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hεn.le))

end SupercriticalLQGUniqueness.B2.PfeWeyl
