import SupercriticalLQGUniqueness.B2.DG20Lim.CircleMinimizers
import Mathlib.Analysis.SpecificLimits.Basic

 

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem exists_tendsto_diagonal {α : Type*} [PseudoMetricSpace α]
    (F : ℕ → ℕ → α) (a : ℕ → α) (L : α)
    (hF : ∀ m, Tendsto (fun n => F n m) atTop (nhds (a m)))
    (ha : Tendsto a atTop (nhds L)) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      Tendsto (fun n => F n (k n)) atTop (nhds L) := by
  let Good : ℕ → ℕ → Prop := fun n m =>
    dist (F n m) (a m) < 1 / ((m : ℝ) + 1)
  have hGood : ∀ m, ∀ᶠ n in atTop, Good n m := by
    intro m
    exact eventually_atTop.2 ((Metric.tendsto_atTop.1 (hF m))
      (1 / ((m : ℝ) + 1)) (by positivity))
  let k : ℕ → ℕ := fun n => Nat.findGreatest (Good n) n
  have hk : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 fun M => ?_
    filter_upwards [hGood M, eventually_ge_atTop M] with n hn hMn
    exact Nat.le_findGreatest hMn hn
  have hkGood : ∀ᶠ n in atTop, Good n (k n) := by
    filter_upwards [hGood 0] with n hn
    exact Nat.findGreatest_spec (Nat.zero_le n) hn
  have hδ : Tendsto (fun n => 1 / ((k n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  refine ⟨k, hk, Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  have heδ : ∀ᶠ n in atTop, 1 / ((k n : ℝ) + 1) < ε / 2 :=
    (tendsto_order.1 hδ).2 (ε / 2) (by positivity)
  have hea : ∀ᶠ n in atTop, dist (a (k n)) L < ε / 2 :=
    (Metric.tendsto_nhds.1 (ha.comp hk)) (ε / 2) (by positivity)
  have hev : ∀ᶠ n in atTop, dist (F n (k n)) L < ε := by
    filter_upwards [hkGood, heδ, hea] with n hn hδn han
    have htri := dist_triangle (F n (k n)) (a (k n)) L
    exact lt_of_le_of_lt htri (by dsimp [Good] at hn; linarith)
  exact eventually_atTop.1 hev

end SupercriticalLQGUniqueness.B2.DG20Lim
