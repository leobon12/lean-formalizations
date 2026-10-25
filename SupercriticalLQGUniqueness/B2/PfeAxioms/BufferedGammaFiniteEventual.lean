import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaMovingBridge
import Mathlib.Data.List.ChainOfFn

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open BufferedMetricTrace

theorem eventually_finite_buffered_bridge_bound
    {G : ℕ → LSCMetric} {V : Set ℂ} (N : ℕ) (δ : ℝ≥0∞)
    (P : (n : ℕ) → Fin (N + 1) → BufferedMetricTrace (G n) V)
    (hbridge : ∀ i : Fin N, ∀ᶠ n in atTop,
      ∃ R : BufferedMetricTrace (G n) V,
        ((P n (Fin.castSucc i)).trace ∩ R.trace).Nonempty ∧
        (R.trace ∩ (P n i.succ).trace).Nonempty ∧ R.cost ≤ δ) :
    ∀ᶠ n in atTop,
      (G n).internal V ((P n 0).first, (P n (Fin.last N)).last) ≤
        finiteBridgeBudget δ (P n 0)
          (List.ofFn (fun i : Fin N => P n i.succ)) := by
  have hall : ∀ᶠ n in atTop, ∀ i : Fin N,
      ∃ R : BufferedMetricTrace (G n) V,
        ((P n (Fin.castSucc i)).trace ∩ R.trace).Nonempty ∧
        (R.trace ∩ (P n i.succ).trace).Nonempty ∧ R.cost ≤ δ := by
    simpa only [Finset.mem_univ, forall_const] using
      (Filter.eventually_all_finset Finset.univ).2
        (fun i _ => hbridge i)
  filter_upwards [hall] with n hn
  have hchain : (List.ofFn (P n)).IsChain fun U W =>
      ∃ R : BufferedMetricTrace (G n) V,
        (U.trace ∩ R.trace).Nonempty ∧
        (R.trace ∩ W.trace).Nonempty ∧ R.cost ≤ δ := by
    apply List.isChain_ofFn.mpr
    intro i hi
    have hleft : Fin.castSucc (⟨i, by omega⟩ : Fin N) =
        (⟨i, by omega⟩ : Fin (N + 1)) := Fin.ext rfl
    have hright : (⟨i, by omega⟩ : Fin N).succ =
        (⟨i + 1, hi⟩ : Fin (N + 1)) := Fin.ext rfl
    simpa only [hleft, hright] using hn ⟨i, by omega⟩
  have hchain' : (P n 0 :: List.ofFn (fun i : Fin N => P n i.succ)).IsChain
      (fun U W => ∃ R : BufferedMetricTrace (G n) V,
        (U.trace ∩ R.trace).Nonempty ∧
        (R.trace ∩ W.trace).Nonempty ∧ R.cost ≤ δ) := by
    simpa only [List.ofFn_succ] using hchain
  have hlast :
      (P n 0 :: List.ofFn (fun i : Fin N => P n i.succ)).getLast
        (List.cons_ne_nil _ _) = P n (Fin.last N) := by
    simpa only [← List.ofFn_succ] using List.getLast_ofFn_succ (P n)
  have hy : (P n (Fin.last N)).last ∈
      ((P n 0 :: List.ofFn (fun i : Fin N => P n i.succ)).getLast
        (List.cons_ne_nil _ _)).trace := by
    rw [hlast]
    exact (P n (Fin.last N)).last_mem_trace
  have hbound := finite_buffered_bridge_bound δ (P n 0)
    (List.ofFn (fun i : Fin N => P n i.succ)) hchain'
    (P n 0).first_mem_trace hy
  simpa only [hlast] using hbound

end SupercriticalLQGUniqueness.B2.PfeAxioms
