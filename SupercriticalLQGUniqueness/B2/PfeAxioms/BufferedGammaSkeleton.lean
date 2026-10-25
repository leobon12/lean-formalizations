import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaPathWitness

 










set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl BufferedMetricTrace

theorem eventually_buffered_skeleton_bound
    {G : ℕ → LSCMetric} {D : LSCMetric} {K V : Set ℂ}
    (hsmall : SmallAnnulusCosts G D K V)
    (hforget : ∀ n, Continuous (euclidForget (G n)))
    (N : ℕ) (P : (n : ℕ) → Fin (N + 1) → BufferedMetricTrace (G n) V)
    (w₁ z w₂ : Fin N → ℂ)
    (hz : ∀ i, z i ∈ K ∧ IsNonsingular D (z i))
    (hw₁ : ∀ i, w₁ i ≠ z i) (hw₂ : ∀ i, w₂ i ≠ z i)
    (hPstart : ∀ i, Tendsto
      (fun n => (P n (Fin.castSucc i)).path (P n (Fin.castSucc i)).start)
      atTop (𝓝 (w₁ i)))
    (hPstop : ∀ i, Tendsto
      (fun n => (P n (Fin.castSucc i)).path (P n (Fin.castSucc i)).stop)
      atTop (𝓝 (z i)))
    (hQstart : ∀ i, Tendsto
      (fun n => (P n i.succ).path (P n i.succ).start)
      atTop (𝓝 (z i)))
    (hQstop : ∀ i, Tendsto
      (fun n => (P n i.succ).path (P n i.succ).stop)
      atTop (𝓝 (w₂ i)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      (G n).internal V ((P n 0).first, (P n (Fin.last N)).last) ≤
        finiteBridgeBudget (ENNReal.ofReal δ) (P n 0)
          (List.ofFn (fun i : Fin N => P n i.succ)) := by
  have hbridge : ∀ i : Fin N, ∀ᶠ n in atTop,
      ∃ R : BufferedMetricTrace (G n) V,
        ((P n (Fin.castSucc i)).trace ∩ R.trace).Nonempty ∧
        (R.trace ∩ (P n i.succ).trace).Nonempty ∧
        R.cost ≤ ENNReal.ofReal δ := by
    intro i
    obtain ⟨A, _, _, hev⟩ := eventually_buffered_bridge_at_junction
      hsmall hforget (hz i).1 (hz i).2 (hw₁ i) (hw₂ i)
      (fun n => P n (Fin.castSucc i)) (fun n => P n i.succ)
      (hPstart i) (hPstop i) (hQstart i) (hQstop i) hδ
    filter_upwards [hev] with n hn
    obtain ⟨R, hPR, hRQ, hcost⟩ := hn
    exact ⟨R, hPR, hRQ, hcost.le⟩
  exact eventually_finite_buffered_bridge_bound N (ENNReal.ofReal δ) P hbridge

end SupercriticalLQGUniqueness.B2.PfeAxioms
