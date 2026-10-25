import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaUniformRecovery

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem uniform_buffered_inner_path_recovery
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (euclidForget (G n)))
    {W V K : Set ℂ} (hWV : W ⊆ V)
    (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (hsmall : SmallAnnulusCosts G D K V)
    {r R : ℝ≥0∞} (hrR : r < R)
    (hR : R < ⨅ p ∈ K ×ˢ frontier V, D p)
    (hrfin : r < ∞)
    {Q : ℝ → ℂ} {L : ℝ}
    (hQ : D.IsCurve Q 0 L)
    (hunit : HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 L))
    (hQW : ∀ u ∈ Icc 0 L, Q u ∈ W)
    (hQK : ∀ u ∈ Icc 0 L, Q u ∈ interior K)
    (hfinite : D.len Q 0 L < ∞)
    {ε : ℝ≥0∞}
    (hnear : D.len Q 0 L <
      D.internal W
        (⟨Q 0, hQW 0 ⟨le_rfl, hQ.1⟩⟩,
          ⟨Q L, hQW L ⟨hQ.1, le_rfl⟩⟩) + ε)
    (N : ℕ)
    (hstepLower : ε ≤ ENNReal.ofReal (L / (N + 1 : ℝ)))
    (hstepUpper : ENNReal.ofReal (L / (N + 1 : ℝ)) < r)
    {B : ℝ≥0∞}
    (hB : ENNReal.ofReal (L / (N + 1 : ℝ)) < B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x y : ℕ → V,
      Tendsto x atTop (𝓝 ⟨Q 0, hWV (hQW 0 ⟨le_rfl, hQ.1⟩)⟩) ∧
      Tendsto y atTop (𝓝 ⟨Q L, hWV (hQW L ⟨hQ.1, le_rfl⟩)⟩) ∧
      ∀ᶠ n in atTop,
        (G n).internal V (x n, y n) ≤
          (N + 1) • B + N • ENNReal.ofReal δ := by
  have hQV : ∀ u ∈ Icc 0 L, Q u ∈ V := fun u hu => hWV (hQW u hu)
  have hL : 0 ≤ L := hQ.1
  have hstepNonzero : ∀ i : Fin (N + 1),
      Q (uniformTime N L (Fin.castSucc i)) ≠
        Q (uniformTime N L i.succ) := by
    intro i hloop
    have hshortLoop := near_minimal_buffered_loop_short D hQ hQW
      (uniformTime_mem N hL (Fin.castSucc i))
      (uniformTime_mem N hL i.succ)
      (uniformTime_mono N hL i) hloop hnear hfinite
    rw [uniformTime_subarc_len D hL hunit N i] at hshortLoop
    exact (not_lt_of_ge hstepLower) hshortLoop
  exact uniform_buffered_path_recovery_core hG hLen hPath hforget hV hK hfront
    hsmall hrR hR hrfin hQ hunit hQV hQK N hstepNonzero
    hstepUpper hB hδ

end SupercriticalLQGUniqueness.B2.PfeAxioms
