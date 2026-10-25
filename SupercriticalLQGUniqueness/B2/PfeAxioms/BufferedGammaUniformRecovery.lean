import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaUniformMesh
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaFiniteRecovery

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem uniform_buffered_path_recovery_core
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (euclidForget (G n)))
    {V K : Set ℂ} (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (hsmall : SmallAnnulusCosts G D K V)
    {r R : ℝ≥0∞} (hrR : r < R)
    (hR : R < ⨅ p ∈ K ×ˢ frontier V, D p)
    (hrfin : r < ∞)
    {Q : ℝ → ℂ} {L : ℝ}
    (hQ : D.IsCurve Q 0 L)
    (hunit : HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 L))
    (hQV : ∀ u ∈ Icc 0 L, Q u ∈ V)
    (hQK : ∀ u ∈ Icc 0 L, Q u ∈ interior K)
    (N : ℕ)
    (hstepNonzero : ∀ i : Fin (N + 1),
      Q (uniformTime N L (Fin.castSucc i)) ≠
        Q (uniformTime N L i.succ))
    (hstepUpper : ENNReal.ofReal (L / (N + 1 : ℝ)) < r)
    {B : ℝ≥0∞}
    (hB : ENNReal.ofReal (L / (N + 1 : ℝ)) < B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x y : ℕ → V,
      Tendsto x atTop (𝓝 ⟨Q 0, hQV 0 ⟨le_rfl, hQ.1⟩⟩) ∧
      Tendsto y atTop (𝓝 ⟨Q L, hQV L ⟨hQ.1, le_rfl⟩⟩) ∧
      ∀ᶠ n in atTop,
        (G n).internal V (x n, y n) ≤
          (N + 1) • B + N • ENNReal.ofReal δ := by
  let t : Fin (N + 2) → ℝ := uniformTime N L
  have hL : 0 ≤ L := hQ.1
  have htmem : ∀ j, t j ∈ Icc 0 L := fun j => uniformTime_mem N hL j
  have htinc : ∀ j : Fin (N + 1), t (Fin.castSucc j) ≤ t j.succ :=
    fun j => uniformTime_mono N hL j
  let a : Fin (N + 1) → V :=
    fun j => ⟨Q (t (Fin.castSucc j)), hQV _ (htmem _)⟩
  let b : Fin (N + 1) → V :=
    fun j => ⟨Q (t j.succ), hQV _ (htmem _)⟩
  have hmatch : ∀ i : Fin N, b (Fin.castSucc i) = a i.succ := by
    intro i
    apply Subtype.ext
    change Q (t (Fin.castSucc i).succ) = Q (t (Fin.castSucc i.succ))
    congr 1
  have hstartK : ∀ i, (a i : ℂ) ∈ interior K := by
    intro i
    exact hQK _ (htmem _)
  have hshort : ∀ i, D ((a i : ℂ), (b i : ℂ)) < r := by
    intro i
    change D (Q (t (Fin.castSucc i)), Q (t i.succ)) < r
    exact (LSCMetric.apply_le_len D Q (htinc i)).trans_lt
      (by rw [uniformTime_subarc_len D hL hunit N i]; exact hstepUpper)
  have hnonzero : ∀ i, a i ≠ b i := by
    intro i heq
    have hloop : Q (t (Fin.castSucc i)) = Q (t i.succ) :=
      congrArg Subtype.val heq
    exact (hstepNonzero i) hloop
  have hNS : ∀ i : Fin N, IsNonsingular D (b (Fin.castSucc i)) := by
    intro i
    unfold PfeWeyl.IsNonsingular
    refine ⟨(a (Fin.castSucc i) : ℂ), ?_, ?_⟩
    · intro heq
      exact hnonzero (Fin.castSucc i) (Subtype.ext heq)
    · have hsym : D ((b (Fin.castSucc i) : ℂ), (a (Fin.castSucc i) : ℂ)) =
          D ((a (Fin.castSucc i) : ℂ), (b (Fin.castSucc i) : ℂ)) :=
        D.isExtMetric.2.2.1 _ _
      rw [hsym]
      exact (hshort (Fin.castSucc i)).trans hrfin
  have hcost : ∀ i, D ((a i : ℂ), (b i : ℂ)) < B := by
    intro i
    change D (Q (t (Fin.castSucc i)), Q (t i.succ)) < B
    exact (LSCMetric.apply_le_len D Q (htinc i)).trans_lt
      (by rw [uniformTime_subarc_len D hL hunit N i]; exact hB)
  obtain ⟨x, y, hx, hy, hbound⟩ :=
    finite_skeleton_internal_recovery hG hLen hPath hforget hV hK hfront
      hsmall hrR hR hrfin N a b hmatch hstartK hshort hnonzero hNS
      (fun _ => B) hcost hδ
  have ha0 : a 0 = ⟨Q 0, hQV 0 ⟨le_rfl, hQ.1⟩⟩ := by
    apply Subtype.ext
    change Q (uniformTime N L (Fin.castSucc 0)) = Q 0
    simpa only [Fin.castSucc_zero] using congrArg Q (uniformTime_first N L)
  have hbLast : b (Fin.last N) =
      ⟨Q L, hQV L ⟨hQ.1, le_rfl⟩⟩ := by
    apply Subtype.ext
    change Q (uniformTime N L (Fin.last N).succ) = Q L
    simpa only [Fin.succ_last] using congrArg Q (uniformTime_last N L)
  refine ⟨x, y, ?_, ?_, ?_⟩
  · simpa only [ha0] using hx
  · simpa only [hbLast] using hy
  · simpa only [Finset.sum_const_zero, Finset.sum_const, Finset.card_fin] using hbound

end SupercriticalLQGUniqueness.B2.PfeAxioms
