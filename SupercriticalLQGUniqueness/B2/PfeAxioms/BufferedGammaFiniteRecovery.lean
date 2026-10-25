import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaSelect
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaPairs

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl BufferedMetricTrace

theorem finite_skeleton_internal_recovery
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
    (N : ℕ) (a b : Fin (N + 1) → V)
    (hmatch : ∀ i : Fin N, b (Fin.castSucc i) = a i.succ)
    (hstartK : ∀ i, (a i : ℂ) ∈ interior K)
    (hshort : ∀ i, D ((a i : ℂ), (b i : ℂ)) < r)
    (hnonzero : ∀ i, a i ≠ b i)
    (hNS : ∀ i : Fin N, IsNonsingular D (b (Fin.castSucc i)))
    (B : Fin (N + 1) → ℝ≥0∞)
    (hB : ∀ i, D ((a i : ℂ), (b i : ℂ)) < B i)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x y : ℕ → V,
      Tendsto x atTop (𝓝 (a 0)) ∧
      Tendsto y atTop (𝓝 (b (Fin.last N))) ∧
      ∀ᶠ n in atTop,
        (G n).internal V (x n, y n) ≤
          (∑ i : Fin (N + 1), B i) + N • ENNReal.ofReal δ := by
  classical
  have hpairs : ∀ i : Fin (N + 1),
      ∃ x y : ℕ → V,
        Tendsto x atTop (𝓝 (a i)) ∧ Tendsto y atTop (𝓝 (b i)) ∧
        Tendsto (fun n => (G n).internal V (x n, y n)) atTop
          (𝓝 (D ((a i : ℂ), (b i : ℂ)))) := by
    intro i
    exact short_segment_internal_recovery hG hLen hPath hV hK hfront
      (a i) (b i) (hstartK i) hrR hR hrfin (hshort i)
  choose x y hx hy hxy using hpairs
  have hcurves : ∀ i : Fin (N + 1), ∀ᶠ n in atTop,
      ∃ P : BufferedMetricTrace (G n) V,
        P.first = x i n ∧ P.last = y i n ∧ P.cost < B i := by
    intro i
    exact eventually_buffered_curves_below (x i) (y i) (hxy i) (hB i)
  obtain ⟨P, hPgood⟩ := select_eventual_segment_curves N x y B hcurves
  have hPfirst (i : Fin (N + 1)) :
      Tendsto (fun n => (P n i).first) atTop (𝓝 (a i)) := by
    have heq : (fun n => (P n i).first) =ᶠ[atTop] x i := by
      filter_upwards [hPgood i] with n hn
      exact hn.1
    exact (hx i).congr' heq.symm
  have hPlast (i : Fin (N + 1)) :
      Tendsto (fun n => (P n i).last) atTop (𝓝 (b i)) := by
    have heq : (fun n => (P n i).last) =ᶠ[atTop] y i := by
      filter_upwards [hPgood i] with n hn
      exact hn.2.1
    exact (hy i).congr' heq.symm
  have hPfirstC (i : Fin (N + 1)) :
      Tendsto (fun n => (P n i).path (P n i).start) atTop
        (𝓝 (a i : ℂ)) :=
    (continuous_subtype_val.tendsto (a i)).comp (hPfirst i)
  have hPlastC (i : Fin (N + 1)) :
      Tendsto (fun n => (P n i).path (P n i).stop) atTop
        (𝓝 (b i : ℂ)) :=
    (continuous_subtype_val.tendsto (b i)).comp (hPlast i)
  have hbridge := eventually_buffered_skeleton_bound hsmall hforget N P
    (fun i => (a (Fin.castSucc i) : ℂ))
    (fun i => (b (Fin.castSucc i) : ℂ))
    (fun i => (b i.succ : ℂ))
    (fun i => ⟨by rw [hmatch i]; exact interior_subset (hstartK i.succ),
      hNS i⟩)
    (fun i => by
      intro heq
      exact hnonzero (Fin.castSucc i) (Subtype.ext heq))
    (fun i => by
      rw [hmatch i]
      intro heq
      exact (hnonzero i.succ).symm (Subtype.ext heq))
    (fun i => hPfirstC (Fin.castSucc i))
    (fun i => hPlastC (Fin.castSucc i))
    (fun i => by simpa only [← hmatch i] using hPfirstC i.succ)
    (fun i => hPlastC i.succ) hδ
  have hcost : ∀ᶠ n in atTop, ∀ i : Fin (N + 1), (P n i).cost ≤ B i := by
    simpa only [Finset.mem_univ, forall_const] using
      (Filter.eventually_all_finset Finset.univ).2
        (fun i _ => (hPgood i).mono (fun n hn => hn.2.2.le))
  refine ⟨fun n => (P n 0).first,
    fun n => (P n (Fin.last N)).last,
    hPfirst 0, hPlast (Fin.last N), ?_⟩
  filter_upwards [hbridge, hcost] with n hbridge' hcost'
  exact hbridge'.trans
    (finiteBridgeBudget_le_fin_sum N (ENNReal.ofReal δ) (P n) B hcost')

end SupercriticalLQGUniqueness.B2.PfeAxioms
