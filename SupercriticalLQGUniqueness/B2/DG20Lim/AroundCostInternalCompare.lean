import SupercriticalLQGUniqueness.B2.DG20Lim.CircleCostInternalCompare

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem len_le_mul_of_internal_le
    (D E : ContMetric) (V : Set ℂ) (k : ℝ≥0∞)
    (hcmp : ∀ z ∈ V, ∀ w ∈ V, E.internal V z w ≤ k * D.internal V z w)
    (P : ℝ → ℂ) (a b : ℝ) (hP : ContinuousOn P (Icc a b))
    (hV : MapsTo P (Icc a b) V) :
    E.len P a b ≤ k * D.len P a b := by
  rw [← LQGMetric.GM.lenFun_internal E hP hV,
    ← LQGMetric.GM.lenFun_internal D hP hV]
  unfold LQGMetric.GM.lenFun
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  apply le_iSup_of_le p
  let n := p.1
  let u := p.2.1
  have hus : ∀ i, u i ∈ Icc a b := p.2.2.2
  calc
    ∑ i ∈ Finset.range n, E.internal V (P (u (i + 1))) (P (u i))
      ≤ ∑ i ∈ Finset.range n, k * D.internal V (P (u (i + 1))) (P (u i)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hcmp _ (hV (hus (i + 1))) _ (hV (hus i))
    _ = k * ∑ i ∈ Finset.range n, D.internal V (P (u (i + 1))) (P (u i)) := by
      rw [Finset.mul_sum]

theorem aroundDist_le_mul_of_internal_le
    (D E : ContMetric) (V A B C : Set ℂ) (hAV : A ⊆ V)
    (k : ℝ≥0∞) (hk0 : k ≠ 0) (hkTop : k ≠ ∞)
    (hcmp : ∀ z ∈ V, ∀ w ∈ V, E.internal V z w ≤ k * D.internal V z w) :
    E.aroundDist A B C ≤ k * D.aroundDist A B C := by
  unfold ContMetric.aroundDist
  simp only [ENNReal.mul_iInf_of_ne hk0 hkTop]
  refine iInf_mono fun a => iInf_mono fun b => iInf_mono fun P =>
    iInf_mono fun hab => iInf_mono fun hPc => iInf_mono fun hcar =>
      iInf_mono fun hdisc => ?_
  exact len_le_mul_of_internal_le D E V k hcmp P a b hPc
    (fun t ht => hAV (hcar ⟨t, ht, rfl⟩))

end SupercriticalLQGUniqueness.B2.DG20Lim
