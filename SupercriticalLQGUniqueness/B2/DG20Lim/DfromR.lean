import SupercriticalLQGUniqueness.B2.DG20Lim.RData

 






set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

namespace RData

 


theorem across_outer_le_inner (R : RData) (a b c d : RatCircle)
    (hdisj : ∀ i j : Fin 4, i ≠ j →
      Disjoint ((![a, b, c, d] : Fin 4 → RatCircle) i).toSet
        ((![a, b, c, d] : Fin 4 → RatCircle) j).toSet)
    (hb : Disconnects b.toSet a.toSet c.toSet)
    (hc : Disconnects c.toSet b.toSet d.toSet) :
    R.across b c ≤ R.across a d := by
  have hsep : ∀ j : ℕ, (hj : 0 < j) → (hk : j < 3) →
      Disconnects ((![a, b, c, d] : Fin 4 → RatCircle) ⟨j, by omega⟩).toSet
        ((![a, b, c, d] : Fin 4 → RatCircle) ⟨j - 1, by omega⟩).toSet
        ((![a, b, c, d] : Fin 4 → RatCircle) ⟨j + 1, by omega⟩).toSet := by
    intro j hj hk
    interval_cases j
    · simpa using hb
    · simpa using hc
  have h := R.chain_lower 3 (![a, b, c, d]) hdisj hsep
  simp [Fin.sum_univ_succ] at h
  have hle : R.across b c ≤ R.across a b + (R.across b c + R.across c d) := by
    calc
      R.across b c ≤ R.across b c + R.across c d :=
        le_add_of_nonneg_right zero_le
      _ ≤ R.across a b + (R.across b c + R.across c d) :=
        le_add_of_nonneg_left zero_le
  exact hle.trans h

 
def DfromR (R : RData) (z w : ℂ) : ℝ≥0∞ :=
  if z = w then 0 else
    ⨆ (O : RatCircle) (_ : O.Surrounds z)
      (P : RatCircle) (_ : P.Surrounds w)
      (_ : Disjoint O.closedDisk P.closedDisk), R.across O P

@[simp] theorem DfromR_self (R : RData) (z : ℂ) : R.DfromR z z = 0 := by
  simp [DfromR]

theorem across_le_DfromR (R : RData) {z w : ℂ} (hzw : z ≠ w)
    (O P : RatCircle) (hO : O.Surrounds z) (hP : P.Surrounds w)
    (hdisj : Disjoint O.closedDisk P.closedDisk) : R.across O P ≤ R.DfromR z w := by
  simp only [DfromR, hzw, ↓reduceIte]
  exact le_iSup_of_le O (le_iSup_of_le hO (le_iSup_of_le P
    (le_iSup_of_le hP (le_iSup_of_le hdisj le_rfl))))

theorem DfromR_pos_of_pair (R : RData) {z w : ℂ} (hzw : z ≠ w)
    (O P : RatCircle) (hO : O.Surrounds z) (hP : P.Surrounds w)
    (hdisj : Disjoint O.closedDisk P.closedDisk) : 0 < R.DfromR z w := by
  have hcircles : Disjoint O.toSet P.toSet :=
    hdisj.mono Metric.sphere_subset_closedBall Metric.sphere_subset_closedBall
  exact (R.across_pos O P hcircles).trans_le
    (R.across_le_DfromR hzw O P hO hP hdisj)

theorem DfromR_symm (R : RData) (z w : ℂ) : R.DfromR z w = R.DfromR w z := by
  by_cases h : z = w
  · subst w; rfl
  apply le_antisymm
  · simp only [DfromR, h, ↓reduceIte]
    apply iSup_le; intro O
    apply iSup_le; intro hO
    apply iSup_le; intro P
    apply iSup_le; intro hP
    apply iSup_le; intro hdisj
    rw [R.across_symm]
    exact R.across_le_DfromR (Ne.symm h) P O hP hO hdisj.symm
  · simp only [DfromR, Ne.symm h, ↓reduceIte]
    apply iSup_le; intro O
    apply iSup_le; intro hO
    apply iSup_le; intro P
    apply iSup_le; intro hP
    apply iSup_le; intro hdisj
    rw [R.across_symm]
    exact R.across_le_DfromR h P O hP hO hdisj.symm

 

theorem tendsto_DfromR_of_cofinal (R : RData) {z w : ℂ} (hzw : z ≠ w)
    (O P : ℕ → RatCircle)
    (hvalid : ∀ᶠ n in Filter.atTop,
      (O n).Surrounds z ∧ (P n).Surrounds w ∧
        Disjoint (O n).closedDisk (P n).closedDisk)
    (hcofinal : ∀ A B : RatCircle, A.Surrounds z → B.Surrounds w →
      Disjoint A.closedDisk B.closedDisk →
        ∀ᶠ n in Filter.atTop, R.across A B ≤ R.across (O n) (P n)) :
    Filter.Tendsto (fun n => R.across (O n) (P n)) Filter.atTop
      (nhds (R.DfromR z w)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    simp only [DfromR, hzw, ↓reduceIte, lt_iSup_iff] at ha
    obtain ⟨A, hA, B, hB, hAB, hab⟩ := ha
    filter_upwards [hcofinal A B hA hB hAB] with n hn
    exact hab.trans_le hn
  · intro b hb
    filter_upwards [hvalid] with n hn
    exact (R.across_le_DfromR hzw (O n) (P n) hn.1 hn.2.1 hn.2.2).trans_lt hb

end RData
end SupercriticalLQGUniqueness.B2.DG20Lim
