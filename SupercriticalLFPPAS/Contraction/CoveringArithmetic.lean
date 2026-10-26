import SupercriticalLFPPAS.Contraction.Hull

/-! The quantitative conversion from a selected interval family to the fixed fraction
`λ = 1/(5A)` used in Lemma 4.1. -/

set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLFPPAS.Contraction

/-- The audited covering bounds imply the good subintervals occupy at least the fraction
`1/(5A)` of the final hull. The factor five leaves room for the endpoint intervals extending
past the covered segment. -/
theorem d4_good_length_fraction {A J S ell G lam : ℝ}
    (hA : 0 < A) (hS : 0 ≤ S)
    (hSle : S ≤ ell) (hell : ell ≤ J + S) (hJ : J ≤ 3 * S)
    (hG : S / A ≤ G) (hlam : lam = 1 / (5 * A)) :
    S ≤ ell ∧ ell ≤ 4 * S ∧ lam * ell ≤ G := by
  have hell4 : ell ≤ 4 * S := by linarith
  have hden₁ : 0 < 5 * A := by positivity
  have hfrac : ell / (5 * A) ≤ S / A := by
    apply (div_le_div_iff₀ hden₁ hA).2
    have hmul : ell * A ≤ (4 * S) * A :=
      mul_le_mul_of_nonneg_right hell4 hA.le
    have hSA : 0 ≤ S * A := mul_nonneg hS hA.le
    nlinarith
  refine ⟨hSle, hell4, ?_⟩
  calc
    lam * ell = ell / (5 * A) := by rw [hlam]; field_simp
    _ ≤ S / A := hfrac
    _ ≤ G := hG

/-- The finite greedy cover, hull bounds, and per-interval good-crossing estimates give the
audited positive fraction `G ≥ λℓ` and the upper bound `G ≤ ℓ`. -/
theorem d4_greedy_cover_good_fraction
    {F : Finset D4Interval} {l : List D4Interval} {a b A lam : ℝ}
    (hpositive : ∀ I ∈ F, I.1 < I.2) (hRun : D4GreedyRun F l)
    (hab : a ≤ b) (hcover : Icc a b ⊆ ⋃ I ∈ F, Ioo I.1 I.2)
    (hmeet : ∀ I ∈ F, (Ioo I.1 I.2 ∩ Icc a b).Nonempty)
    (hA : 0 < A) (hlam : lam = 1 / (5 * A))
    (goodLength : D4Interval → ℝ)
    (hgoodLower : ∀ I ∈ l.toFinset, d4IntervalLength I / A ≤ goodLength I)
    (hgoodUpper : ∀ I ∈ l.toFinset, goodLength I ≤ d4IntervalLength I) :
    ∃ left right, D4IntervalHull l.toFinset a b left right ∧
      (∑ I ∈ l.toFinset, d4IntervalLength I) ≤ right - left ∧
      right - left ≤ 4 * ∑ I ∈ l.toFinset, d4IntervalLength I ∧
      (∑ I ∈ l.toFinset, goodLength I) ≤ right - left ∧
      lam * (right - left) ≤ ∑ I ∈ l.toFinset, goodLength I := by
  classical
  let U := l.toFinset
  obtain ⟨hsub, _, _, _⟩ := d4_greedyRun_spec hpositive hRun
  have hpositiveU : ∀ I ∈ U, I.1 < I.2 := by
    intro I hI
    exact hpositive I (hsub I (List.mem_toFinset.mp hI))
  obtain ⟨left, right, hhull⟩ := d4_intervalHull_exists U a b
  have hdisj : PairwiseDisjoint (U : Set D4Interval) d4IntervalBall :=
    d4_greedyRun_pairwiseDisjoint hpositive hRun
  have hmeetU : ∀ I ∈ U, (Ioo I.1 I.2 ∩ Icc a b).Nonempty := by
    intro I hI
    exact hmeet I (hsub I (List.mem_toFinset.mp hI))
  have hJ : b - a ≤ 3 * ∑ I ∈ U, d4IntervalLength I :=
    d4_greedyRun_interval_length_bound hpositive hRun hcover
  have hS : 0 ≤ ∑ I ∈ U, d4IntervalLength I := by
    apply Finset.sum_nonneg
    intro I hI
    dsimp [d4IntervalLength]
    linarith [hpositive I (hsub I (List.mem_toFinset.mp hI))]
  have hlower : (∑ I ∈ U, d4IntervalLength I) ≤ right - left :=
    d4_hull_lower_length_bound hpositiveU (by simpa only [U] using hdisj)
      hhull hab
  have hupper : right - left ≤ (b - a) + ∑ I ∈ U, d4IntervalLength I :=
    d4_hull_upper_length_bound hpositiveU (by simpa only [U] using hdisj)
      hhull hab hmeetU
  have hupper4 : right - left ≤ 4 * ∑ I ∈ U, d4IntervalLength I := by
    linarith
  have hgoodUpperSum : (∑ I ∈ U, goodLength I) ≤
      ∑ I ∈ U, d4IntervalLength I :=
    Finset.sum_le_sum (fun I hI => hgoodUpper I hI)
  have hgoodLowerSum :
      (∑ I ∈ U, d4IntervalLength I) / A ≤ ∑ I ∈ U, goodLength I := by
    calc
      (∑ I ∈ U, d4IntervalLength I) / A =
          ∑ I ∈ U, d4IntervalLength I / A := Finset.sum_div U _ A
      _ ≤ ∑ I ∈ U, goodLength I :=
        Finset.sum_le_sum (fun I hI => hgoodLower I hI)
  have hfrac := d4_good_length_fraction hA hS hlower hupper hJ
    hgoodLowerSum hlam
  refine ⟨left, right, hhull, hlower, hupper4, ?_, hfrac.2.2⟩
  exact hgoodUpperSum.trans hlower

end SupercriticalLFPPAS.Contraction
