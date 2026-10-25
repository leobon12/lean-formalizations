import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3
import Mathlib




 





set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Assembly.Collision
open LQGMetric (DistC)

theorem dyadic_collision {n : ℕ} (hn : 4 < n)
    {A B : Finset ℕ} (hA : A ⊆ Finset.Icc n (2*n))
    (hB : B ⊆ Finset.Icc n (2*n))
    (ha : 3*n ≤ 4*A.card) (hb : 3*n ≤ 4*B.card) :
    (A ∩ B).Nonempty := by
  by_contra hempty
  have hi : A ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hdisj : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr hi
  have hunion : A ∪ B ⊆ Finset.Icc n (2*n) := Finset.union_subset hA hB
  have hcard : (A ∪ B).card ≤ n + 1 := by
    have hc := Finset.card_le_card hunion
    simp only [Nat.card_Icc] at hc
    omega
  have hsum : A.card + B.card ≤ n + 1 := by
    simpa only [Finset.card_union_of_disjoint hdisj] using hcard
  omega

private def rad (k : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨(8 : ℝ) ^ (-(k : ℤ)), zpow_pos (show (0 : ℝ) < 8 by norm_num) _⟩

private def upperGood {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric) (ξ Q : ℝ)
    (a : Set.Ioo (3/4 : ℝ) 1) (θ C : Set.Ioi (0 : ℝ))
    (p : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc n (2*n)).filter fun k =>
    ENNReal.ofReal p ≤ P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (rad k) a C θ (h ω)}

private def lowerGood {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (κ C : Set.Ioi (0 : ℝ)) (n : ℕ) : Finset ℕ :=
  (Finset.Icc n (2*n)).filter fun k =>
    ENNReal.ofReal κ ≤ P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) (rad k) κ C}

theorem collision_of_section_conclusions
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ Q : ℝ)
    (a : Set.Ioo (3/4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ))
    (p : Set.Ioo (0 : ℝ) 1) (κ Cmid Ctop : Set.Ioi (0 : ℝ))
    (n₁ n₂ : ℕ)
    (hUpper : ∀ n ≥ n₁,
      3*n ≤ 4*(upperGood P h D D' ξ Q a θ Ctop p n).card)
    (hLower : ∀ n ≥ n₂,
      3*n ≤ 4*(lowerGood P h D D' κ Cmid n).card)
    (hCompare : ∀ k : ℕ,
      ENNReal.ofReal κ ≤
        P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) (rad k) κ Cmid} →
      P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (rad k) a Ctop θ (h ω)} <
        ENNReal.ofReal ((p : ℝ)/2)) : False := by
  let n := max (max n₁ n₂) 5
  have hn : 4 < n := by dsimp [n]; omega
  have hn₁ : n₁ ≤ n := by dsimp [n]; omega
  have hn₂ : n₂ ≤ n := by dsimp [n]; omega
  have hi := dyadic_collision hn
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (hUpper n hn₁) (hLower n hn₂)
  obtain ⟨k, hk⟩ := hi
  have hU : ENNReal.ofReal (p : ℝ) ≤
      P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (rad k) a Ctop θ (h ω)} :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hk).1).2
  have hG : ENNReal.ofReal κ ≤
      P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) (rad k) κ Cmid} :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hk).2).2
  have hpHalf : ENNReal.ofReal ((p : ℝ)/2) < ENNReal.ofReal (p : ℝ) := by
    exact (ENNReal.ofReal_lt_ofReal_iff p.property.1).2
      (by have hp := p.property.1; linarith)
  exact not_lt_of_ge hU (lt_trans (hCompare k hG) hpHalf)


end SupercriticalLQGUniqueness.Uniqueness.Assembly.Collision
