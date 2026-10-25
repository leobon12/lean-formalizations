import SupercriticalLQGUniqueness.B2.DG20Lim.NestedCrossingDistance
import SupercriticalLQGUniqueness.B2.DG20Lim.GoodCircleConv

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.nested_good_annulus_costs_tendsto_zero
    (R : RData) (B : ℕ → RatAnnulus) (C : ℝ≥0∞)
    (hC : C ≠ ∞) (z w : ℂ) (hzw : z ≠ w)
    (hfinite : R.DfromR z w ≠ ∞)
    (hGood : ∀ n, (B n).inner.Surrounds z ∧
      R.around (B n) ≤ C * R.across (B n).inner (B n).outer)
    (hnest : ∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer)
    (hrad : Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n => R.across (B n).inner (B n).outer) atTop (𝓝 0) ∧
    Tendsto (fun n => R.around (B n)) atTop (𝓝 0) := by
  have houter : ∀ᶠ n in atTop, (B n).outer.Surrounds z := by
    filter_upwards with n
    exact RatAnnulus.outer_surrounds_of_inner (hGood n).1
  have houtside : ∀ᶠ n in atTop, w ∉ (B n).outer.closedDisk := by
    have hzopen : z ∈ ({w} : Set ℂ)ᶜ := by simpa using hzw
    have hev := RatCircle.eventually_closedDisk_subset_open
      isClosed_singleton.isOpen_compl hzopen
      (fun n => (B n).outer) houter hrad
    filter_upwards [hev] with n hn hw
    exact (hn hw) (by simp)
  obtain ⟨n₀, hw₀⟩ := houtside.exists
  let A : ℕ → RatAnnulus := fun n => B (n + n₀)
  have hnestA (n : ℕ) :
      (A n).inner.SurroundsCircle (A (n + 1)).outer := by
    simpa only [A, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnest (n + n₀)
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range N,
        R.across (A n).inner (A n).outer) ≤ R.DfromR z w := by
    cases N with
    | zero => simp
    | succ N =>
        exact R.nested_crossing_sum_le_DfromR A hnestA z w hzw
          (fun n => (hGood (n + n₀)).1) (by simpa only [A, Nat.zero_add] using hw₀) N
  have hconv := R.good_annulus_costs_tendsto_zero A C (R.DfromR z w)
    hC hfinite (fun n => (hGood (n + n₀)).2) hsum
  exact ⟨(tendsto_add_atTop_iff_nat n₀).mp hconv.1,
    (tendsto_add_atTop_iff_nat n₀).mp hconv.2⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
