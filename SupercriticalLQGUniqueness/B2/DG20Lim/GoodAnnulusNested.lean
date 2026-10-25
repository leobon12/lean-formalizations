import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusSequence
import SupercriticalLQGUniqueness.B2.DG20Lim.Geometry

 

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RatAnnulus.outer_surrounds_of_inner {A : RatAnnulus} {z : ℂ}
    (h : A.inner.Surrounds z) : A.outer.Surrounds z := by
  refine ⟨A.nested.1, ?_⟩
  exact A.nested.2 (A.inner.openDisk_subset_closedDisk h.2)

theorem RData.exists_nested_good_annulus_sequence
    (R : RData) (C : ℝ≥0∞)
    (hsite : ∀ M : ℕ, ∀ᶠ K in atTop,
      ∀ v ∈ dyadicLatticeBox M K, dyadicGoodAt R C K v)
    (z : ℂ) :
    ∃ B : ℕ → RatAnnulus,
      (∀ n, (B n).inner.Surrounds z ∧
        R.around (B n) ≤ C * R.across (B n).inner (B n).outer) ∧
      (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
      Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0) := by
  classical
  obtain ⟨A, hgood, hrad⟩ := R.exists_shrinking_good_annulus_sequence C hsite z
  let Good : ℕ → Prop := fun n => (A n).inner.Surrounds z ∧
    R.around (A n) ≤ C * R.across (A n).inner (A n).outer
  have houter : ∀ᶠ n in atTop, (A n).outer.Surrounds z := by
    filter_upwards [hgood] with n hn
    exact RatAnnulus.outer_surrounds_of_inner hn.1
  have hstep (n : ℕ) (hn : Good n) :
      ∃ m : ℕ, n < m ∧ Good m ∧
        (A n).inner.SurroundsCircle (A m).outer := by
    have hnest := RatCircle.eventually_nested hn.1
      (fun m => (A m).outer) houter hrad
    obtain ⟨m, ⟨hm, hgt⟩, hnm⟩ :=
      ((hgood.and (eventually_gt_atTop n)).and hnest).exists
    exact ⟨m, hgt, hm, hnm⟩
  obtain ⟨n₀, hn₀⟩ := hgood.exists
  let next (q : {n : ℕ // Good n}) : {m : ℕ // Good m} :=
    ⟨(hstep q.1 q.2).choose, (hstep q.1 q.2).choose_spec.2.1⟩
  let f : ℕ → {n : ℕ // Good n} :=
    fun n => Nat.rec (⟨n₀, hn₀⟩ : {n : ℕ // Good n})
      (fun _ q => next q) n
  let φ : ℕ → ℕ := fun n => (f n).1
  have hφstep (n : ℕ) : φ n < φ (n + 1) := by
    exact (hstep (f n).1 (f n).2).choose_spec.1
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ hφstep
  let B : ℕ → RatAnnulus := fun n => A (φ n)
  refine ⟨B, ?_, ?_, ?_⟩
  · intro n
    exact (f n).2
  · intro n
    exact (hstep (f n).1 (f n).2).choose_spec.2.2
  · exact hrad.comp hφ.tendsto_atTop

end SupercriticalLQGUniqueness.B2.DG20Lim
