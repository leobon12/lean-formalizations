import HigherDimLQGMetric.DGZ.NondegGoodCode

/-! The countable pair sum used in the zero-one law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

def nd_positiveCrossEvent (rGrid r : ℝ) : Set (nd_Joint d rGrid) :=
  {s | 0 < nd_crossPhi 0 (2 * r) r s.1}

theorem nd_isOpen_positiveCrossEvent (rGrid r : ℝ) :
    IsOpen (nd_positiveCrossEvent (d := d) rGrid r) :=
  isOpen_lt continuous_const ((nd_continuous_crossPhi 0 (2 * r) r).comp continuous_fst)

def nd_sepPairEvent (rGrid r : ℝ) (j : ℕ) : Set (nd_Joint d rGrid) := by
  classical
  exact ⋃ p : nd_GoodIndex (d := d) rGrid r (2 * r) j ×
      nd_GoodIndex (d := d) rGrid (2 * r) r j,
    if nd_domainSeparated rGrid p.1.1 p.2.1 then
      nd_goodCodeEvent rGrid r (2 * r) j p.1 ∩
        nd_goodCodeEvent rGrid (2 * r) r j p.2
    else ∅

open Classical in theorem nd_sepPairEvent_eq (rGrid r : ℝ) (j : ℕ) :
    nd_sepPairEvent (d := d) rGrid r j =
      ⋃ p : nd_GoodIndex (d := d) rGrid r (2 * r) j ×
          nd_GoodIndex (d := d) rGrid (2 * r) r j,
        if nd_domainSeparated rGrid p.1.1 p.2.1 then
          nd_goodCodeEvent rGrid r (2 * r) j p.1 ∩
            nd_goodCodeEvent rGrid (2 * r) r j p.2
        else ∅ := rfl

theorem nd_measurableSet_sepPairEvent (rGrid r : ℝ) (j : ℕ) :
    MeasurableSet (nd_sepPairEvent (d := d) rGrid r j) := by
  classical
  unfold nd_sepPairEvent
  apply MeasurableSet.iUnion
  intro p
  split_ifs
  · exact (nd_measurableSet_goodCodeEvent rGrid r (2 * r) j p.1).inter
      (nd_measurableSet_goodCodeEvent rGrid (2 * r) r j p.2)
  · exact MeasurableSet.empty

open Classical in theorem nd_measure_pairUnion_le_mul
    {α β X : Type*} [Countable α] [Countable β] [MeasurableSpace X]
    (μ : Measure X) (A : α → Set X) (B : β → Set X) (sep : α → β → Prop)
    (hfac : ∀ i k, sep i k → μ (A i ∩ B k) = μ (A i) * μ (B k))
    {M : ℝ≥0∞} (hA : (∑' i, μ (A i)) ≤ M)
    (hB : (∑' k, μ (B k)) ≤ M) :
    μ (⋃ p : α × β, if sep p.1 p.2 then A p.1 ∩ B p.2 else ∅) ≤
      M * M := by
  classical
  let F (p : α × β) := if sep p.1 p.2 then A p.1 ∩ B p.2 else ∅
  have hterm (p : α × β) : μ (F p) ≤ μ (A p.1) * μ (B p.2) := by
    by_cases hsep : sep p.1 p.2
    · simpa [F, hsep] using (hfac p.1 p.2 hsep).le
    · simp [F, hsep]
  calc
    μ (⋃ p : α × β, if sep p.1 p.2 then A p.1 ∩ B p.2 else ∅) =
        μ (⋃ p, F p) := rfl
    _ ≤ ∑' p, μ (F p) := measure_iUnion_le _
    _ ≤ ∑' p, μ (A p.1) * μ (B p.2) := ENNReal.tsum_le_tsum hterm
    _ = (∑' i, μ (A i)) * (∑' k, μ (B k)) := by
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right]
    _ ≤ M * M := mul_le_mul hA hB (by positivity) (by positivity)

end HigherDimLQGMetric.DGZ
