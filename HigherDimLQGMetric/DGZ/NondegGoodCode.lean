import HigherDimLQGMetric.DGZ.NondegCrossAvoid

/-! Countable disjoint codes for domains containing one sphere and avoiding another. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

def nd_GoodIndex (rGrid r other : ℝ) (j : ℕ) : Type :=
  {i : nd_DomainIndex d rGrid //
    i.1.1 = j ∧ lsph (0 : Rd d) r ⊆ nd_domain rGrid i ∧
      Disjoint (nd_domain rGrid i) (lsph (0 : Rd d) other)}

instance (rGrid r other : ℝ) (j : ℕ) : Countable (nd_GoodIndex (d := d) rGrid r other j) := by
  unfold nd_GoodIndex
  infer_instance

def nd_goodCodeEvent (rGrid r other : ℝ) (j : ℕ)
    (i : nd_GoodIndex (d := d) rGrid r other j) : Set (nd_Joint d rGrid) :=
  nd_selectedEq rGrid r i.1.1.1 i.1.1.2

theorem nd_measurableSet_goodCodeEvent (rGrid r other : ℝ) (j : ℕ)
    (i : nd_GoodIndex (d := d) rGrid r other j) :
    MeasurableSet (nd_goodCodeEvent rGrid r other j i) :=
  nd_measurableSet_selectedEq rGrid r i.1.1.1 i.1.1.2

theorem nd_pairwise_disjoint_goodCodeEvent (rGrid r other : ℝ) (j : ℕ) :
    Pairwise (fun i₁ i₂ : nd_GoodIndex (d := d) rGrid r other j =>
      Disjoint (nd_goodCodeEvent rGrid r other j i₁)
        (nd_goodCodeEvent rGrid r other j i₂)) := by
  intro i₁ i₂ hne
  rw [Set.disjoint_left]
  intro s hs₁ hs₂
  have heq : i₁.1 = i₂.1 :=
    nd_selectedIndex_unique i₁.1 i₂.1 s (i₁.2.1.trans i₂.2.1.symm) hs₁ hs₂
  exact hne (Subtype.ext heq)

theorem nd_measure_iUnion_goodCodeEvent (rGrid r other : ℝ) (j : ℕ)
    (μ : Measure (nd_Joint d rGrid)) :
    μ (⋃ i : nd_GoodIndex (d := d) rGrid r other j,
      nd_goodCodeEvent rGrid r other j i) =
      ∑' i : nd_GoodIndex (d := d) rGrid r other j,
        μ (nd_goodCodeEvent rGrid r other j i) :=
  measure_iUnion (nd_pairwise_disjoint_goodCodeEvent rGrid r other j)
    (nd_measurableSet_goodCodeEvent rGrid r other j)

theorem nd_tsum_goodCodeEvent_le (rGrid r other : ℝ) (j : ℕ)
    (μ : Measure (nd_Joint d rGrid)) (Z Good : Set (nd_Joint d rGrid))
    (hGood : ∀ᵐ s ∂μ, s ∈ Good)
    (hcode : ∀ s ∈ Good, ∀ i : nd_GoodIndex (d := d) rGrid r other j,
      s ∈ nd_goodCodeEvent rGrid r other j i → s ∈ Z) :
    (∑' i : nd_GoodIndex (d := d) rGrid r other j,
      μ (nd_goodCodeEvent rGrid r other j i)) ≤ μ Z := by
  rw [← nd_measure_iUnion_goodCodeEvent rGrid r other j μ]
  apply measure_mono_ae
  filter_upwards [hGood] with s hs hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  exact hcode s hs i hi

theorem nd_domainSeparated_disjoint (rGrid : ℝ)
    (i₁ i₂ : nd_DomainIndex d rGrid)
    (hsep : nd_domainSeparated rGrid i₁ i₂) :
    Disjoint (nd_domain rGrid i₁) (nd_domain rGrid i₂) := by
  obtain ⟨δ, hδ, hgap⟩ := hsep
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have h := hgap x hx₁ x hx₂
  simp only [sub_self, norm_zero] at h
  exact (not_le_of_gt hδ) h

end HigherDimLQGMetric.DGZ
