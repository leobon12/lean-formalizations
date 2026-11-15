/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TestKernel
import InteractingSLE.Spec.Supplement.GB9Stop

/-!
# GW2's actual candidate tests from a crossing before the buffer

Packet PROVE-GW2-TEST; follow-up 5 (4.1)--(4.2). The dense-time step reuses
`GB9Stop.exists_mem_band_interior`. The tests inspect the actual trace at the
prescribed time. No assertion about its value at a first hull-hit time is used.
These helpers leave the conditional crossing estimate and the joint-chart
identification as explicit inputs; they do not prove `GW2RootTestStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem

namespace TestCross

/-- The image of a dense set of nonnegative times, together with the nonpositive
real line, is dense in the real line. -/
theorem dense_coe_union_nonpos {Q : Set ℝ≥0} (hQ : Dense Q) :
    Dense (((↑) : ℝ≥0 → ℝ) '' Q ∪ Iic 0) := by
  intro t
  by_cases ht : t ≤ 0
  · exact subset_closure (Or.inr ht)
  · have ht0 : 0 ≤ t := (lt_of_not_ge ht).le
    have hi : t ∈ closure (((↑) : ℝ≥0 → ℝ) '' Q) :=
      image_closure_subset_closure_image continuous_subtype_val
        ⟨⟨t, ht0⟩, hQ _, rfl⟩
    exact closure_mono subset_union_left hi

/-- The test at a prescribed candidate: strictly after the crossing and before
the finite buffer, with an interior tip and the driver in the selected band. -/
def candidateTest {Ω : Type*} (X : Ω → ℝ → ℝ) (γ : Ω → ℝ → ℂ)
    (S F : Ω → ℝ) (I : Set ℝ) (q : ℝ≥0) : Set Ω :=
  {ω | S ω < q ∧ (q : ℝ) < F ω ∧ γ ω q ∈ H ∧ X ω q ∈ I}

/-- Candidate tests are measurable in any sigma-algebra in which their four
observations are measurable. This applies to the extended schedule record. -/
theorem measurableSet_candidateTest {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ → ℝ} {γ : Ω → ℝ → ℂ} {S F : Ω → ℝ} {I : Set ℝ}
    {q : ℝ≥0} (hS : Measurable S) (hF : Measurable F)
    (hX : Measurable fun ω => X ω q) (hγ : Measurable fun ω => γ ω q)
    (hI : MeasurableSet I) : MeasurableSet (candidateTest X γ S F I q) :=
  (measurableSet_lt hS measurable_const).inter
    ((measurableSet_lt measurable_const hF).inter
      ((hγ QuantumZipper.isOpen_H.measurableSet).inter (hX hI)))

/-- The pathwise candidate step, for the packet's dense `Q : Set ℝ≥0`.
It is a small carrier adapter to the existing real-time band lemma. -/
theorem exists_candidate {X : ℝ → ℝ} {γ : ℝ → ℂ} {S F : ℝ}
    (hS : 0 ≤ S) (hSF : S < F) (hX : ContinuousAt X S) {I : Set ℝ}
    (hI : IsOpen I) (hXS : X S ∈ I) (hγ : ContinuousOn γ (Ioo S F))
    (hnull : volume {t | t ∈ Ioo S F ∧ γ t ∉ H} = 0)
    {Q : Set ℝ≥0} (hQ : Dense Q) :
    ∃ q : Q, S < (q : ℝ≥0) ∧ ((q : ℝ≥0) : ℝ) < F ∧
      γ q ∈ H ∧ X q ∈ I := by
  obtain ⟨q, hq, hSq, hqF, hqH, hqI⟩ :=
    Supp8.GB9Stop.exists_mem_band_interior hSF hX hI hXS hγ hnull
      (dense_coe_union_nonpos hQ)
  rcases hq with ⟨q, hqQ, rfl⟩ | hq0
  · exact ⟨⟨q, hqQ⟩, hSq, hqF, hqH, hqI⟩
  · exact False.elim ((not_lt_of_ge (hq0.trans hS)) hSq)

section Measure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {X : Ω → ℝ → ℝ} {γ : Ω → ℝ → ℂ} {S F : Ω → ℝ} {I : Set ℝ}
  {Q : Set ℝ≥0}

/-- Up to null sets, the union of all candidate tests is exactly the crossing
before the buffer. No measurability of the path-regularity predicate is needed. -/
theorem candidate_union_ae_eq (μ : Measure Ω) (hQ : Dense Q) (hI : IsOpen I)
    (hreg : ∀ᵐ ω ∂μ, S ω < F ω →
      0 ≤ S ω ∧ ContinuousAt (X ω) (S ω) ∧ X ω (S ω) ∈ I ∧
      ContinuousOn (γ ω) (Ioo (S ω) (F ω)) ∧
      volume {t | t ∈ Ioo (S ω) (F ω) ∧ γ ω t ∉ H} = 0) :
    (⋃ q : Q, candidateTest X γ S F I q) =ᵐ[μ] {ω | S ω < F ω} := by
  filter_upwards [hreg] with ω hω
  apply propext
  constructor
  · intro htest
    obtain ⟨q, hq⟩ := mem_iUnion.1 htest
    exact hq.1.trans hq.2.1
  · intro hSF
    obtain ⟨hS, hX, hXS, hγ, hnull⟩ := hω hSF
    obtain ⟨q, hq⟩ := exists_candidate hS hSF hX hI hXS hγ hnull hQ
    exact mem_iUnion.2 ⟨q, hq⟩

/-- Equality of the probabilities of the candidate union and crossing event. -/
theorem measure_candidate_union (μ : Measure Ω) (hQ : Dense Q) (hI : IsOpen I)
    (hreg : ∀ᵐ ω ∂μ, S ω < F ω →
      0 ≤ S ω ∧ ContinuousAt (X ω) (S ω) ∧ X ω (S ω) ∈ I ∧
      ContinuousOn (γ ω) (Ioo (S ω) (F ω)) ∧
      volume {t | t ∈ Ioo (S ω) (F ω) ∧ γ ω t ∉ H} = 0) :
    μ (⋃ q : Q, candidateTest X γ S F I q) = μ {ω | S ω < F ω} :=
  measure_congr (candidate_union_ae_eq μ hQ hI hreg)

end Measure

section Conditional

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {Q : Set ℝ≥0}

/-- The dense-time identity holds under almost every retained conditional law.
This transfers the global path-regularity assertion without assuming that it is
a measurable event of the product sigma-algebra on paths. -/
theorem ae_condExpKernel_candidate_union (h𝒢 : 𝒢 ≤ mΩ) (hQ : Dense Q)
    {X : Ω → ℝ → ℝ} {γ : Ω → ℝ → ℂ} {S F : Ω → ℝ} {I : Set ℝ}
    (hI : IsOpen I)
    (hreg : ∀ᵐ ω ∂P, S ω < F ω →
      0 ≤ S ω ∧ ContinuousAt (X ω) (S ω) ∧ X ω (S ω) ∈ I ∧
      ContinuousOn (γ ω) (Ioo (S ω) (F ω)) ∧
      volume {t | t ∈ Ioo (S ω) (F ω) ∧ γ ω t ∉ H} = 0) :
    ∀ᵐ ω₀ ∂P, condExpKernel P 𝒢 ω₀ (⋃ q : Q, candidateTest X γ S F I q) =
      condExpKernel P 𝒢 ω₀ {ω | S ω < F ω} := by
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hreg] with ω₀ hω₀
  exact measure_candidate_union _ hQ hI hω₀

/-- A countable family of conditional crossing estimates gives the crossing
field of `TestClaims` for the actual dense-time candidate tests. -/
theorem ae_exists_candidate_probability (h𝒢 : 𝒢 ≤ mΩ) (hQ : Dense Q)
    {R : Set Ω} {X : ℕ → Ω → ℝ → ℝ} {γ : ℕ → Ω → ℝ → ℂ}
    {S F : ℕ → Ω → ℝ} {I : ℕ → Set ℝ} (hI : ∀ a, IsOpen (I a))
    (hreg : ∀ a, ∀ᵐ ω ∂P, S a ω < F a ω →
      0 ≤ S a ω ∧ ContinuousAt (X a ω) (S a ω) ∧ X a ω (S a ω) ∈ I a ∧
      ContinuousOn (γ a ω) (Ioo (S a ω) (F a ω)) ∧
      volume {t | t ∈ Ioo (S a ω) (F a ω) ∧ γ a ω t ∉ H} = 0)
    {ε : ℝ≥0∞}
    (hcross : ∀ᵐ ω ∂P, ω ∈ R → ∃ a,
      1 - ε < condExpKernel P 𝒢 ω {ω' | S a ω' < F a ω'}) :
    ∀ᵐ ω ∂P, ω ∈ R → ∃ a, 1 - ε <
      condExpKernel P 𝒢 ω (⋃ q : Q, candidateTest (X a) (γ a) (S a) (F a) (I a) q) := by
  have heq := ae_all_iff.2 fun a =>
    ae_condExpKernel_candidate_union h𝒢 hQ (hI a) (hreg a)
  filter_upwards [heq, hcross] with ω hωeq hωcross hωR
  obtain ⟨a, ha⟩ := hωcross hωR
  exact ⟨a, (hωeq a).symm ▸ ha⟩

end Conditional

end TestCross

end InteractingSLE.Theorem14.GW2TipSystem
