import HigherDimLQGMetric.Locality.JointSkorokhod
import HigherDimLQGMetric.Locality.CountableJointTight
import HigherDimLQGMetric.Locality.FiniteArray

/-! A finite collection of internal metric coordinates can be coupled with
the marked field and full LFPP metric on one Skorokhod space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_exists_finite_internal_joint_skorokhod
    {d : ℕ} {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    {A Ω : Type} [MeasurableSpace Ω]
    [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [BorelSpace A] [PolishSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → A)
    (Y₁ : ℕ → Ω → ∀ i : S,
      C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ))
    (Y₂ : ℕ → Ω → ∀ j : T,
      C((W' j.1 : Set (Rd d)) × (W' j.1 : Set (Rd d)), ℝ))
    (hX : ∀ n, AEMeasurable (X n) P)
    (hY₁ : ∀ n i, AEMeasurable (fun ω => Y₁ n ω i) P)
    (hY₂ : ∀ n j, AEMeasurable (fun ω => Y₂ n ω j) P)
    (hXT : IsTightMeasureSet {ν : Measure A | ∃ n, ν = P.map (X n)})
    (hYT₁ : ∀ i : S, IsTightMeasureSet
      {ν : Measure C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ) |
        ∃ n, ν = P.map (fun ω => Y₁ n ω i)})
    (hYT₂ : ∀ j : T, IsTightMeasureSet
      {ν : Measure C((W' j.1 : Set (Rd d)) × (W' j.1 : Set (Rd d)), ℝ) |
        ∃ n, ν = P.map (fun ω => Y₂ n ω j)}) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ μ : ProbabilityMeasure
        (A × ((∀ i : S, C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ)) ×
          (∀ j : T, C((W' j.1 : Set (Rd d)) × (W' j.1 : Set (Rd d)), ℝ)))),
      ∃ (E : Type) (_ : MeasurableSpace E) (_ : StandardBorelSpace E)
        (Q : Measure E), IsProbabilityMeasure Q ∧
      ∃ (Z : ℕ → E →
        A × ((∀ i : S, C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ)) ×
          (∀ j : T, C((W' j.1 : Set (Rd d)) × (W' j.1 : Set (Rd d)), ℝ))))
        (Zlim : E →
        A × ((∀ i : S, C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ)) ×
          (∀ j : T, C((W' j.1 : Set (Rd d)) × (W' j.1 : Set (Rd d)), ℝ)))),
        (∀ n, Measurable (Z n)) ∧ Measurable Zlim ∧
        (∀ n, Q.map (Z n) = P.map (fun ω =>
          (X (ns n) ω, (Y₁ (ns n) ω, Y₂ (ns n) ω)))) ∧
        Q.map Zlim = μ ∧
        (∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e))) := by
  letI (i : S) : LocallyCompactSpace (W i.1 : Set (Rd d)) :=
    (W i.1).isOpen.locallyCompactSpace
  letI (i : S) : PolishSpace
      C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  letI (j : T) : LocallyCompactSpace (W' j.1 : Set (Rd d)) :=
    (W' j.1).isOpen.locallyCompactSpace
  letI (j : T) : PolishSpace
      C((W' j.1 : Set (Rd d)) × (W' j.1 : Set (Rd d)), ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  letI : PolishSpace (∀ i : S,
      C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ)) :=
    l7a_polish_finite_internal_array S W
  letI : PolishSpace (∀ j : T,
      C((W' j.1 : Set (Rd d)) × (W' j.1 : Set (Rd d)), ℝ)) :=
    l7a_polish_finite_internal_array T W'
  have hT₁ := l7a_tight_countable_coordinates P Y₁ hY₁ hYT₁
  have hT₂ := l7a_tight_countable_coordinates P Y₂ hY₂ hYT₂
  have hTY := l7a_joint_tight_of_marginals P Y₁ Y₂
    (fun n => AEMeasurable.of_eval (hY₁ n))
    (fun n => AEMeasurable.of_eval (hY₂ n)) hT₁ hT₂
  exact l7a_exists_joint_skorokhod P X
    (fun n ω => (Y₁ n ω, Y₂ n ω)) hX
    (fun n => (AEMeasurable.of_eval (hY₁ n)).prodMk
      (AEMeasurable.of_eval (hY₂ n))) hXT hTY

end HigherDimLQGMetric
