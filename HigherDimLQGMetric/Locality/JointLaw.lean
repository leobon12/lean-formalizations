import HigherDimLQGMetric.Limits.JointInternalTight
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Generic joint tightness and subsequence extraction for finite collections
of metric and field observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

theorem l7a_joint_tight_of_marginals
    {A B Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → A) (Y : ℕ → Ω → B)
    (hX : ∀ n, AEMeasurable (X n) P)
    (hY : ∀ n, AEMeasurable (Y n) P)
    (hXT : IsTightMeasureSet {ν : Measure A | ∃ n, ν = P.map (X n)})
    (hYT : IsTightMeasureSet {ν : Measure B | ∃ n, ν = P.map (Y n)}) :
    IsTightMeasureSet {ν : Measure (A × B) |
      ∃ n, ν = P.map (fun ω => (X n ω, Y n ω))} := by
  let S : Set (Measure (A × B)) :=
    {ν | ∃ n, ν = P.map (fun ω => (X n ω, Y n ω))}
  change IsTightMeasureSet S
  have hJ (n : ℕ) : AEMeasurable (fun ω => (X n ω, Y n ω)) P :=
    (hX n).prodMk (hY n)
  have hS0 : IsTightMeasureSet
      ((fun ν : Measure (A × B) => ν.map Prod.fst) '' S) := by
    apply hXT.subset
    rintro ν ⟨μ, ⟨n, rfl⟩, rfl⟩
    refine ⟨n, ?_⟩
    simpa only [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
        (hJ n))
  have hS1 : IsTightMeasureSet
      ((fun ν : Measure (A × B) => ν.map Prod.snd) '' S) := by
    apply hYT.subset
    rintro ν ⟨μ, ⟨n, rfl⟩, rfl⟩
    refine ⟨n, ?_⟩
    simpa only [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        (hJ n))
  exact IsTightMeasureSet.prodMk hS0 hS1

def l7a_jointLaw
    {A B Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → A) (Y : ℕ → Ω → B)
    (hX : ∀ n, AEMeasurable (X n) P)
    (hY : ∀ n, AEMeasurable (Y n) P) (n : ℕ) :
    ProbabilityMeasure (A × B) :=
  ⟨P.map (fun ω => (X n ω, Y n ω)),
    (Measure.isProbabilityMeasure_map_iff ((hX n).prodMk (hY n))).2 inferInstance⟩

theorem l7a_exists_joint_law_subseq
    {A B Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A] [BorelSpace A]
    [PolishSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [OpensMeasurableSpace B] [BorelSpace B]
    [PolishSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → A) (Y : ℕ → Ω → B)
    (hX : ∀ n, AEMeasurable (X n) P)
    (hY : ∀ n, AEMeasurable (Y n) P)
    (hXT : IsTightMeasureSet {ν : Measure A | ∃ n, ν = P.map (X n)})
    (hYT : IsTightMeasureSet {ν : Measure B | ∃ n, ν = P.map (Y n)})
    (ns : ℕ → ℕ) :
    ∃ μ : ProbabilityMeasure (A × B), ∃ ψ : ℕ → ℕ,
      StrictMono ψ ∧ Tendsto
        (fun k => l7a_jointLaw P X Y hX hY (ns (ψ k)))
        atTop (𝓝 μ) := by
  let law : ℕ → ProbabilityMeasure (A × B) := fun n =>
    l7a_jointLaw P X Y hX hY (ns n)
  have hT : IsTightMeasureSet
      {((μ : ProbabilityMeasure (A × B)) : Measure (A × B)) |
        μ ∈ range law} := by
    refine (l7a_joint_tight_of_marginals P X Y hX hY hXT hYT).subset ?_
    rintro ν ⟨μ, ⟨n, rfl⟩, rfl⟩
    exact ⟨ns n, rfl⟩
  obtain ⟨μ, -, ψ, hψ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
      (x := law) (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨μ, ψ, hψ, hlim⟩

end HigherDimLQGMetric
