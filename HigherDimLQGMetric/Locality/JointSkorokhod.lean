import HigherDimLQGMetric.Locality.JointLaw
import LQGMetric.Papers.DFGPS.L2_17Core3B

/-! Tight joint metric-coordinate laws have a Skorokhod representation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

theorem l7a_exists_joint_skorokhod
    {A B Ω : Type} [MeasurableSpace Ω]
    [TopologicalSpace A] [MeasurableSpace A] [OpensMeasurableSpace A]
    [BorelSpace A] [PolishSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [OpensMeasurableSpace B]
    [BorelSpace B] [PolishSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → A) (Y : ℕ → Ω → B)
    (hX : ∀ n, AEMeasurable (X n) P)
    (hY : ∀ n, AEMeasurable (Y n) P)
    (hXT : IsTightMeasureSet {ν : Measure A | ∃ n, ν = P.map (X n)})
    (hYT : IsTightMeasureSet {ν : Measure B | ∃ n, ν = P.map (Y n)}) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ μ : ProbabilityMeasure (A × B),
      ∃ (E : Type) (_ : MeasurableSpace E) (_ : StandardBorelSpace E)
        (Q : Measure E), IsProbabilityMeasure Q ∧
      ∃ (Z : ℕ → E → A × B) (Zlim : E → A × B),
        (∀ n, Measurable (Z n)) ∧ Measurable Zlim ∧
        (∀ n, Q.map (Z n) = P.map (fun ω => (X (ns n) ω, Y (ns n) ω))) ∧
        Q.map Zlim = μ ∧
        (∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e))) := by
  obtain ⟨μ, ns, hns, hlim⟩ :=
    l7a_exists_joint_law_subseq P X Y hX hY hXT hYT id
  obtain ⟨E, mE, hsb, Q, hQ, Z, Zlim, hZm, hZlimm,
    hZlaw, hZlimlaw, hZc⟩ :=
    LQGMetric.DFGPS.L217.exists_skorokhod_representation_sb hlim
  refine ⟨ns, hns, μ, E, mE, hsb, Q, hQ, Z, Zlim,
    hZm, hZlimm, ?_, hZlimlaw, hZc⟩
  intro n
  simpa only [l7a_jointLaw, ProbabilityMeasure.coe_mk,
    Function.comp_def, id_eq] using hZlaw n

end HigherDimLQGMetric
