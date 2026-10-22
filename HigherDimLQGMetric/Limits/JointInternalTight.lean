import HigherDimLQGMetric.Limits.JointInternalConsistent
import HigherDimLQGMetric.DGZ.NondegTight
import HigherDimLQGMetric.DGZ.NondegJoint
import HigherDimLQGMetric.DGZ.NondegProkhorov
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Countable-product assembly for ambient and internal metric laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Marginal tightness of the ambient metric and every connected-domain
internal metric gives tightness of their countable joint state. -/
theorem l6c_joint_tight_of_marginals {d : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : ℕ → Ω → ∀ i : DGZ.nd_DomainIndex d 1 × ℕ,
      C(DGZ.nd_domain 1 i.1 × DGZ.nd_domain 1 i.1, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P)
    (hY : ∀ n i, AEMeasurable (fun ω => Y n ω i) P)
    (hXT : IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) |
      ∃ n, ν = P.map (X n)})
    (hYT : ∀ i : DGZ.nd_DomainIndex d 1 × ℕ,
      IsTightMeasureSet
        {ν : Measure C(DGZ.nd_domain 1 i.1 × DGZ.nd_domain 1 i.1, ℝ) |
          ∃ n, ν = P.map (fun ω => Y n ω i)}) :
    IsTightMeasureSet {ν : Measure (DGZ.nd_Joint d 1) |
      ∃ n, ν = P.map (fun ω => (X n ω, Y n ω))} := by
  let S : Set (Measure (DGZ.nd_Joint d 1)) :=
    {ν | ∃ n, ν = P.map (fun ω => (X n ω, Y n ω))}
  change IsTightMeasureSet S
  have hjoint (n : ℕ) : AEMeasurable (fun ω => (X n ω, Y n ω)) P :=
    (hX n).prodMk (AEMeasurable.of_eval (hY n))
  have hS0 : IsTightMeasureSet
      ((fun ν : Measure (DGZ.nd_Joint d 1) => ν.map Prod.fst) '' S) := by
    apply hXT.subset
    rintro ν ⟨μ, ⟨n, rfl⟩, rfl⟩
    refine ⟨n, ?_⟩
    change (P.map (fun ω => (X n ω, Y n ω))).map Prod.fst = P.map (X n)
    simpa only [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
        (hjoint n))
  have hS1 : IsTightMeasureSet
      ((fun ν : Measure (DGZ.nd_Joint d 1) => ν.map Prod.snd) '' S) := by
    apply DGZ.nd_isTightMeasureSet_pi
    intro i
    apply (hYT i).subset
    rintro ν ⟨μ, ⟨η, ⟨n, rfl⟩, rfl⟩, rfl⟩
    refine ⟨n, ?_⟩
    change ((P.map (fun ω => (X n ω, Y n ω))).map Prod.snd).map
      (fun f => f i) = P.map (fun ω => Y n ω i)
    rw [AEMeasurable.map_map_of_aemeasurable
      (measurable_pi_apply i).aemeasurable measurable_snd.aemeasurable,
      AEMeasurable.map_map_of_aemeasurable
        ((measurable_pi_apply i).comp measurable_snd).aemeasurable (hjoint n)]
    rfl
  exact IsTightMeasureSet.prodMk hS0 hS1

/-- The law of one ambient metric and its countable internal coordinates. -/
def l6c_jointLaw {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : ℕ → Ω → ∀ i : DGZ.nd_DomainIndex d 1 × ℕ,
      C(DGZ.nd_domain 1 i.1 × DGZ.nd_domain 1 i.1, ℝ))
    (n : ℕ) : ProbabilityMeasure (DGZ.nd_Joint d 1) :=
  ⟨P.map (fun ω => (X n ω, Y n ω)), inferInstance⟩

/-- Prokhorov then supplies a jointly convergent subsequence on the product
of all connected dyadic domains. -/
theorem l6c_exists_joint_subseq_of_marginals {d : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : ℕ → Ω → ∀ i : DGZ.nd_DomainIndex d 1 × ℕ,
      C(DGZ.nd_domain 1 i.1 × DGZ.nd_domain 1 i.1, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P)
    (hY : ∀ n i, AEMeasurable (fun ω => Y n ω i) P)
    (hXT : IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) |
      ∃ n, ν = P.map (X n)})
    (hYT : ∀ i : DGZ.nd_DomainIndex d 1 × ℕ,
      IsTightMeasureSet
        {ν : Measure C(DGZ.nd_domain 1 i.1 × DGZ.nd_domain 1 i.1, ℝ) |
          ∃ n, ν = P.map (fun ω => Y n ω i)})
    (ns : ℕ → ℕ) :
    ∃ μ : ProbabilityMeasure (DGZ.nd_Joint d 1), ∃ ψ : ℕ → ℕ,
      StrictMono ψ ∧ Tendsto
        (fun k => l6c_jointLaw P X Y (ns (ψ k)))
        atTop (𝓝 μ) := by
  let law : ℕ → ProbabilityMeasure (DGZ.nd_Joint d 1) :=
    fun n => l6c_jointLaw P X Y (ns n)
  have hT : IsTightMeasureSet
      {((μ : ProbabilityMeasure (DGZ.nd_Joint d 1)) : Measure (DGZ.nd_Joint d 1)) |
        μ ∈ range law} := by
    refine (l6c_joint_tight_of_marginals P X Y hX hY hXT hYT).subset ?_
    rintro ν ⟨μ, ⟨n, rfl⟩, rfl⟩
    exact ⟨ns n, rfl⟩
  obtain ⟨μ, -, ψ, hψ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
      (x := law) (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨μ, ψ, hψ, hlim⟩

end HigherDimLQGMetric
