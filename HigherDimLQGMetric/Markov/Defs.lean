import HigherDimLQGMetric.Sphere.Conv
import HigherDimLQGMetric.Field.StandardBorel
import LQGMetric.Statement.Metric

/-!
# Open-set Gaussian Markov decomposition: exact statement

The definitions in this module reproduce the F5 surface in MA5 Details (c). The proof is in
`Markov/Main.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Metric TopologicalSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*}

/-- `σ(h|_V)` for `V` open -/
@[instance_reducible]
def fieldSigmaRd (h : Ω → DistRd d) (V : TopologicalSpace.Opens (Rd d)) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => restrictTo V (h ω)) inferInstance

/-- the open set `ℝ^d ∖ V̄` -/
def extOpen (V : TopologicalSpace.Opens (Rd d)) : TopologicalSpace.Opens (Rd d) :=
  ⟨(closure (V : Set (Rd d)))ᶜ, isClosed_closure.isOpen_compl⟩

/-- the distribution of a function on an open set `O` -/
def ofFunOn (O : TopologicalSpace.Opens (Rd d)) (f : Rd d → ℝ) : DistOn O :=
  Distribution.ofFun O f volume ⊤

/-- **F5 export (D-M, open-set form)**: for an LGF normalized at a sphere inside a bounded open
`V`, the field outside `V̄` is a continuous `σ(h|_V)`-measurable function plus a field
independent of `h|_V`; if `∂V` is Lebesgue-null, `h` is a.s. determined by the two parts. -/
def DMarkovRd : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P →
  ∀ (V : TopologicalSpace.Opens (Rd d)) (z₀ : Rd d) (ρ : ℝ), Bornology.IsBounded (V : Set (Rd d)) →
    0 < ρ → Metric.sphere z₀ ρ ⊆ V →
    ∃ 𝔥 : Ω → Rd d → ℝ,
      (∀ ω, ContinuousOn (𝔥 ω) (extOpen V)) ∧
      (∃ G : Ω → Rd d → ℝ, Measurable[fieldSigmaRd (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀)) V] G ∧
        𝔥 =ᵐ[P] G) ∧
      ProbabilityTheory.Indep
        (MeasurableSpace.comap (fun ω => restrictTo (extOpen V)
          (addConst (h ω) (-sphereAvg (h ω) ρ z₀)) - ofFunOn (extOpen V) (𝔥 ω)) inferInstance)
        (fieldSigmaRd (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀)) V) P ∧
      (volume (frontier (V : Set (Rd d))) = 0 →
        LQGMetric.AEDeterminedBy (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀))
          (fun ω => (restrictTo V (addConst (h ω) (-sphereAvg (h ω) ρ z₀)),
            restrictTo (extOpen V) (addConst (h ω) (-sphereAvg (h ω) ρ z₀)) -
              ofFunOn (extOpen V) (𝔥 ω))) P)

end HigherDimLQGMetric
