/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StagedEntranceChart

/-!
# Instance tools for the restart gluing

Packet PROVE-STAGEDLOC, item (4). Two hypotheses of `StagedEntrance.isEntranceHistoryLocal_of_restart_isFlowLine` that
hold for every staged path whose first piece is a flow line and whose restart charts are Loewner charts:

* **`isEntranceHistoryLocal_frozenPath_of_isFlowLine`** (`hloc₀`): a path that agrees with a flow line of infinite
  lifetime up to `q₀` is, frozen after `q₀`, entrance-history local for the centred field (Aux. lemma 56 at first
  entrance times, `WholeField.retainedRangeEntranceStatement`); `frozenPath_ae_eq_comp` gives `hdet₀`;
* **`mem_of_mem_closure_dom`** (`hfr`): if the chart domain is a connected component of `ℍ ∖ K`, `K` closed (for a
  Loewner chart at time `t`, `K` is the trace `γ([0, t])`, by the generating-trace property), then every point of
  `ℍ` in the closure of the domain but not in it lies on `K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Restart

namespace StagedEntrance

open Sec6 LocalSets

/-! ### The first piece -/

section First

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **`hloc₀` for a first piece that is a flow line**: a continuous path agreeing up to `q₀` with a flow line of
infinite lifetime is, frozen after `q₀`, entrance-history local for the centred field. -/
theorem isEntranceHistoryLocal_frozenPath_of_isFlowLine (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ b jumps 0 θ P h η ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω))
    (hαm : ∀ t, Measurable fun ω => α ω t) (q₀ : ℝ≥0) (hαη : ∀ᵐ ω ∂P, ∀ t ≤ q₀, α ω t = η ω t) :
    IsEntranceHistoryLocal (fun ω => frozenPath (α ω) q₀) (WholeField.centredField h u₀) P := by
  have hcap : ∀ᵐ ω ∂P, ∀ t, frozenPath (α ω) q₀ t = η ω (capTime q₀ (ζ ω) t) := by
    filter_upwards [hζ, hαη] with ω hω hαω t
    simp only [frozenPath, capTime, hω, min_eq_right le_top, ENNReal.toNNReal_coe]
    exact hαω _ (min_le_right _ _)
  exact (WholeField.retainedRangeEntranceStatement κ hκ hκ4 b jumps hb 0 θ P h hh η ζ hfl u₀ hu₀ q₀
    (fun ω => frozenPath (α ω) q₀) (fun ω => continuous_frozenPath (hαc ω)) (fun t => hαm _)
    hcap).isEntranceHistoryLocal

omit [IsProbabilityMeasure P] in
/-- **`hdet₀` from the determination of the path**: the frozen path is determined at each time if the path is. -/
theorem frozenPath_ae_eq_comp {X : Ω → DistOn upperHalfPlaneOpens} {α : Ω → ℝ≥0 → ℂ}
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (X ω)) (q₀ : ℝ≥0) (t : ℝ≥0) :
    ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => frozenPath (α ω) q₀ t) =ᵐ[P] fun ω => f (X ω) :=
  hdet (min t q₀)

end First

/-! ### The frontier of a chart domain -/

/-- **`hfr` for a chart domain that is a component of `ℍ ∖ K`**: a point of `ℍ` in the closure of the domain but not
in it lies on `K` (`K` closed). -/
theorem mem_of_mem_closure_dom {c : Chart} {K : Set ℂ} (hK : IsClosed K) {z₀ : ℂ}
    (hdom : (c.dom : Set ℂ) = connectedComponentIn (H \ K) z₀) :
    ∀ z ∈ H, z ∈ closure (c.dom : Set ℂ) → z ∉ c.dom → z ∈ K := by
  intro z hzH hzcl hzD
  by_contra hzK
  have hzHK : z ∈ H \ K := ⟨hzH, hzK⟩
  have hopen : IsOpen (H \ K) := QuantumZipper.isOpen_H.sdiff hK
  have hCo : IsOpen (connectedComponentIn (H \ K) z) := hopen.connectedComponentIn
  obtain ⟨w, hwC, hwD⟩ := mem_closure_iff.1 hzcl _ hCo (mem_connectedComponentIn hzHK)
  rw [hdom] at hwD
  have e1 := connectedComponentIn_eq hwC
  have e2 := connectedComponentIn_eq hwD
  have hz : z ∈ connectedComponentIn (H \ K) z₀ := by
    rw [e2, ← e1]
    exact mem_connectedComponentIn hzHK
  exact hzD (by rw [← SetLike.mem_coe, hdom]; exact hz)

end StagedEntrance

end Restart

end InteractingSLE
