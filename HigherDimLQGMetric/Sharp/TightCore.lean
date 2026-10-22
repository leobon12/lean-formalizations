import HigherDimLQGMetric.Frozen.TightOver
import LQGMetric.Papers.GM.S2.TightCore

/-!
# Compact-law consequence of weak metric tightness

Port of `LQGMetric.GM.Tight.tight_mapsTo` to `Rd d`, with the field-law reduction
removed. The input is directly the frozen `TightOver` property.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Filter Topology Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}

/-- Uniform compact-open control under `TightOver`. -/
theorem TightOver.mapsTo (hT : TightOver P X S) {A : ℕ → Set (Rd d × Rd d)}
    (hA : ∀ n, IsCompact (A n)) (hAa : Antitone A) {U : ℕ → Set ℝ}
    (hU : ∀ n, IsOpen (U n)) (hUm : Monotone U)
    (hmet : ∀ g : C(Rd d × Rd d, ℝ), IsContinuousMetric g →
      ∀ x ∈ ⋂ n, A n, ∃ n, g x ∈ U n)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, ∀ r ∈ S, P {ω | ¬ MapsTo (X r ω) (A n) (U n)} < ε := by
  have hS : IsCompact (closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X r)}) := by
    refine isCompact_closure_of_isTightMeasureSet (hT.2.1.subset ?_)
    rintro _ ⟨ν, ⟨r, hr, hν⟩, rfl⟩
    exact ⟨r, hr, hν⟩
  let C : ℕ → Set C(Rd d × Rd d, ℝ) := fun n => {g | ¬ MapsTo g (A n) (U n)}
  have hCc : ∀ n, IsClosed (C n) := fun n =>
    LQGMetric.GM.Tight.isClosed_setOf_not_mapsTo (hA n) (hU n)
  have hCa : Antitone C := fun m n hmn g hg hg' =>
    hg (fun x hx => hUm hmn (hg' (hAa hmn hx)))
  have h0 : ∀ μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X r)},
      (μ : Measure C(Rd d × Rd d, ℝ)) (⋂ n, C n) = 0 := by
    intro μ hμ
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hT.2.2 μ hμ] with g hg hmem
    obtain ⟨x, hx, hxU⟩ := LQGMetric.GM.Tight.exists_mem_iInter_of_not_mapsTo
      hA hAa hU hUm (d := g) (mem_iInter.1 hmem)
    obtain ⟨n, hn⟩ := hmet g hg x hx
    exact hxU n hn
  obtain ⟨n, hn⟩ := LQGMetric.GM.Tight.exists_measure_lt_of_isCompact_closure
    hS hCc hCa h0 hε
  refine ⟨n, fun r hr => ?_⟩
  have hmeas := hT.1 r hr
  have hprob : IsProbabilityMeasure (P.map (X r)) := inferInstance
  have heq : P {ω | ¬ MapsTo (X r ω) (A n) (U n)} =
      (P.map (X r)) (C n) := by
    rw [Measure.map_apply_of_aemeasurable hmeas (hCc n).measurableSet]
    rfl
  rw [heq]
  exact hn ⟨P.map (X r), hprob⟩ ⟨r, hr, rfl⟩

end HigherDimLQGMetric
