import HigherDimLQGMetric.Frozen.TightOver
import LQGMetric.Papers.GM.S2.TightCore
import LQGMetric.Prob.PolishContinuousMap

/-!
# Uniform consequences of tightness for continuous metrics on Euclidean space

The abstract compactness and portmanteau argument is reused from the generic core of
`LQGMetric.Papers.GM.S2.TightCore`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}

/-- The generic GM compactness argument, restricted to a fixed family of scales and a fixed
random field. -/
theorem proper_tight_mapsTo (hT : TightOver P X S)
    {A : ℕ → Set (Rd d × Rd d)} (hA : ∀ n, IsCompact (A n)) (hAa : Antitone A)
    {U : ℕ → Set ℝ} (hU : ∀ n, IsOpen (U n)) (hUm : Monotone U)
    (hmet : ∀ e : C(Rd d × Rd d, ℝ), IsContinuousMetric e →
      ∀ x ∈ ⋂ n, A n, ∃ n, e x ∈ U n)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, ∀ r ∈ S, P {ω | ¬ MapsTo (X r ω) (A n) (U n)} < ε := by
  let V : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
    {ν | ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X r)}
  have hV : IsCompact (closure V) := by
    apply isCompact_closure_of_isTightMeasureSet
    exact hT.2.1.subset (by
      rintro μ ⟨ν, ⟨r, hr, hν⟩, rfl⟩
      exact ⟨r, hr, hν⟩)
  let C : ℕ → Set C(Rd d × Rd d, ℝ) :=
    fun n => {e | ¬ MapsTo e (A n) (U n)}
  have hCc : ∀ n, IsClosed (C n) := fun n =>
    LQGMetric.GM.Tight.isClosed_setOf_not_mapsTo (hA n) (hU n)
  have hCa : Antitone C := fun m n hmn e he he' =>
    he (fun x hx => hUm hmn (he' (hAa hmn hx)))
  have hzero : ∀ μ ∈ closure V,
      (μ : Measure C(Rd d × Rd d, ℝ)) (⋂ n, C n) = 0 := by
    intro μ hμ
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hT.2.2 μ hμ] with e he hmem
    obtain ⟨x, hx, hxU⟩ :=
      LQGMetric.GM.Tight.exists_mem_iInter_of_not_mapsTo hA hAa hU hUm
        (d := e) (mem_iInter.1 hmem)
    obtain ⟨n, hn⟩ := hmet e he x hx
    exact hxU n hn
  obtain ⟨n, hn⟩ := LQGMetric.GM.Tight.exists_measure_lt_of_isCompact_closure
    hV hCc hCa hzero hε
  refine ⟨n, fun r hr => ?_⟩
  have hXm := (hT.1 r hr)
  have heq : P {ω | ¬ MapsTo (X r ω) (A n) (U n)} = (P.map (X r)) (C n) := by
    rw [Measure.map_apply_of_aemeasurable hXm (hCc n).measurableSet]
    rfl
  rw [heq]
  exact hn ⟨P.map (X r), inferInstance⟩ ⟨r, hr, rfl⟩

end HigherDimLQGMetric
