/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalLaws
import InteractingSLE.Spec.Restart.RetPlumbProofFinalModel
import InteractingSLE.Spec.Restart.RetPlumbProofFinalPairings

/-!
# The remaining exact inputs to arbitrary-source model transport

Packet PROVE-RETPLUMB. A canonical trace relation needs a Borel coding before
its almost-sure generating property can be pushed forward. The coordinate
reader and (S)/(L) transport do not by themselves prove this Borel assertion.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open LQGMetric (DistOn TestOn)
open Sec2.Assembly Sec7.PocketTraversal DomainMarkov DomainMarkov.K2 FCDet

/-- Exact remaining Borel coding input for the canonical generating-trace
relation. This names an obligation and does not assert it. -/
def RetCanonicalGeneratingTraceBorel : Prop :=
  MeasurableSet {s : RetCanonSpace | IsGeneratingTrace
    (RetCanonSpace.driver · s) (RetCanonSpace.life s) (RetCanonSpace.trace s)}

/-- Fixed-type left positions on the canonical carrier. -/
def retCanonicalXL (κ θ : ℝ) (a : ForceWordType) (s : RetCanonSpace) : Fin a.nL → ℝ :=
  typeXL κ θ a.nL a.nR a.rhoL a.rhoR s.word

/-- Fixed-type right positions on the canonical carrier. -/
def retCanonicalXR (κ θ : ℝ) (a : ForceWordType) (s : RetCanonSpace) : Fin a.nR → ℝ :=
  typeXR κ θ a.nL a.nR a.rhoL a.rhoR s.word

/-- The canonical killed coordinates are measurable without choosing the
capacity filtration: the constant ambient filtration suffices for this fact. -/
theorem retCanonicalKilledMeas (κ θ : ℝ) (a : ForceWordType) :
    IsMeasurableKilledDriving RetCanonSpace.driver
      (geomLW RetCanonSpace.driver (retCanonicalXL κ θ a))
      (geomRW RetCanonSpace.driver (retCanonicalXR κ θ a)) RetCanonSpace.life := by
  let 𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace RetCanonSpace) :=
    Filtration.const ℝ≥0 inferInstance le_rfl
  apply isMeasurableKilledDriving_geom (𝓗 := 𝓕)
    (fun t => (RetCanonSpace.measurable_driver t).stronglyMeasurable)
    RetCanonSpace.continuous_driver
    ((measurable_typeXL κ θ a.nL a.nR a.rhoL a.rhoR).comp RetCanonSpace.measurable_word)
    ((measurable_typeXR κ θ a.nL a.nR a.rhoL a.rhoR).comp RetCanonSpace.measurable_word)
  intro t
  exact measurableSet_le RetCanonSpace.measurable_life measurable_const

universe v
variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Once the displayed Borel input is supplied, the actual closed-prefix
coordinate reader transports the generating trace property, including its
finite endpoint. No standard Borel assumption is made on the source. -/
theorem ae_retCanonical_generates (hBorel : RetCanonicalGeneratingTraceBorel)
    {Y : Ω → RetCanonSpace} (hY : Measurable Y) {M : Set Ω} (hM : MeasurableSet M)
    {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hWY : ∀ ω t, RetCanonSpace.driver t (Y ω) = W t ω)
    (hVY : ∀ ω, RetCanonSpace.life (Y ω) = V ω)
    (hγY : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) ≤ V ω → RetCanonSpace.trace (Y ω) t = γ ω t)
    (hg : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (V ω) (γ ω)) :
    ∀ᵐ s ∂((P[|M]).map Y), IsGeneratingTrace
      (RetCanonSpace.driver · s) (RetCanonSpace.life s) (RetCanonSpace.trace s) := by
  apply (ae_map_iff hY.aemeasurable hBorel).2
  apply ae_cond_of_ae_imp hM
  filter_upwards [hg] with ω hω hωM
  have hWf : (fun t => RetCanonSpace.driver t (Y ω)) = (W · ω) := funext (hWY ω)
  rw [hWf, hVY]
  exact isGeneratingTrace_congr_le (hω hωM) (hγY ω)

end InteractingSLE.Restart.RetAux79
