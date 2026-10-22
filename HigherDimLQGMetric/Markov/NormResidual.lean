import HigherDimLQGMetric.Markov.Reconstruct

/-! Correcting the smooth-test projection to the sphere normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- The sphere-normalized sample field. -/
def markovSphereField (h : Ω → DistRd d) (z : Rd d) (r : ℝ) : Ω → DistRd d :=
  fun ω => addConst (h ω) (-sphereAvg (h ω) r z)

/-- The constant needed to translate a smooth-test-normalized exterior projection to the
sphere normalization. It is an interior pairing of the sphere-normalized field. -/
def markovSphereCorrection (h : Ω → DistRd d) (z : Rd d) (r : ℝ)
    (ρ : TestRd d) : Ω → ℝ :=
  fun ω => markovSphereField h z r ω ρ

omit [IsProbabilityMeasure P] in
theorem markov_measurable_sphereField (hh : IsWholeSpaceLGF h P)
    (z : Rd d) (r : ℝ) : Measurable (markovSphereField h z r) := by
  exact measurable_addConst.comp
    (hh.measurable.prodMk (((measurable_sphereAvg_left r z).comp hh.measurable).neg))

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem markov_measurable_sphereCorrection
    (V : Opens (Rd d)) (z : Rd d) (r : ℝ) {ρ : TestRd d}
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V) :
    Measurable[fieldSigmaRd (markovSphereField h z r) V]
      (markovSphereCorrection h z r ρ) := by
  have hm : Measurable[fieldSigmaRd (markovSphereField h z r) V]
      (fun ω => restrictTo V (markovSphereField h z r ω) (testOnOf V ρ hρV)) :=
    (measurable_distOn_apply (testOnOf V ρ hρV)).comp
      (comap_measurable (fun ω => restrictTo V (markovSphereField h z r ω)))
  change Measurable[fieldSigmaRd (markovSphereField h z r) V]
    (fun ω => markovSphereField h z r ω ρ)
  simpa only [restrictTo_testOnOf] using hm

/-- The full exterior process, set to zero off the exterior open set. -/
def markovSphereHarmonic (V : Opens (Rd d)) (Y : Ω → Rd d → ℝ)
    (q : Ω → ℝ) : Ω → Rd d → ℝ :=
  by classical exact fun ω x => if x ∈ extOpen V then Y ω x + q ω else 0

omit [MeasurableSpace Ω] in
theorem markovSphereHarmonic_continuousOn (V : Opens (Rd d))
    (Y : Ω → Rd d → ℝ) (q : Ω → ℝ)
    (hYc : ∀ ω, ContinuousOn (Y ω) (extOpen V)) (ω : Ω) :
    ContinuousOn (markovSphereHarmonic V Y q ω) (extOpen V) := by
  have hc : ContinuousOn (fun x : Rd d => Y ω x + q ω) (extOpen V) :=
    (hYc ω).add (continuousOn_const : ContinuousOn (fun _ : Rd d => q ω) (extOpen V))
  apply hc.congr
  intro x hx
  dsimp [markovSphereHarmonic]
  split_ifs with h
  · rfl
  · exact False.elim (h hx)

theorem markovSphereHarmonic_measurable (V : Opens (Rd d))
    (Y : Ω → Rd d → ℝ) (q : Ω → ℝ)
    (hYm : Measurable Y) (hqm : Measurable q) :
    Measurable (markovSphereHarmonic V Y q) := by
  rw [measurable_pi_iff]
  intro x
  by_cases hx : x ∈ extOpen V
  · have hm : Measurable (fun ω => Y ω x + q ω) :=
      (measurable_pi_iff.mp hYm x).add hqm
    simpa [markovSphereHarmonic, hx] using hm
  · simpa only [markovSphereHarmonic, ite_eq_right hx] using
      (measurable_const : Measurable fun _ : Ω => (0 : ℝ))

end HigherDimLQGMetric
