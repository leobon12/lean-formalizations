import MatedCRTHarmonic.GMS4cP.SampleBridge
import MatedCRTHarmonic.GMS4cP.PrimeTransfer

/-!
# Measurable Lemma 4.3 from a configuration reconstruction

Source: [18] Lemma 4.3.

If one Borel map `R₀` of the observation `(h|_V, h^IG|_V, U)` reproduces, almost surely under each of two
laws, the actual local configuration `(μ|_U, h|_U, η_L` excursions into `U)` of an excursion-regular Lebesgue
curve `η_L` whose quantum-time reparametrization `c = η_L ∘ φ` is parametrized by `μ`, then the escape event and
The all-visit inner-degree event on its complement are the preimages of two fixed Borel sets
(`l43pSegments U ⁻¹' locEsc …`, `… locInner …`) under `R₀` for both laws: this is `L43PLocalReconstruction`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c MatedCRTHarmonic.MatedCRT

/-- The almost-sure model facts used at one sample: the reconstruction returns the actual configuration
of an excursion-regular Lebesgue curve, whose quantum-time reparametrization is the given curve. -/
def L43PSampleModel {V U : TopologicalSpace.Opens ℂ}
    (R₀ : L46TLocalFieldPhase V → LocalConfiguration U)
    (obs : L46TLocalFieldPhase V) (c : ℝ → ℂ) : Prop :=
  ∃ (μ : Measure ℂ) (h : LQGMetric.DistC) (ηL : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ),
    R₀ obs = localConfiguration U μ h ηL ∧ μ U < ⊤ ∧ ExcursionRegular U ηL ∧
    (∀ t, c t = ηL (φ t)) ∧ ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)

/-- **Measurable Lemma 4.3 (all-visit form) from a configuration reconstruction.** -/
theorem l43pLocalReconstruction_of_config {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ]
    [MeasurableSpace Ω₀] {V U : TopologicalSpace.Opens ℂ} {w : ℂ} {r R : ℝ}
    (hU : (U : Set ℂ) = ball w R) (hrR : r ≤ R)
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → LQGMetric.DistC} {uγ : Ωγ → ℝ}
    {h₀ hIG₀ : Ω₀ → LQGMetric.DistC} {u₀ : Ω₀ → ℝ}
    {cγ : Ωγ → ℝ → ℂ} {c₀ : Ω₀ → ℝ → ℂ} {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ)
    (R₀ : L46TLocalFieldPhase V → LocalConfiguration U) (hR₀ : Measurable R₀)
    (hγcfg : ∀ᵐ ω ∂Pγ, L43PSampleModel R₀ (l46tLocalFieldPhase V hγ hIGγ uγ ω) (cγ ω))
    (h₀cfg : ∀ᵐ ω ∂P₀, L43PSampleModel R₀ (l46tLocalFieldPhase V h₀ hIG₀ u₀ ω) (c₀ ω)) :
    L43PLocalReconstruction V U Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ cγ c₀ (ball w r) ε N := by
  have hUb : Bornology.IsBounded (U : Set ℂ) := hU ▸ isBounded_ball
  have hSU : ball w r ⊆ (U : Set ℂ) := hU ▸ ball_subset_ball hrR
  let G : L46TLocalFieldPhase V → SegSpace := fun x => l43pSegments U (R₀ x)
  have hG : Measurable G := (measurable_l43pSegments U).comp hR₀
  have hE : MeasurableSet (locEsc (l43pLabels U) (ball w r) U ε) := by
    rw [hU]
    exact measurableSet_locEsc _ w w r R ε
  have hA : MeasurableSet (locInner (l43pLabels U) (ball w r) U ε N) := by
    rw [hU]
    exact measurableSet_locInner _ w w r R ε N
  have key : ∀ (obs : L46TLocalFieldPhase V) (c : ℝ → ℂ), L43PSampleModel R₀ obs c →
      (EscBad c (ball w r) U ε ↔ G obs ∈ locEsc (l43pLabels U) (ball w r) U ε) ∧
      (InnerAt c (ball w r) ε N ∧ ¬ EscBad c (ball w r) U ε ↔
        G obs ∈ locInner (l43pLabels U) (ball w r) U ε N) := by
    rintro obs c ⟨μ, h, ηL, φ, hR, hfin, hreg, hcurve, hparam⟩
    simp only [G, hR]
    exact events_iff_of_cfg hUb hfin hreg hcurve hparam hSU hε N
  refine ⟨G ⁻¹' locEsc (l43pLabels U) (ball w r) U ε,
    G ⁻¹' locInner (l43pLabels U) (ball w r) U ε N, hG hE, hG hA, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hγcfg] with ω hω
    exact propext (key _ _ hω).1
  · filter_upwards [h₀cfg] with ω hω
    exact propext (key _ _ hω).1
  · filter_upwards [hγcfg] with ω hω
    exact propext (key _ _ hω).2
  · filter_upwards [h₀cfg] with ω hω
    exact propext (key _ _ hω).2

end MatedCRTHarmonic.GMS4cP
