/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootS5Delay
import InteractingSLE.Spec.Supplement.GW2RootN4Claims

/-!
# Root tests with a derived uniform slow probability and capacity increment

Continuation of PROVE-T14-GW2ROOT2. The named `HasSlowComparisonModels`
input asks for the qualitative finite-force windows and their probability
comparison with the model's slow event. The positive uniform constant is
derived from Lemma 5.10. The unit implication is derived from dense slow
observations and the actual relative capacity clock. These model and clock
constructions remain explicit mathematical hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open QuantumZipper (H)

universe u v

namespace InteractingSLE.Theorem14.GW2TipSystem.RootS5

/-- Exact remaining slow-model construction input. The comparison windows
have a common drift bound and seed-weight range, while their finite words,
sample spaces and restart times may depend on the retained state. No
positive probability estimate is part of this hypothesis. -/
def HasSlowComparisonModels {Ω L : Type*} [MeasurableSpace Ω]
    (κ C : ℝ) (J : Set ℝ) (P : Measure Ω) (A : L → Set Ω)
    (depth : L → ℕ) (p : L → ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ (k : ℕ) l, depth l = 2 * k + 4 → ∀ a, ∀ᵐ ω ∂P, ω ∈ A l →
    ∃ w : RestartWindow.{u} κ C J, w.e.P w.slowEvent ≤ p l a ω

/-- The finite-force comparison models imply a single positive uniform
slow probability at every required even depth. -/
theorem HasSlowComparisonModels.exists_modelSlow
    {Ω L : Type*} [MeasurableSpace Ω] {κ C : ℝ} {J : Set ℝ}
    {P : Measure Ω} {A : L → Set Ω} {depth : L → ℕ}
    {p : L → ℕ → Ω → ℝ≥0∞}
    (hModels : HasSlowComparisonModels.{u} κ C J P A depth p)
    (hκ : 0 < κ) (hJ : IsCompact J) (hJ2 : J ⊆ Ioi (-2)) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 1 ∧
      ∀ (k : ℕ) l, depth l = 2 * k + 4 → ∀ a, ∀ᵐ ω ∂P,
        ω ∈ A l → ENNReal.ofReal p₀ ≤ p l a ω := by
  obtain ⟨p₀, hp₀, hp₀1, hbound⟩ := exists_uniform_slow_probability hκ hJ hJ2
  refine ⟨p₀, hp₀, hp₀1, ?_⟩
  intro k l hl a
  filter_upwards [hModels k l hl a] with ω hω hωA
  obtain ⟨w, hw⟩ := hω hωA
  exact (hbound w).trans hw

open Exist Staged StagedLaw Restart LQGMetric RootK3

variable {κ : ℝ} {hκ : 0 < κ} {h12p : Theorem12ParamStatement.{u}}
  {βA : BoundaryWord × ℝ × RecData → BoundaryWord}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {c₀ : BoundaryWord}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Θ : Set ℝ} {Q : Set ℝ≥0} {s : ℝ≥0}
  {P : Measure Ω} [IsFiniteMeasure P] {r : ScaledRootIdx Θ Q} {G : Set Ω}
  {Ξ : Type v} [MeasurableSpace Ξ]
  {d : StageModelData Ω Θ Q Ξ (rootSigma hκ h12p βA c₀ h W' ζ' s r)}

/-- The original per-root claims, with their positive constant produced by
Lemma 5.10. Crossing comes from the near-extreme finite-force inputs, and
the unit implication from dense observations and the relative capacity clock.
The old data's `d.p₀` is unused: the result provides the required constant. -/
theorem exists_testClaims_of_near_and_restartModels
    (h13 : Theorem13Statement.{u}) (hκ4 : κ < 4)
    (hβA : Measurable βA) (hh : Measurable h)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hQ : Dense Q)
    (hNear : RootN4.HasNearCrossingModels.{u} κ P (d.alive G)
      (fun l a ω => d.kernel l a ω (d.reach l a)))
    {C : ℝ}
    (hSlow : HasSlowComparisonModels.{u} κ C
      (Icc (-Sec5.angleWeightBound κ) (Sec5.angleWeightBound κ)) P
      (d.alive G) List.length (fun l a ω => d.kernel l a ω (d.slow l a)))
    (hG : MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r []] G)
    (hI : ∀ l a, IsOpen (d.I l a))
    (hObs : ∀ l a (q q' : Q), q ≤ q' →
      Measurable[rootSigma hκ h12p βA c₀ h W' ζ' s r ((d.ang a, q') :: l)]
        (d.observation l a q))
    (hCap : ∀ l, Measurable (capR hκ h12p βA b jumps c₀ h W' ζ' s r l))
    (hReg : ∀ l a, ∀ᵐ ω ∂P, d.S l a ω < d.F l a ω →
      0 ≤ d.S l a ω ∧ ContinuousAt (d.X l a ω) (d.S l a ω) ∧
      d.X l a ω (d.S l a ω) ∈ d.I l a ∧
      ContinuousOn (d.γ l a ω) (Ioo (d.S l a ω) (d.F l a ω)) ∧
      volume {t | t ∈ Ioo (d.S l a ω) (d.F l a ω) ∧ d.γ l a ω t ∉ H} = 0)
    (hSample : ∀ l a, Measurable (d.sample l a))
    (hReachMeas : ∀ l a, MeasurableSet (d.reach l a))
    (hSlowMeas : ∀ l a, MeasurableSet (d.slow l a))
    (hLaw : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
      (condExpKernel P (rootSigma hκ h12p βA c₀ h W' ζ' s r l) ω).map
        (d.sample l a) = d.kernel l a ω)
    (hReachIdent : ∀ l a, d.sample l a ⁻¹' d.reach l a =ᵐ[P]
      {ω | d.S l a ω < d.F l a ω})
    {D : Set ℝ≥0} (hD : Dense D)
    (Y : List (EntryIdx Θ Q) → ℕ → Ω → ℝ≥0 → ℝ)
    (L : List (EntryIdx Θ Q) → ℕ → Ω → ℝ≥0∞)
    (clock : List (EntryIdx Θ Q) → ℕ → Q → Ω → ℝ≥0)
    (hSlowObs : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
      d.sample l a ω ∈ d.slow l a → ∀ t ∈ D, t < 1 →
        (t : ℝ≥0∞) < L l a ω → Y l a ω t ≤ 7 / 4)
    (hClock : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l → ∀ q : Q,
      ω ∈ d.tests l a q →
        ContinuousAt (Y l a ω) (clock l a q ω) ∧
        (clock l a q ω : ℝ≥0∞) < L l a ω ∧
        7 / 4 < Y l a ω (clock l a q ω) ∧
        capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + clock l a q ω ≤
          capR hκ h12p βA b jumps c₀ h W' ζ' s r ((d.ang a, q) :: l) ω) :
    ∃ p₀ : ℝ, TestClaims hκ h12p βA b jumps c₀ h W' ζ' s P r G
      (d.alive G) d.ang d.tests
      (TestEvents.capacityUnit (capR hκ h12p βA b jumps c₀ h W' ζ' s r)) p₀ := by
  have hJ2 : Icc (-Sec5.angleWeightBound κ) (Sec5.angleWeightBound κ) ⊆ Ioi (-2) := by
    intro x hx
    have hM := Sec5.angleWeightBound_lt_two hκ
    exact show -2 < x by linarith only [hx.1, hM]
  obtain ⟨p₀, hp₀, hp₀1, hModelSlow⟩ := hSlow.exists_modelSlow hκ isCompact_Icc hJ2
  have hUnit := ae_unit_of_observed_clock hD Y L clock hSlowObs hClock
  let d' : StageModelData Ω Θ Q Ξ (rootSigma hκ h12p βA c₀ h W' ζ' s r) :=
    { d with p₀ := p₀ }
  refine ⟨p₀, ?_⟩
  exact RootN4.testClaims_of_nearModels (d := d') h13 hκ4 hβA hh hcf hQ
    hNear hG hI hObs hCap hReg hSample hReachMeas hSlowMeas hLaw hReachIdent
    hp₀ hp₀1 hModelSlow hUnit

end InteractingSLE.Theorem14.GW2TipSystem.RootS5
