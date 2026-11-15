/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootV7Model
import InteractingSLE.Spec.Supplement.GW2RootV7Clock
import InteractingSLE.Spec.Supplement.GW2RootN4Claims

/-!
# GW2 tests with the canonical retained driver kernel

Continuation of PROVE-T14-GW2ROOT2. The kernel is constructed by pushing
forward the conditional kernel for the complete retained sigma-algebra,
and the slow event is the measurable common record event. Its finite-force
identification, actual observations and capacity clock remain mathematical
inputs. The final helper is conditional and does not construct the root cover.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootV7

open Exist Staged StagedLaw Restart LQGMetric RootK3

/-- Use the actual conditional driver-record law and the common slow event.
Measurability is required at construction, so the kernel map has no
nonmeasurable branch. All experiment observations and tests are retained. -/
def retainedData {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Θ : Set ℝ} {Q : Set ℝ≥0} {σ : List (EntryIdx Θ Q) → MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (d : StageModelData Ω Θ Q DriverRecord σ)
    (hSample : ∀ l a, Measurable (d.sample l a)) :
    StageModelData Ω Θ Q DriverRecord σ :=
  { d with
    kernel := fun l a => Kernel.mapOfMeasurable (condExpKernel P (σ l))
      (d.sample l a) (hSample l a)
    slow := fun _ _ => slowSet }

/-- The constructed kernel is pointwise the conditional pushforward under
exactly the supplied sigma-algebra, without discarding any retained marks. -/
theorem retainedData_kernel {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Θ : Set ℝ} {Q : Set ℝ≥0} {σ : List (EntryIdx Θ Q) → MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (d : StageModelData Ω Θ Q DriverRecord σ)
    (hSample : ∀ l a, Measurable (d.sample l a)) (l : List (EntryIdx Θ Q))
    (a : ℕ) (ω : Ω) :
    (retainedData P d hSample).kernel l a ω =
      (condExpKernel P (σ l) ω).map (d.sample l a) := rfl

/-- Every slow event of the constructed data is the common measurable event. -/
theorem retainedData_slow {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Θ : Set ℝ} {Q : Set ℝ≥0} {σ : List (EntryIdx Θ Q) → MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (d : StageModelData Ω Θ Q DriverRecord σ)
    (hSample : ∀ l a, Measurable (d.sample l a)) (l : List (EntryIdx Θ Q)) (a : ℕ) :
    (retainedData P d hSample).slow l a = slowSet := rfl

variable {κ : ℝ} {hκ : 0 < κ} {h12p : Theorem12ParamStatement.{u}}
  {βA : BoundaryWord × ℝ × RecData → BoundaryWord}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {c₀ : BoundaryWord}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Θ : Set ℝ} {Q : Set ℝ≥0} {s : ℝ≥0}
  {P : Measure Ω} [IsFiniteMeasure P] {r : ScaledRootIdx Θ Q} {G : Set Ω}
  {d : StageModelData Ω Θ Q DriverRecord (rootSigma hκ h12p βA c₀ h W' ζ' s r)}

/-- The unchanged per-root test claims with a constructed conditional
kernel and slow event, and a derived positive constant and unit clause.
The finite-force identifications and actual clock remain explicit inputs;
this does not assert their existence or construct the initial root cover. -/
theorem exists_testClaims_of_retained_angleModels
    (h13 : Theorem13Statement.{u}) (hκ4 : κ < 4)
    (hβA : Measurable βA) (hh : Measurable h)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hQ : Dense Q)
    (hSample : ∀ l a, Measurable (d.sample l a))
    (hNear : RootN4.HasNearCrossingModels.{u} κ P (d.alive G)
      (fun l a ω => (retainedData P d hSample).kernel l a ω (d.reach l a)))
    {nL₀ nR₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ)
    (hModels : HasAngleDriverModels.{u} κ ρL₀ ρR₀ P (d.alive G) List.length
      (fun l a ω => (retainedData P d hSample).kernel l a ω))
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
    (hReachMeas : ∀ l a, MeasurableSet (d.reach l a))
    (hReachIdent : ∀ l a, d.sample l a ⁻¹' d.reach l a =ᵐ[P]
      {ω | d.S l a ω < d.F l a ω})
    (Y : List (EntryIdx Θ Q) → ℕ → Ω → ℝ≥0 → ℝ)
    (clock : List (EntryIdx Θ Q) → ℕ → Q → Ω → ℝ≥0)
    (hRead : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
      ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (d.sample l a ω).1 →
        (d.sample l a ω).2 q = Y l a ω q)
    (hClock : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l → ∀ q : Q,
      ω ∈ d.tests l a q →
        ContinuousAt (Y l a ω) (clock l a q ω) ∧
        (clock l a q ω : ℝ≥0∞) < (d.sample l a ω).1 ∧
        7 / 4 < Y l a ω (clock l a q ω) ∧
        capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + clock l a q ω ≤
          capR hκ h12p βA b jumps c₀ h W' ζ' s r ((d.ang a, q) :: l) ω) :
    ∃ p₀ : ℝ, TestClaims hκ h12p βA b jumps c₀ h W' ζ' s P r G
      (d.alive G) d.ang d.tests
      (TestEvents.capacityUnit (capR hκ h12p βA b jumps c₀ h W' ζ' s r)) p₀ := by
  obtain ⟨p₀, hp₀, hp₀1, hModelSlow⟩ := hModels.exists_modelSlow hκ hκ4
  let d' : StageModelData Ω Θ Q DriverRecord
      (rootSigma hκ h12p βA c₀ h W' ζ' s r) :=
    { retainedData P d hSample with p₀ := p₀ }
  have hUnit := ae_unit_of_record_clock (d := d') (fun _ _ => rfl) Y clock hRead hClock
  refine ⟨p₀, ?_⟩
  exact RootN4.testClaims_of_nearModels (d := d') h13 hκ4 hβA hh hcf hQ
    hNear hG hI hObs hCap hReg hSample hReachMeas
    (fun _ _ => measurableSet_slowSet)
    (fun _ _ => Eventually.of_forall fun _ _ => rfl)
    hReachIdent hp₀ hp₀1 hModelSlow hUnit

end InteractingSLE.Theorem14.GW2TipSystem.RootV7
