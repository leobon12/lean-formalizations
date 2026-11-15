/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootN4Transfer
import InteractingSLE.Spec.Supplement.GW2RootK3Model

/-!
# GW2 root tests using the near-extreme finite-force estimates

Continuation of PROVE-T14-GW2ROOT2. This conditional helper replaces the
previous model crossing estimate by concrete finite-force inputs and their
candidate identification. All other outstanding geometric and probabilistic
inputs retain their exact types. No unconditional root construction is asserted.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open QuantumZipper (H)

universe u v

namespace InteractingSLE.Theorem14.GW2TipSystem.RootN4

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

/-- The per-root claims follow from TIP11's finite-force families, full
retained model law, observable experiments, ambient capacity measurability,
raw regularity, and the slow-event inputs. The model crossing estimate is
derived from `hNear`, rather than assumed. The other fourteen field families
of `IsStageModel` remain explicit hypotheses. -/
theorem testClaims_of_nearModels
    (h13 : Theorem13Statement.{u}) (hκ4 : κ < 4)
    (hβA : Measurable βA) (hh : Measurable h)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hQ : Dense Q)
    (hNear : HasNearCrossingModels.{u} κ P (d.alive G)
      (fun l a ω => d.kernel l a ω (d.reach l a)))
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
    (hp₀ : 0 < d.p₀) (hp₀1 : d.p₀ ≤ 1)
    (hModelSlow : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ a,
      ∀ᵐ ω ∂P, ω ∈ d.alive G l →
        ENNReal.ofReal d.p₀ ≤ d.kernel l a ω (d.slow l a))
    (hUnit : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
      d.sample l a ω ∈ d.slow l a → ∀ q : Q, ω ∈ d.tests l a q →
        capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + 1 ≤
          capR hκ h12p βA b jumps c₀ h W' ζ' s r ((d.ang a, q) :: l) ω) :
    TestClaims hκ h12p βA b jumps c₀ h W' ζ' s P r G
      (d.alive G) d.ang d.tests
      (TestEvents.capacityUnit (capR hκ h12p βA b jumps c₀ h W' ζ' s r)) d.p₀ := by
  have hm : IsStageModel hκ h12p βA b jumps c₀ h W' ζ' s P r G d :=
    { hG := hG
      hI := hI
      hObs := hObs
      hCap := hCap
      hReg := hReg
      hSample := hSample
      hReachMeas := hReachMeas
      hSlowMeas := hSlowMeas
      hLaw := hLaw
      hReachIdent := hReachIdent
      hModelCross := hNear.modelCross h13 hκ hκ4
      hp₀ := hp₀
      hp₀1 := hp₀1
      hModelSlow := hModelSlow
      hUnit := hUnit }
  exact hm.testClaims hβA hh hcf hQ

end InteractingSLE.Theorem14.GW2TipSystem.RootN4
