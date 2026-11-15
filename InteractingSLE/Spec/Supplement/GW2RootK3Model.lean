/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootK3Kernel
import InteractingSLE.Spec.Supplement.GW2Root2Cap
import InteractingSLE.Spec.Supplement.GW2TestClaims

/-!
# GW2 root tests from observable experiments and their retained model laws

Continuation of PROVE-T14-GW2ROOT2. `IsStageModel` states the remaining
mathematical hypotheses explicitly for given experiment data. They are inputs,
not proved constructions. The assembly proves the crossing, comparison,
alive-event, and unit-event clauses from these hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open QuantumZipper (H)

universe u v

namespace InteractingSLE.Theorem14.GW2TipSystem.RootK3

open Exist Staged StagedLaw Restart LQGMetric

/-- The observations and model sample of a root's next-piece experiments.
The model kernel is indexed by the full retained stage sigma-algebra. -/
structure StageModelData (Ω : Type u) (Θ : Set ℝ) (Q : Set ℝ≥0)
    (Ξ : Type v) [mΞ : MeasurableSpace Ξ]
    (σ : List (EntryIdx Θ Q) → MeasurableSpace Ω) where
  ang : ℕ → Θ
  X : List (EntryIdx Θ Q) → ℕ → Ω → ℝ → ℝ
  γ : List (EntryIdx Θ Q) → ℕ → Ω → ℝ → ℂ
  S : List (EntryIdx Θ Q) → ℕ → Ω → ℝ
  F : List (EntryIdx Θ Q) → ℕ → Ω → ℝ
  I : List (EntryIdx Θ Q) → ℕ → Set ℝ
  sample : List (EntryIdx Θ Q) → ℕ → Ω → Ξ
  kernel : (l : List (EntryIdx Θ Q)) → ℕ → @Kernel Ω Ξ (σ l) mΞ
  reach : List (EntryIdx Θ Q) → ℕ → Set Ξ
  slow : List (EntryIdx Θ Q) → ℕ → Set Ξ
  p₀ : ℝ

/-- The dense-time tests read from a model's actual observations. -/
def StageModelData.tests {Ω : Type u} {Θ : Set ℝ} {Q : Set ℝ≥0}
    {Ξ : Type v} [MeasurableSpace Ξ] {σ}
    (d : StageModelData Ω Θ Q Ξ σ) : List (EntryIdx Θ Q) → ℕ → Q → Set Ω :=
  experimentTests d.X d.γ d.S d.F d.I

/-- Alive prefixes remember actual successful tests, not favourable future data
added to the retained stage record. -/
def StageModelData.alive {Ω : Type u} {Θ : Set ℝ} {Q : Set ℝ≥0}
    {Ξ : Type v} [MeasurableSpace Ξ] {σ}
    (d : StageModelData Ω Θ Q Ξ σ) (G : Set Ω) : List (EntryIdx Θ Q) → Set Ω :=
  TestEvents.aliveTests G d.ang d.tests

/-- Observe the driver and tip only after crossing and before the buffer stop.
Otherwise the observation is zero, whose tip is outside the open half-plane.
In particular this observation does not reveal a future stopping time's value. -/
def StageModelData.observation {Ω : Type u} {Θ : Set ℝ} {Q : Set ℝ≥0}
    {Ξ : Type v} [MeasurableSpace Ξ] {σ}
    (d : StageModelData Ω Θ Q Ξ σ) (l : List (EntryIdx Θ Q)) (a : ℕ)
    (q : Q) (ω : Ω) : ℝ × ℂ :=
  if d.S l a ω < (q : ℝ≥0) ∧ ((q : ℝ≥0) : ℝ) < d.F l a ω then
    (d.X l a ω q, d.γ l a ω q) else (0, 0)

/-- A candidate test is precisely the open-band/interior-tip event of its
gated observation. No observability of the full stopping times is needed. -/
theorem StageModelData.tests_eq_preimage_observation
    {Ω : Type u} {Θ : Set ℝ} {Q : Set ℝ≥0}
    {Ξ : Type v} [MeasurableSpace Ξ] {σ}
    (d : StageModelData Ω Θ Q Ξ σ) (l : List (EntryIdx Θ Q))
    (a : ℕ) (q : Q) :
    d.tests l a q = d.observation l a q ⁻¹' (d.I l a ×ˢ H) := by
  ext ω
  change (d.S l a ω < (q : ℝ≥0) ∧ ((q : ℝ≥0) : ℝ) < d.F l a ω ∧
    d.γ l a ω q ∈ H ∧ d.X l a ω q ∈ d.I l a) ↔ _
  by_cases hg : d.S l a ω < (q : ℝ≥0) ∧ ((q : ℝ≥0) : ℝ) < d.F l a ω
  · simp only [mem_preimage, StageModelData.observation, hg, ↓reduceIte,
      mem_prod, true_and, and_comm]
  · constructor
    · intro ht
      exact False.elim (hg ⟨ht.1, ht.2.1⟩)
    · intro ht
      have hzero : (0 : ℂ) ∈ H := by
        simpa only [mem_preimage, StageModelData.observation, hg,
          ↓reduceIte, mem_prod] using ht.2
      exact False.elim ((lt_irrefl (0 : ℝ)) hzero)

section Root

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
  (ζ' : Ω → ℝ≥0∞) {Θ : Set ℝ} {Q : Set ℝ≥0} (s : ℝ≥0)
  (P : Measure Ω) [IsFiniteMeasure P] (r : ScaledRootIdx Θ Q) (G : Set Ω)
  {Ξ : Type v} [MeasurableSpace Ξ]
  (d : StageModelData Ω Θ Q Ξ (rootSigma hκ h12p βA c₀ h W' ζ' s r))

/-- The explicit mathematical inputs for a given root experiment. In
particular, `hLaw` identifies the actual sample law given `rootSigma`;
`hModelCross` and `hModelSlow` are estimates under that model law. These
assertions remain hypotheses until a geometric model is constructed. -/
structure IsStageModel : Prop where
  hG : MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r []] G
  hI : ∀ l a, IsOpen (d.I l a)
  hObs : ∀ l a (q q' : Q), q ≤ q' →
    Measurable[rootSigma hκ h12p βA c₀ h W' ζ' s r ((d.ang a, q') :: l)]
      (d.observation l a q)
  hCap : ∀ l, Measurable (capR hκ h12p βA b jumps c₀ h W' ζ' s r l)
  hReg : ∀ l a, ∀ᵐ ω ∂P, d.S l a ω < d.F l a ω →
    0 ≤ d.S l a ω ∧ ContinuousAt (d.X l a ω) (d.S l a ω) ∧
    d.X l a ω (d.S l a ω) ∈ d.I l a ∧
    ContinuousOn (d.γ l a ω) (Ioo (d.S l a ω) (d.F l a ω)) ∧
    volume {t | t ∈ Ioo (d.S l a ω) (d.F l a ω) ∧ d.γ l a ω t ∉ H} = 0
  hSample : ∀ l a, Measurable (d.sample l a)
  hReachMeas : ∀ l a, MeasurableSet (d.reach l a)
  hSlowMeas : ∀ l a, MeasurableSet (d.slow l a)
  hLaw : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
    (condExpKernel P (rootSigma hκ h12p βA c₀ h W' ζ' s r l) ω).map
      (d.sample l a) = d.kernel l a ω
  hReachIdent : ∀ l a, d.sample l a ⁻¹' d.reach l a =ᵐ[P]
    {ω | d.S l a ω < d.F l a ω}
  hModelCross : ∀ l (ε : ℝ≥0∞), 0 < ε → ∀ᵐ ω ∂P,
    ω ∈ d.alive G l → ∃ a, 1 - ε < d.kernel l a ω (d.reach l a)
  hp₀ : 0 < d.p₀
  hp₀1 : d.p₀ ≤ 1
  hModelSlow : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ a,
    ∀ᵐ ω ∂P, ω ∈ d.alive G l →
      ENNReal.ofReal d.p₀ ≤ d.kernel l a ω (d.slow l a)
  hUnit : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
    d.sample l a ω ∈ d.slow l a → ∀ q : Q, ω ∈ d.tests l a q →
      capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + 1 ≤
        capR hκ h12p βA b jumps c₀ h W' ζ' s r ((d.ang a, q) :: l) ω

variable {hκ h12p βA b jumps c₀ h W' ζ' s P r G d}

/-- Observable root experiments with the stated model laws give all the
per-candidate claims. The crossing and comparison are derived by law transfer. -/
theorem IsStageModel.testClaims (hβA : Measurable βA) (hh : Measurable h)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hQ : Dense Q)
    (hm : IsStageModel hκ h12p βA b jumps c₀ h W' ζ' s P r G d) :
    TestClaims hκ h12p βA b jumps c₀ h W' ζ' s P r G
      (d.alive G) d.ang d.tests
      (TestEvents.capacityUnit (capR hκ h12p βA b jumps c₀ h W' ζ' s r)) d.p₀ := by
  have hle : ∀ l, rootSigma hκ h12p βA c₀ h W' ζ' s r l ≤ mΩ :=
    fun l => stageSigma_le hβA hh hcf s _ _
  refine testClaims_of_crossing_and_comparison hβA hh hcf hQ hm.hG
    d.ang d.X d.γ d.S d.F d.I hm.hI ?_ ?_ hm.hReg ?_
    (fun l a => d.sample l a ⁻¹' d.slow l a)
    (fun l a => hm.hSample l a (hm.hSlowMeas l a)) hm.hp₀ hm.hp₀1 ?_ hm.hUnit
  · intro l a q q' hqq'
    change MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r
      ((d.ang a, q') :: l)] (d.tests l a q)
    rw [d.tests_eq_preimage_observation l a q]
    exact hm.hObs l a q q' hqq'
      ((hm.hI l a).measurableSet.prod QuantumZipper.isOpen_H.measurableSet)
  · intro l
    exact (measurable_capR_iff hκ h12p βA c₀ h b jumps hβA hh
      s W' ζ' hcf r l).2 (hm.hCap l)
  · intro l ε hε
    have heq := ae_all_iff.2 fun a =>
      ae_condExpKernel_event_eq_of_map (hle l) (hm.hSample l a)
        (hm.hReachMeas l a) (hm.hLaw l a) (hm.hReachIdent l a)
    filter_upwards [heq, hm.hModelCross l ε hε] with ω hωeq hωcross hωA
    obtain ⟨a, ha⟩ := hωcross hωA
    exact ⟨a, (hωeq a hωA).symm ▸ ha⟩
  · intro k l hl a C hC hCA
    exact le_measure_inter_preimage_of_map (hle l) (hm.hSample l a)
      (hm.hSlowMeas l a) (hm.hLaw l a) (hm.hModelSlow k l hl a) hC hCA

end Root

end InteractingSLE.Theorem14.GW2TipSystem.RootK3
