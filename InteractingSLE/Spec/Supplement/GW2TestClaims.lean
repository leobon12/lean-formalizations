/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TestEvents

/-!
# Conditional assembly of GW2's repaired root tests

Packet PROVE-GW2-TEST. This file proves `testClaims_of_crossing_and_comparison`.
Its inputs are explicitly conditional: observable joint-chart experiments,
measurable regularized capacity, crossing estimates in the complete retained
filtration, and a slow-event comparison with its geometric capacity implication.
It does not discharge these inputs or prove `GW2RootTestStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem

open GW2Schedule Exist Staged StagedLaw Restart LQGMetric

section Events

variable {Ω : Type*} {Θ : Set ℝ} {Q : Set ℝ≥0}

/-- The actual candidate tests of all the stage experiments. -/
def experimentTests (X : List (EntryIdx Θ Q) → ℕ → Ω → ℝ → ℝ)
    (γ : List (EntryIdx Θ Q) → ℕ → Ω → ℝ → ℂ)
    (S F : List (EntryIdx Θ Q) → ℕ → Ω → ℝ)
    (I : List (EntryIdx Θ Q) → ℕ → Set ℝ) :
    List (EntryIdx Θ Q) → ℕ → Q → Set Ω :=
  fun l a q => TestCross.candidateTest (X l a) (γ l a) (S l a) (F l a) (I l a) q

end Events

section Root

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] (h : Ω → DistOn upperHalfPlaneOpens)
  (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {Θ : Set ℝ} {Q : Set ℝ≥0}
  (s : ℝ≥0) (r : ScaledRootIdx Θ Q)

omit mΩ in
/-- The inherited record is measurable after any further prescribed switch. -/
theorem rootSigma_le_cons (l : List (EntryIdx Θ Q)) (x : EntryIdx Θ Q) :
    rootSigma hκ h12p βA c₀ h W' ζ' s r l ≤
      rootSigma hκ h12p βA c₀ h W' ζ' s r (x :: l) := by
  change stageSigma hκ h12p βA c₀ h s W' ζ'
      (schedSpec (rootPt r.1) (schedOf (rootEntry r.1) (entryList l)))
      ((entryList l).length + 1) ≤
    stageSigma hκ h12p βA c₀ h s W' ζ'
      (schedSpec (rootPt r.1) (schedOf (rootEntry r.1) (entryList (x :: l))))
      ((entryList (x :: l)).length + 1)
  rw [entryList_cons]
  exact stageSigma_schedOf_mono s W' ζ' (rootPt r.1) (rootEntry r.1) _ (entryList l)

variable {hκ h12p βA b jumps c₀ h W' ζ' s r}

/-- Assemble per-candidate claims from joint-chart crossing experiments and a
slow-event comparison. Every unproved probabilistic or geometric input appears
with its full Lean type; no source theorem is replaced by this conditional helper.

`hreach` is the remaining retained-kernel crossing assertion. `hcomp` can be
supplied by `Sec5.Prop59Stage.IsStageLaw.le_measure`; `hslow` is its deterministic
capacity consequence. The events chosen here discharge all alive and unit
bookkeeping, including the exact `hcapU` clause. -/
theorem testClaims_of_crossing_and_comparison [StandardBorelSpace Ω]
    (hβA : Measurable βA) (hh : Measurable h)
    {P : Measure Ω} [IsFiniteMeasure P] (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hQ : Dense Q) {G : Set Ω}
    (hG : MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r []] G)
    (ang : ℕ → Θ)
    (X : List (EntryIdx Θ Q) → ℕ → Ω → ℝ → ℝ)
    (γ : List (EntryIdx Θ Q) → ℕ → Ω → ℝ → ℂ)
    (S F : List (EntryIdx Θ Q) → ℕ → Ω → ℝ)
    (I : List (EntryIdx Θ Q) → ℕ → Set ℝ) (hI : ∀ l a, IsOpen (I l a))
    (hT : ∀ l a (q q' : Q), q ≤ q' →
      MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r ((ang a, q') :: l)]
        (experimentTests X γ S F I l a q))
    (hcap : ∀ l, Measurable[rootSigma hκ h12p βA c₀ h W' ζ' s r l]
      (capR hκ h12p βA b jumps c₀ h W' ζ' s r l))
    (hreg : ∀ l a, ∀ᵐ ω ∂P, S l a ω < F l a ω →
      0 ≤ S l a ω ∧ ContinuousAt (X l a ω) (S l a ω) ∧ X l a ω (S l a ω) ∈ I l a ∧
      ContinuousOn (γ l a ω) (Ioo (S l a ω) (F l a ω)) ∧
      volume {t | t ∈ Ioo (S l a ω) (F l a ω) ∧ γ l a ω t ∉ H} = 0)
    (hreach : ∀ l (ε : ℝ≥0∞), 0 < ε → ∀ᵐ ω ∂P,
      ω ∈ TestEvents.aliveTests G ang (experimentTests X γ S F I) l → ∃ a,
        1 - ε < condExpKernel P (rootSigma hκ h12p βA c₀ h W' ζ' s r l) ω
          {ω' | S l a ω' < F l a ω'})
    (E : List (EntryIdx Θ Q) → ℕ → Set Ω) (hE : ∀ l a, MeasurableSet (E l a))
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hcomp : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ a (C : Set Ω),
      MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r l] C →
      C ⊆ TestEvents.aliveTests G ang (experimentTests X γ S F I) l →
      ENNReal.ofReal p₀ * P C ≤ P (C ∩ E l a))
    (hslow : ∀ l a, ∀ᵐ ω ∂P,
      ω ∈ TestEvents.aliveTests G ang (experimentTests X γ S F I) l →
      ω ∈ E l a → ∀ q : Q, ω ∈ experimentTests X γ S F I l a q →
        capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + 1 ≤
          capR hκ h12p βA b jumps c₀ h W' ζ' s r ((ang a, q) :: l) ω) :
    TestClaims hκ h12p βA b jumps c₀ h W' ζ' s P r G
      (TestEvents.aliveTests G ang (experimentTests X γ S F I)) ang
      (experimentTests X γ S F I)
      (TestEvents.capacityUnit (capR hκ h12p βA b jumps c₀ h W' ζ' s r)) p₀ := by
  have hmono := rootSigma_le_cons hκ h12p βA c₀ h W' ζ' s r
  have hle : ∀ l, rootSigma hκ h12p βA c₀ h W' ζ' s r l ≤ mΩ := fun l =>
    stageSigma_le hβA hh hcf s _ _
  have hA := TestEvents.measurableSet_aliveTests hmono hG
    (fun l a q => hT l a q q le_rfl)
  refine
    { hG := hG
      hGA := Subset.rfl
      hA := hA
      hT := hT
      hTA := TestEvents.aliveTests_inter_subset
      hV := TestEvents.measurableSet_capacityUnit hmono hcap
      hcross := ?_
      hp₀ := hp₀
      hp₀1 := hp₀1
      hnounit := ?_
      hcapU := fun _ _ _ _ hωV => hωV }
  · intro l ε hε
    exact TestCross.ae_exists_candidate_probability (hle l) hQ (hI l) (hreg l)
      (hreach l ε hε)
  · intro k l hl
    have hunit : ∀ a, ∀ᵐ ω ∂P,
        ω ∈ TestEvents.aliveTests G ang (experimentTests X γ S F I) l →
        condExpKernel P (rootSigma hκ h12p βA c₀ h W' ζ' s r l) ω
          (⋃ q : Q, experimentTests X γ S F I l a q \
            TestEvents.capacityUnit
              (capR hκ h12p βA b jumps c₀ h W' ζ' s r) ((ang a, q) :: l)) ≤
          ENNReal.ofReal (1 - p₀) := fun a =>
      TestKernel.ae_no_unit_le_of_comparison (hle l) (hA l) (hE l a) hp₀.le
        (hcomp k l hl a) (hslow l a)
    filter_upwards [ae_all_iff.2 hunit] with ω hω hωA a
    exact hω a hωA

end Root

end InteractingSLE.Theorem14.GW2TipSystem
