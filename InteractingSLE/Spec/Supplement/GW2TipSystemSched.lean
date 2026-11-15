/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TipSystemSelect
import InteractingSLE.Spec.Supplement.KernelTower

/-!
# GW2's stage experiment: the adaptive tree from non-adaptive per-schedule kernels

Packet PROVE-T14-TIP12. In GW2's stage experiment (follow-up note A.2–A.5,
`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L80–L241; GB9, `source/spec/p481-528.md` L1082–L1100) the
stage from a realized history uses "the retained kernel at state `z`" of **that** history, and "Every successful
finite history uses only `Θ` and `Q`. Canonical field determination and consistency identify it with a member of the
originally fixed countable family, even though its indices were chosen from revealed histories." So every stage-start
state is the state of one **fixed** schedule (a root and finitely many angle–time entries), and every statement about a
stage is a statement about a fixed schedule, non-adaptive: its stage-start σ-algebra `𝒢 s` (the counterflow history
and the canonical prefix of `s`), its regular conditional law `condExpKernel P (𝒢 s)`, the success events `E s i` of
the countably many rules `i` from `s`, the outcomes `O s i o` (switching at the candidate `o`, which extends `s` by
the entry `entry i o`).

This file builds the adaptive construction from these non-adaptive data and proves its validity:

* `SchedRule`: the per-schedule data, with an "alive" event `A s` (the prefix of `s` is available, interior and
  separated: the event on which the stage bounds are claimed);
* `SchedRule.toRule`: the stage rule (`GW2TipSystem.StageRule`) whose nodes are a root and the realized
  rule–outcome pairs; the schedule of a node is `sched`; the information at a node is `𝒢 (sched n)`; the outcome
  `(i, o)` of the stage from `n` is `selOut` of the kernel `condExpKernel P (𝒢 (sched n))` (least rule index with
  conditional success probability `≥ 1 − ε_j`);
* `SchedRule.IsValid`: the per-schedule statements — measurability and monotonicity of the schedule σ-algebras, the
  outcome events known at the extended schedule, disjoint outcomes of one rule, **the stage claim of A.3–A.4 at a fixed
  schedule** (`hstep`: almost surely on `A s` some rule succeeds with conditional probability at least `1 − ε_j`),
  **the uniform Lemma 5.10 at a fixed schedule** (`hunit`), the initial cover, the capacity bookkeeping on `A`;
* **`SchedRule.IsValid.toRule_isValid`**: a valid schedule rule gives a valid stage rule, hence (by
  `GW2TipSystem.StageRule.IsValid.toSystem_isValid`) a valid stage system;
* **`ae_not_isBounded_of_schedRules`**: unboundedness of the target from valid schedule rules for every tolerance.

The statements are generic (no SLE content).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSystem

open Supp8.GB9Stop

/-- **Non-adaptive per-schedule data of an alternating construction.** A schedule is a root and a list of entries,
the latest first. -/
structure SchedRule (Ω : Type*) [MeasurableSpace Ω] where
  /-- The roots (initial prefixes). -/
  ι : Type
  /-- The schedule entries (an angle and a switching time). -/
  X : Type
  /-- The outcomes of one rule (the switching candidates). -/
  K : Type
  countableι : Countable ι
  countableX : Countable X
  countableK : Countable K
  /-- The stage-start information of a fixed schedule. -/
  𝒢 : ι × List X → MeasurableSpace Ω
  /-- The event of a root. -/
  R₀ : ι → Set Ω
  /-- The event on which the stage bounds from a schedule are claimed. -/
  A : ι × List X → Set Ω
  /-- The success event of rule `i` from a schedule. -/
  E : ι × List X → ℕ → Set Ω
  /-- The outcome `o` of rule `i` from a schedule. -/
  O : ι × List X → ℕ → K → Set Ω
  /-- The entry by which outcome `o` of rule `i` extends the schedule. -/
  entry : ℕ → K → X
  /-- The unit event of the stage ending at a schedule. -/
  V : ι × List X → Set Ω
  /-- An event containing "rule `i` succeeds and the stage consumes no unit". -/
  D : ι × List X → ℕ → Set Ω
  /-- The failure tolerance of the stage from depth `j`. -/
  ε : ℕ → ℝ≥0∞
  /-- The unit probability of the even stages. -/
  p₀ : ℝ
  /-- The relative capacity of a schedule's prefix. -/
  cap : ι × List X → Ω → ℝ

namespace SchedRule

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (T : SchedRule Ω)

/-- The schedule of a node: the entries of its realized rule–outcome pairs. -/
def sched (n : T.ι × List (ℕ × T.K)) : T.ι × List T.X := (n.1, n.2.map fun c => T.entry c.1 c.2)

@[simp] theorem sched_nil (r : T.ι) : T.sched (r, []) = (r, []) := rfl

@[simp] theorem sched_cons (r : T.ι) (c : ℕ × T.K) (l : List (ℕ × T.K)) :
    T.sched (r, c :: l) = (r, T.entry c.1 c.2 :: (T.sched (r, l)).2) := rfl

@[simp] theorem sched_fst (n : T.ι × List (ℕ × T.K)) : (T.sched n).1 = n.1 := rfl

theorem length_sched (n : T.ι × List (ℕ × T.K)) : (T.sched n).2.length = n.2.length := by
  simp [sched]

/-- The outcome `(i, o)` of the stage from a node: the least qualifying rule of the node's schedule kernel, then the
outcome. -/
def succ (P : Measure Ω) [IsFiniteMeasure P] [StandardBorelSpace Ω] (n : T.ι × List (ℕ × T.K)) (c : ℕ × T.K) :
    Set Ω :=
  @selOut Ω Ω T.K (T.𝒢 (T.sched n)) mΩ (condExpKernel P (T.𝒢 (T.sched n))) id (T.E (T.sched n))
    (T.ε n.2.length) (T.O (T.sched n)) c

/-- **The stage rule of a schedule rule.** -/
def toRule (P : Measure Ω) [IsFiniteMeasure P] [StandardBorelSpace Ω] : StageRule Ω where
  ι := T.ι
  C := ℕ × T.K
  countableι := T.countableι
  countableC := by
    have := T.countableK
    infer_instance
  𝓕 n := T.𝒢 (T.sched n)
  R₀ := T.R₀
  succ := T.succ P
  U n := T.V (T.sched n)
  ε := T.ε
  p₀ := T.p₀
  cap n := T.cap (T.sched n)

/-- **Validity of a schedule rule**: the per-schedule statements. -/
structure IsValid (P : Measure Ω) [IsFiniteMeasure P] [StandardBorelSpace Ω] (G : Set Ω) (S : Ω → Set ℂ)
    (ε₀ : ℝ≥0∞) : Prop where
  h𝒢 : ∀ s, T.𝒢 s ≤ mΩ
  h𝒢mono : ∀ r l x, T.𝒢 (r, l) ≤ T.𝒢 (r, x :: l)
  hR₀ : ∀ r, MeasurableSet[T.𝒢 (r, [])] (T.R₀ r)
  hR₀disj : Pairwise fun r r' => Disjoint (T.R₀ r) (T.R₀ r')
  hR₀A : ∀ r, T.R₀ r ⊆ T.A (r, [])
  hE : ∀ s i, MeasurableSet (T.E s i)
  hO : ∀ r l i o, MeasurableSet[T.𝒢 (r, T.entry i o :: l)] (T.O (r, l) i o)
  hOdisj : ∀ s i, Pairwise fun o o' => Disjoint (T.O s i o) (T.O s i o')
  hEO : ∀ s i, T.E s i ⊆ ⋃ o, T.O s i o
  hOA : ∀ r l i o, T.O (r, l) i o ⊆ T.A (r, T.entry i o :: l)
  hV : ∀ s, MeasurableSet[T.𝒢 s] (T.V s)
  hD : ∀ s i, MeasurableSet (T.D s i)
  hOD : ∀ r l i o, T.O (r, l) i o \ T.V (r, T.entry i o :: l) ⊆ T.D (r, l) i
  /-- **The stage claim at a fixed schedule** (A.3–A.4: "Lemma A.1 therefore gives a successful interior
  `Q`-switch with conditional probability greater than `1 − ε`"). -/
  hstep : ∀ s, ∀ᵐ ω ∂P, ω ∈ T.A s → ∃ i, 1 - T.ε s.2.length ≤ condExpKernel P (T.𝒢 s) ω (T.E s i)
  hp₀ : 0 < T.p₀
  hp₀1 : T.p₀ ≤ 1
  /-- **The uniform Lemma 5.10 at a fixed schedule** (A.5: "every reached even stage `j ≥ 4` has conditional
  probability at least `p₀` to abort or consume at least one unit of relative capacity"). -/
  hunit : ∀ (k : ℕ) s, s.2.length = 2 * k + 4 → ∀ᵐ ω ∂P, ω ∈ T.A s → ∀ i,
    condExpKernel P (T.𝒢 s) ω (T.D s i) ≤ ENNReal.ofReal (1 - T.p₀)
  hε : ∑' j, T.ε j ≤ ε₀
  hcover : ∀ᵐ ω ∂P, ω ∈ G → ∃ r, ω ∈ T.R₀ r
  hcapMono : ∀ r l x, ∀ ω ∈ T.A (r, x :: l), T.cap (r, l) ω ≤ T.cap (r, x :: l) ω
  hcapU : ∀ r l x, ∀ ω ∈ T.A (r, x :: l), ω ∈ T.V (r, x :: l) → T.cap (r, l) ω + 1 ≤ T.cap (r, x :: l) ω
  hcapB : ∀ s, ∀ ω ∈ T.A s, ∀ ρ : ℝ, S ω ⊆ Metric.closedBall 0 ρ → T.cap s ω ≤ 2 * ρ ^ 2

variable {T}

section Valid

variable {P : Measure Ω} [IsFiniteMeasure P] [StandardBorelSpace Ω] {G : Set Ω} {S : Ω → Set ℂ}
  {ε₀ : ℝ≥0∞}

/-- A realized node is alive for its schedule. -/
theorem IsValid.real_subset_A (hv : T.IsValid P G S ε₀) (r : T.ι) (l : List (ℕ × T.K)) :
    (T.toRule P).real (r, l) ⊆ T.A (T.sched (r, l)) := by
  cases l with
  | nil => exact hv.hR₀A r
  | cons c l =>
    intro ω hω
    have h := hω.2.2
    rw [sched_cons]
    exact hv.hOA r (T.sched (r, l)).2 c.1 c.2 h

/-- **A valid schedule rule gives a valid stage rule.** -/
theorem IsValid.toRule_isValid (hv : T.IsValid P G S ε₀) : (T.toRule P).IsValid P G S ε₀ := by
  -- the kernel identity of a node's schedule kernel
  have hK : ∀ s : T.ι × List T.X, ∀ (C : Set Ω) (B : Set Ω), MeasurableSet[T.𝒢 s] C → MeasurableSet B →
      P (id ⁻¹' C ∩ B) = ∫⁻ ω in id ⁻¹' C, condExpKernel P (T.𝒢 s) (id ω) B ∂P := fun s C B hC hB =>
    (KernelTower.setLIntegral_condExpKernel (hv.h𝒢 s) hC hB).symm
  have hZ : ∀ s : T.ι × List T.X, @Measurable Ω Ω mΩ (T.𝒢 s) id := fun s => measurable_id'' (hv.h𝒢 s)
  refine
    { h𝓕 := fun n => hv.h𝒢 _, h𝓕succ := ?_, hR₀ := hv.hR₀, hsucc := ?_, hR₀disj := hv.hR₀disj,
      hsuccdisj := ?_, hU := fun n => hv.hV _, hstep := ?_, hp₀ := hv.hp₀, hp₀1 := hv.hp₀1, hunit := ?_,
      hε := hv.hε, hcover := hv.hcover, hcapMono := ?_, hcapU := ?_, hcapB := ?_ }
  · intro (r : T.ι) (l : List (ℕ × T.K)) (c : ℕ × T.K)
    change T.𝒢 (T.sched (r, l)) ≤ T.𝒢 (T.sched (r, c :: l))
    rw [sched_cons]
    exact hv.h𝒢mono r _ _
  · intro (r : T.ι) (l : List (ℕ × T.K)) (c : ℕ × T.K)
    change MeasurableSet[T.𝒢 (T.sched (r, c :: l))] (T.succ P (r, l) c)
    rw [sched_cons]
    refine MeasurableSet.inter ?_ (hv.hO r (T.sched (r, l)).2 c.1 c.2)
    have h := @measurableSet_selIndex_eq Ω Ω (T.𝒢 (T.sched (r, l))) mΩ (condExpKernel P (T.𝒢 (T.sched (r, l))))
      id (T.E (T.sched (r, l))) (hv.hE _) (T.ε l.length) c.1
    rw [MeasurableSpace.comap_id] at h
    exact hv.h𝒢mono r _ _ _ h
  · intro (n : T.ι × List (ℕ × T.K))
    exact @pairwise_disjoint_selOut Ω Ω T.K (T.𝒢 (T.sched n)) mΩ _ id _ _ _ (hv.hOdisj _)
  · intro (n : T.ι × List (ℕ × T.K)) B hB hBR
    have hex : ∀ᵐ ω ∂P, ω ∈ id ⁻¹' B → ∃ i, 1 - T.ε n.2.length ≤
        condExpKernel P (T.𝒢 (T.sched n)) (id ω) (T.E (T.sched n) i) := by
      filter_upwards [hv.hstep (T.sched n)] with ω hω hωB
      have h := hω (hv.real_subset_A n.1 n.2 (hBR hωB))
      rwa [length_sched] at h
    exact @measure_diff_iUnion_selOut_le Ω Ω T.K (T.𝒢 (T.sched n)) mΩ P (condExpKernel P (T.𝒢 (T.sched n)))
      _ id (hZ _) (T.E (T.sched n)) (hv.hE _) (T.O (T.sched n)) (hv.hEO _) (hK _) (T.ε n.2.length) B hB hex
  · intro k (n : T.ι × List (ℕ × T.K)) B hk hB hBR
    have hp : ∀ᵐ ω ∂P, ω ∈ id ⁻¹' B →
        condExpKernel P (T.𝒢 (T.sched n)) (id ω) (T.D (T.sched n)
          (@selIndex Ω Ω (T.𝒢 (T.sched n)) mΩ (condExpKernel P (T.𝒢 (T.sched n))) (T.E (T.sched n))
            (T.ε n.2.length) (id ω))) ≤
          ENNReal.ofReal (1 - T.p₀) := by
      have hk' : (T.sched n).2.length = 2 * k + 4 := by rw [length_sched]; exact hk
      filter_upwards [hv.hunit k (T.sched n) hk'] with ω hω hωB
      exact hω (hv.real_subset_A n.1 n.2 (hBR hωB)) _
    have hOD : ∀ i o, T.O (T.sched n) i o \ T.V (n.1, T.entry i o :: (T.sched n).2) ⊆ T.D (T.sched n) i :=
      fun i o => hv.hOD n.1 (T.sched n).2 i o
    have h := @measure_inter_iUnion_selOut_diff_le Ω Ω T.K (T.𝒢 (T.sched n)) mΩ P
      (condExpKernel P (T.𝒢 (T.sched n))) id (hZ _) (T.E (T.sched n)) (hv.hE _) (T.O (T.sched n))
      (fun i o => T.V (n.1, T.entry i o :: (T.sched n).2)) (T.D (T.sched n)) (hv.hD _) hOD (hK _)
      (T.ε n.2.length) (ENNReal.ofReal (1 - T.p₀)) B hB hp
    exact h
  · intro (r : T.ι) (l : List (ℕ × T.K)) (c : ℕ × T.K) ω hω
    have h := hv.real_subset_A r (c :: l) hω
    change T.cap (T.sched (r, l)) ω ≤ T.cap (T.sched (r, c :: l)) ω
    rw [sched_cons] at h ⊢
    exact hv.hcapMono r _ _ ω h
  · intro (r : T.ι) (l : List (ℕ × T.K)) (c : ℕ × T.K) ω hω hU
    have h := hv.real_subset_A r (c :: l) hω
    change ω ∈ T.V (T.sched (r, c :: l)) at hU
    change T.cap (T.sched (r, l)) ω + 1 ≤ T.cap (T.sched (r, c :: l)) ω
    rw [sched_cons] at h hU ⊢
    exact hv.hcapU r _ _ ω h hU
  · intro (n : T.ι × List (ℕ × T.K)) ω hω ρ hρ
    exact hv.hcapB (T.sched n) ω (hv.real_subset_A n.1 n.2 hω) ρ hρ

end Valid

end SchedRule

/-- **Unboundedness from valid schedule rules for every tolerance** (follow-up note A.5): the adaptive construction
along the countable tree of rule–outcome histories (`SchedRule.toRule`), validity transferred to the stage rule and the
stage system, and the iteration of `GW2TipStage.ae_not_isBounded_of_stageSystems`. -/
theorem ae_not_isBounded_of_schedRules {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {G : Set Ω} {S : Ω → Set ℂ}
    (hT : ∀ ε₀ : ℝ≥0∞, 0 < ε₀ → ∃ T : SchedRule Ω, T.IsValid P G S ε₀) :
    ∀ᵐ ω ∂P, ω ∈ G → ¬ Bornology.IsBounded (S ω) :=
  ae_not_isBounded_of_stageRules fun ε₀ hε₀ => by
    obtain ⟨T, hv⟩ := hT ε₀ hε₀
    exact ⟨T.toRule P, hv.toRule_isValid⟩

end GW2TipSystem

end Theorem14

end InteractingSLE
