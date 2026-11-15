/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TipStageTree

/-!
# GW2's stage experiment: the tree of histories from local stage rules

Packet PROVE-T14-TIP12. PROVE-T14-TIP11 reduced GW2's tip exhaustion to a valid stage system
(`GW2TipStage.StageSystem.IsValid`), whose fields are global statements about a whole tree: disjointness of all
reached nodes of one depth, containment in the parent, a success bound at every node. In the source the tree is built
**stage by stage** (follow-up note A.2–A.5, `source/external/AstraIG1/ig1_followup_a_e_audited.txt` L80–L241; GB9,
`source/spec/p481-528.md` L1082–L1100, pp. 525–526): "Retain a canonical stage-start history and its conditional
next-piece kernel"; the stage either succeeds with one of countably many outcomes (a rule index and a switching time
in `Q`) or aborts; "Every successful finite history uses only `Θ` and `Q`".

This file builds the stage system from such **local** data and proves its validity from **per-node** statements:

* `StageRule`: countable roots `ι` (the initial prefixes of A.5's countable cover), countable stage outcomes `C`, the
  stage-start information `𝓕` and the unit event `U` of every node (a root and the list of the realized outcomes,
  latest first), the initial events `R₀`, the outcome events `succ n c` of the stage started at node `n`;
* `StageRule.real`: the event that a node is realized (the root's event, then the outcomes in order);
* `StageRule.toSystem`: the stage system (depth = number of stages, parent = drop the latest outcome);
* `StageRule.IsValid`: the local statements — the outcome events of one stage are pairwise disjoint and known at the
  child, the stage-start information grows along the tree, the one-stage success bound `P(B \ ⋃_c succ n c) ≤ ε_j P(B)`
  and the unit bound for the stage started at `n`, the initial cover, the capacity bookkeeping;
* **`StageRule.IsValid.toSystem_isValid`**: a valid stage rule gives a valid stage system (the global disjointness by
  induction along the two histories, the reached events by recursion);
* **`ae_not_isBounded_of_stageRules`**: hence the unboundedness conclusion of
  `GW2TipStage.ae_not_isBounded_of_stageSystems`.

The statements are generic (no SLE content).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSystem

open GW2TipStage

/-- **A stage rule**: the local data of an adaptive alternating construction. A node is a root and the list of the
realized stage outcomes, the latest first. -/
structure StageRule (Ω : Type*) [MeasurableSpace Ω] where
  /-- The roots (initial prefixes of the countable initial cover). -/
  ι : Type
  /-- The outcomes of one stage. -/
  C : Type
  /-- The roots are countably many. -/
  countableι : Countable ι
  /-- The outcomes are countably many. -/
  countableC : Countable C
  /-- The information at the start of the stage from a node. -/
  𝓕 : ι × List C → MeasurableSpace Ω
  /-- The event of a root. -/
  R₀ : ι → Set Ω
  /-- The event that the stage started at a node has a given outcome. -/
  succ : ι × List C → C → Set Ω
  /-- The event that the stage ending at a node consumed a unit of relative capacity. -/
  U : ι × List C → Set Ω
  /-- The failure tolerance of the stage from depth `j`. -/
  ε : ℕ → ℝ≥0∞
  /-- The unit probability of the even stages. -/
  p₀ : ℝ
  /-- The relative capacity of a realized node. -/
  cap : ι × List C → Ω → ℝ

namespace StageRule

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (T : StageRule Ω)

/-- The event that the outcomes `l` (latest first) are realized from the root `r`. -/
def realL (r : T.ι) : List T.C → Set Ω
  | [] => T.R₀ r
  | c :: l => realL r l ∩ T.succ (r, l) c

/-- **The event that a node is realized.** -/
def real (n : T.ι × List T.C) : Set Ω := T.realL n.1 n.2

@[simp] theorem real_nil (r : T.ι) : T.real (r, []) = T.R₀ r := rfl

@[simp] theorem real_cons (r : T.ι) (c : T.C) (l : List T.C) :
    T.real (r, c :: l) = T.real (r, l) ∩ T.succ (r, l) c := rfl

theorem real_cons_subset (r : T.ι) (c : T.C) (l : List T.C) : T.real (r, c :: l) ⊆ T.real (r, l) :=
  inter_subset_left

/-- **The stage system of a stage rule**: nodes `ι × List C`, depth = number of stages, parent = drop the latest
outcome. -/
def toSystem : StageSystem Ω where
  N := T.ι × List T.C
  countable := by
    have := T.countableι
    have := T.countableC
    infer_instance
  depth n := n.2.length
  par n := (n.1, n.2.tail)
  𝓕 := T.𝓕
  R := T.real
  U := T.U
  ε := T.ε
  p₀ := T.p₀
  cap := T.cap

/-- **Validity of a stage rule** for the target "`S ω` is unbounded on `G`", with total tolerance `ε₀`: the local
statements of the stage-by-stage construction. -/
structure IsValid (P : Measure Ω) (G : Set Ω) (S : Ω → Set ℂ) (ε₀ : ℝ≥0∞) : Prop where
  h𝓕 : ∀ n, T.𝓕 n ≤ mΩ
  h𝓕succ : ∀ r l c, T.𝓕 (r, l) ≤ T.𝓕 (r, c :: l)
  hR₀ : ∀ r, MeasurableSet[T.𝓕 (r, [])] (T.R₀ r)
  hsucc : ∀ r l c, MeasurableSet[T.𝓕 (r, c :: l)] (T.succ (r, l) c)
  hR₀disj : Pairwise fun r r' => Disjoint (T.R₀ r) (T.R₀ r')
  hsuccdisj : ∀ n, Pairwise fun c c' => Disjoint (T.succ n c) (T.succ n c')
  hU : ∀ n, MeasurableSet[T.𝓕 n] (T.U n)
  hstep : ∀ n B, MeasurableSet[T.𝓕 n] B → B ⊆ T.real n →
    P (B \ ⋃ c, T.succ n c) ≤ T.ε n.2.length * P B
  hp₀ : 0 < T.p₀
  hp₀1 : T.p₀ ≤ 1
  hunit : ∀ (k : ℕ) n B, n.2.length = 2 * k + 4 → MeasurableSet[T.𝓕 n] B → B ⊆ T.real n →
    P (B ∩ ⋃ c, (T.succ n c \ T.U (n.1, c :: n.2))) ≤ ENNReal.ofReal (1 - T.p₀) * P B
  hε : ∑' j, T.ε j ≤ ε₀
  hcover : ∀ᵐ ω ∂P, ω ∈ G → ∃ r, ω ∈ T.R₀ r
  hcapMono : ∀ r l c, ∀ ω ∈ T.real (r, c :: l), T.cap (r, l) ω ≤ T.cap (r, c :: l) ω
  hcapU : ∀ r l c, ∀ ω ∈ T.real (r, c :: l), ω ∈ T.U (r, c :: l) → T.cap (r, l) ω + 1 ≤ T.cap (r, c :: l) ω
  hcapB : ∀ n, ∀ ω ∈ T.real n, ∀ ρ : ℝ, S ω ⊆ Metric.closedBall 0 ρ → T.cap n ω ≤ 2 * ρ ^ 2

variable {T}

/-- The realized events are known at their node. -/
theorem IsValid.measurableSet_real {P : Measure Ω} {G : Set Ω} {S : Ω → Set ℂ} {ε₀ : ℝ≥0∞}
    (hv : T.IsValid P G S ε₀) (n : T.ι × List T.C) : MeasurableSet[T.𝓕 n] (T.real n) := by
  obtain ⟨r, l⟩ := n
  induction l with
  | nil => exact hv.hR₀ r
  | cons c l ih => exact (hv.h𝓕succ r l c _ ih).inter (hv.hsucc r l c)

/-- **Realized nodes of one depth are disjoint** (induction along the two histories: equal parents and different
outcomes, or disjoint parents). -/
theorem IsValid.disjoint_real {P : Measure Ω} {G : Set Ω} {S : Ω → Set ℂ} {ε₀ : ℝ≥0∞}
    (hv : T.IsValid P G S ε₀) (r : T.ι) (l : List T.C) :
    ∀ (r' : T.ι) (l' : List T.C), l.length = l'.length → (r, l) ≠ (r', l') →
      Disjoint (T.real (r, l)) (T.real (r', l')) := by
  induction l with
  | nil =>
    intro r' l' hlen hne
    have hl' : l' = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst hl'
    have hr : r ≠ r' := fun h => hne (by rw [h])
    exact hv.hR₀disj hr
  | cons c l ih =>
    intro r' l' hlen hne
    cases l' with
    | nil => exact absurd hlen (by simp)
    | cons c' l' =>
      have hlen' : l.length = l'.length := by simpa using hlen
      by_cases hpar : (r, l) = (r', l')
      · have hc : c ≠ c' := by
          intro hcc
          apply hne
          rw [Prod.mk.injEq] at hpar ⊢
          exact ⟨hpar.1, by rw [hpar.2, hcc]⟩
        rw [real_cons, real_cons, ← hpar]
        exact (hv.hsuccdisj (r, l) hc).mono inter_subset_right inter_subset_right
      · exact (ih r' l' hlen' hpar).mono (real_cons_subset T r c l) (real_cons_subset T r' c' l')

/-- **A valid stage rule gives a valid stage system.** -/
theorem IsValid.toSystem_isValid {P : Measure Ω} {G : Set Ω} {S : Ω → Set ℂ} {ε₀ : ℝ≥0∞}
    (hv : T.IsValid P G S ε₀) : T.toSystem.IsValid P G S ε₀ := by
  -- the parent of a node of positive depth
  have hcons : ∀ n : T.ι × List T.C, 0 < n.2.length → ∃ c l, n = (n.1, c :: l) := by
    rintro ⟨r, l⟩ h
    cases l with
    | nil => exact absurd h (by simp)
    | cons c l => exact ⟨c, l, rfl⟩
  -- a realized child of a node of depth `j` is a child of that node
  have hchild : ∀ (n : T.ι × List T.C) (m : T.ι × List T.C) (ω : Ω), ω ∈ T.real n → ω ∈ T.real m →
      m.2.length = n.2.length + 1 → ∃ c, m = (n.1, c :: n.2) ∧ ω ∈ T.succ n c := by
    rintro ⟨r, l⟩ ⟨r', l'⟩ ω hn hm hlen
    cases l' with
    | nil => exact absurd hlen (by simp)
    | cons c l' =>
      have hlen' : l.length = l'.length := by simpa using hlen.symm
      have hpar : (r, l) = (r', l') := by
        by_contra hne
        exact (hv.disjoint_real r l r' l' hlen' hne).le_bot ⟨hn, real_cons_subset T r' c l' hm⟩
      rw [Prod.mk.injEq] at hpar
      obtain ⟨rfl, rfl⟩ := hpar
      exact ⟨c, rfl, hm.2⟩
  refine
    { hpar := ?_, h𝓕 := hv.h𝓕, h𝓕par := ?_, hR := hv.measurableSet_real, hRpar := ?_, hdisj := ?_,
      hU := hv.hU, hstep := ?_, hp₀ := hv.hp₀, hp₀1 := hv.hp₀1, hunit := ?_, hε := hv.hε, hcover := ?_,
      hcapMono := ?_, hcapU := ?_, hcapB := hv.hcapB }
  · intro n hn
    obtain ⟨c, l, hcl⟩ := hcons n hn
    change n.2.tail.length + 1 = n.2.length
    rw [hcl]
    simp
  · intro n hn
    obtain ⟨c, l, hcl⟩ := hcons n hn
    change T.𝓕 (n.1, n.2.tail) ≤ T.𝓕 n
    rw [hcl]
    exact hv.h𝓕succ n.1 l c
  · intro n hn
    obtain ⟨c, l, hcl⟩ := hcons n hn
    change T.real n ⊆ T.real (n.1, n.2.tail)
    rw [hcl]
    exact real_cons_subset T n.1 c l
  · rintro ⟨r, l⟩ ⟨r', l'⟩ hlen hne
    exact hv.disjoint_real r l r' l' hlen hne
  · intro n B hB hBR
    have hsub : B \ reachedAt T.toSystem.depth T.toSystem.R (T.toSystem.depth n + 1) ⊆
        B \ ⋃ c, T.succ n c := by
      intro ω hω
      refine ⟨hω.1, fun hU => hω.2 ?_⟩
      obtain ⟨c, hc⟩ := mem_iUnion.1 hU
      simp only [reachedAt, mem_iUnion]
      refine ⟨(n.1, c :: n.2), ?_, ?_⟩
      · change (c :: n.2).length = n.2.length + 1
        simp
      · change ω ∈ T.real (n.1, c :: n.2)
        rw [real_cons]
        exact ⟨hBR hω.1, hc⟩
    exact le_trans (measure_mono hsub) (hv.hstep n B hB hBR)
  · intro k n B hk hB hBR
    have hsub : B ∩ (reachedAt T.toSystem.depth T.toSystem.R (T.toSystem.depth n + 1) \
        unitAt T.toSystem.depth T.toSystem.R T.toSystem.U (T.toSystem.depth n)) ⊆
        B ∩ ⋃ c, (T.succ n c \ T.U (n.1, c :: n.2)) := by
      rintro ω ⟨hωB, hreach, hnunit⟩
      refine ⟨hωB, ?_⟩
      simp only [reachedAt, mem_iUnion] at hreach
      obtain ⟨m, hm, hωm⟩ := hreach
      obtain ⟨c, rfl, hcs⟩ := hchild n m ω (hBR hωB) hωm hm
      refine mem_iUnion.2 ⟨c, hcs, fun hUc => hnunit ?_⟩
      simp only [unitAt, mem_iUnion]
      exact ⟨(n.1, c :: n.2), hm, hωm, hUc⟩
    exact le_trans (measure_mono hsub) (hv.hunit k n B hk hB hBR)
  · filter_upwards [hv.hcover] with ω hω hG
    obtain ⟨r, hr⟩ := hω hG
    simp only [reachedAt, mem_iUnion]
    exact ⟨(r, []), rfl, hr⟩
  · intro n hn ω hω
    obtain ⟨c, l, hcl⟩ := hcons n hn
    change T.cap (n.1, n.2.tail) ω ≤ T.cap n ω
    change ω ∈ T.real n at hω
    rw [hcl] at hω ⊢
    exact hv.hcapMono n.1 l c ω hω
  · intro n hn ω hω hU
    obtain ⟨c, l, hcl⟩ := hcons n hn
    change T.cap (n.1, n.2.tail) ω + 1 ≤ T.cap n ω
    change ω ∈ T.real n at hω
    change ω ∈ T.U n at hU
    rw [hcl] at hω hU ⊢
    exact hv.hcapU n.1 l c ω hω hU

end StageRule

/-- **Unboundedness from valid stage rules for every tolerance** (follow-up note A.5, via
`GW2TipStage.ae_not_isBounded_of_stageSystems`). -/
theorem ae_not_isBounded_of_stageRules {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Set Ω} {S : Ω → Set ℂ} (hT : ∀ ε₀ : ℝ≥0∞, 0 < ε₀ → ∃ T : StageRule Ω, T.IsValid P G S ε₀) :
    ∀ᵐ ω ∂P, ω ∈ G → ¬ Bornology.IsBounded (S ω) :=
  ae_not_isBounded_of_stageSystems fun ε₀ hε₀ => by
    obtain ⟨T, hv⟩ := hT ε₀ hε₀
    exact ⟨T.toSystem, hv.toSystem_isValid⟩

end GW2TipSystem

end Theorem14

end InteractingSLE
