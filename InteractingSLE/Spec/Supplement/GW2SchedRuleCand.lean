/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SchedRuleWire

/-!
# GW2's finite-candidate rules (Lemma A.1): rules, outcomes and their bookkeeping

Packet PROVE-GW2-SCHED. Follow-up note A.2, Lemma A.1 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt`
L80–L117): "Enumerate `Q = {q1, q2, …}`. On the full canonical next-piece space set
`E_m = ⋃_{n ≤ m} {S < q_n < F, γ(q_n) ∈ ℍ, X_{q_n} ∈ I_e}` … Inspect the finite list `q1, …, q_{m(z)}` in
chronological order. Stop at its first qualifying member, or at `F` if there is none. Each test at `q` is measurable at
`q` … The rule is therefore a stopping time"; A.4: "enumerate the admissible triples consisting of a buffer, an angle
index and a candidate count, and take the least triple whose finite-candidate success probability exceeds `1 − ε`".

This file builds the rules and outcomes of the one-root rule (`GW2TipSystem.gw2RootRule`) from **test events**:
`Tst s a n` — "the stage from the schedule `s` with rule parameter `a` (a buffer and an angle index) passes the test at
the candidate `q_n`". A rule is a pair `(a, m)` (encoded by `Nat.pair`); its success event is `E = A ∩ ⋃_{n ≤ m} Tst`;
its outcome `o` is "`q_o` is the chronologically first qualifying candidate among `q_0, …, q_m`", which extends the
schedule by the entry `(θ_a, q_o)`; the no-unit event of a rule is the union of its outcomes that consume no unit.

* `GW2CandData` (alive events, angles of the parameters, the candidate enumeration, tests, unit events, tolerances),
  `GW2CandData.toStageData`;
* **`GW2CandData.rootClaims`**: the stage claims of the one-root rule (`SchedRule.RootClaims`) from the per-test claims
  (`CandClaims`: the test at `q_n` is known once the new piece has reached any `q_{n'} ≥ q_n`; a passed test from an
  alive schedule gives an alive extension; the stage and unit claims for these rules) — the outcomes are disjoint
  (`candO_disjoint`, by injectivity of the enumeration), cover the success event (`candE_subset`, the chronologically
  first qualifying candidate), and are known at the extended schedule (`measurableSet_candO`);
* **`GW2RootCandStatement`** (named) and **`gw2RootStageStatement_of_cand`**,
  **`gw2TipExhaustionCanonStatement_of_cand`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSystem

open GW2Schedule GW2Cone GW2Later GW2Tip GW2TipStage Exist Staged StagedLaw Restart LQGMetric

/-- **The finite-candidate data of GW2's stages from one root**: the alive events, the angle of each rule parameter
(a parameter encodes a buffer and an angle index), the enumeration of the candidate times, the test events (schedule,
parameter, candidate index), the unit events, the tolerances and the unit probability. -/
structure GW2CandData (Θ : Set ℝ) (Q : Set ℝ≥0) (Ω : Type u) where
  /-- The event on which the stage bounds from a schedule are claimed. -/
  A : Unit × List (EntryIdx Θ Q) → Set Ω
  /-- The angle of a rule parameter. -/
  ang : ℕ → Θ
  /-- The enumeration of the candidate times. -/
  qe : ℕ → Q
  /-- The test at the candidate `qe n` of the stage from a schedule with a rule parameter. -/
  Tst : Unit × List (EntryIdx Θ Q) → ℕ → ℕ → Set Ω
  /-- The unit event of the stage ending at a schedule. -/
  V : Unit × List (EntryIdx Θ Q) → Set Ω
  /-- The failure tolerance of the stage from depth `j`. -/
  ε : ℕ → ℝ≥0∞
  /-- The unit probability of the even stages. -/
  p₀ : ℝ

namespace GW2CandData

variable {Θ : Set ℝ} {Q : Set ℝ≥0} {Ω : Type u} (c : GW2CandData Θ Q Ω)

/-- The success event of the rule `i = (a, m)` from a schedule: alive, and some candidate among the first `m + 1`
passes. -/
def candE (s : Unit × List (EntryIdx Θ Q)) (i : ℕ) : Set Ω :=
  c.A s ∩ ⋃ n ∈ Finset.range ((Nat.unpair i).2 + 1), c.Tst s (Nat.unpair i).1 n

/-- The outcome `o` of the rule `i = (a, m)`: alive, `o ≤ m`, the candidate `qe o` passes, and no earlier candidate
among the first `m + 1` passes. -/
def candO (s : Unit × List (EntryIdx Θ Q)) (i o : ℕ) : Set Ω :=
  c.A s ∩ {_ω | o ≤ (Nat.unpair i).2} ∩ c.Tst s (Nat.unpair i).1 o ∩
    ⋂ n ∈ Finset.range ((Nat.unpair i).2 + 1), {ω | c.qe n < c.qe o → ω ∉ c.Tst s (Nat.unpair i).1 n}

/-- The entry of the outcome `o` of the rule `i = (a, m)`: the parameter's angle and the candidate time. -/
def candEntry (i o : ℕ) : EntryIdx Θ Q := (c.ang (Nat.unpair i).1, c.qe o)

/-- The no-unit event of the rule `i`: one of its outcomes, without a unit at the extended schedule. -/
def candD (s : Unit × List (EntryIdx Θ Q)) (i : ℕ) : Set Ω :=
  ⋃ o, (c.candO s i o \ c.V (s.1, c.candEntry i o :: s.2))

/-- The stage data of the finite-candidate rules. -/
def toStageData : GW2StageData Θ Q Ω where
  A := c.A
  E := c.candE
  O := c.candO
  entry := c.candEntry
  V := c.V
  D := c.candD
  ε := c.ε
  p₀ := c.p₀

/-- **The outcomes of one rule are disjoint** (the candidate enumeration is injective). -/
theorem candO_disjoint (hqe : Function.Injective c.qe) (s : Unit × List (EntryIdx Θ Q)) (i : ℕ) :
    Pairwise fun o o' => Disjoint (c.candO s i o) (c.candO s i o') := by
  have key : ∀ o o', c.qe o < c.qe o' → Disjoint (c.candO s i o) (c.candO s i o') := by
    intro o o' hlt
    refine Set.disjoint_left.2 fun ω h1 h2 => ?_
    have hom : o ≤ (Nat.unpair i).2 := h1.1.1.2
    have hT : ω ∈ c.Tst s (Nat.unpair i).1 o := h1.1.2
    have h3 := mem_iInter₂.1 h2.2 o (Finset.mem_range.2 (Nat.lt_succ_of_le hom))
    exact h3 hlt hT
  intro o o' hne
  rcases lt_trichotomy (c.qe o) (c.qe o') with hlt | heq | hgt
  · exact key o o' hlt
  · exact absurd (hqe heq) hne
  · exact (key o' o hgt).symm

/-- **The outcomes cover the success event**: the chronologically first passing candidate is an outcome. -/
theorem candE_subset (s : Unit × List (EntryIdx Θ Q)) (i : ℕ) : c.candE s i ⊆ ⋃ o, c.candO s i o := by
  classical
  intro ω ⟨hA, hT⟩
  obtain ⟨n, hn, hTn⟩ := mem_iUnion₂.1 hT
  set F : Finset ℕ := (Finset.range ((Nat.unpair i).2 + 1)).filter (fun n => ω ∈ c.Tst s (Nat.unpair i).1 n)
    with hF
  have hne : F.Nonempty := ⟨n, Finset.mem_filter.2 ⟨hn, hTn⟩⟩
  obtain ⟨o, hoF, homin⟩ := F.exists_min_image (fun n => c.qe n) hne
  obtain ⟨hor, hoT⟩ := Finset.mem_filter.1 hoF
  refine mem_iUnion.2 ⟨o, ⟨⟨⟨hA, Nat.lt_succ_iff.1 (Finset.mem_range.1 hor)⟩, hoT⟩, mem_iInter₂.2 fun n' hn' => ?_⟩⟩
  intro hlt hT'
  exact absurd (homin n' (Finset.mem_filter.2 ⟨hn', hT'⟩)) (not_le.2 hlt)

/-- An outcome lies in the test of its candidate, from an alive schedule. -/
theorem candO_subset (s : Unit × List (EntryIdx Θ Q)) (i o : ℕ) :
    c.candO s i o ⊆ c.A s ∩ c.Tst s (Nat.unpair i).1 o :=
  fun _ hω => ⟨hω.1.1.1, hω.1.2⟩

/-- The success events of the rules `(a, m)` increase with the candidate count `m`. -/
theorem monotone_candE (s : Unit × List (EntryIdx Θ Q)) (a : ℕ) :
    Monotone fun m => c.candE s (Nat.pair a m) := by
  intro m m' hmm' ω hω
  simp only [candE, Nat.unpair_pair] at hω ⊢
  obtain ⟨hA, hT⟩ := hω
  obtain ⟨n, hn, hTn⟩ := mem_iUnion₂.1 hT
  exact ⟨hA, mem_iUnion₂.2 ⟨n, Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hn) (by omega)), hTn⟩⟩

/-- The success events of the rules `(a, m)` exhaust "alive, and some candidate passes". -/
theorem iUnion_candE (s : Unit × List (EntryIdx Θ Q)) (a : ℕ) :
    ⋃ m, c.candE s (Nat.pair a m) = c.A s ∩ ⋃ n, c.Tst s a n := by
  ext ω
  simp only [candE, Nat.unpair_pair, mem_iUnion, mem_inter_iff, Finset.mem_range]
  constructor
  · rintro ⟨m, hA, n, -, hT⟩
    exact ⟨hA, n, hT⟩
  · rintro ⟨hA, n, hT⟩
    exact ⟨n, hA, n, Nat.lt_succ_self n, hT⟩

/-- **A finite candidate count suffices** (Lemma A.1: "`E_m ↑ {S < F}` … choose `m(z) = min{m : K_z(E_m) > 1 − ε}`.
This exists … by the strict probability margin"): if, for some parameter `a`, "alive, and some candidate passes" has
probability greater than `1 − ε`, then some rule `(a, m)` succeeds with probability at least `1 − ε`. -/
theorem exists_candE_of_lt [MeasurableSpace Ω] (ν : Measure Ω) (s : Unit × List (EntryIdx Θ Q)) (a : ℕ) {ε : ℝ≥0∞}
    (hlt : 1 - ε < ν (c.A s ∩ ⋃ n, c.Tst s a n)) : ∃ i, 1 - ε ≤ ν (c.candE s i) := by
  have htend := tendsto_measure_iUnion_atTop (μ := ν) (c.monotone_candE s a)
  rw [c.iUnion_candE s a] at htend
  obtain ⟨m, hm⟩ := (htend.eventually (lt_mem_nhds hlt)).exists
  exact ⟨Nat.pair a m, hm.le⟩

end GW2CandData

/-! ### The per-test claims -/

section Claims

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u} [mΩ : MeasurableSpace Ω]
  (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {Θ : Set ℝ} {Q : Set ℝ≥0}
  (hΘc : Θ.Countable) (hQc : Q.Countable) (s : ℝ≥0) (r : ScaledRootIdx Θ Q) (G : Set Ω)

/-- **The per-test claims of the finite-candidate rules from the root `r`** with initial event `G`, for the concrete
one-root rule `T` (its stage-start σ-algebras and relative capacity): the candidate enumeration is injective; the
initial event is known at the root and alive; the alive and unit events are known at their schedule; the test at the
candidate `q_n` is known at every extension by a candidate `q_{n'} ≥ q_n` (A.2: "Each test at `q` is measurable at
`q`"); a passed test from an alive schedule gives an alive extension; **the stage claim** (A.3–A.4: some rule succeeds
with conditional probability at least `1 − ε_j`); **the uniform Lemma 5.10** at even depths `≥ 4` (A.5); the tolerances;
the unit bookkeeping. -/
structure CandClaims [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (ε₀ : ℝ≥0∞)
    (cd : GW2CandData Θ Q Ω) : Prop where
  hqe : Function.Injective cd.qe
  hG : MeasurableSet[(gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), [])] G
  hGA : G ⊆ cd.A ((), [])
  hA : ∀ l, MeasurableSet[(gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), l)]
    (cd.A ((), l))
  hTst : ∀ l a n n', cd.qe n ≤ cd.qe n' →
    MeasurableSet[(gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢
      ((), (cd.ang a, cd.qe n') :: l)] (cd.Tst ((), l) a n)
  hTstA : ∀ l a n, cd.A ((), l) ∩ cd.Tst ((), l) a n ⊆ cd.A ((), (cd.ang a, cd.qe n) :: l)
  hV : ∀ l, MeasurableSet[(gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), l)]
    (cd.V ((), l))
  /-- **The stage claim** (A.3–A.4). -/
  hstep : ∀ l, ∀ᵐ ω ∂P, ω ∈ cd.A ((), l) → ∃ i, 1 - cd.ε l.length ≤
    condExpKernel P ((gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), l)) ω
      (cd.candE ((), l) i)
  hp₀ : 0 < cd.p₀
  hp₀1 : cd.p₀ ≤ 1
  /-- **The uniform Lemma 5.10** (A.5). -/
  hunit : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ᵐ ω ∂P, ω ∈ cd.A ((), l) → ∀ i,
    condExpKernel P ((gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), l)) ω
      (cd.candD ((), l) i) ≤ ENNReal.ofReal (1 - cd.p₀)
  hε : ∑' j, cd.ε j ≤ ε₀
  hcapU : ∀ l x, ∀ ω ∈ cd.A ((), x :: l), ω ∈ cd.V ((), x :: l) →
    (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).cap ((), l) ω + 1 ≤
      (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).cap ((), x :: l) ω
variable {hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G}

/-- **An outcome is known at its extended schedule** (A.2: "Each test at `q` is measurable at `q` … The rule is
therefore a stopping time"): the alive event at the schedule, the test at the candidate, and the failed tests at the
earlier candidates. -/
theorem measurableSet_candO [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {ε₀ : ℝ≥0∞}
    {cd : GW2CandData Θ Q Ω} (hc : CandClaims hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G P ε₀ cd)
    (l : List (EntryIdx Θ Q)) (i o : ℕ) :
    MeasurableSet[(gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢
      ((), cd.candEntry i o :: l)] (cd.candO ((), l) i o) := by
  set T := gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData with hT
  have hmono : T.𝒢 ((), l) ≤ T.𝒢 ((), cd.candEntry i o :: l) :=
    gw2RootRule_sigma_mono hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData () l _
  refine ((MeasurableSet.inter (hmono _ (hc.hA l)) (MeasurableSet.const _)).inter
    (hc.hTst l (Nat.unpair i).1 o o le_rfl)).inter ?_
  refine Finset.measurableSet_biInter _ fun n _ => ?_
  by_cases hlt : cd.qe n < cd.qe o
  · have e : {ω | cd.qe n < cd.qe o → ω ∉ cd.Tst ((), l) (Nat.unpair i).1 n} =
        (cd.Tst ((), l) (Nat.unpair i).1 n)ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, hlt, true_imp_iff]
    rw [e]
    exact (hc.hTst l (Nat.unpair i).1 n o hlt.le).compl
  · have e : {ω | cd.qe n < cd.qe o → ω ∉ cd.Tst ((), l) (Nat.unpair i).1 n} = univ := by
      ext ω
      simp only [mem_ofPred_eq, hlt, false_imp_iff, mem_univ]
    rw [e]
    exact MeasurableSet.univ

/-- **The stage claims of the one-root rule from the per-test claims** (Lemma A.1's rules and outcomes). -/
theorem GW2CandData.rootClaims [StandardBorelSpace Ω] (hβA : Measurable βA) (hh : Measurable h) {P : Measure Ω}
    [IsFiniteMeasure P] (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {ε₀ : ℝ≥0∞} {cd : GW2CandData Θ Q Ω}
    (hc : CandClaims hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G P ε₀ cd) :
    (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).RootClaims P ε₀ := by
  set T := gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData with hT
  have hle : ∀ n, T.𝒢 n ≤ mΩ :=
    gw2RootRule_sigma_le hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData hβA hh hcf
  have hOm : ∀ (l : List (EntryIdx Θ Q)) (i o : ℕ), MeasurableSet (cd.candO ((), l) i o) := fun l i o =>
    hle _ _ (measurableSet_candO hc l i o)
  refine
    { hR₀ := fun _ => hc.hG
      hR₀A := fun _ => hc.hGA
      hE := ?_
      hO := fun _ l i o => measurableSet_candO hc l i o
      hOdisj := fun _ i => cd.candO_disjoint hc.hqe _ i
      hEO := fun _ i => cd.candE_subset _ i
      hOA := fun _ l i o => (cd.candO_subset ((), l) i o).trans (hc.hTstA l (Nat.unpair i).1 o)
      hV := fun n => hc.hV n.2
      hD := ?_
      hOD := fun _ l i o => subset_iUnion (fun o => cd.candO ((), l) i o \ cd.V ((), cd.candEntry i o :: l)) o
      hstep := fun n => hc.hstep n.2
      hp₀ := hc.hp₀
      hp₀1 := hc.hp₀1
      hunit := fun k n hn => hc.hunit k n.2 hn
      hε := hc.hε
      hcapU := fun _ l x => hc.hcapU l x }
  · rintro ⟨⟨⟩, l⟩ i
    refine (hle _ _ (hc.hA l)).inter (Finset.measurableSet_biUnion _ fun n _ => ?_)
    exact hle _ _ (hc.hTst l (Nat.unpair i).1 n n le_rfl)
  · rintro ⟨⟨⟩, l⟩ i
    exact MeasurableSet.iUnion fun o => (hOm l i o).diff (hle _ _ (hc.hV _))

end Claims
/-! ### The named finite-candidate statement and the reduction -/

/-- **Named statement: GW2's initial cover and the per-test claims of the finite-candidate rules** (follow-up note
A.1–A.5; GB9, pp. 525–526). Binders of `GW2TipSystem.GW2SchedRuleStatement` up to the stop `s`; conclusion: initial
events `G₀ r` for the roots `r` covering `{γ(s) ∈ ℍ}` almost surely (A.5), and for every root and every tolerance
`ε₀ > 0` finite-candidate data (alive events, parameter angles, candidate enumeration, tests at the candidates, unit
events) satisfying the per-test claims (`CandClaims`) for the concrete one-root rule. -/
def GW2RootCandStatement : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord), IsStopLaw.{u} κ βA →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord), IsPiecewiseConstantBoundaryData b jumps →
      c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → ∀ hΘc : Θ.Countable,
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∀ Q : Set ℝ≥0, ∀ hQc : Q.Countable, Dense Q → (∀ q ∈ Q, 0 < q) →
      ∀ γ : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω)) →
        ∀ s : ℝ≥0, ∃ G₀ : ScaledRootIdx Θ Q → Set Ω, (∀ᵐ ω ∂P, γ ω s ∈ H → ∃ r, ω ∈ G₀ r) ∧
          ∀ r, ∀ ε₀ : ℝ≥0∞, 0 < ε₀ → ∃ cd : GW2CandData Θ Q Ω,
            CandClaims hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r (G₀ r) P ε₀ cd

/-- **The root stages from the finite-candidate rules** (`GW2CandData.rootClaims`). -/
theorem gw2RootStageStatement_of_cand (hS : GW2RootCandStatement.{u}) : GW2RootStageStatement.{u} := by
  intro κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos
    γ hγ s
  obtain ⟨G₀, hcov, hroot⟩ :=
    hS κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos γ hγ s
  refine ⟨G₀, hcov, fun r ε₀ hε₀ => ?_⟩
  obtain ⟨cd, hcd⟩ := hroot r ε₀ hε₀
  exact ⟨cd.toStageData, GW2CandData.rootClaims hβA.1 hh.1 hcf hcd⟩

/-- **The canonical tip exhaustion from the finite-candidate rules.** -/
theorem gw2TipExhaustionCanonStatement_of_cand (hS : GW2RootCandStatement.{u}) :
    GW2TipExhaustionCanonStatement.{u} :=
  gw2TipExhaustionCanonStatement_of_rootStage (gw2RootStageStatement_of_cand hS)

end GW2TipSystem

end Theorem14

end InteractingSLE
