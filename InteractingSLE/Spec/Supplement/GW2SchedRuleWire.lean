/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SchedRuleCap

/-!
# GW2's concrete schedule rules: one tree per root, stage-start σ-algebras and capacity

Packet PROVE-GW2-SCHED. PROVE-T14-TIP12 reduced GW2's tip exhaustion to valid schedule rules
(`GW2TipSystem.SchedRule.IsValid`). This file builds the **concrete** rules of follow-up note A.2–A.5
(`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L80–L241) as far as they are fixed by the source independently
of the stage events:

* the roots (A.5: "The observed events indexed by a fixed root and fixed `q ∈ Q`"): `RootIdx Θ Q` — the root `0` or a
  rational root of the first low right arc, an initial angle in `Θ` and an initial time in `Q`; the entries
  `EntryIdx Θ Q = Θ × Q` (A.5: "Every successful finite history uses only `Θ` and `Q`");
* **one schedule tree per root** (A.5: "Work conditionally on each of these ordinary retained histories"), joined by the
  countable initial cover (`ae_not_isBounded_of_cover`). A single tree over all roots (TIP12's
  `GW2SchedRuleStatement`) would need pairwise disjoint initial events, each known at its own root's stage-start
  σ-algebra; the initial prefixes of different roots overlap and are not known at each other's σ-algebras, and adding
  them to the conditioning data would change the stage kernels;
* the stage-start σ-algebra of a schedule (A.5: "No first successful future prefix is added to the conditioning data"):
  `GW2TipSystem.stageSigma` — the counterflow record at `s` and the canonical pieces **stopped at their switching
  times**;
* the relative capacity of a schedule: `GW2TipSystem.schedCap` (the joint-chart image of its prefix), multiplied by
  `4ᵏ` for a root with dilation scale `k` (`ScaledRootIdx`: the source dilates the joint chart at initialization so
  that the labels lie outside `[−3, 3]`; a dilated unit is then at least `4⁻ᵏ` fixed units), against the target scaled
  by `2ᵏ` (`scaledTarget`, unbounded exactly when the target is);
* the stage events (alive events, rules, outcomes, unit events), tolerances and unit probability are the data
  `GW2StageData`; their claims are `SchedRule.RootClaims` (the fields of `SchedRule.IsValid` other than `h𝒢`,
  `h𝒢mono`, `hcapMono`, `hcapB`, `hR₀disj`, `hcover`).

Main results:

* **`SchedRule.IsValid.of_rootClaims`**: a one-root rule with its stage claims, the cover of the target event and the
  four structural fields is valid;
* `gw2RootRule`: the concrete one-root rule; **`gw2RootRule_sigma_le`**, **`gw2RootRule_sigma_mono`**,
  **`gw2RootRule_capMono`**, **`gw2RootRule_capB`** (proved), **`gw2RootRule_isValid`**;
* **`GW2RootStageStatement`** (named): the initial cover and, per root and tolerance, stage data with the stage claims;
* **`gw2TipJointUnboundedStatement_of_rootStage`**, **`gw2TipExhaustionCanonStatement_of_rootStage`**: GW2's
  joint-chart unboundedness and the canonical tip exhaustion (TIP9's chain).
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

/-! ### Stage claims of a schedule rule -/

namespace SchedRule

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (T : SchedRule Ω)

/-- **The stage claims of a one-root schedule rule**: the fields of `SchedRule.IsValid` other than the structural
ones (`h𝒢`, `h𝒢mono`, `hcapMono`, `hcapB`) and the root bookkeeping (`hR₀disj`, `hcover`), which hold for a single
root whose event is the target event. -/
structure RootClaims (P : Measure Ω) [IsFiniteMeasure P] [StandardBorelSpace Ω] (ε₀ : ℝ≥0∞) : Prop where
  hR₀ : ∀ r, MeasurableSet[T.𝒢 (r, [])] (T.R₀ r)
  hR₀A : ∀ r, T.R₀ r ⊆ T.A (r, [])
  hE : ∀ s i, MeasurableSet (T.E s i)
  hO : ∀ r l i o, MeasurableSet[T.𝒢 (r, T.entry i o :: l)] (T.O (r, l) i o)
  hOdisj : ∀ s i, Pairwise fun o o' => Disjoint (T.O s i o) (T.O s i o')
  hEO : ∀ s i, T.E s i ⊆ ⋃ o, T.O s i o
  hOA : ∀ r l i o, T.O (r, l) i o ⊆ T.A (r, T.entry i o :: l)
  hV : ∀ s, MeasurableSet[T.𝒢 s] (T.V s)
  hD : ∀ s i, MeasurableSet (T.D s i)
  hOD : ∀ r l i o, T.O (r, l) i o \ T.V (r, T.entry i o :: l) ⊆ T.D (r, l) i
  /-- **The stage claim at a fixed schedule** (A.3–A.4). -/
  hstep : ∀ s, ∀ᵐ ω ∂P, ω ∈ T.A s → ∃ i, 1 - T.ε s.2.length ≤ condExpKernel P (T.𝒢 s) ω (T.E s i)
  hp₀ : 0 < T.p₀
  hp₀1 : T.p₀ ≤ 1
  /-- **The uniform Lemma 5.10 at a fixed schedule** (A.5). -/
  hunit : ∀ (k : ℕ) s, s.2.length = 2 * k + 4 → ∀ᵐ ω ∂P, ω ∈ T.A s → ∀ i,
    condExpKernel P (T.𝒢 s) ω (T.D s i) ≤ ENNReal.ofReal (1 - T.p₀)
  hε : ∑' j, T.ε j ≤ ε₀
  hcapU : ∀ r l x, ∀ ω ∈ T.A (r, x :: l), ω ∈ T.V (r, x :: l) → T.cap (r, l) ω + 1 ≤ T.cap (r, x :: l) ω

variable {T}

/-- **Validity of a one-root rule from its stage claims, the cover of the target event and the four structural
fields.** -/
theorem IsValid.of_rootClaims {P : Measure Ω} [IsFiniteMeasure P] [StandardBorelSpace Ω] {G : Set Ω}
    {S : Ω → Set ℂ} {ε₀ : ℝ≥0∞} (hc : T.RootClaims P ε₀) (hsub : Subsingleton T.ι)
    (hcover : ∀ᵐ ω ∂P, ω ∈ G → ∃ r, ω ∈ T.R₀ r) (h𝒢 : ∀ s, T.𝒢 s ≤ mΩ)
    (h𝒢mono : ∀ r l x, T.𝒢 (r, l) ≤ T.𝒢 (r, x :: l))
    (hcapMono : ∀ r l x, ∀ ω ∈ T.A (r, x :: l), T.cap (r, l) ω ≤ T.cap (r, x :: l) ω)
    (hcapB : ∀ s, ∀ ω ∈ T.A s, ∀ ρ : ℝ, S ω ⊆ Metric.closedBall 0 ρ → T.cap s ω ≤ 2 * ρ ^ 2) :
    T.IsValid P G S ε₀ where
  h𝒢 := h𝒢
  h𝒢mono := h𝒢mono
  hR₀ := hc.hR₀
  hR₀disj := fun r r' hne => absurd (Subsingleton.elim r r') hne
  hR₀A := hc.hR₀A
  hE := hc.hE
  hO := hc.hO
  hOdisj := hc.hOdisj
  hEO := hc.hEO
  hOA := hc.hOA
  hV := hc.hV
  hD := hc.hD
  hOD := hc.hOD
  hstep := hc.hstep
  hp₀ := hc.hp₀
  hp₀1 := hc.hp₀1
  hunit := hc.hunit
  hε := hc.hε
  hcover := hcover
  hcapMono := hcapMono
  hcapU := hc.hcapU
  hcapB := hcapB

end SchedRule

/-! ### Roots and entries -/

/-- **The roots of GW2's schedule rule**: the root `0` (`none`) or a rational root `v` (`some v`), an initial angle in
`Θ`, an initial time in `Q`. -/
abbrev RootIdx (Θ : Set ℝ) (Q : Set ℝ≥0) : Type := Option ℚ × Θ × Q

/-- **The entries of GW2's schedules**: an angle in `Θ` and a switching time in `Q`. -/
abbrev EntryIdx (Θ : Set ℝ) (Q : Set ℝ≥0) : Type := Θ × Q

section Idx

variable {Θ : Set ℝ} {Q : Set ℝ≥0}

/-- The physical root of a root index. -/
def rootPt (r : RootIdx Θ Q) : ℝ :=
  match r.1 with
  | none => 0
  | some v => (v : ℝ)

/-- The initial entry of a root index. -/
def rootEntry (r : RootIdx Θ Q) : ℝ × ℝ≥0 := ((r.2.1 : ℝ), (r.2.2 : ℝ≥0))

/-- The entries of a schedule as angle–time pairs. -/
def entryList (xs : List (EntryIdx Θ Q)) : List (ℝ × ℝ≥0) := xs.map fun x => ((x.1 : ℝ), (x.2 : ℝ≥0))

@[simp] theorem entryList_cons (x : EntryIdx Θ Q) (xs : List (EntryIdx Θ Q)) :
    entryList (x :: xs) = ((x.1 : ℝ), (x.2 : ℝ≥0)) :: entryList xs := rfl

/-- The history of a schedule of the rule. -/
def schedSpecOf (r : RootIdx Θ Q) (xs : List (EntryIdx Θ Q)) : ExplSpec :=
  schedSpec (rootPt r) (schedOf (rootEntry r) (entryList xs))

end Idx

/-- **A root with a dilation scale**: the source places the labels outside `[−3, 3]` by dilating the joint chart at
initialization (A.3; Prop. 5.9, p. 143: "Rescale it"); a stage then spends one unit of capacity of the dilated chart.
The scale index `k` covers the dilation factors `≤ 2ᵏ`, for which one dilated unit is at least `4⁻ᵏ` units of the
fixed joint chart. -/
abbrev ScaledRootIdx (Θ : Set ℝ) (Q : Set ℝ≥0) : Type := RootIdx Θ Q × ℕ

/-- The target scaled by `2ᵏ` (unbounded exactly when the target is). -/
def scaledTarget {Ω : Type*} (k : ℕ) (S : Ω → Set ℂ) (ω : Ω) : Set ℂ := (fun z : ℂ => (2 : ℂ) ^ k * z) '' S ω

theorem norm_two_pow_mul (k : ℕ) (z : ℂ) : ‖(2 : ℂ) ^ k * z‖ = (2 : ℝ) ^ k * ‖z‖ := by
  rw [norm_mul, norm_pow, Complex.norm_two]

/-- A set whose scaled copy lies in `B̄(0, ρ)` lies in `B̄(0, ρ/2ᵏ)`. -/
theorem subset_closedBall_of_scaledTarget {Ω : Type*} {k : ℕ} {S : Ω → Set ℂ} {ω : Ω} {ρ : ℝ}
    (h : scaledTarget k S ω ⊆ Metric.closedBall 0 ρ) : S ω ⊆ Metric.closedBall 0 (ρ / 2 ^ k) := by
  intro z hz
  have h1 := h ⟨z, hz, rfl⟩
  rw [mem_closedBall_zero_iff, norm_two_pow_mul] at h1
  rw [mem_closedBall_zero_iff, le_div_iff₀ (by positivity), mul_comm]
  exact h1

/-- The scaled target is unbounded when the target is. -/
theorem not_isBounded_of_scaledTarget {Ω : Type*} {k : ℕ} {S : Ω → Set ℂ} {ω : Ω}
    (h : ¬ Bornology.IsBounded (scaledTarget k S ω)) : ¬ Bornology.IsBounded (S ω) := by
  intro hb
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
  refine h ((Metric.isBounded_iff_subset_closedBall (0 : ℂ)).2 ⟨(2 : ℝ) ^ k * ρ, ?_⟩)
  rintro _ ⟨z, hz, rfl⟩
  have h1 := hρ hz
  rw [mem_closedBall_zero_iff] at h1 ⊢
  rw [norm_two_pow_mul]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ### The concrete one-root schedule rule -/

/-- **The stage data of GW2's schedule rule from one root** not fixed by the source independently of the stages: the
alive events, the rule success and outcome events (rule `i`, candidate `o`), the entry of an outcome, the unit events,
the no-unit events, the tolerances and the unit probability. Schedules are lists of entries, the latest first. -/
structure GW2StageData (Θ : Set ℝ) (Q : Set ℝ≥0) (Ω : Type u) where
  /-- The event on which the stage bounds from a schedule are claimed. -/
  A : Unit × List (EntryIdx Θ Q) → Set Ω
  /-- The success event of rule `i` from a schedule. -/
  E : Unit × List (EntryIdx Θ Q) → ℕ → Set Ω
  /-- The outcome `o` of rule `i` from a schedule. -/
  O : Unit × List (EntryIdx Θ Q) → ℕ → ℕ → Set Ω
  /-- The entry by which outcome `o` of rule `i` extends the schedule. -/
  entry : ℕ → ℕ → EntryIdx Θ Q
  /-- The unit event of the stage ending at a schedule. -/
  V : Unit × List (EntryIdx Θ Q) → Set Ω
  /-- An event containing "rule `i` succeeds and the stage consumes no unit". -/
  D : Unit × List (EntryIdx Θ Q) → ℕ → Set Ω
  /-- The failure tolerance of the stage from depth `j`. -/
  ε : ℕ → ℝ≥0∞
  /-- The unit probability of the even stages. -/
  p₀ : ℝ

section Rule

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u} [mΩ : MeasurableSpace Ω]
  (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {Θ : Set ℝ} {Q : Set ℝ≥0}
  (hΘc : Θ.Countable) (hQc : Q.Countable) (s : ℝ≥0)

/-- **GW2's concrete schedule rule from the root `r`** (A.5: "Work conditionally on each of these ordinary retained
histories"), with initial event `G` and stage data `d`: one root, entries `EntryIdx Θ Q`, outcomes `ℕ` (candidate
indices), the stage-start σ-algebra `stageSigma` of the schedule's history (the counterflow record at `s` and the
canonical pieces stopped at their switching times) and the relative capacity `schedCap`. -/
def gw2RootRule (r : ScaledRootIdx Θ Q) (G : Set Ω) (d : GW2StageData Θ Q Ω) : SchedRule Ω where
  ι := Unit
  X := EntryIdx Θ Q
  K := ℕ
  countableι := inferInstance
  countableX := by
    have := hΘc.to_subtype
    have := hQc.to_subtype
    infer_instance
  countableK := inferInstance
  𝒢 n := stageSigma hκ h12p βA c₀ h s W' ζ' (schedSpecOf r.1 n.2) ((entryList n.2).length + 1)
  R₀ _ := G
  A := d.A
  E := d.E
  O := d.O
  entry := d.entry
  V := d.V
  D := d.D
  ε := d.ε
  p₀ := d.p₀
  cap n := 4 ^ r.2 * schedCap hκ h12p βA b jumps c₀ h W' s Θ Q (rootPt r.1) (rootEntry r.1) (entryList n.2)

variable (r : ScaledRootIdx Θ Q) (G : Set Ω) (d : GW2StageData Θ Q Ω)

/-- **Field `h𝒢` of the concrete rule.** -/
theorem gw2RootRule_sigma_le (hβA : Measurable βA) (hh : Measurable h) {P : Measure Ω}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') :
    ∀ n, (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).𝒢 n ≤ mΩ := fun _ =>
  stageSigma_le hβA hh hcf s _ _

/-- **Field `h𝒢mono` of the concrete rule**: the stage-start σ-algebra increases along extensions (the stopped
records of the earlier pieces do not change). -/
theorem gw2RootRule_sigma_mono :
    ∀ r' l x, (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).𝒢 (r', l) ≤
      (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).𝒢 (r', x :: l) := by
  intro (r' : Unit) (l : List (EntryIdx Θ Q)) (x : EntryIdx Θ Q)
  change stageSigma hκ h12p βA c₀ h s W' ζ' (schedSpec (rootPt r.1) (schedOf (rootEntry r.1) (entryList l)))
      ((entryList l).length + 1) ≤
    stageSigma hκ h12p βA c₀ h s W' ζ' (schedSpec (rootPt r.1) (schedOf (rootEntry r.1) (entryList (x :: l))))
      ((entryList (x :: l)).length + 1)
  rw [entryList_cons]
  exact stageSigma_schedOf_mono s W' ζ' (rootPt r.1) (rootEntry r.1) _ (entryList l)

/-- **Field `hcapMono` of the concrete rule** (everywhere, not only on the alive events). -/
theorem gw2RootRule_capMono :
    ∀ r' l x, ∀ ω, (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).cap (r', l) ω ≤
      (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).cap (r', x :: l) ω := by
  intro (r' : Unit) (l : List (EntryIdx Θ Q)) (x : EntryIdx Θ Q) ω
  change 4 ^ r.2 * schedCap hκ h12p βA b jumps c₀ h W' s Θ Q (rootPt r.1) (rootEntry r.1) (entryList l) ω ≤
    4 ^ r.2 * schedCap hκ h12p βA b jumps c₀ h W' s Θ Q (rootPt r.1) (rootEntry r.1) (entryList (x :: l)) ω
  rw [entryList_cons]
  exact mul_le_mul_of_nonneg_left (schedCap_le_cons hκ h12p βA b jumps c₀ h W' s Θ Q _ _ _ _ ω) (by positivity)

/-- **Field `hcapB` of the concrete rule** for the joint target scaled by `2ᵏ` (everywhere, not only on the alive
events). -/
theorem gw2RootRule_capB :
    ∀ n, ∀ ω, ∀ ρ : ℝ, scaledTarget r.2 (jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s) ω ⊆ Metric.closedBall 0 ρ →
      (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).cap n ω ≤ 2 * ρ ^ 2 := by
  intro n ω ρ hS
  have h1 := schedCap_le_of_subset hκ h12p βA b jumps c₀ h W' s Θ Q (rootPt r.1) (rootEntry r.1) (entryList n.2)
    (subset_closedBall_of_scaledTarget hS)
  change 4 ^ r.2 * schedCap hκ h12p βA b jumps c₀ h W' s Θ Q (rootPt r.1) (rootEntry r.1) (entryList n.2) ω ≤ _
  have h4 : ((2 : ℝ) ^ r.2) ^ 2 = 4 ^ r.2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hpos : (0 : ℝ) < 4 ^ r.2 := by positivity
  rw [div_pow, h4] at h1
  calc 4 ^ r.2 * schedCap hκ h12p βA b jumps c₀ h W' s Θ Q (rootPt r.1) (rootEntry r.1) (entryList n.2) ω
      ≤ 4 ^ r.2 * (2 * (ρ ^ 2 / 4 ^ r.2)) := mul_le_mul_of_nonneg_left h1 hpos.le
    _ = 2 * ρ ^ 2 := by field_simp

/-- **The concrete one-root rule is valid for its initial event as soon as its stage claims hold.** -/
theorem gw2RootRule_isValid [StandardBorelSpace Ω] (hβA : Measurable βA) (hh : Measurable h) {P : Measure Ω}
    [IsFiniteMeasure P] (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {ε₀ : ℝ≥0∞}
    (hc : (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).RootClaims P ε₀) :
    (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).IsValid P G
      (scaledTarget r.2 (jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s)) ε₀ :=
  SchedRule.IsValid.of_rootClaims hc (inferInstanceAs (Subsingleton Unit))
    (Eventually.of_forall fun _ hω => ⟨(), hω⟩)
    (gw2RootRule_sigma_le hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d hβA hh hcf)
    (gw2RootRule_sigma_mono hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d)
    (fun r' l x ω _ => gw2RootRule_capMono hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d r' l x ω)
    (fun n ω _ ρ hS => gw2RootRule_capB hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d n ω ρ hS)

end Rule

/-! ### Countably many roots -/

/-- **Unboundedness from a countable cover by events of almost sure unboundedness** (A.5: "let `ε ↓ 0` and then use
the countable initial-prefix cover"). -/
theorem ae_not_isBounded_of_cover {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Countable ι]
    {G : Set Ω} {G₀ : ι → Set Ω} {S : Ω → Set ℂ} (hcov : ∀ᵐ ω ∂P, ω ∈ G → ∃ r, ω ∈ G₀ r)
    (hr : ∀ r, ∀ᵐ ω ∂P, ω ∈ G₀ r → ¬ Bornology.IsBounded (S ω)) :
    ∀ᵐ ω ∂P, ω ∈ G → ¬ Bornology.IsBounded (S ω) := by
  filter_upwards [hcov, ae_all_iff.2 hr] with ω hc hall hG
  obtain ⟨r, hrω⟩ := hc hG
  exact hall r hrω

/-! ### The named root-stage statement and the reduction -/

/-- **Named statement: GW2's initial cover and the stage claims of the one-root rules** (follow-up note A.2–A.5; GB9,
pp. 525–526). Binders of `GW2TipSystem.GW2SchedRuleStatement` up to the stop `s`; conclusion: there are initial events
`G₀ r` for the roots `r` (A.5: "The observed events indexed by a fixed root and fixed `q ∈ Q`, on which this prefix is
available, interior and disjoint, form a countable almost-sure cover") covering `{γ(s) ∈ ℍ}` almost surely, and for
every root and every tolerance `ε₀ > 0` stage data whose one-root rule (stage-start σ-algebras of the counterflow
record and the **stopped** canonical pieces; relative capacity of the joint-chart prefix images) satisfies the stage
claims (`SchedRule.RootClaims`). -/
def GW2RootStageStatement : Prop :=
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
          ∀ r, ∀ ε₀ : ℝ≥0∞, 0 < ε₀ → ∃ d : GW2StageData Θ Q Ω,
            (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r (G₀ r) d).RootClaims P ε₀

/-- **GW2's joint-chart unboundedness from the root stages**: each one-root rule is valid for its initial event
(`gw2RootRule_isValid`), so the joint target is almost surely unbounded on that event
(`GW2TipSystem.ae_not_isBounded_of_schedRules`, TIP12's adaptive tree); the countable initial cover finishes. -/
theorem gw2TipJointUnboundedStatement_of_rootStage (hS : GW2RootStageStatement.{u}) :
    GW2TipJointUnboundedStatement.{u} := by
  intro κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos
    γ hγ s
  obtain ⟨G₀, hcov, hroot⟩ :=
    hS κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos γ hγ s
  have hc : Countable (ScaledRootIdx Θ Q) := by
    have := hΘc.to_subtype
    have := hQc.to_subtype
    infer_instance
  have key := ae_not_isBounded_of_cover (P := P) (G := {ω | γ ω s ∈ H}) (G₀ := G₀)
    (S := jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s) hcov fun r => by
      have hr := ae_not_isBounded_of_schedRules (P := P) (G := G₀ r)
        (S := scaledTarget r.2 (jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s)) fun ε₀ hε₀ => by
          obtain ⟨d, hd⟩ := hroot r ε₀ hε₀
          exact ⟨_, gw2RootRule_isValid hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r (G₀ r) d hβA.1 hh.1 hcf hd⟩
      filter_upwards [hr] with ω hω hG
      exact not_isBounded_of_scaledTarget (hω hG)
  exact key

/-- **The canonical tip exhaustion from the root stages** (TIP9's chain). -/
theorem gw2TipExhaustionCanonStatement_of_rootStage (hS : GW2RootStageStatement.{u}) :
    GW2TipExhaustionCanonStatement.{u} :=
  gw2TipExhaustionCanonStatement_of_canonAllQ
    (gw2TipExhaustionCanonAllQStatement_of_jointUnbounded (gw2TipJointUnboundedStatement_of_rootStage hS))

end GW2TipSystem

end Theorem14

end InteractingSLE
