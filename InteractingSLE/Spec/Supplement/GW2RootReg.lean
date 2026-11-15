/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SchedRuleCand

/-!
# GW2's one-root rule with the capacity of the regularized counterflow record

Packet PROVE-GW2-ROOT. `GW2RootTwin.lean` shows that `GW2TipSystem.GW2RootCandStatement` cannot hold on twinned
spaces: its rule `gw2RootRule` measures capacities in the joint chart of the **raw** counterflow driver, while its
stage-start σ-algebras see only the **regularized** record `GW2JointKernel.cfE s W' ζ'` (dyadic samples), and the unit
clause `hcapU` is required at every sample. This file gives the repaired rule and statement:

* `regW`: the regularized counterflow driver at the stop `s` (the driver read off the stage record);
* **`gw2RootRuleR`**: `gw2RootRule` with its capacity computed in the joint chart of `regW` (same stage-start
  σ-algebras, alive, rule, outcome and unit events); its structural fields (`gw2RootRuleR_sigma_le`, `_sigma_mono`,
  `_capMono`, `_capB`) and **`gw2RootRuleR_isValid`** for the scaled joint target of `regW`;
* `CandClaimsR` (the per-test claims for `gw2RootRuleR`), **`GW2CandData.rootClaimsR`**;
* **`GW2RootCandRStatement`** (named; replaces `GW2RootCandStatement`), and its consequences
  **`gw2TipJointUnboundedStatement_of_candR`**, **`gw2TipExhaustionCanonStatement_of_candR`**: almost surely the
  regularized driver is the driver (`GW2JointKernel.cfE_eq`: infinite lifetime, continuous from `0`), so the two joint
  targets agree almost surely.
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

/-- **The regularized counterflow driver at the stop `s`**: the driver of the stage record `GW2JointKernel.cfE`. -/
def regW {Ω : Type*} (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (GW2JointKernel.cfE s W' ζ' ω).1 t

/-- On a sample with infinite lifetime and a continuous driver from `0`, the regularized driver is the driver. -/
theorem regW_eq {Ω : Type*} (s : ℝ≥0) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ' ω = ⊤)
    (hW0 : W' 0 ω = 0) (hWc : Continuous fun t => W' t ω) (t : ℝ≥0) : regW s W' ζ' t ω = W' t ω := by
  unfold regW
  rw [GW2JointKernel.cfE_eq s hζ hW0 hWc]

/-- The joint target only depends on the counterflow driver of the sample. -/
theorem jointTarget_congr {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord)
    {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens) {W₁ W₂ : ℝ≥0 → Ω → ℝ} (Θ : Set ℝ) (Q : Set ℝ≥0) (s : ℝ≥0)
    {ω : Ω} (hW : ∀ t, W₁ t ω = W₂ t ω) :
    jointTarget hκ h12p βA b jumps c₀ h W₁ Θ Q s ω = jointTarget hκ h12p βA b jumps c₀ h W₂ Θ Q s ω := by
  unfold jointTarget
  simp only [hW]

/-! ### The repaired rule -/

section Rule

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u} [mΩ : MeasurableSpace Ω]
  (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {Θ : Set ℝ} {Q : Set ℝ≥0}
  (hΘc : Θ.Countable) (hQc : Q.Countable) (s : ℝ≥0)

/-- **GW2's one-root rule with the capacity of the regularized counterflow record**: `gw2RootRule` (stage-start
σ-algebras of the counterflow record and the stopped canonical pieces) with the relative capacity of the prefix images
in the joint chart of `regW s W' ζ'`. -/
def gw2RootRuleR (r : ScaledRootIdx Θ Q) (G : Set Ω) (d : GW2StageData Θ Q Ω) : SchedRule Ω :=
  { gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d with
    cap := fun n => 4 ^ r.2 *
      schedCap hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q (rootPt r.1) (rootEntry r.1) (entryList n.2) }

variable (r : ScaledRootIdx Θ Q) (G : Set Ω) (d : GW2StageData Θ Q Ω)

/-- **Field `h𝒢` of the repaired rule.** -/
theorem gw2RootRuleR_sigma_le (hβA : Measurable βA) (hh : Measurable h) {P : Measure Ω}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') :
    ∀ n, (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).𝒢 n ≤ mΩ :=
  gw2RootRule_sigma_le hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d hβA hh hcf

/-- **Field `h𝒢mono` of the repaired rule.** -/
theorem gw2RootRuleR_sigma_mono :
    ∀ r' l x, (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).𝒢 (r', l) ≤
      (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).𝒢 (r', x :: l) :=
  gw2RootRule_sigma_mono hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d

/-- **Field `hcapMono` of the repaired rule** (everywhere). -/
theorem gw2RootRuleR_capMono :
    ∀ r' l x, ∀ ω, (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).cap (r', l) ω ≤
      (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).cap (r', x :: l) ω :=
  gw2RootRule_capMono hκ h12p βA b jumps c₀ h (regW s W' ζ') ζ' hΘc hQc s r G d

/-- **Field `hcapB` of the repaired rule** for the scaled joint target of the regularized driver (everywhere). -/
theorem gw2RootRuleR_capB :
    ∀ n, ∀ ω, ∀ ρ : ℝ,
      scaledTarget r.2 (jointTarget hκ h12p βA b jumps c₀ h (regW s W' ζ') Θ Q s) ω ⊆ Metric.closedBall 0 ρ →
      (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).cap n ω ≤ 2 * ρ ^ 2 :=
  gw2RootRule_capB hκ h12p βA b jumps c₀ h (regW s W' ζ') ζ' hΘc hQc s r G d

/-- **The repaired one-root rule is valid for its initial event as soon as its stage claims hold.** -/
theorem gw2RootRuleR_isValid [StandardBorelSpace Ω] (hβA : Measurable βA) (hh : Measurable h) {P : Measure Ω}
    [IsFiniteMeasure P] (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {ε₀ : ℝ≥0∞}
    (hc : (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).RootClaims P ε₀) :
    (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).IsValid P G
      (scaledTarget r.2 (jointTarget hκ h12p βA b jumps c₀ h (regW s W' ζ') Θ Q s)) ε₀ :=
  SchedRule.IsValid.of_rootClaims hc (inferInstanceAs (Subsingleton Unit))
    (Eventually.of_forall fun _ hω => ⟨(), hω⟩)
    (gw2RootRuleR_sigma_le hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d hβA hh hcf)
    (gw2RootRuleR_sigma_mono hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d)
    (fun r' l x ω _ => gw2RootRuleR_capMono hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d r' l x ω)
    (fun n ω _ ρ hS => gw2RootRuleR_capB hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d n ω ρ hS)

end Rule

/-! ### The per-test claims for the repaired rule -/

section Claims

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u} [mΩ : MeasurableSpace Ω]
  (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {Θ : Set ℝ} {Q : Set ℝ≥0}
  (hΘc : Θ.Countable) (hQc : Q.Countable) (s : ℝ≥0) (r : ScaledRootIdx Θ Q) (G : Set Ω)

/-- **The per-test claims of the finite-candidate rules for the repaired rule** (`GW2TipSystem.CandClaims` with the
capacity of `gw2RootRuleR` in the unit clause `hcapU`; all other fields verbatim). -/
structure CandClaimsR [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (ε₀ : ℝ≥0∞)
    (cd : GW2CandData Θ Q Ω) : Prop where
  hqe : Function.Injective cd.qe
  hG : MeasurableSet[(gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), [])]
    G
  hGA : G ⊆ cd.A ((), [])
  hA : ∀ l, MeasurableSet[(gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢
    ((), l)] (cd.A ((), l))
  hTst : ∀ l a n n', cd.qe n ≤ cd.qe n' →
    MeasurableSet[(gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢
      ((), (cd.ang a, cd.qe n') :: l)] (cd.Tst ((), l) a n)
  hTstA : ∀ l a n, cd.A ((), l) ∩ cd.Tst ((), l) a n ⊆ cd.A ((), (cd.ang a, cd.qe n) :: l)
  hV : ∀ l, MeasurableSet[(gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢
    ((), l)] (cd.V ((), l))
  /-- **The stage claim** (A.3–A.4). -/
  hstep : ∀ l, ∀ᵐ ω ∂P, ω ∈ cd.A ((), l) → ∃ i, 1 - cd.ε l.length ≤
    condExpKernel P ((gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), l)) ω
      (cd.candE ((), l) i)
  hp₀ : 0 < cd.p₀
  hp₀1 : cd.p₀ ≤ 1
  /-- **The uniform Lemma 5.10** (A.5). -/
  hunit : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ᵐ ω ∂P, ω ∈ cd.A ((), l) → ∀ i,
    condExpKernel P ((gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), l)) ω
      (cd.candD ((), l) i) ≤ ENNReal.ofReal (1 - cd.p₀)
  hε : ∑' j, cd.ε j ≤ ε₀
  /-- The unit clause, for the capacity of the regularized counterflow record. -/
  hcapU : ∀ l x, ∀ ω ∈ cd.A ((), x :: l), ω ∈ cd.V ((), x :: l) →
    (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).cap ((), l) ω + 1 ≤
      (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).cap ((), x :: l) ω

variable {hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G}

/-- An outcome is known at its extended schedule (as `measurableSet_candO`). -/
theorem measurableSet_candO_R [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {ε₀ : ℝ≥0∞}
    {cd : GW2CandData Θ Q Ω} (hc : CandClaimsR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G P ε₀ cd)
    (l : List (EntryIdx Θ Q)) (i o : ℕ) :
    MeasurableSet[(gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢
      ((), cd.candEntry i o :: l)] (cd.candO ((), l) i o) := by
  have hmono : (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), l) ≤
      (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 ((), cd.candEntry i o :: l) :=
    gw2RootRuleR_sigma_mono hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData () l _
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

/-- **The stage claims of the repaired rule from the per-test claims** (as `GW2CandData.rootClaims`). -/
theorem GW2CandData.rootClaimsR [StandardBorelSpace Ω] (hβA : Measurable βA) (hh : Measurable h) {P : Measure Ω}
    [IsFiniteMeasure P] (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {ε₀ : ℝ≥0∞} {cd : GW2CandData Θ Q Ω}
    (hc : CandClaimsR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G P ε₀ cd) :
    (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).RootClaims P ε₀ := by
  have hle : ∀ n, (gw2RootRuleR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData).𝒢 n ≤ mΩ :=
    gw2RootRuleR_sigma_le hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G cd.toStageData hβA hh hcf
  have hOm : ∀ (l : List (EntryIdx Θ Q)) (i o : ℕ), MeasurableSet (cd.candO ((), l) i o) := fun l i o =>
    hle _ _ (measurableSet_candO_R hc l i o)
  refine
    { hR₀ := fun _ => hc.hG
      hR₀A := fun _ => hc.hGA
      hE := ?_
      hO := fun _ l i o => measurableSet_candO_R hc l i o
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

/-! ### The repaired named statement and the reduction -/

/-- **Named statement: GW2's initial cover and the per-test claims of the repaired one-root rules** (follow-up note
A.1–A.5; follow-up 5 §4.1; GB9, pp. 525–526). `GW2TipSystem.GW2RootCandStatement` verbatim, with `CandClaimsR` (the
relative capacity measured in the joint chart of the regularized counterflow record, which the stage-start
σ-algebras see) in place of `CandClaims`. Replaces `GW2RootCandStatement`, which fails on twinned spaces
(`GW2RootTwin.lean`). -/
def GW2RootCandRStatement : Prop :=
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
            CandClaimsR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r (G₀ r) P ε₀ cd

/-- **GW2's joint-chart unboundedness from the repaired root stages**: each repaired one-root rule is valid for its
initial event (`gw2RootRuleR_isValid`), so the joint target of the regularized driver is almost surely unbounded on
that event (TIP12's adaptive tree); the countable initial cover finishes, and almost surely the regularized driver is
the driver. -/
theorem gw2TipJointUnboundedStatement_of_candR (hS : GW2RootCandRStatement.{u}) :
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
    (S := jointTarget hκ h12p βA b jumps c₀ h (regW s W' ζ') Θ Q s) hcov fun r => by
      have hr := ae_not_isBounded_of_schedRules (P := P) (G := G₀ r)
        (S := scaledTarget r.2 (jointTarget hκ h12p βA b jumps c₀ h (regW s W' ζ') Θ Q s)) fun ε₀ hε₀ => by
          obtain ⟨cd, hcd⟩ := hroot r ε₀ hε₀
          exact ⟨_, gw2RootRuleR_isValid hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r (G₀ r) cd.toStageData hβA.1 hh.1
            hcf (GW2CandData.rootClaimsR hβA.1 hh.1 hcf hcd)⟩
      filter_upwards [hr] with ω hω hG
      exact not_isBounded_of_scaledTarget (hω hG)
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  filter_upwards [key, hdrv, hζ'] with ω hk hdω hζω hsH
  rw [hζω] at hdω
  have hWc : Continuous fun t => W' t ω := by
    have h2 := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at h2
    exact continuousOn_univ.1 h2
  have he := jointTarget_congr hκ h12p βA b jumps c₀ h Θ Q s (W₁ := regW s W' ζ') (W₂ := W') (ω := ω)
    (regW_eq s hζω hdω.1 hWc)
  have hk' := hk hsH
  rw [he] at hk'
  exact hk'

/-- **The canonical tip exhaustion from the repaired root stages** (TIP9's chain). -/
theorem gw2TipExhaustionCanonStatement_of_candR (hS : GW2RootCandRStatement.{u}) :
    GW2TipExhaustionCanonStatement.{u} :=
  gw2TipExhaustionCanonStatement_of_canonAllQ
    (gw2TipExhaustionCanonAllQStatement_of_jointUnbounded (gw2TipJointUnboundedStatement_of_candR hS))

end GW2TipSystem

end Theorem14

end InteractingSLE
