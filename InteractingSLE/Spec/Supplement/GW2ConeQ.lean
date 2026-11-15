/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6PastStep
import InteractingSLE.Spec.Supplement.GW2TipWire

/-!
# Lemma GW2 with GB9a's schedule set: only schedules whose switching tips are interior

Packet PROVE-T14-BR7. The containment half of Lemma GW2 (supplement p. 621) runs GW1's induction through the switching
tips of each schedule; GB6 applies only at an interior tip (`p ∈ D`). The supplement chooses the schedule set
accordingly (GW2, proof ¶1: "one deterministic dense countable `Q` for which all switching and terminal tips of
successful schedules are interior", by GB9a's ordered time-vector Tonelli argument, p. 527), and the tip exhaustion
works for every deterministic countable dense `Q` (follow-up note,
`source/external/AstraIG1/ig1_followup_a_e_audited.txt` A.1, lines 59–76: "In fact the argument works for any
deterministic dense `Q` with the stated truncation convention"; its construction only switches at interior points).
This file assembles Lemma GW2 (version 2, ruling R51) on that route.

* `GW2InteriorScheduleQStatement` (named input, GB9a): a deterministic countable dense `Q ⊂ (0, ∞)` such that, for every
  regular staged family, every `Θ`-schedule with times in `Q` from `0` or from a root of the first low right arc has
  almost surely interior switching tips while it is successful.
* `GW2TipExhaustionAllQStatement` (named input, GW2's exhaustion for every `Q`; the form of follow-up A.1) and
  `gw2TipExhaustionR51Statement_of_allQ` (it implies the version-2 exhaustion of `GW2Tip`).
* **`gw2LightConeR51Statement_of_interiorQ`**: Lemma GW2 (version 2) from Theorem 1.3, BR6, BR4a, GB6 (restart form and
  prefix form), GB9a's `Q` and the exhaustion for every `Q`. The schedule containments come from GW1's induction
  (`GW2Later.ae_physSet_subset_of_step`, with the inductive step `gb6PastStepStatement_of_prefix`).
* `completedRange_eq_closure_lightCone_of_interiorQ`: the version-2 light-cone anchor's shape on this route (with Lemma
  GW2a for the `gw2 = false` histories).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Tip

open GW2Cone GW2Schedule GW2Later

/-- **Named input: GB9a's schedule set** (supplement p. 527, Lemma GB9a; GW2, p. 621, proof ¶1: "one deterministic dense
countable `Q` for which all switching and terminal tips of successful schedules are interior"). For `0 < κ < 4`, a GFF
`h` with piecewise-constant data and a countable `Θ ⊂ (−π/2, π/2)`, there is a deterministic countable dense
`Q ⊂ (0, ∞)` such that for every staged-history family with almost surely continuous launched pieces (ruling R51), every
`Θ`-schedule `l` with times in `Q` run in the GW2 convention from the root `0` or from a root of the first low right
arc, and every `k`: almost surely, if the first `k` pieces were successful then their switching tips are interior. -/
def GW2InteriorScheduleQStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) → ∀ l : List (ℝ × ℝ≥0), IsSchedule Θ Q l →
          ∀ k : ℕ, ∀ᵐ ω ∂P, AllSucc (schedDelta 0 l) (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k →
            SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩ (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k

/-- **Named input: GW2's exhaustion at an interior counterflow tip, for every deterministic countable dense schedule
set** (version 2, ruling R51; follow-up note A.1: "In fact the argument works for any deterministic dense `Q`"): as
`GW2TipExhaustionR51Statement`, with `Q` arbitrary instead of chosen. -/
def GW2TipExhaustionAllQStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∀ Q : Set ℝ≥0, Q.Countable → Dense Q → (∀ q ∈ Q, 0 < q) →
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        ∀ γ : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω)) →
          ∀ s : ℝ≥0, ∀ᵐ ω ∂P, γ ω s ∈ H →
            -(γ ω s)⁻¹ ∈ closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω))

/-- The positive rational points of `ℝ≥0` form a countable dense set. -/
theorem exists_countable_dense_pos : ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ ∀ q ∈ Q, 0 < q := by
  refine ⟨range (fun q : ℚ => (q : ℝ).toNNReal) \ {0}, (countable_range _).mono sdiff_subset,
    Dense.sdiff_singleton (s := range fun q : ℚ => (q : ℝ).toNNReal) Exist.StagedLaw.denseRange_rat_toNNReal 0,
    fun q hq => ?_⟩
  exact pos_iff_ne_zero.2 hq.2

/-- **The exhaustion for every `Q` gives the version-2 exhaustion** (choose the positive rationals). -/
theorem gw2TipExhaustionR51Statement_of_allQ (hEx : GW2TipExhaustionAllQStatement.{u}) :
    GW2TipExhaustionR51Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  obtain ⟨Q, hQc, hQd, hQpos⟩ := exists_countable_dense_pos
  exact ⟨Q, hQc, hQd, hQpos, hEx κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos⟩

/-- **Lemma GW2, version 2, on GB9a's schedule set** (supplement pp. 621–623). From Theorem 1.3 (frozen type, at `u`
and `0`), BR6 (the forced arcs), BR4a (the pair at a boundary root), GB6's restart law (the first piece), GB6
conditioned on the piece's prefix (GW1's inductive step, `gb6PastStepStatement_of_prefix`), GB9a's set `Q` (interior
switching tips) and the tip exhaustion for every `Q`. -/
theorem gw2LightConeR51Statement_of_interiorQ (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GB6PrefixPairStatement.{u})
    (hQ : GW2InteriorScheduleQStatement.{u}) (hEx : GW2TipExhaustionAllQStatement.{u}) :
    GW2LightConeR51Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  obtain ⟨Q, hQc, hQd, hQpos, hQint⟩ := hQ κ hκ hκ4 b jumps hb P h hh Θ hΘ hΘc
  refine ⟨Q, hQc, hQd, hQpos, fun E hE hreg => ?_⟩
  have hStep := gb6PastStepStatement_of_prefix hG hT13
  have hSc := countable_setOf_isSchedule hΘc hQc
  have hRc := countable_lowerArcRoots κ b jumps
  have hsched : ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) → ∀ l ∈ {l | IsSchedule Θ Q l},
      ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun k => E ⟨x, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    fun x hx l hl => ae_physSet_subset_of_step hStep hBR4a hGB6 hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hE hreg hx
      (mem_Icc_of_isSchedule hΘ hl) hl.2 (hQint E hE hreg x hx l hl)
  have h0 : ∀ᵐ ω ∂P, ∀ l ∈ {l | IsSchedule Θ Q l}, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
      (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hSc).2 fun l hl => hsched 0 (Or.inl rfl) l hl
  have harc : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps,
      ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => gw2ForcedArcStatement_of_br6 hBR6
      (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀) hT13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' v hv
  have hv : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps, ∀ l ∈ {l | IsSchedule Θ Q l},
      ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => (ae_ball_iff hSc).2 fun l hl => hsched v (Or.inr hv) l hl
  have hEQ := hEx κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos E hE hreg
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hκ' : 0 < 16 / κ := by positivity
  have hγ := GW2aSingle.ae_chosenTrace hT13 hκ' hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  have hγtop : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (GW2aSingle.chosenTrace W' ζ' ω) := by
    filter_upwards [hγ, hζ'] with ω hω hζ
    rw [hζ] at hω
    exact hω.1
  have hex : ∀ᵐ ω ∂P, ∀ q : ℚ, GW2aSingle.chosenTrace W' ζ' ω (q : ℝ).toNNReal ∈ H →
      -(GW2aSingle.chosenTrace W' ζ' ω (q : ℝ).toNNReal)⁻¹ ∈
        closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω)) :=
    ae_all_iff.2 fun q => hEQ (GW2aSingle.chosenTrace W' ζ') hγtop (q : ℝ).toNNReal
  filter_upwards [hγ, hζ', hdrv, h0, harc, hv, hex] with ω hγω hζω hdω h0ω harcω hvω hexω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  exact closure_union_zero_eq hγω.1 hWc hdω.1 (hγω.2 rfl)
    (boundaryLightConeFamily_subset h0ω harcω hvω) hexω

/-- **Theorem 1.4, light cone, version 2** (`IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`, R51),
provider shape, on GB9a's schedule set: from Theorem 1.3 (frozen type, at `u` and `0`), BR6, BR4a, GB6 (restart form
and prefix form), GB9a's `Q`, the exhaustion for every `Q` and Lemma GW2a (conditional helper; not the provider). -/
theorem completedRange_eq_closure_lightCone_of_interiorQ (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GB6PrefixPairStatement.{u})
    (hQ : GW2InteriorScheduleQStatement.{u}) (hEx : GW2TipExhaustionAllQStatement.{u})
    (hGW2a : GW2aContainmentStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {Θ : Set ℝ} (hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by assumption)
    (hΘc : Θ.Countable := by assumption)
    (hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ := by assumption) :
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        (∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
            counterflowCompletedRange (fun t => W' t ω)) ∧
        ∀ 𝒞 : Set (List Instr), 𝒞.Countable → (∀ p ∈ 𝒞, IsBoundaryContinuedProgram p) →
          ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪
              (⋃ p ∈ 𝒞, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω)) ∪
              {0}) =
            counterflowCompletedRange (fun t => W' t ω) := by
  have hGW2 := gw2LightConeR51Statement_of_interiorQ h13 h13₀ hBR6 hBR4a hGB6 hG hQ hEx
  obtain ⟨Q, hQc, hQd, hQpos, hQ'⟩ := hGW2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  refine ⟨Q, hQc, hQd, hQpos, fun E hE hreg => ⟨hQ' E hE hreg, fun 𝒞 h𝒞 h𝒞p => ?_⟩⟩
  have hcont : ∀ᵐ ω ∂P, ∀ p ∈ 𝒞,
      ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff h𝒞).2 fun p hp => hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE p (h𝒞p p hp)
  filter_upwards [hQ' E hE hreg, hcont] with ω h1 h2
  exact closure_union_union_eq h1 (iUnion₂_subset h2)

end GW2Tip

end Theorem14

end InteractingSLE
