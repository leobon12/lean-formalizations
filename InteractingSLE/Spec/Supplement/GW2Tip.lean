/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleR51Ident
import InteractingSLE.Spec.Supplement.GW2Cone
import InteractingSLE.Spec.Supplement.GW2Sched
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Exist.StagedLaw3Main

/-!
# GW2's tip exhaustion: only the canonical construction matters (ruling R51)

Packet PROVE-T14-TIP6. The named step `GW2Cone.GW2TipExhaustionStatement` (GW2, pp. 621–623) quantifies over every
staged-history family `E`. Under ruling R51 the version-2 Theorem 1.4 anchors assume, besides `IsStagedHistory`, that
the launched pieces are almost surely continuous curves (`StagedPiecesRegular`), and only for such families is the
exhaustion provable (R51's finding: without pathwise regularity a staged family may be irregular on a set of positive
outer measure). This file

* states the exhaustion in the shape of the version-2 anchors (`GW2TipExhaustionR51Statement`: the same statement with
  the added hypothesis `StagedPiecesRegular` for every boundary-continued program);
* states the exhaustion for the **canonical construction** (`GW2TipExhaustionCanonStatement`): the canonical pieces
  `GW2Schedule.canonFam` of every GW2 schedule, built from the field sample alone, jointly measurably in the own times
  (PROVE-T14-TIP3), for any valid construction parameters (a single-stage law `βA`, a word `c₀` of the boundary data);
* proves `gw2TipExhaustionR51Statement_of_canon`: the exhaustion for every R51 family follows from the exhaustion for
  the canonical construction, by the identification `GW2Schedule.ae_physSet_eq_canon_R51` ("By field determination and
  canonical consistency it is a member of the originally fixed countable family", shortcut note §1.2; GB9, p. 526),
  intersected over the countably many schedules and roots of the family.

The canonical form is the one in which the central-band experiment is run: Lemma 1.2 of the shortcut note selects its
integer with "the retained conditional next-piece kernel `K_z`, with stage-start state `z`", which the canonical
construction provides as a measurable function of the field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Tip

open GW2Schedule GW2Cone GW2Sched Exist Staged StagedLaw Restart LQGMetric

/-! ### The canonical family of every program -/

/-- The angle of instruction `j` of a history (`0` beyond the program). -/
def specAngle (spec : ExplSpec) (j : ℕ) : ℝ := instrAngle spec j

/-- The own time of instruction `j` of a history, made finite (`0` where it is `⊤`). -/
def specDelta (spec : ExplSpec) (j : ℕ) : ℝ≥0∞ := if instrTime spec j = ⊤ then 0 else instrTime spec j

theorem specDelta_ne_top (spec : ExplSpec) (j : ℕ) : specDelta spec j ≠ ⊤ := by
  unfold specDelta
  split_ifs with h
  · exact ENNReal.zero_ne_top
  · exact h

/-- A schedule program, read with `specAngle` and `specDelta`, is a flow program. -/
theorem isFlowProg_spec (x : ℝ) (gw : Bool) (l : List (ℝ × ℝ≥0)) :
    IsFlowProg (scheduleProgram 0 l) (specAngle ⟨x, gw, scheduleProgram 0 l⟩)
      (specDelta ⟨x, gw, scheduleProgram 0 l⟩) := by
  intro j hj
  have h := isFlowProg_scheduleProgram 0 l j hj
  have ha : specAngle ⟨x, gw, scheduleProgram 0 l⟩ j = schedAngle l j := by
    change instrAngle ⟨x, gw, scheduleProgram 0 l⟩ j = _
    simp only [instrAngle, h]
  have ht : instrTime ⟨x, gw, scheduleProgram 0 l⟩ j = schedDelta 0 l j := by
    simp only [instrTime, h]
  have hd : specDelta ⟨x, gw, scheduleProgram 0 l⟩ j = schedDelta 0 l j := by
    simp only [specDelta, ht, schedDelta_ne_top, ite_false]
  rw [ha, hd]
  exact h

/-- **The canonical family**: for every history `spec`, the canonical pieces of its program (`GW2Schedule.canonFam`,
root `spec.1`), a measurable function of the field sample. -/
def canonSpecFam {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) {Ω : Type*}
    (h : Ω → DistOn upperHalfPlaneOpens) : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  fun spec => canonFam hκ h12p βA c₀ (specAngle spec) (specDelta spec) spec.1 h

/-! ### The statements -/

/-- **Named statement: GW2's exhaustion at an interior counterflow tip, version-2 form** (ruling R51): as
`GW2Cone.GW2TipExhaustionStatement`, for the staged families whose launched pieces are almost surely continuous curves
(`StagedPiecesRegular`, the added hypothesis of the version-2 Theorem 1.4 anchors). -/
def GW2TipExhaustionR51Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        ∀ γ : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω)) →
          ∀ s : ℝ≥0, ∀ᵐ ω ∂P, γ ω s ∈ H →
            -(γ ω s)⁻¹ ∈ closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω))

/-- **Named statement: GW2's exhaustion at an interior counterflow tip for the canonical construction.** For every
valid set of construction parameters (Theorem 1.2 in its word-measurable form, a single-stage law `βA`
(`IsStopLaw`), a word `c₀` of the boundary data), there is a deterministic countable dense schedule set `Q` such that,
for every process `γ` almost surely generating the counterflow driver and every time `s`, almost surely on the event of
an interior current tip `p = −γ(s)⁻¹`, `p` lies in the closure of the GW2 family of the canonical pieces
(`canonSpecFam`). This is the form in which the central-band experiment (pp. 621–623; shortcut note §1.2) is run. -/
def GW2TipExhaustionCanonStatement : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord), IsStopLaw.{u} κ βA →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord), IsPiecewiseConstantBoundaryData b jumps →
      c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ γ : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω)) →
        ∀ s : ℝ≥0, ∀ᵐ ω ∂P, γ ω s ∈ H →
          -(γ ω s)⁻¹ ∈ closure (boundaryLightConeFamily κ b jumps Θ Q
            (fun spec k => canonSpecFam hκ h12p βA c₀ h spec k ω))

/-! ### The reduction -/

/-- **The GW2 family of an R51 staged family is the canonical one**: almost surely, simultaneously for the countably
many schedules from `0` and from the roots of the first low right arc, the physical sets of `E` are those of the
canonical construction, so the two families coincide. -/
theorem ae_boundaryLightConeFamily_eq_canon {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    {βA : BoundaryWord × ℝ × RecData → BoundaryWord} {c₀ : BoundaryWord} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) {Θ : Set ℝ} (hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hΘc : Θ.Countable) {Q : Set ℝ≥0} (hQc : Q.Countable) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec)) :
    ∀ᵐ ω ∂P, boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) =
      boundaryLightConeFamily κ b jumps Θ Q (fun spec k => canonSpecFam hκ h12p βA c₀ h spec k ω) := by
  have hSc := countable_setOf_isSchedule hΘc hQc
  have hRc := countable_lowerArcRoots κ b jumps
  have hid : ∀ x : ℝ, ∀ᵐ ω ∂P, ∀ l ∈ {l | IsSchedule Θ Q l},
      ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (fun k => E ⟨x, true, scheduleProgram 0 l⟩ k ω) =
        ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
          (fun k => canonSpecFam hκ h12p βA c₀ h ⟨x, true, scheduleProgram 0 l⟩ k ω) := fun x =>
    (ae_ball_iff hSc).2 fun l hl => by
      have hprog := isBoundaryContinuedProgram_scheduleProgram (mem_Icc_of_isSchedule hΘ hl) 0
      exact ae_physSet_eq_canon_R51 hκ h12p _ _ βA c₀ h13 hβA hb hc₀J hc₀ hh rfl (isFlowProg_spec x true l)
        (specDelta_ne_top _) (hE _ hprog) (hreg _ hprog)
  have hv : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps, ∀ l ∈ {l | IsSchedule Θ Q l},
      ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) =
        ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩
          (fun k => canonSpecFam hκ h12p βA c₀ h ⟨v, true, scheduleProgram 0 l⟩ k ω) :=
    (ae_ball_iff hRc).2 fun v _ => hid v
  filter_upwards [hid 0, hv] with ω h0ω hvω
  simp only [boundaryLightConeFamily]
  refine congrArg₂ (· ∪ ·) (iUnion₂_congr fun l hl => h0ω l hl) ?_
  exact iUnion₂_congr fun v hv => congrArg (_ ∪ ·) (iUnion₂_congr fun l hl => hvω v hv l hl)

/-- **GW2's exhaustion for every R51 staged family from the exhaustion for the canonical construction** (Theorems
1.2–1.3 as their frozen types: the canonical construction and its identification use Theorem 1.2 in its
word-measurable form and the complete trace of Theorem 1.3). -/
theorem gw2TipExhaustionR51Statement_of_canon (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (hcanon : GW2TipExhaustionCanonStatement.{u}) : GW2TipExhaustionR51Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  have h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  obtain ⟨βA, hβA⟩ := (stopLawStatement_iff.1 stopLawStatement.{u}) κ hκ hκ4
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  obtain ⟨Q, hQc, hQd, hQ0, hQ⟩ :=
    hcanon κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  refine ⟨Q, hQc, hQd, hQ0, fun E hE hreg γ hγ s => ?_⟩
  filter_upwards [ae_boundaryLightConeFamily_eq_canon hκ h12p h13 hβA hb hc₀J hc₀ hh hΘ hΘc hQc hE hreg,
    hQ γ hγ s] with ω hfam hω hs
  rw [hfam]
  exact hω hs

end GW2Tip

end Theorem14

end InteractingSLE
