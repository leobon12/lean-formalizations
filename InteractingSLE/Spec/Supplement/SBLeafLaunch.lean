/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLeafWord
import InteractingSLE.Spec.Supplement.FlowDilateFlow
import InteractingSLE.Spec.Supplement.GW2aSingle
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Sec7.StripWallStage0
import InteractingSLE.Spec.Supplement.GW2ScheduleLaw
import InteractingSLE.Spec.Supplement.GW2SchedulePast
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# The new upper piece and its conditional field from the staged launch clause

Packet PROVE-T14-SBTAIL. In SB4's switch step the new upper piece "starts at its own driver" in
"the same conditional field" as the relative lower tail (specification p. 634). For an actual
staged schedule this is the frozen `IsStagedHistory` launch clause: under the conditional law given
the retained past `pastSigma k`, the driver of instruction `k` is a flow-line driver of the field
read in the launch chart, with some piecewise-constant data `b'`. This file derives from it, for
every real translation `m` of the launch chart (the relative chart in which the relative lower walk
starts at `0` and the new piece at `m ≤ 0`):

* `relFlowLine_of_isFlowLineDriver`: the translated field is a GFF with the translated data, and the
  translated chosen trace (Theorem 1.3, `GW2aSingle.chosenTrace`) is a frozen `IsFlowLine` from `m`
  (`FlowDilate`'s affine transport with `a = 1`);
* `launch_angle_mem_schedule`: a launched schedule angle is one of the schedule's angles;
* `HasLaunchRelativeTail`: the switch data in which the field, the data `b'` and the new piece are
  the launch clause's own (quantified over every witness), so that only SB2(2)'s relative walk, the
  height classification of SB4's word paragraph, positivity of the lifetime and the gluing geometry
  remain;
* `hasConditionalRelativeTail_of_launch`: this data gives `HasConditionalRelativeTail`;
* `HasScheduleLaunchTail`, `hasLaunchRelativeTail_of_schedule`: for schedules the launch event is an
  event of the retained past (`measurableSet_launchEvent_schedule`, from the landed
  `launch_ne_none_iff` and `measurableSet_allSucc`), so its null-measurability and the non-launched
  realizations need no data.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Leaf

open Sec4 FlowDilate GW2Schedule Exist.StagedLaw

/-- **The new piece in a translated launch chart.** A flow-line driver from `0` with data `b'` gives,
after translating the chart by `m`, a GFF with the translated data and the frozen flow line from `m`
traced by the translated chosen trace (Theorem 1.3). -/
theorem relFlowLine_of_isFlowLineDriver (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b' J') {θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hl : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b' J' θ Q hl W ζ) (m : ℝ) :
    IsPiecewiseConstantBoundaryData (affData 1 m b') (affJumps 1 m J') ∧
      IsGFFWithBoundaryData Q (fun ω => affField m one_pos (hl ω)) (affData 1 m b')
        (affJumps 1 m J') ∧
      IsFlowLine κ (affData 1 m b') (affJumps 1 m J') m θ Q (fun ω => affField m one_pos (hl ω))
        (fun ω t => aff 1 m (GW2aSingle.chosenTrace W ζ ω t)) ζ := by
  have htr := GW2aSingle.ae_chosenTrace h13 hκ hfl
  have h0 : IsFlowLine κ b' J' 0 θ Q hl (GW2aSingle.chosenTrace W ζ) ζ :=
    Sec7.StripWall.isFlowLine_of_isFlowLineDriver hfl (htr.mono fun ω hω => hω.1)
  have h1 := h0.affine (a := 1) (m := m) one_pos hb
  have hc : cDil 1 = 1 := by simp only [cDil, inv_one, one_pow, Real.toNNReal_one]
  have hr : raff 1 m 0 = m := by simp only [raff, mul_zero, zero_add]
  simp only [hc, hr, one_mul, ENNReal.coe_one, div_one] at h1
  exact ⟨isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb,
    (GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb hfl).affine_finset one_pos, h1⟩

/-- A launched instruction of a schedule program carries one of the schedule's angles. -/
theorem launch_angle_mem_schedule {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {c : Chart} {θ : ℝ}
    (h : (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ D (k + 1)).2.2.2.1 k =
      some (c, θ)) :
    ∃ q ∈ l, θ = q.1 := by
  obtain ⟨hi, -, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D h
  change (scheduleProgram 0 l)[k]? = _ at hi
  have hk : k < (scheduleProgram 0 l).length := by
    by_contra hk
    rw [List.getElem?_eq_none (not_lt.1 hk)] at hi
    exact (Option.some_ne_none _).symm hi
  rw [isFlowProg_scheduleProgram 0 l k hk] at hi
  have hθ : schedAngle l k = θ := by
    simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at hi
    exact hi.1
  rw [length_scheduleProgram] at hk
  refine ⟨l[k], List.getElem_mem hk, ?_⟩
  rw [← hθ]
  unfold schedAngle
  rw [List.getD_eq_getElem _ _ hk]

/-- The event that instruction `k` of a history launches. -/
def launchEvent (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) {Ω : Type u}
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : Set Ω :=
  {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none}

/-- **The data at one launched realization** `ω₀` with launch chart `c` and angle `θ`: for every
witness of the frozen launch clause (data `b'` off `J'`, launch-chart field `hl`), a translation
`m ≤ 0` of the launch chart carries SB2(2)'s relative lower walk `EL` of the translated field (a
regular staged history), the height classification of SB4's word paragraph on `(m, 0)` (old
schedule sides, low groups, or the retained original word `original`), a positive lifetime, and the
S1-free gluing geometry of the translated chosen trace. -/
def LaunchRelData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (k : ℕ) (l : List (ℝ × ℝ≥0)) (original : Set ℝ) (A S : Ω → Set ℂ) (ω₀ : Ω) (c : Chart)
    (θ : ℝ) : Prop :=
  ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (hl : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hl ω)) →
    IsFlowLineDriver κ b' J' θ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) hl
      (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) →
    ∃ (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), m ≤ 0 ∧
      (IsBoundaryContinuedProgram
          (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true).2.2 →
        IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
            (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)
            (fun ω => affField m one_pos (hl ω))
            (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true) EL ∧
          StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m J')
            (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)
            (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true) EL) ∧
      (∀ x ∈ Ioo m 0, x ∉ affJumps 1 m J' →
        (∃ p ∈ l, affData 1 m b' x = sleLambda κ - p.1 * chiC κ ∨
            affData 1 m b' x = -sleLambda κ - p.1 * chiC κ) ∨
          affData 1 m b' x ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨
          affData 1 m b' x ∈ original) ∧
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), 0 < (E k ω).2) ∧
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        ω ∈ launchEvent κ b jumps spec E k →
        HasRelTailGeometry (A ω) (S ω)
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω) m
          (fun t => aff 1 m (GW2aSingle.chosenTrace (fun t ω => (E k ω).1 t)
            (fun ω => (E k ω).2) ω t)) (E k ω).2

/-- **The switch data in launch form.** The conditional σ-algebra is the history's own retained past
`pastSigma k`; at almost every realization either the sewing certificate holds conditionally on the
launch event (null launch, or the singleton seed of an inadmissible angle), or the realization is a
launch whose data `LaunchRelData` hold. -/
def HasLaunchRelativeTail (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (k : ℕ) (l : List (ℝ × ℝ≥0)) (original : Set ℝ) (A S : Ω → Set ℂ) : Prop :=
  ∃ a : Ω → ℝ≥0 → ℂ,
    NullMeasurableSet (launchEvent κ b jumps spec E k) P ∧
    (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
    (∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps spec E k →
      Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) ∧
    ∀ᵐ ω₀ ∂P,
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        ω ∈ launchEvent κ b jumps spec E k → HasActualTailSewing (A ω) (S ω)) ∨
      ∃ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) ∧
        LaunchRelData κ b jumps P h spec E k l original A S ω₀ c θ

/-- **The launch form gives the S1-free switch data.** Under (SB4.1) and the bridge hypothesis, the
launch clause of the staged history supplies the conditional field and the new piece of the SB3
instance; the remaining fields are those of `HasLaunchRelativeTail`. -/
theorem hasConditionalRelativeTail_of_launch (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) {k : ℕ} {l : List (ℝ × ℝ≥0)}
    {original : Set ℝ} {A S : Ω → Set ℂ}
    (hangles : ∀ p ∈ l, -(Real.pi / 2) < p.1)
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hθl : ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∃ q ∈ l, θ = q.1)
    (hL : HasLaunchRelativeTail κ b jumps P h spec E k l original A S) :
    HasConditionalRelativeTail κ P (launchEvent κ b jumps spec E k) A S := by
  obtain ⟨a, hF, hm, hreg, hcond⟩ := hL
  refine ⟨⟨pastSigma κ b jumps spec E k, hE.2.1 k⟩, a, hF, hm, hreg, ?_⟩
  filter_upwards [hcond, hE.2.2.2 k, hθl] with ω₀ hω₀ hlaunch hθ
  rcases hω₀ with hdir | ⟨c, θ, hcθ, hall⟩
  · exact Or.inl hdir
  · obtain ⟨b', J', hl, hb', hct, hfl⟩ := hlaunch c θ hcθ
    obtain ⟨m, EL, hm0, hEL, hword, hpos, hgeo⟩ := hall b' J' hl hb' hct hfl
    obtain ⟨q, hq, rfl⟩ := hθ c θ hcθ
    obtain ⟨hpc, hG, hFL⟩ := relFlowLine_of_isFlowLineDriver h13 hκ hb' hfl m
    refine Or.inr ⟨fun ω => affField m one_pos (hl ω), affData 1 m b', affJumps 1 m J', EL, m, q.1,
      fun ω t => aff 1 m (GW2aSingle.chosenTrace (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) ω t),
      fun ω => (E k ω).2, ?_, hgeo⟩
    exact isRelSB3Instance_of_word hκ hκ4 hangles hgaps hbridge
      ⟨hpc, hG, hEL, hm0, ⟨q, hq, rfl⟩, hword, hFL, hpos⟩

/-! ### Schedules: the launch event is determined by the retained past -/

/-- A schedule instruction launches exactly when every earlier piece ran its full own time. -/
theorem launchEvent_schedule_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {Ω : Type u} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k < (scheduleProgram 0 l).length) :
    launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k =
      {ω | AllSucc (schedDelta 0 l) (fun j => E j ω) k} := by
  ext ω
  exact launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) (schedAngle l) (schedDelta 0 l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) (fun j => E j ω) hk

/-- The launch event of a schedule instruction is an event of its retained past. -/
theorem measurableSet_launchEvent_schedule {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {Ω : Type u} [MeasurableSpace Ω] (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) :
    MeasurableSet[pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k]
      (launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) := by
  rw [launchEvent_schedule_eq E hk]
  exact measurableSet_allSucc rfl (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) E hk.le

/-- **The schedule form of the launch data**: the launch event's measurability and the
non-launched realizations are handled by the retained past, so only launched realizations carry
data (the sewing certificate directly, or `LaunchRelData`). -/
def HasScheduleLaunchTail (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (x : ℝ) (l : List (ℝ × ℝ≥0))
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (original : Set ℝ) (A S : Ω → Set ℂ) : Prop :=
  ∃ a : Ω → ℝ≥0 → ℂ,
    (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
    (∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
      Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) ∧
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (fun j => E j ω₀) (k + 1)).2.2.2.1 k =
        some (c, θ) →
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
          ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
          HasActualTailSewing (A ω) (S ω)) ∨
        LaunchRelData κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E k l original A S ω₀ c θ

theorem hasLaunchRelativeTail_of_schedule {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {original : Set ℝ} {A S : Ω → Set ℂ}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E)
    (hk : k < (scheduleProgram 0 l).length)
    (hL : HasScheduleLaunchTail κ b jumps P h x l E k original A S) :
    HasLaunchRelativeTail κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E k l original A S := by
  obtain ⟨a, hm, hreg, hcond⟩ := hL
  have hF := measurableSet_launchEvent_schedule (κ := κ) (b := b) (jumps := jumps) (x := x) E hk
  refine ⟨a, (hE.2.1 k _ hF).nullMeasurableSet, hm, hreg, ?_⟩
  filter_upwards [hcond, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (hE.2.1 k) hF.compl]
    with ω₀ h1 h2
  by_cases hω₀ : ω₀ ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k
  · obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω₀
    rcases h1 c θ hcθ with hd | hd
    · exact Or.inl hd
    · exact Or.inr ⟨c, θ, hcθ, hd⟩
  · refine Or.inl ?_
    filter_upwards [h2 hω₀] with ω hω hωF
    exact absurd hωF hω

end InteractingSLE.Theorem14.SB.Leaf
