/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RSymRun
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.WalkUnionLawMain
import InteractingSLE.Spec.Supplement.GW1Later
import InteractingSLE.Spec.Sec5.CfDownRec
import InteractingSLE.Spec.Sec7.StripWallInputsRefl
import InteractingSLE.Spec.Sec7.StripWallInputsReflDet
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Exist.StagedLawPast
import InteractingSLE.Spec.Exist.StagedLaw2Run

/-!
# The reflection symmetry of staged histories

Packet PROVE-T14-SB4LEAF (ruling R104). Through the reflection `ρ(z) = −z̄`, a staged history `D` of the field `h`
(data `b`) with drivers regular at every sample becomes the staged history `−D` of the reflected program of the
reflected field `−h ∘ ρ` (data `y ↦ −b(−y)`), as soon as the reflected run is almost surely the reflected run
(`RunsRefl`):

* `negPast`, `pastMap_refl`, **`ae_condExpKernel_refl`**: the reflected retained past is the negated one, so the two
  retained σ-algebras have almost surely the same regular conditional laws;
* **`isStagedHistory_refl`**, **`stagedPiecesRegular_refl`**: the reflected history is a staged history with regular
  pieces;
* `runsRefl_schedule` (every sample: GW2 schedules, `run_reflState_stuck`) and **`ae_runsRefl_leftWalk`** (almost
  surely: no piece of the left walk ends at a two-sided hit, since none ends at a right record,
  `GW1W.ae_status_ne_right_left_walk`, under GW1's ambient bound).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Exist.Staged Exist.StagedLaw GW2Schedule
open Sec7.StripWall (negDrv measurable_negDrv isRegularDriver_negDrv)
open Sec7.FlowReflect (reflData reflJumps reflField)

/-! ### The negated retained past -/

/-- The negated retained past: every stopped driver negated. -/
def negPast {k : ℕ} (x : PastData k) : PastData k := fun i => (fun q => -(x i).1 q, (x i).2.1, (x i).2.2)

theorem negPast_negPast {k : ℕ} (x : PastData k) : negPast (negPast x) = x := by
  funext i
  simp only [negPast, neg_neg]

theorem measurable_negPast (k : ℕ) : Measurable (negPast (k := k)) := by
  refine measurable_pi_iff.2 fun i => Measurable.prodMk ?_ (measurable_snd.comp (measurable_pi_apply i))
  exact measurable_pi_iff.2 fun q => Measurable.neg (f := fun x : PastData k => (x i).1 q)
    ((measurable_pi_apply q).comp (measurable_fst.comp (measurable_pi_apply i)))

/-- The negated retained past generates the same σ-algebra. -/
theorem comap_negPast_comp {Ω : Type*} {k : ℕ} (f : Ω → PastData k) :
    MeasurableSpace.comap (negPast ∘ f) inferInstance = MeasurableSpace.comap f inferInstance := by
  apply le_antisymm
  · rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_negPast k).comap_le
  · conv_lhs => rw [show f = negPast ∘ (fun ω => negPast (f ω)) from funext fun ω => (negPast_negPast _).symm]
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_negPast k).comap_le

/-! ### Reflected runs -/

/-- `s'` has the reflected pieces, connectors, retained data and launch records of `s`. -/
def CompRefl (s' s : ExplState) : Prop :=
  s'.1 = (reflState s).1 ∧ s'.2.1 = (reflState s).2.1 ∧ s'.2.2.1 = (reflState s).2.2.1 ∧
    s'.2.2.2.1 = (reflState s).2.2.2.1

theorem compRefl_reflState (s : ExplState) : CompRefl (reflState s) s := ⟨rfl, rfl, rfl, rfl⟩

theorem StuckRel.compRefl {s s' : ExplState} (h : StuckRel s s') : CompRefl s' s :=
  let c := h.components
  ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1⟩

/-- **The run of the reflected program with the drivers `D'` has the reflected components of the run with `D`.** -/
def RunsRefl (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (spec : ExplSpec) (D' D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ k, CompRefl (ExplState.run κ (reflData b) (reflJumps J) (reflSpec spec) D' k) (ExplState.run κ b J spec D k)

theorem RunsRefl.congr_right {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {spec : ExplSpec} {D' D D₁ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h : RunsRefl κ b J spec D' D) (h₁ : ∀ k, ExplState.run κ b J spec D k = ExplState.run κ b J spec D₁ k) :
    RunsRefl κ b J spec D' D₁ := fun k => by
  rw [← h₁ k]
  exact h k

theorem scheduleProgram_flow (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    ∀ (j : ℕ) (i : Instr), (scheduleProgram τ₀ l)[j]? = some i → ∃ θ t, i = .inl (θ, t) := by
  induction l generalizing τ₀ with
  | nil => intro j i h; simp [scheduleProgram] at h
  | cons p l ih =>
    intro j i h
    rcases j with _ | j
    · simp only [scheduleProgram, List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨_, _, h.symm⟩
    · exact ih p.2 j i (by simpa [scheduleProgram] using h)

/-- **A GW2 schedule always reflects** (`run_reflState_stuck`). -/
theorem runsRefl_schedule {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    RunsRefl κ b J (x, true, scheduleProgram 0 l) (reflDrv D) D := fun k =>
  (run_reflState_stuck hb (x, true, scheduleProgram 0 l) rfl (scheduleProgram_flow 0 l) D k).compRefl

section Staged

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- The reflected retained past is the negated retained past. -/
theorem pastMap_refl {spec : ExplSpec} {D' D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}
    (h : RunsRefl κ b J spec (fun j => D' j ω) (fun j => D j ω)) (k : ℕ) :
    pastMap κ (reflData b) (reflJumps J) (reflSpec spec) D' k ω = negPast (pastMap κ b J spec D k ω) := by
  funext i
  simp only [pastMap]
  rw [(h k).2.2.1, reflState_retained]
  rfl

variable [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The reflected retained σ-algebra has almost surely the regular conditional law of the original one.** -/
theorem ae_condExpKernel_refl (hb : IsPiecewiseConstantBoundaryData b J) {spec : ExplSpec}
    {D' D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD' : ∀ k, Measurable (D' k)) (hreg' : ∀ k ω, IsRegularDriver (D' k ω))
    (hD : ∀ k, pastSigma κ b J spec D k ≤ mΩ)
    (hrel : ∀ᵐ ω ∂P, RunsRefl κ b J spec (fun j => D' j ω) (fun j => D j ω)) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ (reflData b) (reflJumps J) (reflSpec spec) D' k) ω₀ =
      condExpKernel P (pastSigma κ b J spec D k) ω₀ := by
  have hb' := Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb
  have hpm' : Measurable (pastMap κ (reflData b) (reflJumps J) (reflSpec spec) D' k) :=
    measurable_pastMap runMeasStatement hb' (reflSpec spec) (fun j _ => hD' j) (fun j _ ω => hreg' j ω) k le_rfl
  have hpm : Measurable (pastMap κ b J spec D k) := Measurable.of_comap_le (hD k)
  have hpast : pastMap κ (reflData b) (reflJumps J) (reflSpec spec) D' k =ᵐ[P]
      fun ω => negPast (pastMap κ b J spec D k ω) := hrel.mono fun ω hω => pastMap_refl hω k
  filter_upwards [StagedReg.ae_condExpKernel_eq_of_ae_eq hpm' ((measurable_negPast k).comp hpm) hpast] with ω₀ hK
  rw [pastSigma_eq_comap, hK, comap_negPast_comp, ← pastSigma_eq_comap]

theorem launch_of_runsRefl {spec : ExplSpec} {D' D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hr : RunsRefl κ b J spec D' D)
    {k : ℕ} {c' : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ (reflData b) (reflJumps J) (reflSpec spec) D' (k + 1)).2.2.2.1 k = some (c', θ')) :
    ∃ c : Chart, c' = reflChart c ∧ (ExplState.run κ b J spec D (k + 1)).2.2.2.1 k = some (c, -θ') := by
  rw [(hr (k + 1)).2.2.2, reflState_launches] at hl
  obtain ⟨⟨c, θ⟩, hl0, he⟩ := Option.map_eq_some_iff.1 hl
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨c, rfl, by rw [hl0, neg_neg]⟩

/-- **The reflection of a staged history** whose drivers are regular at every sample and whose reflected run is almost
surely the reflected run. -/
theorem isStagedHistory_refl (hb : IsPiecewiseConstantBoundaryData b J) {spec : ExplSpec}
    {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : IsStagedHistory κ b J P h spec D)
    (hreg : ∀ k ω, IsRegularDriver (D k ω))
    (hrel : ∀ᵐ ω ∂P, RunsRefl κ b J spec (fun j => negDrv (D j ω)) (fun j => D j ω)) :
    IsStagedHistory κ (reflData b) (reflJumps J) P (fun ω => reflField (h ω)) (reflSpec spec)
      (fun k ω => negDrv (D k ω)) := by
  have hb' := Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb
  have hm' : ∀ k, Measurable fun ω => negDrv (D k ω) := fun k => measurable_negDrv.comp (hD.1 k)
  have hreg' : ∀ k ω, IsRegularDriver (negDrv (D k ω)) := fun k ω => isRegularDriver_negDrv (hreg k ω)
  refine ⟨hm', fun k => (measurable_pastMap runMeasStatement hb' (reflSpec spec) (fun j _ => hm' j)
    (fun j _ ω => hreg' j ω) k le_rfl).comap_le, fun k => Eventually.of_forall fun ω => (hreg' k ω).2.2.2,
    fun k => ?_⟩
  filter_upwards [hD.2.2.2 k, ae_condExpKernel_refl hb hm' hreg' hD.2.1 hrel k, hrel] with ω₀ h4 hK hω c' θ' hl'
  obtain ⟨c, rfl, hl⟩ := launch_of_runsRefl hω hl'
  obtain ⟨b', J', h', hb'', htr, hfl⟩ := h4 c (-θ') hl
  refine ⟨reflData b', reflJumps J', fun ω => reflField (h' ω),
    Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb'', fun ω => ?_, ?_⟩
  · have := Sec5.CfDown.IsChartTransport.reflect_of (c' := reflChart c) (fun z => rfl) (fun w _ => rfl)
      (fun z => rfl) (htr ω)
    rwa [neg_zero] at this
  · rw [hK]
    have := Sec7.StripWall.isFlowLineDriver_reflect hb'' hfl
    rw [neg_neg] at this
    exact this

omit [StandardBorelSpace Ω] [IsFiniteMeasure P] in
/-- **The reflection of a staged history with regular pieces has regular pieces.** -/
theorem stagedPiecesRegular_refl {spec : ExplSpec} {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b J P spec D)
    (hrel : ∀ᵐ ω ∂P, RunsRefl κ b J spec (fun j => negDrv (D j ω)) (fun j => D j ω)) :
    StagedPiecesRegular κ (reflData b) (reflJumps J) P (reflSpec spec) (fun k ω => negDrv (D k ω)) := by
  filter_upwards [hR, hrel] with ω hω hr
  intro k θ' t c' hk hl'
  rw [getElem?_reflSpec] at hk
  obtain ⟨i, hi, hie⟩ := Option.map_eq_some_iff.1 hk
  have hi' : spec.2.2[k]? = some (.inl (-θ', t)) := by
    rcases i with ⟨θ, t'⟩ | pref | ⟨v, pref⟩
    · simp only [reflInstr, Sum.inl.injEq, Prod.mk.injEq] at hie
      obtain ⟨rfl, rfl⟩ := hie
      rw [hi, neg_neg]
    · simp [reflInstr] at hie
    · simp [reflInstr] at hie
  obtain ⟨c, -, hl⟩ := launch_of_runsRefl hr hl'
  obtain ⟨h0, hc, η, hη, htr⟩ := hω k (-θ') t c hi' hl
  refine ⟨?_, hc.neg, fun s => refl (η s), LP.isGeneratingTrace_reflect hη, fun hT => ?_⟩
  · show -(D k ω).1 0 = 0
    rw [h0, neg_zero]
  · simpa only [norm_refl] using htr hT

end Staged

/-! ### The left walk reflects almost surely -/

section LeftWalk

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The left walk reflects almost surely**: no launch of the left walk has a two-sided hit, since no piece of it
ends at a new right record (Lemma GW1 reflected, `GW1W.ae_status_ne_right_left_walk`, under GW1's ambient bound
from the complete centred counterflow), and a two-sided hit would be classified as a right threshold. -/
theorem ae_runsRefl_leftWalk (h13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : IsStagedHistory κ b J P h (boundaryWalkSpec b J (Real.pi / 2) false) D)
    (hreg : ∀ k ω, IsRegularDriver (D k ω)) :
    ∀ᵐ ω ∂P, ∀ k, ExplState.run κ (reflData b) (reflJumps J) (reflSpec (boundaryWalkSpec b J (Real.pi / 2) false))
        (fun j => negDrv (D j ω)) k =
      reflState (ExplState.run κ b J (boundaryWalkSpec b J (Real.pi / 2) false) (fun j => D j ω) k) := by
  have hamb := (GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hb hh hcf hζ').2
  filter_upwards [GW1W.ae_status_ne_right_left_walk hκ hb hh hD hreg hamb] with ω hω
  intro k
  refine run_reflState hb _ (fun j => D j ω) k fun j _ θ t hj hfl => ?_
  by_contra hnt
  apply hω j
  rw [run_succ, hj]
  show stStatus (ExplState.flowStep κ b (boundaryWalkSpec b J (Real.pi / 2) false).2.1
    (ExplState.run κ b J (boundaryWalkSpec b J (Real.pi / 2) false) (fun j => D j ω) j) j (D j ω) θ t) = _
  rw [hfl]
  exact (launch_status_of_not_tieFree _ j _ θ t hnt).1

end LeftWalk

end InteractingSLE.Theorem14.SB.Lf
