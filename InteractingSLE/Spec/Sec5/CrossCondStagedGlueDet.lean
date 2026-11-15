/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleInduction
import InteractingSLE.Spec.Supplement.WalkPastLaw
import InteractingSLE.Spec.Supplement.SB4SewGermRestart

/-!
# The staged records of an extreme-angle schedule are almost surely Borel functions of the field (R48-safe)

Packet PROVE-STAGED5 (Theorem 1.2's Proposition 5.9; PROVE-CROSSCOND-STAGED4 §5.1, the gate of S2 on the glued space).
The stage iteration of marked locality (`WalkLaw.isHistoryAvoidanceLocal_of_stages`) and the path route
(`Sec6.isHistoryAvoidanceLocal_explored`, `SewGerm.isHistoryAvoidanceLocal_stage_of_path`) both need that the retained
past of the staged prefix is almost surely a Borel function of the field. For a general staged history this is the
source's induction with Theorems 1.2–1.3 at each stage (`Theorem14.StagedDet.exists_pastMap_eq_comp_field`), which
Theorem 1.2's own inputs may not use (ruling R48). Proposition 5.9's pieces are flow lines at the **extreme angles**
`±π/2` from a root word with the extreme heights, and for those the §4.2 determination applies at every stage
(`Prop513Schedule.ae_schedule_drivers`: every piece is `codeDriver … (h ω)`, from
`AdmCode.Theorem12ParamCond44Statement`, the approved restricted §4.2 input). Here:

* `run_congr_of_lt_length`, `pastMap_eq_of_lt_length`: the retained past before `k` only reads the drivers of the
  instructions of the program before `k` (the instructions past the end of the program do nothing);
* **`codePast`**, `measurable_codePast`: the Borel map field ↦ retained past of the schedule (the retained past of the
  code drivers `codeDriver … f`);
* **`ae_pastMap_eq_codePast`**: almost surely the retained past before every `k` is `codePast k (h ω)`;
  `exists_pastMap_eq_comp_field_schedule`, **`pastSigma_le_aeSigma_schedule`** (the input `hdet` of the stage
  iteration, for the centred field);
* **`frozenPath_determined_of_schedule`**, **`isHistoryAvoidanceLocal_stage_of_path_schedule`**,
  **`isEntranceHistoryLocal_staged_of_pathRecords_schedule`**: the R48-safe forms of PROVE-T14-SB4's path-route
  results (`SewGerm.frozenPath_determined_of_staged`, `…isHistoryAvoidanceLocal_stage_of_path`,
  `…isEntranceHistoryLocal_staged_of_pathRecords`, which take `Theorem12ParamStatement` and Theorem 1.3), for the staged
  histories of extreme-angle schedules.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result; the
only named input is `AdmCode.Theorem12ParamCond44Statement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u v

namespace InteractingSLE.Sec5.CrossCond.StagedGlue

open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule
open Restart (BoundaryWord)
open Restart.StagedEntrance (frozenPath)
open Theorem14.SB.SewGerm (frozenHistory)

/-! ### The retained past only reads the drivers of the program -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The state after `k` instructions only reads the drivers of the program's instructions before `k`**: past the
end of the program a step does nothing. -/
theorem run_congr_of_lt_length (spec : ExplSpec) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (h : ∀ j < k, j < spec.2.2.length → D j = D' j) :
    ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run_succ, run_succ, ih fun j hj hl => h j (Nat.lt_succ_of_lt hj) hl]
    cases hk : spec.2.2[k]? with
    | none => rfl
    | some a =>
      exact step_congr _ _ _ (h k (Nat.lt_succ_self k) (List.getElem?_eq_some_iff.1 hk).1)

/-- **The retained past before `k` only reads the drivers of the program's instructions before `k`.** -/
theorem pastMap_eq_of_lt_length (spec : ExplSpec) {Ω : Type u} {Ω' : Type v}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {E' : ℕ → Ω' → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {ω : Ω} {ω' : Ω'}
    (h : ∀ j < k, j < spec.2.2.length → E j ω = E' j ω') :
    pastMap κ b jumps spec E k ω = pastMap κ b jumps spec E' k ω' := by
  unfold pastMap
  rw [run_congr_of_lt_length spec (D := fun j => E j ω) (D' := fun j => E' j ω') h]

end Run

/-! ### The retained past of an extreme-angle schedule as a Borel function of the field -/

section Code

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

/-- **The field-to-past map of an extreme-angle schedule**: the retained past before `k` of the code drivers
`codeDriver … j f` (the §4.2 determination maps of the successive stage words, read on the field `f`). -/
def codePast (c : BoundaryWord) (s : Schedule) (k : ℕ) : DistOn upperHalfPlaneOpens → PastData k :=
  pastMap κ c.fn c.jumps (scheduleSpec s) (fun j f => codeDriver h44 hκ hκ4 c (scheduleSpec s) j f) k

theorem measurable_codePast (c : BoundaryWord) (s : Schedule) (k : ℕ) :
    Measurable (codePast h44 hκ hκ4 c s k) :=
  measurable_pastMap runMeasStatement c.isPiecewiseConstantBoundaryData (scheduleSpec s)
    (E := fun j f => codeDriver h44 hκ hκ4 c (scheduleSpec s) j f) (k := k)
    (fun j _ => measurable_codeDriver h44 hκ hκ4 c _ j)
    (fun j _ f => codeDriver_regular h44 hκ hκ4 c _ j f) k le_rfl

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h44 hκ hκ4

/-- **Almost surely the retained past of an extreme-angle schedule is `codePast` of the field**, before every
instruction count simultaneously (R48-safe: `Prop513Schedule.ae_schedule_drivers`). -/
theorem ae_pastMap_eq_codePast (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, ∀ k, pastMap κ c.fn c.jumps (scheduleSpec s) E k ω = codePast h44 hκ hκ4 c s k (h ω) := by
  filter_upwards [ae_schedule_drivers h44 hκ hκ4 c hc hh s hE hr] with ω hω k
  exact pastMap_eq_of_lt_length _ fun j _ hj => (hω j hj).2

/-- **The retained past of an extreme-angle schedule is almost surely a Borel function of the field** (the R48-safe
form of `Theorem14.StagedDet.exists_pastMap_eq_comp_field` for these schedules). -/
theorem exists_pastMap_eq_comp_field_schedule (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ f : DistOn upperHalfPlaneOpens → PastData k, Measurable f ∧
      pastMap κ c.fn c.jumps (scheduleSpec s) E k =ᵐ[P] f ∘ h :=
  ⟨codePast h44 hκ hκ4 c s k, measurable_codePast h44 hκ hκ4 c s k,
    (ae_pastMap_eq_codePast h44 hκ hκ4 c hc hh s hE hr).mono fun _ hω => hω k⟩

/-- **The retained past is, up to null sets, an event family of the centred field** (the input `hdet` of
`WalkLaw.isHistoryAvoidanceLocal_of_stages`, R48-safe for extreme-angle schedules). -/
theorem pastSigma_le_aeSigma_schedule (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω))
    (u₀ : ℂ → ℝ) (k : ℕ) :
    _root_.InteractingSLE.pastSigma κ c.fn c.jumps (scheduleSpec s) E k ≤
      LocalSets.aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P :=
  Theorem14.WalkLaw.pastSigma_le_aeSigma_centred (measurable_codePast h44 hκ hκ4 c s k)
    ((ae_pastMap_eq_codePast h44 hκ hκ4 c hc hh s hE hr).mono fun _ hω => hω k) u₀

/-- **The launched pieces are almost surely Borel functions of the field** (with infinite lifetime): the records of
the schedule's pieces are `codeDriver … (h ω)`. Restatement of `Prop513Schedule.ae_schedule_drivers`. -/
theorem ae_drivers_eq_codeDriver (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤ ∧
      E j ω = codeDriver h44 hκ hκ4 c (scheduleSpec s) j (h ω) :=
  ae_schedule_drivers h44 hκ hκ4 c hc hh s hE hr

end Code

/-! ### The path route, R48-safe for extreme-angle schedules -/

section Path

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h44 hκ hκ4

/-- **A continuous parametrization reconstructed from the staged record of an extreme-angle schedule is determined by
the centred field** (R48-safe form of `SewGerm.frozenPath_determined_of_staged`). -/
theorem frozenPath_determined_of_schedule (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω))
    (u₀ : ℂ → ℝ) {k : ℕ} {α : Ω → ℝ≥0 → ℂ} {T : ℝ≥0} {r : ℝ≥0 → PastData k → ℂ}
    (hrm : ∀ t, Measurable (r t))
    (hrr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) T t) =ᵐ[P]
      fun ω => r t (pastMap κ c.fn c.jumps (scheduleSpec s) E k ω)) (t : ℝ≥0) :
    ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => frozenPath (α ω) T t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω) := by
  refine ⟨fun X => r t (codePast h44 hκ hκ4 c s k (X + SupercriticalConformalCovariance.GM24.smoothDist
    upperHalfPlaneOpens u₀)), (hrm t).comp
      ((measurable_codePast h44 hκ hκ4 c s k).comp (Coupling.measurable_add_distOnConst _)), ?_⟩
  filter_upwards [hrr t, ae_pastMap_eq_codePast h44 hκ hκ4 c hc hh s hE hr] with ω hrω hfω
  simp only [hrω, hfω, WholeField.centredField, sub_add_cancel]

/-- **The staged prefix of an extreme-angle schedule is a marked local set, from a continuous retained path and its
entrance-history locality** (R48-safe form of `SewGerm.isHistoryAvoidanceLocal_stage_of_path`): if `α` is a
continuous path (from a fixed point, measurable at fixed times) whose stopped path at `T` is reconstructed by a Borel
map `r` from the retained past and conversely (`ψ`), whose range through `T` in `ℍ` is the explored set, and which is
entrance-history local for the centred field, then the explored set is history-avoidance local for the retained past
`pastSigma k`. -/
theorem isHistoryAvoidanceLocal_stage_of_path_schedule (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω))
    (u₀ : ℂ → ℝ) {k : ℕ} {α : Ω → ℝ≥0 → ℂ} {T : ℝ≥0} {r : ℝ≥0 → PastData k → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) {x : ℂ} (hα0 : ∀ ω, α ω 0 = x)
    (hαm : ∀ t, Measurable fun ω => α ω t) (hrm : ∀ t, Measurable (r t))
    (hrr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) T t) =ᵐ[P]
      fun ω => r t (pastMap κ c.fn c.jumps (scheduleSpec s) E k ω))
    {ψ : (Fin 1 → Sec6.Hist) → PastData k} (hψ : Measurable ψ)
    (hrec : pastMap κ c.fn c.jumps (scheduleSpec s) E k =ᵐ[P] fun ω => ψ (frozenHistory α T ω))
    (hset : ∀ᵐ ω ∂P, α ω '' Icc 0 T ∩ H = Theorem14.WalkLaw.stageSet κ c.fn c.jumps (scheduleSpec s) E k ω)
    (hentr : Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (α ω) T) (WholeField.centredField h u₀) P) :
    WholeField.IsHistoryAvoidanceLocal (_root_.InteractingSLE.pastSigma κ c.fn c.jumps (scheduleSpec s) E k)
      (Theorem14.WalkLaw.stageSet κ c.fn c.jumps (scheduleSpec s) E k) (WholeField.centredField h u₀) P := by
  have hdet := frozenPath_determined_of_schedule h44 hκ hκ4 c hc hh s hE hr u₀ hrm hrr
  have hp := Sec6.isHistoryAvoidanceLocal_explored
    (η := fun _ : Fin 1 => fun ω => frozenPath (α ω) T) (x := fun _ => x)
    (τ := fun _ _ => (T : ℝ≥0∞)) (S := fun _ _ _ => (T : ℝ≥0∞))
    (WholeField.measurable_centredField hh.1 u₀)
    (fun _ ω => Restart.StagedEntrance.continuous_frozenPath (hαc ω))
    (fun _ ω => by rw [Restart.StagedEntrance.frozenPath_zero]; exact hα0 ω)
    (fun _ t => hαm _) (fun _ => hdet) (fun _ => hentr)
    (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
  rw [show Sec6.explored (fun _ : Fin 1 => fun ω => frozenPath (α ω) T)
    (fun _ _ => (T : ℝ≥0∞)) = fun ω => α ω '' Icc 0 T ∩ H from
      funext Restart.StagedEntrance.explored_frozenPath] at hp
  have hle := KernelTower.comap_le_aeSigma_comap hψ hrec
  exact Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae hset
    (Sec7.StripMark.isHistoryAvoidanceLocal_of_ae_le hp fun F hF => hle F hF)

/-- **The restart step for a piece of an extreme-angle schedule** (R48-safe form of
`SewGerm.isEntranceHistoryLocal_staged_of_pathRecords`): the landed staged restart
(`Restart.StagedEntrance.Staged.isEntranceHistoryLocal_frozenPath_staged`) with the past determination from the §4.2
codes, the kernel identity from the two record reconstructions, and the frontier from the chart domain. -/
theorem isEntranceHistoryLocal_staged_of_pathRecords_schedule (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀) (k : ℕ) (θ : ℝ)
    {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hxH : x ∉ H) (hαc : ∀ ω, Continuous (α ω))
    (hα0 : ∀ ω, α ω 0 = x) (hαm : ∀ t, Measurable fun ω => α ω t)
    {q₀ : ℚ≥0} (m : ℝ≥0) {r : ℝ≥0 → PastData k → ℂ}
    (hrm : ∀ t, Measurable (r t))
    (hrr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) q₀ t) =ᵐ[P]
      fun ω => r t (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω))
    {ψ : (Fin 1 → Sec6.Hist) → PastData k} (hψ : Measurable ψ)
    (hrec : pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k =ᵐ[P] fun ω => ψ (frozenHistory α q₀ ω))
    (hloc₀ : Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (α ω) q₀) (WholeField.centredField h u₀) P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hℓ : ∀ ω, LocallyIntegrableOn (fun w => (c ω).2.2 ((c ω).2.1 w)) H)
    (hlaunch : ∀ᵐ ω ∂P, (ExplState.run κ c₀.fn c₀.jumps (scheduleSpec s) (fun j => E j ω) (k + 1)).2.2.2.1 k =
      some (c ω, θ))
    (hfr : ∀ ω, ∀ z ∈ H, z ∈ closure ((c ω).dom : Set ℂ) → z ∉ (c ω).dom → z ∈ α ω '' Icc 0 (q₀ : ℝ≥0))
    {β ηc : Ω → ℝ≥0 → ℂ} (hηc : ∀ ω, Continuous (ηc ω))
    (hηm : ∀ t, Measurable fun ω => ηc ω t) (hη0 : ∀ ω, ηc ω 0 = 0)
    (htrβ : ∀ᵐ ω ∂P, IsGeneratingTrace (E k ω).1 (E k ω).2 (β ω))
    (hηβ : ∀ᵐ ω ∂P, ∀ t, ηc ω t = β ω (Restart.capTime m (E k ω).2 t))
    (hdetη : ∀ᵐ ω₀ ∂P, ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ηc ω t) =ᵐ[condExpKernel P (Restart.StagedEntrance.pastSigma α q₀) ω₀]
        fun ω => f (Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω)))
    (hcat : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → ηc ω s ∈ H ∧
      frozenPath (α ω) ((q₀ : ℝ≥0) + m) ((q₀ : ℝ≥0) + s) = (c ω).2.1 (ηc ω s)) :
    Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (α ω) ((q₀ : ℝ≥0) + m))
      (WholeField.centredField h u₀) P := by
  have hdet₀ := frozenPath_determined_of_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hreg u₀ hrm hrr
  have hK := Theorem14.SB.SewGerm.ae_condExpKernel_stage_eq_path hE hαm hrm hrr hψ hrec
  exact Restart.StagedEntrance.Staged.isEntranceHistoryLocal_frozenPath_staged hκ hκ4 hh hu₀
    hE hreg k θ hxH hαc hα0 hαm m hdet₀ hloc₀ hK hc hℓ hlaunch hfr
    hηc hηm hη0 htrβ hηβ hdetη hcat

end Path

end InteractingSLE.Sec5.CrossCond.StagedGlue
