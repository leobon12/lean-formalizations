/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TipSystemWire
import InteractingSLE.Spec.Supplement.GW2JointKernelProof

/-!
# GW2's concrete schedules and their stage-start σ-algebras

Packet PROVE-GW2-SCHED. In GW2's stage experiment (follow-up note A.2–A.5,
`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L80–L241; GB9, `source/spec/p481-528.md` L1082–L1100) every
stage starts from a **fixed** finite schedule: an initial entry `(θ₀, q₀)` from a root and later entries `(θ, q)`
with angles in `Θ` and times in `Q` (A.5: "Every successful finite history uses only `Θ` and `Q`"). The schedule's
pieces are the canonical pieces of the field (`GW2Tip.canonSpecFam`), and "Work conditionally on each of these ordinary
retained histories. No first successful future prefix is added to the conditioning data."

This file fixes the stage-start information of a schedule as PROVE-T14-TIP12 §4.1 designs it: the counterflow record
at the stop `s` (the σ-algebra of GW2's joint kernel, `GW2JointKernel.exists_jointKernel_r1`) together with the
records of the canonical pieces **stopped at their switching times** (`GW2Schedule.canonRec`). (Conditioning on the
full drivers would reveal the last piece's continuation beyond its switch — a flow line of the remaining field — and
change the next stage's conditional law.)

* `schedOf`, `schedSpec`: the frozen schedule `(θ₀, q₀) :: xs.reverse` of a SchedRule schedule `xs` (latest first),
  its history; `schedOf_cons`: an extension appends one entry;
* `scheduleProgram_getElem?_append`, `specAngle_schedSpec_append`, `specDelta_schedSpec_append`: appending an entry does
  not change the earlier instructions;
* `canonState_congr₂`, `canonRec_congr₂`: the canonical state and stopped records only depend on the earlier angles
  and own times;
* `cfRec`, `stopRec`, `stageMap`, **`stageSigma`**: the stage-start record and σ-algebra;
* **`stageSigma_le`**, **`stageSigma_mono`**: it is a sub-σ-algebra, increasing along extensions (the fields `h𝒢`
  and `h𝒢mono` of `GW2TipSystem.SchedRule.IsValid`);
* `isSchedule_schedOf`: the frozen schedule is a `Θ`-schedule with times in `Q` when its times increase.
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

/-! ### The frozen schedule of a SchedRule schedule -/

/-- The frozen schedule of an initial entry `e₀` and later entries `xs`, the latest first. -/
def schedOf (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) : List (ℝ × ℝ≥0) := e₀ :: xs.reverse

@[simp] theorem schedOf_nil (e₀ : ℝ × ℝ≥0) : schedOf e₀ [] = [e₀] := rfl

theorem schedOf_cons (e₀ x : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) : schedOf e₀ (x :: xs) = schedOf e₀ xs ++ [x] := by
  simp [schedOf]

@[simp] theorem length_schedOf (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) :
    (schedOf e₀ xs).length = xs.length + 1 := by
  simp [schedOf]

/-- The history of the frozen schedule `l` from the root `x` (a GW2 history). -/
def schedSpec (x : ℝ) (l : List (ℝ × ℝ≥0)) : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩

theorem schedAngle_append {l : List (ℝ × ℝ≥0)} (y : ℝ × ℝ≥0) {j : ℕ} (hj : j < l.length) :
    schedAngle (l ++ [y]) j = schedAngle l j := by
  simp only [schedAngle, List.getD_append _ _ _ _ hj]

theorem schedTime_append (τ₀ : ℝ≥0) {l : List (ℝ × ℝ≥0)} (y : ℝ × ℝ≥0) {j : ℕ} (hj : j ≤ l.length) :
    schedTime τ₀ (l ++ [y]) j = schedTime τ₀ l j := by
  rcases j with _ | j
  · rfl
  · simp only [schedTime, List.getD_append _ _ _ _ (Nat.lt_of_succ_le hj)]

theorem schedDelta_append (τ₀ : ℝ≥0) {l : List (ℝ × ℝ≥0)} (y : ℝ × ℝ≥0) {j : ℕ} (hj : j < l.length) :
    schedDelta τ₀ (l ++ [y]) j = schedDelta τ₀ l j := by
  simp only [schedDelta, List.getD_append _ _ _ _ hj, schedTime_append τ₀ y hj.le]

/-- **Appending an entry does not change the earlier instructions.** -/
theorem scheduleProgram_getElem?_append (τ₀ : ℝ≥0) {l : List (ℝ × ℝ≥0)} (y : ℝ × ℝ≥0) {j : ℕ}
    (hj : j < l.length) : (scheduleProgram τ₀ (l ++ [y]))[j]? = (scheduleProgram τ₀ l)[j]? := by
  have h1 := isFlowProg_scheduleProgram τ₀ (l ++ [y]) j
    (by rw [length_scheduleProgram, List.length_append]; omega)
  have h2 := isFlowProg_scheduleProgram τ₀ l j (by rw [length_scheduleProgram]; exact hj)
  rw [h1, h2, schedAngle_append y hj, schedDelta_append τ₀ y hj]

theorem specAngle_schedSpec_append (x : ℝ) {l : List (ℝ × ℝ≥0)} (y : ℝ × ℝ≥0) {j : ℕ} (hj : j < l.length) :
    specAngle (schedSpec x (l ++ [y])) j = specAngle (schedSpec x l) j := by
  have e := scheduleProgram_getElem?_append 0 y hj
  simp only [specAngle, instrAngle, schedSpec] at e ⊢
  rw [e]

theorem instrTime_schedSpec_append (x : ℝ) {l : List (ℝ × ℝ≥0)} (y : ℝ × ℝ≥0) {j : ℕ} (hj : j < l.length) :
    instrTime (schedSpec x (l ++ [y])) j = instrTime (schedSpec x l) j := by
  have e := scheduleProgram_getElem?_append 0 y hj
  simp only [instrTime, schedSpec] at e ⊢
  rw [e]

theorem specDelta_schedSpec_append (x : ℝ) {l : List (ℝ × ℝ≥0)} (y : ℝ × ℝ≥0) {j : ℕ} (hj : j < l.length) :
    specDelta (schedSpec x (l ++ [y])) j = specDelta (schedSpec x l) j := by
  simp only [specDelta, instrTime_schedSpec_append x y hj]

/-- The frozen schedule is a `Θ`-schedule with times in `Q` when its entries are in `Θ × Q` and its times
increase. -/
theorem isSchedule_schedOf {Θ : Set ℝ} {Q : Set ℝ≥0} {e₀ : ℝ × ℝ≥0} {xs : List (ℝ × ℝ≥0)}
    (hmem : ∀ p ∈ schedOf e₀ xs, p.1 ∈ Θ ∧ p.2 ∈ Q)
    (hinc : (schedOf e₀ xs).Pairwise (fun p q => p.2 < q.2)) : IsSchedule Θ Q (schedOf e₀ xs) :=
  ⟨hmem, hinc⟩

/-! ### The canonical state depends only on the earlier angles and own times -/

section Canon

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (c₀ : BoundaryWord) (x₀ : ℝ)

/-- **The canonical state before instruction `k` only depends on the earlier angles and own times.** -/
theorem canonState_congr₂ {θ θ' : ℕ → ℝ} {Δ Δ' : ℕ → ℝ≥0∞} (f : DistOn upperHalfPlaneOpens) :
    ∀ {k : ℕ}, (∀ j < k, θ j = θ' j) → (∀ j < k, Δ j = Δ' j) →
      canonState hκ h12p βA c₀ x₀ θ Δ f k = canonState hκ h12p βA c₀ x₀ θ' Δ' f k
  | 0, _, _ => rfl
  | k + 1, hθ, hΔ => by
    have ih := canonState_congr₂ (θ := θ) (θ' := θ') (Δ := Δ) (Δ' := Δ') f
      (fun j hj => hθ j (Nat.lt_succ_of_lt hj)) (fun j hj => hΔ j (Nat.lt_succ_of_lt hj))
    change canonStep hκ h12p βA (θ k) (Δ k) _ = canonStep hκ h12p βA (θ' k) (Δ' k) _
    rw [ih, hθ k (Nat.lt_succ_self k), hΔ k (Nat.lt_succ_self k)]

/-- **The stopped record of the canonical `k`-th piece only depends on the angles and own times up to `k`.** -/
theorem canonRec_congr₂ {θ θ' : ℕ → ℝ} {Δ Δ' : ℕ → ℝ≥0∞} (f : DistOn upperHalfPlaneOpens) {k : ℕ}
    (hθ : ∀ j ≤ k, θ j = θ' j) (hΔ : ∀ j ≤ k, Δ j = Δ' j) :
    canonRec hκ h12p βA c₀ x₀ θ Δ f k = canonRec hκ h12p βA c₀ x₀ θ' Δ' f k := by
  have hs := canonState_congr₂ hκ h12p βA c₀ x₀ f (k := k) (fun j hj => hθ j hj.le) (fun j hj => hΔ j hj.le)
  simp only [canonRec, canonDrive, hs, hθ k le_rfl, hΔ k le_rfl]

end Canon
/-! ### The stage-start records and σ-algebras -/

section Sigma

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (c₀ : BoundaryWord) {Ω : Type u} [mΩ : MeasurableSpace Ω] (h : Ω → DistOn upperHalfPlaneOpens)

/-- The record of the counterflow at the stop `s` (the regularized driver read at rational times; the record of GW2's
joint kernel, `GW2JointKernel.exists_jointKernel_r1`). -/
def cfRec (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (ω : Ω) : RecData :=
  recOf (s : ℝ≥0∞) (GW2JointKernel.cfE s W' ζ' ω)

/-- The record of the canonical `j`-th piece of the history `spec`, **stopped at its switching time**
(`GW2Schedule.canonRec`). -/
def stopRec (spec : ExplSpec) (j : ℕ) (ω : Ω) : RecData :=
  canonRec hκ h12p βA c₀ spec.1 (specAngle spec) (specDelta spec) (h ω) j

/-- The stage-start record of the first `n` pieces of `spec`: the counterflow record at `s` and the stopped records. -/
def stageMap (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ) (ω : Ω) :
    RecData × (Fin n → RecData) :=
  (cfRec s W' ζ' ω, fun j => stopRec hκ h12p βA c₀ h spec j ω)

/-- **The stage-start σ-algebra** of the first `n` pieces of `spec` at the counterflow stop `s`. -/
@[instance_reducible]
def stageSigma (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (stageMap hκ h12p βA c₀ h s W' ζ' spec n) inferInstance

variable {hκ h12p βA c₀ h}

/-- The counterflow record at `s` is measurable. -/
theorem measurable_cfRec {P : Measure Ω} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (s : ℝ≥0) : Measurable (cfRec s W' ζ') := by
  obtain ⟨_b', _J', _h', _hb', _hT, hfl⟩ := hcf
  obtain ⟨_h'', _𝓕, _VL, _VR, _B, _htr', hC⟩ := hfl
  have hWa := hC.1.2.1
  have hζm : Measurable ζ' := Sec2.Assembly.measurable_lifetime hWa
  have hKm : ∀ t, Measurable (GW2JointKernel.cfKW W' ζ' t) := fun t =>
    Restart.measurable_ite_of_adaptedBefore hWa t
  have hEm : Measurable (GW2JointKernel.cfE s W' ζ') :=
    (StagedReg.measurable_regularize _).comp ((measurable_pi_iff.2 hKm).prodMk hζm)
  exact measurable_recOf hEm (fun ω => StagedReg.isRegularDriver_regularize _ _) _

/-- The stopped canonical records are measurable. -/
theorem measurable_stopRec (hβA : Measurable βA) (hh : Measurable h) (spec : ExplSpec) (j : ℕ) :
    Measurable (stopRec hκ h12p βA c₀ h spec j) :=
  measurable_comp_const_left (F := fun Δ' f => canonRec hκ h12p βA c₀ spec.1 (specAngle spec) Δ' f j)
    (measurable_canonRec hκ h12p βA c₀ spec.1 (specAngle spec) hβA j) (specDelta spec) hh

/-- **The stage-start σ-algebra is a sub-σ-algebra** (field `h𝒢` of `SchedRule.IsValid`). -/
theorem stageSigma_le (hβA : Measurable βA) (hh : Measurable h) {P : Measure Ω} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (s : ℝ≥0) (spec : ExplSpec) (n : ℕ) :
    stageSigma hκ h12p βA c₀ h s W' ζ' spec n ≤ mΩ := by
  have hm : Measurable (stageMap hκ h12p βA c₀ h s W' ζ' spec n) :=
    (measurable_cfRec hcf s).prodMk (measurable_pi_iff.2 fun j =>
      measurable_stopRec (hκ := hκ) (h12p := h12p) (c₀ := c₀) hβA hh spec (j : ℕ))
  exact hm.comap_le

omit mΩ in
/-- **The stage-start σ-algebra increases along an extension** whose first `n` instructions have the same angles and
own times and whose root is the same (field `h𝒢mono` of `SchedRule.IsValid`). -/
theorem stageSigma_mono (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {spec spec' : ExplSpec} {n : ℕ}
    (hroot : spec'.1 = spec.1) (hθ : ∀ j < n, specAngle spec' j = specAngle spec j)
    (hΔ : ∀ j < n, specDelta spec' j = specDelta spec j) :
    stageSigma hκ h12p βA c₀ h s W' ζ' spec n ≤ stageSigma hκ h12p βA c₀ h s W' ζ' spec' (n + 1) := by
  have hrec : ∀ (j : ℕ), j < n → ∀ ω, stopRec hκ h12p βA c₀ h spec' j ω = stopRec hκ h12p βA c₀ h spec j ω := by
    intro j hj ω
    simp only [stopRec, hroot]
    exact canonRec_congr₂ hκ h12p βA c₀ spec.1 (h ω) (fun i hi => hθ i (lt_of_le_of_lt hi hj))
      (fun i hi => hΔ i (lt_of_le_of_lt hi hj))
  have hfac : stageMap hκ h12p βA c₀ h s W' ζ' spec n =
      (fun p : RecData × (Fin (n + 1) → RecData) => (p.1, fun j : Fin n => p.2 (Fin.castSucc j))) ∘
        stageMap hκ h12p βA c₀ h s W' ζ' spec' (n + 1) := by
    funext ω
    simp only [stageMap, Function.comp_apply, Fin.val_castSucc]
    refine Prod.ext rfl (funext fun j => ?_)
    exact (hrec j j.2 ω).symm
  have hg : Measurable (fun p : RecData × (Fin (n + 1) → RecData) => (p.1, fun j : Fin n => p.2 (Fin.castSucc j))) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun j => (measurable_pi_apply _).comp measurable_snd)
  unfold stageSigma
  rw [hfac, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

omit mΩ in
/-- **The stage-start σ-algebras of a schedule and of its extension by one entry** (same root): the frozen schedule
of the extension appends the entry. -/
theorem stageSigma_schedOf_mono (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (x : ℝ) (e₀ y : ℝ × ℝ≥0)
    (xs : List (ℝ × ℝ≥0)) :
    stageSigma hκ h12p βA c₀ h s W' ζ' (schedSpec x (schedOf e₀ xs)) (xs.length + 1) ≤
      stageSigma hκ h12p βA c₀ h s W' ζ' (schedSpec x (schedOf e₀ (y :: xs))) ((y :: xs).length + 1) := by
  rw [List.length_cons, schedOf_cons]
  refine stageSigma_mono s W' ζ' rfl (fun j hj => ?_) (fun j hj => ?_)
  · exact specAngle_schedSpec_append x y (by rw [length_schedOf]; exact hj)
  · exact specDelta_schedSpec_append x y (by rw [length_schedOf]; exact hj)

end Sigma

end GW2TipSystem

end Theorem14

end InteractingSLE
