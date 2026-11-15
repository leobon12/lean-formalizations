/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField8Local
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Coupling.Assembly11Drv
import InteractingSLE.Spec.Restart.R1Flow

/-!
# The trace is read off the driving filtration; observables at deterministic times below a stop

Packet PROVE-WHOLEFIELD8, the stopping-time part of the reduction of Aux. lemma 56 at first entrance times
(`Restart.RetainedRangeEntranceStatement`) to the retained-range kernels.

* `measurableSet_le_inter`, `measurable_ite_le`: an observable of `𝓕_s` restricted to `{s ≤ τ}` is an observable of
  `𝓕_τ`; `measurable_ite_exists_le`: along a nondecreasing sequence of stops, restricted to `{∃ n, s ≤ τₙ}`, it is an
  observable of `⋁ₙ 𝓕_{τₙ}`.
* `stopW`, `traceVal`: the killed driving path frozen after `s`, and the trace value `x + traceAt s (stopW s)`,
  which is `𝓕_s`-measurable (`measurable_traceVal`) and is the trace point `η(s)` for `s < ζ`
  (`traceVal_eq`).
* `measurable_aeSigma_of_ae_eq'`: a random variable almost surely equal to an `𝒦`-measurable one is measurable for the
  σ-algebra of events almost surely equal to events of `𝒦`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets

/-! ### Observables at deterministic times below a stop -/

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **An event of `𝓕_s` restricted to `{s ≤ τ}` is an event of `𝓕_τ`.** -/
theorem measurableSet_le_inter {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0)) {s : ℝ≥0}
    {B : Set Ω} (hB : MeasurableSet[𝓕 s] B) : MeasurableSet[hτ.measurableSpace] ({ω | s ≤ τ ω} ∩ B) := by
  have hlt : MeasurableSet[𝓕 s] {ω | τ ω < s} := by
    have := hτ.measurableSet_lt s
    simpa only [WithTop.coe_lt_coe] using this
  rw [hτ.measurableSet]
  refine ⟨?_, fun t => ?_⟩
  · have e : {ω | s ≤ τ ω} = {ω | τ ω < s}ᶜ := by ext ω; simp [not_lt]
    rw [e]
    exact (le_iSup (fun t => (𝓕 t : MeasurableSpace Ω)) s _ hlt).compl.inter
      (le_iSup (fun t => (𝓕 t : MeasurableSpace Ω)) s _ hB)
  by_cases hst : s ≤ t
  · have hle : MeasurableSet[𝓕 t] {ω | (τ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := hτ t
    have e : {ω | s ≤ τ ω} ∩ B ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
        ({ω | τ ω < s}ᶜ ∩ B) ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
      ext ω; simp [not_lt]
    rw [e]
    exact ((𝓕.mono hst _ hlt).compl.inter (𝓕.mono hst _ hB)).inter hle
  · have e : {ω | s ≤ τ ω} ∩ B ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe, mem_empty_iff_false, iff_false, not_and]
      exact fun h1 h2 => hst (h1.1.trans h2)
    rw [e]
    exact @MeasurableSet.empty _ (𝓕 t)

/-- **An observable of `𝓕_s` restricted to `{s ≤ τ}` is an observable of `𝓕_τ`.** -/
theorem measurable_ite_le {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0)) {s : ℝ≥0}
    {X : Ω → ℂ} (hX : Measurable[𝓕 s] X) :
    Measurable[hτ.measurableSpace] fun ω => if s ≤ τ ω then X ω else 0 := by
  classical
  intro B hB
  have e : (fun ω => if s ≤ τ ω then X ω else 0) ⁻¹' B =
      ({ω | s ≤ τ ω} ∩ X ⁻¹' B) ∪ (if (0 : ℂ) ∈ B then {ω | s ≤ τ ω}ᶜ else ∅) := by
    ext ω
    by_cases h1 : s ≤ τ ω <;> by_cases h0 : (0 : ℂ) ∈ B <;> simp [h1, h0]
  rw [e]
  refine (measurableSet_le_inter hτ (hX hB)).union ?_
  split_ifs
  · have := measurableSet_le_inter hτ (B := univ) (@MeasurableSet.univ _ (𝓕 s))
    rw [inter_univ] at this
    exact this.compl
  · exact @MeasurableSet.empty _ hτ.measurableSpace

/-- The events `{s ≤ τₙ}` are events of the join of the stopped σ-algebras. -/
theorem measurableSet_exists_le {τ : ℕ → Ω → ℝ≥0} (hτ : ∀ n, IsStoppingTime 𝓕 fun ω => (τ n ω : WithTop ℝ≥0))
    (s : ℝ≥0) : MeasurableSet[⨆ n, (hτ n).measurableSpace] {ω | ∃ n, s ≤ τ n ω} := by
  have e : {ω | ∃ n, s ≤ τ n ω} = ⋃ n, ({ω | s ≤ τ n ω} ∩ univ) := by ext ω; simp
  rw [e]
  refine MeasurableSet.iUnion fun n => ?_
  exact (le_iSup (fun n => (hτ n).measurableSpace) n) _
    (measurableSet_le_inter (hτ n) (@MeasurableSet.univ _ (𝓕 s)))

open scoped Classical in
/-- **Along a nondecreasing sequence of stops, an observable of `𝓕_s` restricted to `{∃ n, s ≤ τₙ}` is an observable
of `⋁ₙ 𝓕_{τₙ}`** (the pointwise limit of the restrictions to `{s ≤ τₙ}`). -/
theorem measurable_ite_exists_le {τ : ℕ → Ω → ℝ≥0} (hτ : ∀ n, IsStoppingTime 𝓕 fun ω => (τ n ω : WithTop ℝ≥0))
    (hmono : ∀ ω, Monotone fun n => τ n ω) {s : ℝ≥0} {X : Ω → ℂ} (hX : Measurable[𝓕 s] X) :
    Measurable[⨆ n, (hτ n).measurableSpace] fun ω => if ∃ n, s ≤ τ n ω then X ω else 0 := by
  refine @measurable_of_tendsto_metrizable Ω ℂ (⨆ n, (hτ n).measurableSpace) _ _ _ _
    (fun n ω => if s ≤ τ n ω then X ω else 0) _ (fun n => ?_) ?_
  · exact (measurable_ite_le (hτ n) hX).mono (le_iSup (fun n => (hτ n).measurableSpace) n) le_rfl
  · rw [tendsto_pi_nhds]
    intro ω
    by_cases h : ∃ n, s ≤ τ n ω
    · obtain ⟨n₀, hn₀⟩ := h
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n₀] with n hn
      show (if ∃ n, s ≤ τ n ω then X ω else 0) = if s ≤ τ n ω then X ω else 0
      rw [ite_eq_left (hn₀.trans (hmono ω hn)), ite_eq_left ⟨n₀, hn₀⟩]
    · push Not at h
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      show (if ∃ n, s ≤ τ n ω then X ω else 0) = if s ≤ τ n ω then X ω else 0
      rw [ite_eq_right (not_le.2 (h n)), ite_eq_right (by push Not; exact h)]

end Stop

/-! ### Almost-sure versions -/

section AeVersion

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A random variable almost surely equal to an `𝒦`-measurable one is measurable for `aeSigma 𝒦 P`. -/
theorem measurable_aeSigma_of_ae_eq' {β : Type*} [MeasurableSpace β] {𝒦 : MeasurableSpace Ω} {Y Z : Ω → β}
    (hZ : Measurable[𝒦] Z) (hYZ : Y =ᵐ[P] Z) : Measurable[aeSigma 𝒦 P] Y := by
  intro B hB
  refine ⟨Z ⁻¹' B, hZ hB, ?_⟩
  filter_upwards [hYZ] with ω hω
  simp only [mem_preimage, hω]

end AeVersion

/-! ### The trace value at a deterministic time is an observable of the driving filtration -/

section TraceVal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The killed driving path frozen after `s`: `W(r ∧ s)` while `r ∧ s < ζ`, and `0` otherwise. -/
def stopW (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (ω : Ω) : ℝ≥0 → ℝ :=
  fun r => if ((min r s : ℝ≥0) : ℝ≥0∞) < ζ ω then W (min r s) ω else 0

theorem measurable_killedVal (hW : AdaptedBefore 𝓕 ζ W) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => if (t : ℝ≥0∞) < ζ ω then W t ω else 0 := by
  classical
  intro A hA
  have e : (fun ω => if (t : ℝ≥0∞) < ζ ω then W t ω else 0) ⁻¹' A =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω ∈ A} ∪
        (if (0 : ℝ) ∈ A then {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω ∈ univ}ᶜ else ∅) := by
    ext ω
    by_cases h1 : (t : ℝ≥0∞) < ζ ω <;> by_cases h0 : (0 : ℝ) ∈ A <;> simp [h1, h0]
  rw [e]
  refine (hW t A hA).union ?_
  split_ifs
  · exact (hW t univ MeasurableSet.univ).compl
  · exact @MeasurableSet.empty _ (𝓕 t)

theorem measurable_stopW (hW : AdaptedBefore 𝓕 ζ W) (s : ℝ≥0) : Measurable[𝓕 s] (stopW W ζ s) := by
  refine @Measurable.of_eval Ω ℝ≥0 (fun _ => ℝ) (𝓕 s) (fun _ => inferInstance) _ fun r => ?_
  exact (measurable_killedVal hW (min r s)).mono (𝓕.mono (min_le_right r s)) le_rfl

/-- **The trace value** `x + traceAt s (stopW s)` (the trace point `η(s)` for `s < ζ`). -/
def traceVal (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (x : ℝ) (s : ℝ≥0) (ω : Ω) : ℂ :=
  (x : ℂ) + LP.traceAt s (stopW W ζ s ω)

theorem measurable_traceVal (hW : AdaptedBefore 𝓕 ζ W) (x : ℝ) (s : ℝ≥0) :
    Measurable[𝓕 s] (traceVal W ζ x s) :=
  measurable_const.add ((LP.measurable_traceAt s).comp (measurable_stopW hW s))

/-- **The trace value is the trace point** before the lifetime. -/
theorem traceVal_eq {x : ℝ} {ω : Ω} {η' : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun t => W t ω) (ζ ω) η')
    (hw : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω}) (hw0 : W 0 ω = 0) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ ω) : traceVal W ζ x s ω = x + η' s := by
  unfold traceVal
  rw [LP.traceAt_congr (w' := fun t => W t ω) fun r hr => ?_,
    LP.traceAt_eq_of_isGeneratingTrace hη hw hw0 hs]
  have hrs : min r s = r := min_eq_left hr
  have hr' : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hs
  simp only [stopW, hrs]
  exact ite_eq_left hr'

end TraceVal

/-! ### The first entrance of a capped path, read from rational times before the lifetime -/

section Entrance

/-- The first rational time before `ζ` at which the values `Γ` enter `U`. -/
def ratEntrance (U : Set ℂ) (Γ : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (q : ℚ≥0) (_ : ((q : ℝ≥0) : ℝ≥0∞) < ζ ∧ Γ q ∈ U), (((q : ℝ≥0) : ℝ≥0∞))

theorem ratEntrance_le {U : Set ℂ} {Γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < ζ)
    (hU : Γ q ∈ U) : ratEntrance U Γ ζ ≤ ((q : ℝ≥0) : ℝ≥0∞) :=
  iInf₂_le q ⟨hq, hU⟩

theorem ratEntrance_lt_iff {U : Set ℂ} {Γ : ℝ≥0 → ℂ} {ζ b : ℝ≥0∞} :
    ratEntrance U Γ ζ < b ↔ ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ ∧ Γ q ∈ U ∧ ((q : ℝ≥0) : ℝ≥0∞) < b := by
  unfold ratEntrance
  simp only [iInf_lt_iff, exists_prop]
  constructor
  · rintro ⟨q, ⟨h1, h2⟩, h3⟩; exact ⟨q, h1, h2, h3⟩
  · rintro ⟨q, h1, h2, h3⟩; exact ⟨q, ⟨h1, h2⟩, h3⟩

theorem ratEntrance_lt_of_lt_top {U : Set ℂ} {Γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (h : ratEntrance U Γ ζ < ⊤) :
    ratEntrance U Γ ζ < ζ := by
  obtain ⟨q, hq, hU, -⟩ := ratEntrance_lt_iff.1 h
  exact lt_of_le_of_lt (ratEntrance_le hq hU) hq

end Entrance

end WholeField

end InteractingSLE
