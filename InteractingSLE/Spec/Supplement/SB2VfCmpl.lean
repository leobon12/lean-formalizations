/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineIfaceR
import InteractingSLE.Spec.Supplement.SB2TcFilt

/-!
# SB2(1)'s version half: measurability for the completed line filtration

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The measurability fields of
`Lv.SB2LineVersionR` are for `D.lineFiltC t = mΩ ⊓ LocalSets.aeSigma (D.absMarks t) P`: an ambient-measurable set or
function that agrees almost surely with a line-mark one belongs to it. Generic tools:

* `exists_measurable_conull`: an almost-sure property holds on a measurable conull event;
* `measurableSet_cmpl`, `measurableSet_cmpl_of_conull`, `measurable_cmpl`: ambient-measurable sets / functions a.s.
  equal to `𝒢`-measurable ones are `mΩ ⊓ aeSigma 𝒢 P`-measurable;
* `measurableSet_lineFiltC`, `measurable_lineFiltC`: the same for `D.lineFiltC t` and `D.absMarks t`;
* **`stronglyAdapted_tcFilt_of_ae_read`**: a relative process is adapted to the time change `Tc.tcFilt 𝓖 a` of a
  filtration closed under null modifications as soon as, at relative time `q`, it is read almost surely on
  `{q ≤ a t}` from a `𝓖 t`-measurable variable (the a.e. form of `Tc.stronglyAdapted_tcFilt_of_read`);
* `lineFiltC_closed`: the completed line filtration is closed under null modifications.

Deterministic measure theory; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vf

section Generic

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **An almost-sure property holds on a measurable conull event.** -/
theorem exists_measurable_conull {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∃ M : Set Ω, MeasurableSet M ∧ P Mᶜ = 0 ∧ ∀ ω ∈ M, p ω := by
  refine ⟨(toMeasurable P {ω | ¬ p ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 h
  · by_contra hn
    exact hω (subset_toMeasurable _ _ hn)

/-- **An ambient-measurable set a.s. equal to a `𝒢`-set is measurable for the completion.** -/
theorem measurableSet_cmpl {s s' : Set Ω} (hs : MeasurableSet s) (hs' : MeasurableSet[𝒢] s')
    (he : s =ᵐ[P] s') : MeasurableSet[mΩ ⊓ LocalSets.aeSigma 𝒢 P] s :=
  MeasurableSpace.measurableSet_inf.2 ⟨hs, ⟨s', hs', he⟩⟩

/-- **A measurable conull set is measurable for the completion.** -/
theorem measurableSet_cmpl_of_conull {s : Set Ω} (hs : MeasurableSet s) (h : P sᶜ = 0) :
    MeasurableSet[mΩ ⊓ LocalSets.aeSigma 𝒢 P] s :=
  measurableSet_cmpl hs (@MeasurableSet.univ Ω 𝒢) (ae_eq_univ.2 h)

/-- **An ambient-measurable function a.s. equal to a `𝒢`-measurable one is measurable for the completion.** -/
theorem measurable_cmpl {β : Type*} [MeasurableSpace β] {f g : Ω → β} (hf : Measurable f)
    (hg : Measurable[𝒢] g) (he : f =ᵐ[P] g) : Measurable[mΩ ⊓ LocalSets.aeSigma 𝒢 P] f := fun _ hB =>
  measurableSet_cmpl (hf hB) (hg hB) (he.preimage _)

/-- **The completion is closed under null modifications** (inside the ambient σ-algebra). -/
theorem cmpl_closed {s s' : Set Ω} (hs : MeasurableSet s) (hs' : MeasurableSet[mΩ ⊓ LocalSets.aeSigma 𝒢 P] s')
    (he : s =ᵐ[P] s') : MeasurableSet[mΩ ⊓ LocalSets.aeSigma 𝒢 P] s := by
  obtain ⟨-, s'', hs'', he'⟩ := MeasurableSpace.measurableSet_inf.1 hs'
  exact measurableSet_cmpl hs hs'' (he.trans he')

end Generic

section TimeChange

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Adaptedness to the time change from almost-sure readings**: if the filtration `𝓖` is closed under null
modifications, `W q` is measurable and, almost surely on `{q ≤ a t}`, equals a `𝓖 t`-measurable `Y q t`, then `W` is
strongly adapted to `Tc.tcFilt 𝓖 a`. -/
theorem stronglyAdapted_tcFilt_of_ae_read {𝓖 : Filtration ℝ≥0 mΩ} {a : ℝ≥0 → Ω → ℝ≥0∞}
    {ha : ∀ t, Measurable[𝓖 t] (a t)}
    (hcl : ∀ t (s s' : Set Ω), MeasurableSet s → MeasurableSet[𝓖 t] s' → s =ᵐ[P] s' → MeasurableSet[𝓖 t] s)
    {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ q, Measurable (W q)) (Y : ℝ≥0 → ℝ≥0 → Ω → ℝ)
    (hY : ∀ q t, Measurable[𝓖 t] (Y q t))
    (hread : ∀ q t : ℝ≥0, ∀ᵐ ω ∂P, (q : ℝ≥0∞) ≤ a t ω → W q ω = Y q t ω) :
    StronglyAdapted (Tc.tcFilt 𝓖 a ha) W := by
  intro q
  refine Measurable.stronglyMeasurable fun B hB => ⟨hWm q hB, fun t => ?_⟩
  have hA : MeasurableSet[𝓖 t] {ω | (q : ℝ≥0∞) ≤ a t ω} := measurableSet_le measurable_const (ha t)
  have hAm : MeasurableSet {ω | (q : ℝ≥0∞) ≤ a t ω} := 𝓖.le t _ hA
  refine hcl t _ (Y q t ⁻¹' B ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}) ((hWm q hB).inter hAm) ((hY q t hB).inter hA) ?_
  filter_upwards [hread q t] with ω hω
  apply propext
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
  exact ⟨fun h => ⟨hω h.2 ▸ h.1, h.2⟩, fun h => ⟨(hω h.2).symm ▸ h.1, h.2⟩⟩

end TimeChange

section Line

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The completed line filtration is closed under null modifications.** -/
theorem lineFiltC_closed (D : Lv.EntranceUnion κ b jumps P h E k u η ζ u₀)
    (HP : Lv.SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (t : ℝ≥0) {s s' : Set Ω} (hs : MeasurableSet s)
    (hs' : MeasurableSet[D.lineFiltC HP t] s') (he : s =ᵐ[P] s') : MeasurableSet[D.lineFiltC HP t] s :=
  cmpl_closed hs hs' he

/-- **A line-mark reading, up to a null set, is measurable for the completed line filtration.** -/
theorem measurable_lineFiltC (D : Lv.EntranceUnion κ b jumps P h E k u η ζ u₀)
    (HP : Lv.SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (t : ℝ≥0) {β : Type*} [MeasurableSpace β] {f g : Ω → β}
    (hf : Measurable f) (hg : Measurable[D.absMarks (t : ℝ≥0∞)] g) (he : f =ᵐ[P] g) :
    Measurable[D.lineFiltC HP t] f :=
  measurable_cmpl hf hg he

/-- **A line-mark event, up to a null set, is an event of the completed line filtration.** -/
theorem measurableSet_lineFiltC (D : Lv.EntranceUnion κ b jumps P h E k u η ζ u₀)
    (HP : Lv.SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (t : ℝ≥0) {s s' : Set Ω} (hs : MeasurableSet s)
    (hs' : MeasurableSet[D.absMarks (t : ℝ≥0∞)] s') (he : s =ᵐ[P] s') : MeasurableSet[D.lineFiltC HP t] s :=
  measurableSet_cmpl hs hs' he

end Line

end InteractingSLE.Theorem14.SB.Vf
