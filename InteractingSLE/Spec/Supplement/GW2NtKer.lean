/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NtCap
import InteractingSLE.Spec.Supplement.GW2StlThr
import InteractingSLE.Spec.Supplement.GW2ScheduleIdent

/-!
# GW2's `noThreshold`: the kernel-to-`P` transfer

Packet PROVE-GW2-NOTHR (round 2, decision D38). Route (M) proves the absence of a threshold under the launch kernel
`condExpKernel P 𝒢 ω₀` of the earlier pieces (SAFE's collision exclusion for the candidate and the conditional
counterflow). The statement wanted, `GW2Rz.NoThresholdX`, is at `P` level. A kernel-almost-sure statement passes to
`P` for a MEASURABLE event (`GW2Schedule.ae_of_ae_condExpKernel_on`), and the no-threshold event of a stage variable
is measurable: split by the (countably many) word types; on one type the weights are fixed and "no threshold below the
cap" is "the cap is at most the threshold time" (`GW2Sf.le_thr_iff_no_threshold`), a measurable event
(`Restart.FCDet.measurable_thr`).

* `thresholdCondition_iff_of_isFlowType`: the threshold does not see the re-indexing of a typed word;
* **`measurableSet_noThr`**: the no-threshold event of a measurable stage record, word map with countably many types,
  measurable continuous driver and measurable cap is measurable;
* **`ae_noThr_of_kernel`**: the kernel-to-`P` transfer.

Deterministic and measure-theoretic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Nt

open Restart Exist.StagedLaw MartChar.RealFlow Supp8.Q3Stop Sec7.PocketTraversal

/-- **The threshold does not see the re-indexing of a typed word.** -/
theorem thresholdCondition_iff_of_isFlowType {κ : ℝ} {c : BoundaryWord} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (htype : FCDet.IsFlowType κ 0 c xL xR ρL ρR)
    {D : ℝ → ℝ} {u : ℝ} :
    ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) (D u)
        (fun i => -rightImg (fun v => -D v) (-flowLineXL c.fn c.jumps 0 i) u)
        (fun j => rightImg D (flowLineXR c.fn c.jumps 0 j) u) ↔
      ForceWord.ThresholdCondition ρL ρR (D u) (fun i => -rightImg (fun v => -D v) (-xL i) u)
        (fun j => rightImg D (xR j) u) := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := htype
  subst nL nR
  change xL = flowLineXL c.fn c.jumps 0 at hxL
  change xR = flowLineXR c.fn c.jumps 0 at hxR
  change ρL = flowLineRhoL κ c.fn c.jumps 0 0 at hρL
  change ρR = flowLineRhoR κ c.fn c.jumps 0 0 at hρR
  rw [hxL, hxR, hρL, hρR]

section Event

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The no-threshold event of a stage variable (record `rec`, record event `E`, word map `β`, driver `D`, cap). -/
def NoThrEvent (κ : ℝ) (rec : Ω → RecData) (E : Set RecData) (β : RecData → BoundaryWord) (D : ℝ≥0 → Ω → ℝ)
    (cap : Ω → ℝ≥0∞) : Set Ω :=
  {ω | rec ω ∈ E → ∀ u : ℝ≥0, (u : ℝ≥0∞) < cap ω →
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ (β (rec ω)).fn (β (rec ω)).jumps 0 0)
      (flowLineRhoR κ (β (rec ω)).fn (β (rec ω)).jumps 0 0) (D u ω)
      (fun i => -rightImg (fun v : ℝ => -D v.toNNReal ω) (-flowLineXL (β (rec ω)).fn (β (rec ω)).jumps 0 i) u)
      (fun j => rightImg (fun v : ℝ => D v.toNNReal ω) (flowLineXR (β (rec ω)).fn (β (rec ω)).jumps 0 j) u)}

/-- On one word type, no threshold below the cap is the cap below the typed threshold time. -/
theorem mem_noThrEvent_iff_typed {κ : ℝ} {rec : Ω → RecData} {E : Set RecData} {β : RecData → BoundaryWord}
    {D : ℝ≥0 → Ω → ℝ} (hDc : ∀ ω, Continuous fun t => D t ω) {cap : Ω → ℝ≥0∞} {ω : Ω} (hE : rec ω ∈ E)
    {w : WordType} (hw : wordType κ (β (rec ω)) = w) :
    ω ∈ NoThrEvent κ rec E β D cap ↔ cap ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) D
      (fun ω => typedXL κ w (β (rec ω))) (fun ω => typedXR κ w (β (rec ω))) ω := by
  rw [GW2Sf.le_thr_iff_no_threshold hDc _ _ cap ω]
  have htype := isFlowType_typed hw
  refine ⟨fun h u hu => ?_, fun h _ u hu => ?_⟩
  · have h1 := h hE u hu
    have h2 := (thresholdCondition_iff_of_isFlowType htype (D := fun v : ℝ => D v.toNNReal ω) (u := u)).not.1
      (by simpa only [Real.toNNReal_coe] using h1)
    simp only [Real.toNNReal_coe] at h2
    exact h2
  · have h1 := h u hu
    have h2 := (thresholdCondition_iff_of_isFlowType htype (D := fun v : ℝ => D v.toNNReal ω) (u := u)).not.2
      (by simp only [Real.toNNReal_coe]; exact h1)
    simp only [Real.toNNReal_coe] at h2
    exact h2

/-- **The no-threshold event of a stage variable is measurable.** -/
theorem measurableSet_noThr {κ : ℝ} {rec : Ω → RecData} (hrec : Measurable rec) {E : Set RecData}
    (hE : MeasurableSet E) {β : RecData → BoundaryWord} (hβ : Measurable β)
    (hcount : (range fun y => wordType κ (β y)).Countable) {D : ℝ≥0 → Ω → ℝ} (hDm : ∀ t, Measurable (D t))
    (hDc : ∀ ω, Continuous fun t => D t ω) {cap : Ω → ℝ≥0∞} (hcap : Measurable cap) :
    MeasurableSet (NoThrEvent κ rec E β D cap) := by
  set Tw : WordType → Set Ω := fun w => {ω | rec ω ∈ E ∧ wordType κ (β (rec ω)) = w ∧
    cap ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) D (fun ω => typedXL κ w (β (rec ω)))
      (fun ω => typedXR κ w (β (rec ω))) ω} with hTw
  have heq : NoThrEvent κ rec E β D cap = {ω | rec ω ∉ E} ∪ ⋃ w ∈ range fun y => wordType κ (β y), Tw w := by
    ext ω
    constructor
    · intro h
      by_cases hE' : rec ω ∈ E
      · refine Or.inr (mem_biUnion (x := wordType κ (β (rec ω))) ⟨rec ω, rfl⟩ ⟨hE', rfl, ?_⟩)
        exact (mem_noThrEvent_iff_typed hDc hE' rfl).1 h
      · exact Or.inl hE'
    · rintro (h | h)
      · exact fun h' => absurd h' h
      · obtain ⟨w, -, hE', hw, hle⟩ := mem_iUnion₂.1 h
        exact (mem_noThrEvent_iff_typed hDc hE' hw).2 hle
  rw [heq]
  refine (hrec hE).compl.union (MeasurableSet.biUnion hcount fun w _ => ?_)
  have h𝓗 : StronglyAdapted (Filtration.const (ι := ℝ≥0) mΩ le_rfl : Filtration ℝ≥0 mΩ) D :=
    fun t => (hDm t).stronglyMeasurable
  have hxL : Measurable fun ω => typedXL κ w (β (rec ω)) := (measurable_typedXL κ w).comp (hβ.comp hrec)
  have hxR : Measurable fun ω => typedXR κ w (β (rec ω)) := (measurable_typedXR κ w).comp (hβ.comp hrec)
  exact (hrec hE).inter (((measurable_wordType κ).comp (hβ.comp hrec) (measurableSet_singleton w)).inter
    (measurableSet_le hcap (FCDet.measurable_thr (ρL := typedRhoL w) (ρR := typedRhoR w)
      (𝓗 := Filtration.const (ι := ℝ≥0) mΩ le_rfl) hDc h𝓗 hxL hxR)))

end Event

/-- **The kernel-to-`P` transfer of the no-threshold event.** If, for `P`-almost every `ω₀` of a `𝒢`-measurable event
`L` carrying the record event, the no-threshold event holds almost surely under the conditional law
`condExpKernel P 𝒢 ω₀`, it holds `P`-almost surely. -/
theorem ae_noThr_of_kernel {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {κ : ℝ} {rec : Ω → RecData} (hrec : Measurable rec) {E : Set RecData} (hE : MeasurableSet E)
    {β : RecData → BoundaryWord} (hβ : Measurable β) (hcount : (range fun y => wordType κ (β y)).Countable)
    {D : ℝ≥0 → Ω → ℝ} (hDm : ∀ t, Measurable (D t)) (hDc : ∀ ω, Continuous fun t => D t ω)
    {cap : Ω → ℝ≥0∞} (hcap : Measurable cap) {L : Set Ω} (hL : MeasurableSet[𝒢] L)
    (hcov : ∀ᵐ ω ∂P, rec ω ∈ E → ω ∈ L)
    (hker : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ NoThrEvent κ rec E β D cap) :
    ∀ᵐ ω ∂P, ω ∈ NoThrEvent κ rec E β D cap := by
  filter_upwards [GW2Schedule.ae_of_ae_condExpKernel_on h𝒢 hL
    (measurableSet_noThr hrec hE hβ hcount hDm hDc hcap) hker, hcov] with ω h1 h2 hEω
  exact h1 (h2 hEω) hEω


end InteractingSLE.Theorem14.GW2Nt
