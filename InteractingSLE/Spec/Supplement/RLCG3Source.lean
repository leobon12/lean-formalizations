/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG3Shift
import InteractingSLE.Spec.Restart.FlowStopIdentCMContact

/-!
# Lemma G3 in the source's form: per-seed buffers (ruling R60)

Packet PROVE-G3SRC. Source: Lemma G3 and its proof (supplement §7.3, `source/spec/p481-528.md` L290–L320,
pp. 492–493), hypothesis 4: "`U₀` is bounded and buffered in a bounded relatively open set `U` […] The closure of `U`
meets the real line only in two disjoint intervals on which the respective canonical seed germs just stated hold […]
Each future is stopped on exiting `U₀` or on its first new old-boundary contact".

PROVE-RLC-A's `RLC.G3ChartComparisonStatement` stops both futures on exiting one buffer `V` whose closure may meet `ℝ`
anywhere in the agreement set `O`; it drops the source's stop at the first new boundary contact, which makes it stronger
than Lemma G3 and blocks the Cameron–Martin proof (`planning/handoffs/PROVE-L1-CM.md` §4.2). Here each future has its
own buffer `Vᵢ`, whose closure meets `ℝ` only in one closed interval `[aᵢ, cᵢ] ⊆ O` ("per-seed buffers"). The source's
stop is the special case `Vᵢ ∩ ℝ` = a small interval around the seed `yᵢ` (a path leaving that interval through `ℝ` has
made a new boundary contact); allowing contacts inside `[aᵢ, cᵢ]` is G7a's extension to untouched real intervals with
the same data, in the case where they are adjacent to the seed.

* `exitTime_mono`, `StoppedAgree.mono`: exit times are monotone in the buffer, and stopped agreement passes to a smaller
  buffer;
* `G3SourceStatement`: **Lemma G3 in the source's form** (per-seed buffers, one density);
* `g3SourceStatement_of_g3`: PROVE-RLC-A's single-buffer form implies it (buffer `V₁ ∪ V₂`), so it is no stronger;
* **`g3SourceStatement_of_shiftIntervalLocality`**: from flow locality for shift pairs and buffers over one interval
  (`Restart.FlowStopIdentCM.FlowLocalityShiftIntervalStatement`) and Theorems 1.2 (param) / 1.3; the shift is
  `RLC.exists_shift_isGFFWithBoundaryData` for the compact set `shiftHullSet V₁ a₁ c₁ ∪ shiftHullSet V₂ a₂ c₂ ∪
  closure V₁ ∪ closure V₂`, which contains every hull of either stopped path;
* **`g3SourceStatement_of_CMInterval`**: from the restricted Cameron–Martin input
  `Restart.FlowStopIdentCM.FlowLineStopIdentCMIntervalStatement`, the WFS kernel target and Theorems 1.2 (param) / 1.3.

R43/R48: this serves Theorem 1.5 only (Lemma G3 is an input of W5); Theorems 1.2–1.3 are hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric

universe u

namespace InteractingSLE

namespace RLC

open Restart.FlowStopIdentCM

/-! ### Monotonicity of exit times and stopped agreement -/

/-- **The exit time is monotone in the buffer.** -/
theorem exitTime_mono {V V' : Set ℂ} (hVV' : V ⊆ V') (γ : ℝ≥0 → ℂ) (U : ℝ≥0∞) :
    exitTime V γ U ≤ exitTime V' γ U := by
  unfold exitTime
  exact min_le_min le_rfl (le_iInf₂ fun s hs => iInf₂_le s fun h => hs (hVV' h))

/-- One half of `StoppedAgree.mono`: the exit time of the first path from the smaller buffer is at most that of the
second path. -/
theorem exitTime_le_of_stoppedAgree {V V' : Set ℂ} (hVV' : V ⊆ V') {γ γ' : ℝ≥0 → ℂ} {U U' : ℝ≥0∞}
    (he : exitTime V' γ U = exitTime V' γ' U')
    (hag : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ exitTime V' γ U → γ s = γ' s) :
    exitTime V γ U ≤ exitTime V γ' U' := by
  have hle : exitTime V γ U ≤ exitTime V' γ U := exitTime_mono hVV' γ U
  have hU' : exitTime V' γ' U' ≤ U' := min_le_left _ _
  refine le_min (hle.trans (he.trans_le hU')) (le_iInf₂ fun s hs => ?_)
  by_cases hse : (s : ℝ≥0∞) ≤ exitTime V' γ U
  · have hs' : γ s ∉ V := by rw [hag s hse]; exact hs
    exact (min_le_right _ _).trans (iInf₂_le s hs')
  · exact hle.trans (not_le.1 hse).le

/-- **Stopped agreement passes to a smaller buffer.** -/
theorem StoppedAgree.mono {V V' : Set ℂ} (hVV' : V ⊆ V') {γ γ' : ℝ≥0 → ℂ} {U U' : ℝ≥0∞}
    (h : StoppedAgree V' γ U γ' U') : StoppedAgree V γ U γ' U' := by
  obtain ⟨he, hag⟩ := h
  have hag' : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ exitTime V' γ' U' → γ' s = γ s := fun s hs => (hag s (he ▸ hs)).symm
  have h1 := exitTime_le_of_stoppedAgree hVV' he hag
  have h2 := exitTime_le_of_stoppedAgree hVV' he.symm hag'
  refine ⟨le_antisymm h1 h2, fun s hs => hag s (hs.trans (exitTime_mono hVV' γ U))⟩

/-! ### Lemma G3 in the source's form -/

/-- **Lemma G3 in the source's form: per-seed buffers** (supplement §7.3, pp. 492–493, hypothesis 4 and the proof;
ruling R60). Let `0 < κ < 4`, let `b` (jumps `J`) and `bR` (jumps `Ĵ`) be piecewise constant data which agree, together
with their jump sets, on an open set `O ⊆ ℝ`, and let `V₁`, `V₂` be bounded open buffers whose closures meet `ℝ` only in
closed intervals `[a₁, c₁] ⊆ O` and `[a₂, c₂] ⊆ O` respectively. Let `H₀` be a GFF with data `b` under `Q₀`, with
angle-`θ₁` and angle-`θ₂` flow lines `Γ₁` from `y₁` and `Γ₂` from `y₂`. Then there are one density `Z > 0` with
`E_{Q₀} Z = 1` and, under `Q = Z·Q₀`, a GFF `Ĥ` with data `bR` and its flow lines `α̂₁`, `α̂₂` from the same seeds at
the same angles such that, `Q₀`-almost surely, each `Γᵢ` agrees with `α̂ᵢ` up to and including their common exit time
from its own buffer `Vᵢ`. -/
def G3SourceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    (∀ x ∈ O, x ∈ J ↔ x ∈ Ĵ) → ∀ V₁ V₂ : Set ℂ, IsOpen V₁ → IsOpen V₂ → Bornology.IsBounded V₁ →
    Bornology.IsBounded V₂ → ∀ a₁ c₁ a₂ c₂ : ℝ, Icc a₁ c₁ ⊆ O → Icc a₂ c₂ ⊆ O →
    (∀ z ∈ closure V₁, z.im = 0 → z.re ∈ Icc a₁ c₁) → (∀ z ∈ closure V₂, z.im = 0 → z.re ∈ Icc a₂ c₂) →
    ∀ y₁ y₂ θ₁ θ₂ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
      (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
    ∀ (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞),
      IsFlowLine κ b J y₁ θ₁ Q₀ H₀ Γ₁ U₁ → IsFlowLine κ b J y₂ θ₂ Q₀ H₀ Γ₂ U₂ →
    ∃ (Z : S → ℝ) (Ĥ : S → LQGMetric.DistOn upperHalfPlaneOpens) (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
      AEMeasurable Z Q₀ ∧ (∀ᵐ x ∂Q₀, 0 < Z x) ∧ ∫ x, Z x ∂Q₀ = 1 ∧
      IsGFFWithBoundaryData (Q₀.withDensity fun x => ENNReal.ofReal (Z x)) Ĥ bR Ĵ ∧
      IsFlowLine κ bR Ĵ y₁ θ₁ (Q₀.withDensity fun x => ENNReal.ofReal (Z x)) Ĥ α₁ ζ₁ ∧
      IsFlowLine κ bR Ĵ y₂ θ₂ (Q₀.withDensity fun x => ENNReal.ofReal (Z x)) Ĥ α₂ ζ₂ ∧
      ∀ᵐ x ∂Q₀, StoppedAgree V₁ (Γ₁ x) (U₁ x) (α₁ x) (ζ₁ x) ∧ StoppedAgree V₂ (Γ₂ x) (U₂ x) (α₂ x) (ζ₂ x)

/-- **PROVE-RLC-A's single-buffer G3 implies the source form** (apply it to the buffer `V₁ ∪ V₂` and restrict the
stopped agreement to each `Vᵢ`). So the source form is no stronger. -/
theorem g3SourceStatement_of_g3 (hG3 : G3ChartComparisonStatement.{u}) : G3SourceStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO hJO V₁ V₂ hV₁ hV₂ hV₁b hV₂b a₁ c₁ a₂ c₂ hI₁ hI₂ hV₁I hV₂I y₁ y₂ θ₁ θ₂
    S _ Q₀ _ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  have hVO : ∀ z ∈ closure (V₁ ∪ V₂), z.im = 0 → z.re ∈ O := by
    intro z hz hz0
    rw [closure_union] at hz
    rcases hz with hz | hz
    · exact hI₁ (hV₁I z hz hz0)
    · exact hI₂ (hV₂I z hz hz0)
  obtain ⟨Z, Ĥ, α₁, α₂, ζ₁, ζ₂, hZm, hZpos, hZ1, hĤ, hα₁, hα₂, hag⟩ :=
    hG3 κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO hJO (V₁ ∪ V₂) (hV₁.union hV₂) (hV₁b.union hV₂b) hVO y₁ y₂ θ₁ θ₂ Q₀ H₀
      hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  refine ⟨Z, Ĥ, α₁, α₂, ζ₁, ζ₂, hZm, hZpos, hZ1, hĤ, hα₁, hα₂, ?_⟩
  filter_upwards [hag] with x hx
  exact ⟨hx.1.mono subset_union_left, hx.2.mono subset_union_right⟩

/-- The compact set of the shift: both buffers' closures and their hull sets. -/
theorem isCompact_g3SourceSet {V₁ V₂ : Set ℂ} (hV₁b : Bornology.IsBounded V₁) (hV₂b : Bornology.IsBounded V₂)
    (a₁ c₁ a₂ c₂ : ℝ) :
    IsCompact (shiftHullSet V₁ a₁ c₁ ∪ shiftHullSet V₂ a₂ c₂ ∪ (closure V₁ ∪ closure V₂)) :=
  ((isCompact_shiftHullSet hV₁b a₁ c₁).union (isCompact_shiftHullSet hV₂b a₂ c₂)).union
    (hV₁b.isCompact_closure.union hV₂b.isCompact_closure)

/-- The real points of the shift's compact set lie over `O`. -/
theorem re_mem_of_mem_g3SourceSet {O : Set ℝ} {V₁ V₂ : Set ℂ} (hV₁b : Bornology.IsBounded V₁)
    (hV₂b : Bornology.IsBounded V₂) {a₁ c₁ a₂ c₂ : ℝ} (hI₁ : Icc a₁ c₁ ⊆ O) (hI₂ : Icc a₂ c₂ ⊆ O)
    (hV₁I : ∀ z ∈ closure V₁, z.im = 0 → z.re ∈ Icc a₁ c₁) (hV₂I : ∀ z ∈ closure V₂, z.im = 0 → z.re ∈ Icc a₂ c₂)
    {z : ℂ} (hz : z ∈ shiftHullSet V₁ a₁ c₁ ∪ shiftHullSet V₂ a₂ c₂ ∪ (closure V₁ ∪ closure V₂)) (h0 : z.im = 0) :
    z.re ∈ O := by
  rcases hz with (hz | hz) | (hz | hz)
  · exact re_mem_of_mem_shiftHullSet hV₁b (fun w hw hw0 => hI₁ (hV₁I w hw hw0)) hI₁ hz h0
  · exact re_mem_of_mem_shiftHullSet hV₂b (fun w hw hw0 => hI₂ (hV₂I w hw hw0)) hI₂ hz h0
  · exact hI₁ (hV₁I z hz h0)
  · exact hI₂ (hV₂I z hz h0)

/-- **Lemma G3 in the source's form from flow locality for shift pairs and buffers over one interval**, and Theorems
1.2 (param) / 1.3. The shift pair is `RLC.exists_shift_isGFFWithBoundaryData` for the compact set
`shiftHullSet V₁ a₁ c₁ ∪ shiftHullSet V₂ a₂ c₂ ∪ closure V₁ ∪ closure V₂`; the reference flow lines are the canonical
ones of `H₀ + T` under `Z · Q₀`; locality is applied to each curve with its own buffer. -/
theorem g3SourceStatement_of_shiftIntervalLocality (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hloc : FlowLocalityShiftIntervalStatement.{0}) :
    G3SourceStatement.{0} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO _hJO V₁ V₂ hV₁ hV₂ hV₁b hV₂b a₁ c₁ a₂ c₂ hI₁ hI₂ hV₁I hV₂I y₁ y₂ θ₁ θ₂
    S _ Q₀ _ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  obtain ⟨Z, T, N, hNo, hKN, hNO, hZm, hZpos, hZ1, hĤ, hT0⟩ :=
    exists_shift_isGFFWithBoundaryData hb hbR hO hbO (isCompact_g3SourceSet hV₁b hV₂b a₁ c₁ a₂ c₂)
      (fun z hz h0 => re_mem_of_mem_g3SourceSet hV₁b hV₂b hI₁ hI₂ hV₁I hV₂I hz h0) Q₀ hH
  set Q := Q₀.withDensity fun x => ENNReal.ofReal (Z x) with hQ
  have hint : Integrable Z Q₀ := Integrable.of_integral_ne_zero (by rw [hZ1]; exact one_ne_zero)
  have hQprob : IsProbabilityMeasure Q := by
    constructor
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (hZpos.mono fun x hx => hx.le), hZ1, ENNReal.ofReal_one]
  have hPQ : Q₀ ≪ Q := by
    refine withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hZm).aemeasurable ?_
    filter_upwards [hZpos] with x hx
    exact (ENNReal.ofReal_pos.2 hx).ne'
  have hQP : Q ≪ Q₀ := withDensity_absolutelyContinuous _ _
  have hs₁ : shiftHullSet V₁ a₁ c₁ ⊆ N := fun z hz => hKN (Or.inl (Or.inl hz))
  have hs₂ : shiftHullSet V₂ a₂ c₂ ⊆ N := fun z hz => hKN (Or.inl (Or.inr hz))
  have hc₁ : closure V₁ ⊆ N := fun z hz => hKN (Or.inr (Or.inl hz))
  have hc₂ : closure V₂ ⊆ N := fun z hz => hKN (Or.inr (Or.inr hz))
  obtain ⟨α₁, ζ₁, hα₁⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₁ θ₁ hĤ
  obtain ⟨α₂, ζ₂, hα₂⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₂ θ₂ hĤ
  refine ⟨Z, fun x => H₀ x + T, α₁, α₂, ζ₁, ζ₂, hZm.aemeasurable, hZpos, hZ1, hĤ, hα₁, hα₂, ?_⟩
  filter_upwards [hloc κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hNo hNO V₁ hV₁ hV₁b hc₁ a₁ c₁ hI₁ hV₁I hs₁ y₁ θ₁ Q₀ Q
      hPQ hQP H₀ _ T hH hĤ (fun _ => rfl) hT0 Γ₁ α₁ U₁ ζ₁ h₁ hα₁,
    hloc κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hNo hNO V₂ hV₂ hV₂b hc₂ a₂ c₂ hI₂ hV₂I hs₂ y₂ θ₂ Q₀ Q
      hPQ hQP H₀ _ T hH hĤ (fun _ => rfl) hT0 Γ₂ α₂ U₂ ζ₂ h₂ hα₂] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩

/-- **Lemma G3 in the source's form from the restricted Cameron–Martin input** (`FlowLineStopIdentCMIntervalStatement`,
(L1) with the lifetime clause for shift pairs on the enlargement and buffers over one interval), the WFS kernel target
for `0 < κ < 4` and Theorems 1.2 (param) / 1.3. -/
theorem g3SourceStatement_of_CMInterval (hCM : FlowLineStopIdentCMIntervalStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3SourceStatement.{0} :=
  g3SourceStatement_of_shiftIntervalLocality h12p h13
    (flowLocalityShiftIntervalStatement_of_CMInterval_through hCM hT h12p h13)

end RLC

end InteractingSLE
