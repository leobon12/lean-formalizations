/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RS133
import InteractingSLE.Spec.Sec7.StripMark
import InteractingSLE.Spec.Sec7.SideHeightBoxProb
import InteractingSLE.WangWu.Adapted

/-!
# (RS13.3) in full, almost surely

Packet PROVE-STRIPSYS19. Specification §7.4, proof of Aux. lemma 130 (`source/spec/p385-432.md` L440–L456, p. 411):
"Retain the two full marked local sets. Nested local-set boundary comparison identifies the union mean with each
single-path mean on this collar. To implement that statement with own-path couplings, choose finite rational own times
beyond the compact subarc, use the two stopped canonical means, and then enlarge to the complete marked union. A single
probability-one event for these countably many comparisons suffices before the arc and the rational times are
selected."

* **`ae_tendsto_sub_ranges`** (nested local-set boundary comparison for two stopped ranges): for two paths with
  Lemma 6.2's inputs (continuous versions from real seeds, field-determined, history-sensitively local at first
  entrance times, in the closed upper half-plane), the ranges `A = α([0, q₁]) ∩ ℍ`, `B = β([0, q₂]) ∩ ℍ` are
  field-determined local sets, and almost surely the harmonic representatives of their local-set means agree at the
  boundary at every common point where the two ranges locally coincide (`SideHeightBox.ae_tendsto_sub_of_locals`);
* **`ae_late_of_sideHeights`** ((RS13.3) almost surely): with the single-path side heights at countably many stops
  (for `α` the (S) of `StripMark.ae_hasSideHeights_stage_of_lemma62` at the stops `t₀ + r`, for `β = η_{π/2}` the
  single-path side heights `Aux70.SinglePathSideHeightStatement`), almost surely `β` has points outside the complete
  range of `α` at arbitrarily late times — the `late` field of `StripSys.IsSelectionConfig`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Bornology Function
open scoped NNReal ENNReal Real

open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE

namespace Sec7

namespace RS133

open StripGeom LocalSets

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- **Lemma 6.2 for one path at a deterministic time: a field-determined local set.** -/
theorem isLocalSet_range_and_aeDetermined (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {α : Ω → ℝ≥0 → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (X ω))
    (hloc : Sec6.IsEntranceHistoryLocal α X P) (q : ℝ≥0) :
    IsLocalSet (fun ω => α ω '' Icc 0 q ∩ H) X P ∧
      MeasurableSpace.comap (fun ω => α ω '' Icc 0 q ∩ H) hittingSigma ≤
        aeSigma (MeasurableSpace.comap X inferInstance) P := by
  have h := WangWu.isLocalSet_explored_and_aeDetermined (P := P) (η := fun _ : Fin 1 => α)
    (x := fun _ => (0 : ℂ)) (τ := fun _ _ => (q : ℝ≥0∞)) (S := fun _ _ _ => (q : ℝ≥0∞)) hX (fun _ => hαc)
    (fun _ => hα0) (fun _ => hαm) (fun _ => hdet) (fun _ => hloc) (fun _ => measurable_const)
    (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ => measurable_const) (Eventually.of_forall fun ω => ?_)
  · rw [show Sec6.explored (fun _ : Fin 1 => α) (fun _ _ => (q : ℝ≥0∞)) = fun ω => α ω '' Icc 0 q ∩ H from
      funext (StripMark.explored_const α q)] at h
    exact ⟨h.1, fun s hs => h.2 s hs⟩
  · rw [StripMark.explored_const, sdiff_inter_self_eq_sdiff]
    exact QuantumZipper.isOpen_H.sdiff (isCompact_Icc.image (hαc ω)).isClosed

omit [IsProbabilityMeasure P] in
/-- Every point of a path range from a real seed connects to `∞` through the range and the closed lower half-plane. -/
theorem ae_not_isBounded_lowerUnion_range {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω))
    (hα0 : ∀ ω, α ω 0 = 0) (him : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (α ω t).im) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (α ω '' Icc 0 q ∩ H),
      ¬ IsBounded (connectedComponentIn (lowerUnion (α ω '' Icc 0 q ∩ H)) z) := by
  filter_upwards [him] with ω hω
  have h := Sec6.not_isBounded_lowerUnion_explored (η := fun _ : Fin 1 => α) (τ := fun _ _ => (q : ℝ≥0∞))
    (ω := ω) (fun _ => hαc ω) (fun _ => by rw [hα0]; simp) (fun _ t => hω t)
  rwa [StripMark.explored_const] at h

/-- **Nested local-set boundary comparison for two stopped ranges** (Proposition 3.8 twice, through the union): for
two paths with Lemma 6.2's inputs, almost surely the harmonic representatives of the local-set means of
`A = α([0, q₁]) ∩ ℍ` and `B = β([0, q₂]) ∩ ℍ` agree at the boundary at every common point where `A` and `B` locally
coincide. -/
theorem ae_tendsto_sub_ranges (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {α β : Ω → ℝ≥0 → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (X ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α X P) (hαim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (α ω t).im)
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (X ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β X P) (hβim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (β ω t).im) (q₁ q₂ : ℝ≥0)
    {gA gB : Ω → DistOn upperHalfPlaneOpens} (hgA : IsLocalSetMean (fun ω => α ω '' Icc 0 q₁ ∩ H) X P gA)
    (hgB : IsLocalSetMean (fun ω => β ω '' Icc 0 q₂ ∩ H) X P gB) :
    ∀ᵐ ω ∂P, ∀ vA vB : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd vA (H \ (α ω '' Icc 0 q₁ ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (α ω '' Icc 0 q₁ ∩ H) → gA ω φ = ∫ z, vA z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ (β ω '' Icc 0 q₂ ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (β ω '' Icc 0 q₂ ∩ H) → gB ω φ = ∫ z, vB z * φ z) →
      ∀ z₀ ∈ α ω '' Icc 0 q₁ ∩ H, z₀ ∈ β ω '' Icc 0 q₂ ∩ H →
      (∃ r > 0, β ω '' Icc 0 q₂ ∩ H ∩ ball z₀ r ⊆ α ω '' Icc 0 q₁ ∩ H) →
      (∃ r > 0, α ω '' Icc 0 q₁ ∩ H ∩ ball z₀ r ⊆ β ω '' Icc 0 q₂ ∩ H) →
      Tendsto (fun z => vA z - vB z) (𝓝[H \ (α ω '' Icc 0 q₁ ∩ H ∪ β ω '' Icc 0 q₂ ∩ H)] z₀) (𝓝 0) := by
  obtain ⟨hAloc, hAdet⟩ := isLocalSet_range_and_aeDetermined hX hαc hα0 hαm hαdet hαloc q₁
  obtain ⟨hBloc, hBdet⟩ := isLocalSet_range_and_aeDetermined hX hβc hβ0 hβm hβdet hβloc q₂
  have h := SideHeightBox.ae_tendsto_sub_of_locals hX (StripMark.measurable_range hαc hαm q₁)
    (StripMark.measurable_range hβc hβm q₂) hAloc hBloc hAdet hBdet
    (ae_not_isBounded_lowerUnion_range hαc hα0 hαim q₁) (ae_not_isBounded_lowerUnion_range hβc hβ0 hβim q₂)
    hgA hgB
  filter_upwards [h] with ω hω vA vB hvA hgvA hvB hgvB z₀ hz₁ hz₂ hl₁ hl₂
  obtain ⟨r₁, hr₁, hs₁⟩ := hl₁
  obtain ⟨r₂, hr₂, hs₂⟩ := hl₂
  exact hω vA vB hvA hgvA hvB hgvB z₀ (Or.inl hz₁) (Or.inl hz₂) ⟨r₁, hr₁, fun w hw => hs₁ hw⟩
    ⟨r₂, hr₂, fun w hw => hs₂ hw⟩

/-- **(RS13.3) almost surely: `β` has points outside the complete range of `α` at arbitrarily late times.** Two paths
with Lemma 6.2's inputs for the centred field `X`; almost surely simple transient generating traces of continuous
drivers, with first-visit times `T` decreasing strictly along both; at the stops of countable unbounded sets `Q₁`, `Q₂`
the harmonic representatives of the local-set means of the stopped ranges have the single-path side heights (angle
`θ₁ ∈ [−π/2, π/2)` for `α` at its points after `t₀`, angle `π/2` for `β`). The countably many probability-one events
(side heights, and the nested boundary comparison of every pair of stopped ranges, `ae_tendsto_sub_ranges`) are
intersected before the arc and the rational times are selected (`late_of_sideHeights`). -/
theorem ae_late_of_sideHeights (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {α β : Ω → ℝ≥0 → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (X ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α X P) (hαim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (α ω t).im)
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (X ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β X P) (hβim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (β ω t).im)
    {W₁ W₂ : Ω → ℝ≥0 → ℝ} (T : Ω → ℂ → ℝ≥0∞)
    (hpath : ∀ᵐ ω ∂P, IsGeneratingTrace (W₁ ω) ⊤ (α ω) ∧ Continuous (W₁ ω) ∧ W₁ ω 0 = 0 ∧
      IsGeneratingTrace (W₂ ω) ⊤ (β ω) ∧ Continuous (W₂ ω) ∧ W₂ ω 0 = 0 ∧ Injective (α ω) ∧ Injective (β ω) ∧
      (∀ t, 0 < t → α ω t ∈ H) ∧ Tendsto (fun t => ‖α ω t‖) atTop atTop ∧
      Tendsto (fun t => ‖β ω t‖) atTop atTop ∧ StrictAntiOn (fun t => T ω (α ω t)) (Ioi 0) ∧
      StrictAntiOn (fun t => T ω (β ω t)) (Ioi 0))
    {κ θ₁ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(π / 2) ≤ θ₁) (hθ₁' : θ₁ < π / 2) {u₀ : ℂ → ℝ}
    {t₀ : ℝ≥0} {Q₁ Q₂ : Set ℝ≥0} (hQ₁c : Q₁.Countable) (hQ₂c : Q₂.Countable) (hQ₁ : ∀ a, ∃ q ∈ Q₁, a ≤ q)
    (hQ₂ : ∀ a, ∃ q ∈ Q₂, a < q) {gα gβ : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgα : ∀ q ∈ Q₁, IsLocalSetMean (fun ω => α ω '' Icc 0 q ∩ H) X P (gα q))
    (hgβ : ∀ q ∈ Q₂, IsLocalSetMean (fun ω => β ω '' Icc 0 q ∩ H) X P (gβ q))
    (hside₁ : ∀ q ∈ Q₁, ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (α ω '' Icc 0 q ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (α ω '' Icc 0 q ∩ H) → gα q ω φ = ∫ z, v z * φ z) →
      ∀ s, t₀ < s → s < q → HasSideHeights κ θ₁ (α ω) 0 (W₁ ω) q (α ω s) v u₀)
    (hside₂ : ∀ q ∈ Q₂, ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (β ω '' Icc 0 q ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (β ω '' Icc 0 q ∩ H) → gβ q ω φ = ∫ z, v z * φ z) →
      ∀ s, 0 < s → s < q → HasSideHeights κ (π / 2) (β ω) 0 (W₂ ω) q (β ω s) v u₀) :
    ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ closure (range (α ω)) := by
  classical
  -- harmonic representatives of the stopped means
  set vα : ℝ≥0 → Ω → ℂ → ℝ := fun q ω =>
    if hq : IsHarmonicDistOn (gα q ω) (H \ (α ω '' Icc 0 q ∩ H)) then hq.choose else 0 with hvαdef
  set vβ : ℝ≥0 → Ω → ℂ → ℝ := fun q ω =>
    if hq : IsHarmonicDistOn (gβ q ω) (H \ (β ω '' Icc 0 q ∩ H)) then hq.choose else 0 with hvβdef
  have hvα : ∀ q ∈ Q₁, ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (vα q ω) (H \ (α ω '' Icc 0 q ∩ H)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (α ω '' Icc 0 q ∩ H) →
        gα q ω φ = ∫ z, vα q ω z * φ z := by
    intro q hq
    filter_upwards [(hgα q hq).2.1] with ω hω
    simp only [hvαdef, hω, ↓reduceDIte]
    exact hω.choose_spec
  have hvβ : ∀ q ∈ Q₂, ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (vβ q ω) (H \ (β ω '' Icc 0 q ∩ H)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (β ω '' Icc 0 q ∩ H) →
        gβ q ω φ = ∫ z, vβ q ω z * φ z := by
    intro q hq
    filter_upwards [(hgβ q hq).2.1] with ω hω
    simp only [hvβdef, hω, ↓reduceDIte]
    exact hω.choose_spec
  -- one probability-one event for the countably many statements
  have h1 := (ae_ball_iff hQ₁c).2 fun q hq => (hvα q hq).and (hside₁ q hq)
  have h2 := (ae_ball_iff hQ₂c).2 fun q hq => (hvβ q hq).and (hside₂ q hq)
  have h3 := (ae_ball_iff hQ₁c).2 fun q₁ hq₁ => (ae_ball_iff hQ₂c).2 fun q₂ hq₂ =>
    ae_tendsto_sub_ranges hX hαc hα0 hαm hαdet hαloc hαim hβc hβ0 hβm hβdet hβloc hβim q₁ q₂ (hgα q₁ hq₁)
      (hgβ q₂ hq₂)
  filter_upwards [hpath, h1, h2, h3] with ω hp hω1 hω2 hω3
  obtain ⟨hg₁, hW₁c, hW₁0, hg₂, hW₂c, hW₂0, hαi, hβi, hαH, hαu, hβu, hTα, hTβ⟩ := hp
  exact late_of_sideHeights (T ω) hg₁ hW₁c hW₁0 hg₂ hW₂c hW₂0 hαi hβi hαH hαu hβu hTα hTβ hκ hκ4 hθ₁ hθ₁' hQ₁ hQ₂
    (v₁ := fun q => vα q ω) (v₂ := fun q => vβ q ω)
    (fun q hq s hs1 hs2 => (hω1 q hq).2 _ (hω1 q hq).1.1 (hω1 q hq).1.2 s hs1 hs2)
    (fun q hq s hs1 hs2 => (hω2 q hq).2 _ (hω2 q hq).1.1 (hω2 q hq).1.2 s hs1 hs2)
    (fun q₁ hq₁ q₂ hq₂ z₀ hz₁ hz₂ hl₁ hl₂ => hω3 q₁ hq₁ q₂ hq₂ _ _ (hω1 q₁ hq₁).1.1 (hω1 q₁ hq₁).1.2
      (hω2 q₂ hq₂).1.1 (hω2 q₂ hq₂).1.2 z₀ hz₁ hz₂ hl₁ hl₂)

end Prob

/-! ### The side heights of the angle-varying path in the form of `ae_late_of_sideHeights` -/

section Stage

universe u

open StripSideHeightProb Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ}
  {t₀ : ℝ≥0} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **(S) for the angle-varying path at the stop `t₀ + r`, read with its global driver** (the input `hside₁` of
`ae_late_of_sideHeights` at the stop `t₀ + r`): from `StripMark.ae_hasSideHeights_stage_of_lemma62`, when almost surely
`αc` is a simple transient generating trace of a continuous driver `W₁` that agrees on `[0, t₀ + r]` with the
concatenated record driver of the stopped program. -/
theorem ae_sideHeights_stage (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (r : ℝ≥0) (hT : 0 < t₀ + r) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hgood : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E)
    {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => αc ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hloc : Sec6.IsEntranceHistoryLocal αc (WholeField.centredField h u₀) P) {W₁ : Ω → ℝ≥0 → ℝ}
    (hW : ∀ᵐ ω ∂P, IsGeneratingTrace (W₁ ω) ⊤ (αc ω) ∧ Continuous (W₁ ω) ∧ W₁ ω 0 = 0 ∧ Injective (αc ω) ∧
      (∀ t, 0 < t → αc ω t ∈ H) ∧ ∀ s : ℝ≥0, s ≤ t₀ + r →
        W₁ ω s = catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) s)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => αc ω '' Icc 0 (t₀ + r) ∩ H) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (αc ω '' Icc 0 (t₀ + r) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (αc ω '' Icc 0 (t₀ + r) ∩ H) →
        g ω φ = ∫ z, v z * φ z) →
      ∀ s, t₀ < s → s < t₀ + r → HasSideHeights κ θ (αc ω) 0 (W₁ ω) (t₀ + r) (αc ω s) v u₀ := by
  have htr : ∀ᵐ ω ∂P, ∃ (W' : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞), ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ' ∧
      IsGeneratingTrace W' ζ' (αc ω) ∧ ∀ s : ℝ≥0, s ≤ t₀ + r →
        W' s = catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) s := by
    filter_upwards [hW] with ω hω
    exact ⟨W₁ ω, ⊤, ENNReal.coe_lt_top, hω.1, hω.2.2.2.2.2⟩
  have hS' := StripMark.ae_hasSideHeights_stage_of_lemma62 hκ hb hh hS hreg r hT hu₀ hgood hαc hα0 hαm hdet hloc
    htr hg
  filter_upwards [hS', hgood, hW] with ω hω hωg hωW v hv hgv s hs1 hs2
  obtain ⟨hg₁, hW₁c, hW₁0, hαi, hαH, hagree⟩ := hωW
  exact hω hωg v hv hgv (W₁ ω) (αc ω) ⊤ hg₁ hW₁c.continuousOn hW₁0 hagree hαi.injOn ENNReal.coe_lt_top s hs1
    ENNReal.coe_lt_top (hαH s (lt_of_le_of_lt zero_le hs1))

end Stage

end RS133

end Sec7

end InteractingSLE
