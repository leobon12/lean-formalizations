/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma57
import InteractingSLE.Spec.Sec4.Aux25Term

/-!
# Lemma 5.6 for one angle: continuity and simplicity of a strip flow line

Packet PROVE-SEC5-F. Specification Lemma 5.6 (`source/spec/p097-144.md` L867, p. 137): "Let `η` be an angle-varying
flow line of `h` [...] non-boundary-intersecting. Then `η` is almost surely simple and continuous." Its proof
(L885): "Induct on the number `ℓ` of pieces [...] For the first piece, noncolliding seed entrance and bounded-gap
localization transfer ordinary SLE continuity and simplicity."

For one piece (`ℓ = 1`) this file proves the continuity and simplicity clause for every flow line of a strip field
(`IsStripFlowLineAt`, the frozen `IsFlowLine` of the `E`-transported data at angle `α + θ`), for `0 < κ < 4`:

* `IsStripFlowLineAt.ae_continuousOn_injOn`: almost surely `η(0) = 0` and `η` is continuous and injective on its
  whole available interval `[0, ζ]`. Continuity is the generating-trace conjunct of the frozen `IsFlowLine`;
  simplicity is Aux. lemma 25 (`Theorem15.aux25Statement`, proved for every finite-force integrated evolution with
  `κ < 4`), applied to the flow line's own evolution.
* `IsStripFlowLineAt.ae_lemma56_horizon`: the form used by Lemma 5.7's proof: on any horizon `T` before which the
  flow line is alive, `s ↦ η(s⁺)` is continuous on `[0, T]` and injective on `[0, T)`.

Consequence: `lemma57_of_counterflowSegmentRestart'`, PROVE-SEC5-E's Lemma 5.7 (one angle) without its Lemma 5.6
hypothesis `ha` (only `0 < T` is kept). It is still a conditional helper (it takes the cross-conditioning carrier
`CounterflowSegmentRestartStatement` and Aux. 7 for `κ'`) and replaces no source theorem.

Angle-varying flow lines (`ℓ ≥ 2`) need the conditional law of each later piece given the earlier ones; for the frozen
staged histories it is the per-stage kernel of `IsStagedHistory`, whose boundary data are pinned only existentially
(see the handoff).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Sec5

open Sec4 Restart MarkovOther

/-- **Lemma 5.6 for one angle (continuity and simplicity)**, `0 < κ < 4`: almost surely the flow line `η` of a strip
field (`IsStripFlowLineAt`, any frame `α`, angle `θ`, boundary data) starts at `0` and is continuous and injective on
its available interval `[0, ζ]`. -/
theorem IsStripFlowLineAt.ae_continuousOn_injOn {κ α θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hη : IsStripFlowLineAt κ α θ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, η ω 0 = 0 ∧ ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} ∧
      InjOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} := by
  obtain ⟨_, 𝓕, W, VL, VR, B, _, hcpl, htr⟩ := hη
  have hword := Theorem15.isOrderedForceWord_flowLine (stripHData κ bL bU) (stripHJumps JL JU) 0
  have h25 := Theorem15.aux25Statement κ hκ hκ4 _ _ _ _ hword P 𝓕 W VL VR B ζ hcpl.1
  filter_upwards [h25, htr] with ω h25ω htrω
  have htr0 : IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htrω
  exact ⟨htr0.1, htr0.2.1, h25ω _ htr0⟩

/-- A real horizon `T` all of whose earlier times are alive is at most the lifetime. -/
theorem le_of_forall_lt_imp_lt {T : ℝ} {ζ : ℝ≥0∞} (hT : ∀ t : ℝ≥0, (t : ℝ) < T → (t : ℝ≥0∞) < ζ) :
    ((T.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ := by
  refine le_of_forall_lt fun c hc => ?_
  lift c to ℝ≥0 using ne_top_of_lt hc
  have hcT : (c : ℝ) < T := by
    have h1 : c < T.toNNReal := by exact_mod_cast hc
    have h2 := (Real.lt_toNNReal_iff_coe_lt).1 h1
    exact h2
  exact hT c hcT

/-- **Lemma 5.6 for one angle, on a horizon**: if every time before `T` is alive, then `s ↦ η(s⁺)` is continuous on
`[0, T]` and injective on `[0, T)` (the hypothesis `ha` of Lemma 5.7's proof). -/
theorem IsStripFlowLineAt.ae_lemma56_horizon {κ α θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hη : IsStripFlowLineAt κ α θ bL bU JL JU P h η ζ) {T : Ω → ℝ}
    (hT : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) < T ω → (t : ℝ≥0∞) < ζ ω) :
    ∀ᵐ ω ∂P, ContinuousOn (fun s : ℝ => η ω s.toNNReal) (Icc 0 (T ω)) ∧
      InjOn (fun s : ℝ => η ω s.toNNReal) (Ico 0 (T ω)) := by
  filter_upwards [hη.ae_continuousOn_injOn hκ hκ4, hT] with ω ⟨_, hc, hinj⟩ hTω
  have hTζ := le_of_forall_lt_imp_lt hTω
  have hmaps : MapsTo (fun s : ℝ => s.toNNReal) (Icc 0 (T ω)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} :=
    fun s hs => le_trans (by exact_mod_cast Real.toNNReal_le_toNNReal hs.2) hTζ
  refine ⟨hc.comp continuous_real_toNNReal.continuousOn hmaps, fun s hs s' hs' hss' => ?_⟩
  have h1 := hinj (hmaps (Ico_subset_Icc_self hs)) (hmaps (Ico_subset_Icc_self hs')) hss'
  have h2 : ((s.toNNReal : ℝ≥0) : ℝ) = ((s'.toNNReal : ℝ≥0) : ℝ) :=
    congrArg (fun x : ℝ≥0 => (x : ℝ)) h1
  rwa [Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ hs'.1] at h2

variable {κ α x₀ a b a' b' θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}

/-- **Lemma 5.7 for one angle, with Lemma 5.6 discharged** (conditional helper; PROVE-SEC5-E's
`lemma57_of_counterflowSegmentRestart` without its Lemma 5.6 hypothesis): from the cross-conditioning carrier,
Aux. 7 for `κ' = 16/κ`, the counterflow's continuity and transience and the conditional independence, on every
positive horizon `T` before which the flow line is alive and in `ℍ`, the counterflow first hits the explored flow-line
segment at its tip, contains `η([0, T])` and visits its points in reverse chronological order. -/
theorem lemma57_of_counterflowSegmentRestart' (hR : CounterflowSegmentRestartStatement.{u})
    (h7 : Aux7Statement.{0} (16 / κ)) (hκ : 0 < κ) (hκ4 : κ < 4) (hbd : IsFig51Bounds κ a b a' b')
    (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2) (hhm : Measurable h) (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hη : IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {T : Ω → ℝ} (hT0 : ∀ᵐ ω ∂P, 0 < T ω)
    (hT : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < T ω → (t : ℝ≥0∞) < ζ ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T ω → η ω t ∈ H) :
    ∀ᵐ ω ∂P,
      (∀ τ ∈ Icc 0 (T ω), IsFirstHitPoint (stripCounterflowPath (Real.exp (π * x₀)) (γ' ω)) 1
          (lowerLineH ∪ (fun s : ℝ => η ω s.toNNReal) '' Icc 0 τ) (η ω τ.toNNReal)) ∧
      (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (T ω) ⊆
        stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) '' Icc 0 1 ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T ω →
        ∃ v ∈ Icc (0 : ℝ) 1, stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) v = η ω t.toNNReal ∧
          ∀ w ∈ Icc 0 v, stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) w ≠ η ω s.toNNReal := by
  have h56 := hη.ae_lemma56_horizon hκ hκ4 (hT.mono fun ω hω => hω.1)
  refine lemma57_of_counterflowSegmentRestart hR h7 hκ hκ4 hbd hθ₁ hθ₂ hhm hh hη hcf htr' hci hγ hT ?_
  filter_upwards [hT0, h56] with ω h0 h1
  exact ⟨h0, h1.1, h1.2⟩

end InteractingSLE.Sec5
