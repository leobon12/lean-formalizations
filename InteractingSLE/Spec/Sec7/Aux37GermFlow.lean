/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux119Heights

/-!
# Aux. lemma 37 at one rational witness: the flow-side germ of the marked union mean (G1)

Packet PROVE-STRIPSYS36, item (G1). Specification §6.2, Aux. lemma 36 ("Boundary data on the incoming sides",
`source/spec/p193-240.md` L60, p. 196) and Aux. lemma 37's proof (L118, p. 199: "At time `r` the mean on this collar
has the canonical flow-side germ"):

> At a point of an open incoming side away from its angle marks and attachments, the old counterflow range has
> positive distance. Compact separation from other flow pieces follows from injectivity, the open-disjoint selected
> sides, and the common-contact-order observation above. The marked single-piece boundary comparison therefore gives
> its canonical flow height and winding term. One may equivalently first compare the full flow union with that piece
> and then use part (i) of Aux. lemma 35.

The exploration of Aux. lemma 37 at a deterministic time `t` is the union `A ∪ (α ∪ β) ∩ ℍ` of a local set `A` (the
counterflow hull at `t`) with the complete marked wall union `wallUnion` (Aux. lemma 119's walls; field-determined by
Lemma 6.2, `Aux119Nested.isLocalSet_wallUnion`). This file proves, by the source's second route:

* **`ae_tendsto_sub_wallUnion`** (Proposition 3.8 for the union and the walls): `A` and the walls are conditionally
  independent given the field (the walls are field-determined, `Sec6.condIndepEv_of_le_aeSigma`), so for every version
  `g` of the union mean, almost surely its harmonic representative minus the walls' representative tends to `0` at
  every wall point near which `A` is absent (`IsLocalSetMean.ae_tendsto_sub_of_union`).
* **`ae_ownHeights_union`** (G1): on one probability-one event, for every flow chart of a change pocket of the walls
  and every wall point off the other wall and the exceptional own times at positive distance from `A`, the union
  mean has the wall's own height along the pocket approach: `λ − θ_Lχ` on the left wall (the pocket on its right),
  `−λ − θ_Rχ` on the right wall (the pocket on its left), in the wall's own coordinate at a rational own time beyond
  the point — Aux. lemma 119's own heights (`Aux119Heights.ae_ownHeights`) transported to the union.

Conditional helpers; they replace no source theorem. No Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Bornology Function
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux37Germ

open QuantumZipper (H Hbar logDerivFwd fwdMap chiC)
open PocketCoord PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux119Heights

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 3.8 for the union of a local set with the complete wall union**: if `A` is a hitting-measurable local
set and the walls have Lemma 6.2's inputs and are transient, then for versions `g` of the union mean and `gU` of the
walls' mean, almost surely, for all harmonic representatives `v` (off the union) and `w` (off the walls),
`v − w → 0` along `ℍ ∖ (A ∪ walls)` at every wall point near which `A` is empty. -/
theorem ae_tendsto_sub_wallUnion (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {Lw Rw : Ω → ℝ≥0 → ℂ}
    (hLc : ∀ ω, Continuous (Lw ω)) (hL0 : ∀ ω, Lw ω 0 = 0) (hLm : ∀ t, Measurable fun ω => Lw ω t)
    (hLdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Lw ω t) =ᵐ[P] fun ω => f (X ω))
    (hLloc : Sec6.IsEntranceHistoryLocal Lw X P) (hLim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Lw ω t).im)
    (hRc : ∀ ω, Continuous (Rw ω)) (hR0 : ∀ ω, Rw ω 0 = 0) (hRm : ∀ t, Measurable fun ω => Rw ω t)
    (hRdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Rw ω t) =ᵐ[P] fun ω => f (X ω))
    (hRloc : Sec6.IsEntranceHistoryLocal Rw X P) (hRim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Rw ω t).im)
    (htr : ∀ᵐ ω ∂P, Tendsto (Lw ω) atTop (cobounded ℂ) ∧ Tendsto (Rw ω) atTop (cobounded ℂ))
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A X P)
    {g gU : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => A ω ∪ wallUnion Lw Rw ω) X P g)
    (hgU : IsLocalSetMean (wallUnion Lw Rw) X P gU) :
    ∀ᵐ ω ∂P, ∀ v w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A ω ∪ wallUnion Lw Rw ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ wallUnion Lw Rw ω) → g ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd w (H \ wallUnion Lw Rw ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion Lw Rw ω → gU ω φ = ∫ z, w z * φ z) →
      ∀ z₀ ∈ wallUnion Lw Rw ω, (∃ ε > 0, A ω ∩ ball z₀ ε = ∅) →
        Tendsto (fun z => v z - w z) (𝓝[H \ (A ω ∪ wallUnion Lw Rw ω)] z₀) (𝓝 0) := by
  obtain ⟨hWm, hWloc, hWdet⟩ := isLocalSet_wallUnion hX hLc hL0 hLm hLdet hLloc hRc hR0 hRm hRdet hRloc htr
  have hci : LQGMetric.CondIndepEv (MeasurableSpace.comap X inferInstance) (MeasurableSpace.comap A hittingSigma)
      (MeasurableSpace.comap (wallUnion Lw Rw) hittingSigma) P :=
    (Sec6.condIndepEv_of_le_aeSigma hX.measurable.comap_le hAm.comap_le hWdet).symm
  have hunb := ae_not_isBounded_lowerUnion_wallUnion hLc hL0 hLim hRc hR0 hRim
  filter_upwards [IsLocalSetMean.ae_tendsto_sub_of_union hX hAm hWm hci hAloc hWloc hunb hg hgU, hAloc.2.1,
    hWloc.2.1] with ω ⟨u, hu, hur, hul⟩ hAo hWo v w hv hvr hw hwr z₀ hz₀ ⟨ε, hε, hAε⟩
  have hO : IsOpen (H \ (A ω ∪ wallUnion Lw Rw ω)) := by
    have e : H \ (A ω ∪ wallUnion Lw Rw ω) = (H \ A ω) ∩ (H \ wallUnion Lw Rw ω) := by
      ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
    rw [e]
    exact hAo.2.inter hWo.2
  have hAW : A ω ∩ ball z₀ ε ⊆ wallUnion Lw Rw ω := by rw [hAε]; exact empty_subset _
  refine Sec7.tendsto_sub_of_union_means (g := g ω) (ua := fun _ => 0) hO subset_rfl
    (sdiff_subset_sdiff_right subset_union_right) hv hvr hw hwr (fun z _ => InnerProductSpace.harmonicAt_const 0)
    (fun φ _ => by simp) hu hur tendsto_const_nhds (hul z₀ (Or.inl hz₀) ⟨ε, hε, hAW⟩)

/-- **(G1) The flow-side germ of the marked union mean** (Aux. lemma 36's incoming-side boundary data, through the full
flow union and Aux. lemma 119's own heights). For two transient walls with Lemma 6.2's inputs, a hitting-measurable
local set `A`, versions `g` of the mean of `A ∪ walls`, `gU` of the walls' mean and `gL q`, `gR q` of the prefix means,
and the single-path side heights of each wall point off the exceptional own times at some rational stop: almost
surely, for every harmonic representative `v` of the union mean, every flow chart of a change pocket of the walls
(pocket on the left of the right wall) and continuous drivers from `0` generating the walls, every left-wall point
`Lw s` off the right wall and `SL` at positive distance from `A` has an own time `q > s` with
`v + u₀ + χ Im (log f_q′) → λ − θL(s)χ` along the pocket approach; every right-wall point likewise with
`−λ − θR(s)χ`. -/
theorem ae_ownHeights_union (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {Lw Rw : Ω → ℝ≥0 → ℂ}
    (hLc : ∀ ω, Continuous (Lw ω)) (hL0 : ∀ ω, Lw ω 0 = 0) (hLm : ∀ t, Measurable fun ω => Lw ω t)
    (hLdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Lw ω t) =ᵐ[P] fun ω => f (X ω))
    (hLloc : Sec6.IsEntranceHistoryLocal Lw X P) (hLim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Lw ω t).im)
    (hRc : ∀ ω, Continuous (Rw ω)) (hR0 : ∀ ω, Rw ω 0 = 0) (hRm : ∀ t, Measurable fun ω => Rw ω t)
    (hRdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Rw ω t) =ᵐ[P] fun ω => f (X ω))
    (hRloc : Sec6.IsEntranceHistoryLocal Rw X P) (hRim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Rw ω t).im)
    (htr : ∀ᵐ ω ∂P, Tendsto (Lw ω) atTop (cobounded ℂ) ∧ Tendsto (Rw ω) atTop (cobounded ℂ))
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A X P)
    {g gU : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => A ω ∪ wallUnion Lw Rw ω) X P g)
    (hgU : IsLocalSetMean (wallUnion Lw Rw) X P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Lw ω '' Icc 0 q ∩ H) X P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Rw ω '' Icc 0 q ∩ H) X P (gR q))
    {κ : ℝ} {u₀ : ℂ → ℝ} {θL θR : ℝ≥0 → ℝ} {SL SR : Set ℝ≥0} {WL WR : Ω → ℝ≥0 → ℝ}
    (hsideL : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, Lw ω s ∉ range (Rw ω) → s ∉ SL → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (Lw ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (Lw ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          gL q ω φ = ∫ z, v z * φ z) →
        HasSideHeights κ (θL s) (Lw ω) 0 (WL ω) q (Lw ω s) v u₀)
    (hsideR : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, Rw ω s ∉ range (Lw ω) → s ∉ SR → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (Rw ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (Rw ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          gR q ω φ = ∫ z, v z * φ z) →
        HasSideHeights κ (θR s) (Rw ω) 0 (WR ω) q (Rw ω s) v u₀) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A ω ∪ wallUnion Lw Rw ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ wallUnion Lw Rw ω) → g ω φ = ∫ z, v z * φ z) →
      ∀ (r : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (Rw ω) (Lw ω) r Ψ c →
      changePocket (Rw ω) (Lw ω) r ⊆ leftSideOf (range (Rw ω)) →
      IsGeneratingTrace (WL ω) ⊤ (Lw ω) → Continuous (WL ω) → WL ω 0 = 0 →
      IsGeneratingTrace (WR ω) ⊤ (Rw ω) → Continuous (WR ω) → WR ω 0 = 0 →
      (∀ s : ℝ≥0, Lw ω s ∉ range (Rw ω) → s ∉ SL → (∃ ε > 0, A ω ∩ ball (Lw ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ => WL ω t.toNNReal) q z).im)
          (𝓝[changePocket (Rw ω) (Lw ω) r] (Lw ω s)) (𝓝 (sleLambda κ - θL s * chiC κ))) ∧
      (∀ s : ℝ≥0, Rw ω s ∉ range (Lw ω) → s ∉ SR → (∃ ε > 0, A ω ∩ ball (Rw ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ => WR ω t.toNNReal) q z).im)
          (𝓝[changePocket (Rw ω) (Lw ω) r] (Rw ω s)) (𝓝 (-sleLambda κ - θR s * chiC κ))) := by
  have hcmp := ae_tendsto_sub_wallUnion hX hLc hL0 hLm hLdet hLloc hLim hRc hR0 hRm hRdet hRloc hRim htr hAm hAloc
    hg hgU
  have hown := ae_ownHeights hX hLc hL0 hLm hLdet hLloc hLim hRc hR0 hRm hRdet hRloc hRim htr hgU hgL hgR hsideL
    hsideR
  filter_upwards [hcmp, hown, hgU.2.1] with ω hωc hωo hωU v hv hvr r Ψ c hF hCl htrL hWLc hWL0 htrR hWRc hWR0
  obtain ⟨hvW, hvWr⟩ := harmRep_spec hωU
  set vW := harmRep (gU ω) (H \ wallUnion Lw Rw ω)
  obtain ⟨vL, vR, hL, hR⟩ := hωo vW hvW hvWr r Ψ c hF hCl htrL hWLc hWL0 htrR hWRc hWR0
  have hCW := changePocket_subset_H_diff hF.config
  -- the pocket approach stays off the union near a wall point at positive distance from `A`
  have hle : ∀ z₀ : ℂ, ∀ ε > 0, A ω ∩ ball z₀ ε = ∅ →
      𝓝[changePocket (Rw ω) (Lw ω) r] z₀ ≤ 𝓝[H \ (A ω ∪ wallUnion Lw Rw ω)] z₀ := by
    intro z₀ ε hε hAε
    refine nhdsWithin_le_of_mem (mem_nhdsWithin.2 ⟨ball z₀ ε, isOpen_ball, mem_ball_self hε, ?_⟩)
    rintro z ⟨hzb, hzC⟩
    obtain ⟨hzH, hzW⟩ := hCW hzC
    refine ⟨hzH, fun hz => hz.elim (fun hzA => ?_) fun hzU => hzW hzU.1⟩
    have : z ∈ A ω ∩ ball z₀ ε := ⟨hzA, hzb⟩
    rw [hAε] at this
    exact this
  refine ⟨fun s hsR hsS ⟨ε, hε, hAε⟩ => ?_, fun s hsL hsS ⟨ε, hε, hAε⟩ => ?_⟩
  · obtain ⟨q, hsq, hd, hh⟩ := hL s hsR hsS
    have hs0 : 0 < s := pos_of_ne_zero fun h0 => hsR ⟨0, by rw [h0, hL0, hR0]⟩
    have hmem : Lw ω s ∈ wallUnion Lw Rw ω := ⟨Or.inl ⟨s, rfl⟩, hF.config.left.2.2.2.1 s hs0⟩
    have h1 := (hωc v vW hv hvr hvW hvWr _ hmem ⟨ε, hε, hAε⟩).mono_left (hle _ ε hε hAε)
    have h2 := (h1.add hd).add hh
    rw [zero_add, zero_add] at h2
    exact ⟨q, hsq, h2.congr fun z => by ring⟩
  · obtain ⟨q, hsq, hd, hh⟩ := hR s hsL hsS
    have hs0 : 0 < s := pos_of_ne_zero fun h0 => hsL ⟨0, by rw [h0, hR0, hL0]⟩
    have hmem : Rw ω s ∈ wallUnion Lw Rw ω := ⟨Or.inr ⟨s, rfl⟩, hF.config.right.2.2.2.1 s hs0⟩
    have h1 := (hωc v vW hv hvr hvW hvWr _ hmem ⟨ε, hε, hAε⟩).mono_left (hle _ ε hε hAε)
    have h2 := (h1.add hd).add hh
    rw [zero_add, zero_add] at h2
    exact ⟨q, hsq, h2.congr fun z => by ring⟩

end InteractingSLE.Sec7.Aux37Germ
