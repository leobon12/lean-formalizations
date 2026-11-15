/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37GermFlowStrip
import InteractingSLE.Spec.Sec7.Aux37GermBranch

/-!
# Aux. lemma 37 at one rational witness: the counterflow-side comparison (G2) and the flat clock (FC)

Packet PROVE-STRIPSYS36, items (G2) and (FC). Specification §6.2, Aux. lemma 36 ("Boundary data on the exposed
counterflow part", `source/spec/p193-240.md` L62, p. 196) and Aux. lemma 37's proof (L104–L118, pp. 198–199).

* **`ae_tendsto_sub_hull`** (G2's comparison, Proposition 3.8 toward the hull): for a hitting-measurable local set `A`
  whose lower union has only unbounded components (the counterflow hull: `not_isBounded_lowerUnion_cfHull`) and the
  complete walls, every version of the mean of `A ∪ walls` minus the mean of `A` alone tends to `0` at every point of
  `A` near which the walls lie in `A` ("near `z₀` the exploration is the counterflow hull": the visited arc). With it,
  the counterflow-side germ of the union mean is the counterflow hull's own germ; the latter (the old counterflow
  heights `±λ′ − πχ` on the exposed sides, read in the counterflow coordinate, with the traversal-side claim (PFI3)) is
  not proved here.
* **`FlatClockStatement`** (FC, a named input with its exact type; it waits for the marked union law at stopping times,
  PROVE-STRIPSYS35): for an increasing exploration `E t` and versions `g t` of its means, almost surely, between two
  deterministic times `r ≤ s`, the harmonic representatives of `g r` and `g s` agree on every component of `ℍ ∖ E s`
  that is also a component of `ℍ ∖ E r` (p. 198: "one version of the harmonic mean which is constant […] on every
  interval on which it remains globally active and its component is unchanged"; a component equal at both ends of
  `[r, s]` is unchanged throughout, the exploration being increasing). It is the source's flat clock read at two
  deterministic times, a consequence of the source statement.
* `stripExpl`: the strip exploration `m⁻¹(K′_t) ∪ α ∪ β` to which FC is applied; `eventuallyEq_of_flatClock`: FC's
  conclusion along an approach that stays in one unchanged component (the `hFC` input of `false_of_flat_germs`).

No Theorem 1.2/1.3 (R43, R48). Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Bornology Function
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Aux37Germ

open QuantumZipper (H Hbar chiC)
open LocalSets Aux119Nested

/-! ### The counterflow-side comparison -/

section Hull

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 3.8 toward the local set** (G2's comparison): for a hitting-measurable local set `A` whose lower
union has only unbounded components, two transient walls with Lemma 6.2's inputs, and versions `g` of the mean of
`A ∪ walls` and `gA` of the mean of `A`: almost surely, for all harmonic representatives `v` (off the union) and `w`
(off `A`), `v − w → 0` along `ℍ ∖ (A ∪ walls)` at every point of `A` near which the walls lie in `A`. -/
theorem ae_tendsto_sub_hull (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {Lw Rw : Ω → ℝ≥0 → ℂ}
    (hLc : ∀ ω, Continuous (Lw ω)) (hL0 : ∀ ω, Lw ω 0 = 0) (hLm : ∀ t, Measurable fun ω => Lw ω t)
    (hLdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Lw ω t) =ᵐ[P] fun ω => f (X ω))
    (hLloc : Sec6.IsEntranceHistoryLocal Lw X P)
    (hRc : ∀ ω, Continuous (Rw ω)) (hR0 : ∀ ω, Rw ω 0 = 0) (hRm : ∀ t, Measurable fun ω => Rw ω t)
    (hRdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Rw ω t) =ᵐ[P] fun ω => f (X ω))
    (hRloc : Sec6.IsEntranceHistoryLocal Rw X P)
    (htr : ∀ᵐ ω ∂P, Tendsto (Lw ω) atTop (cobounded ℂ) ∧ Tendsto (Rw ω) atTop (cobounded ℂ))
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A X P)
    (hAunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω), ¬ IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    {g gA : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => A ω ∪ wallUnion Lw Rw ω) X P g)
    (hgA : IsLocalSetMean A X P gA) :
    ∀ᵐ ω ∂P, ∀ v w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A ω ∪ wallUnion Lw Rw ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ wallUnion Lw Rw ω) → g ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd w (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → gA ω φ = ∫ z, w z * φ z) →
      ∀ z₀ ∈ A ω, (∃ ε > 0, wallUnion Lw Rw ω ∩ ball z₀ ε ⊆ A ω) →
        Tendsto (fun z => v z - w z) (𝓝[H \ (A ω ∪ wallUnion Lw Rw ω)] z₀) (𝓝 0) := by
  obtain ⟨hWm, hWloc, hWdet⟩ := isLocalSet_wallUnion hX hLc hL0 hLm hLdet hLloc hRc hR0 hRm hRdet hRloc htr
  have hci : LQGMetric.CondIndepEv (MeasurableSpace.comap X inferInstance)
      (MeasurableSpace.comap (wallUnion Lw Rw) hittingSigma) (MeasurableSpace.comap A hittingSigma) P :=
    Sec6.condIndepEv_of_le_aeSigma hX.measurable.comap_le hAm.comap_le hWdet
  have hg' : IsLocalSetMean (fun ω => wallUnion Lw Rw ω ∪ A ω) X P g := by
    have e : (fun ω => wallUnion Lw Rw ω ∪ A ω) = fun ω => A ω ∪ wallUnion Lw Rw ω :=
      funext fun ω => union_comm _ _
    rw [e]
    exact hg
  filter_upwards [IsLocalSetMean.ae_tendsto_sub_of_union hX hWm hAm hci hWloc hAloc hAunb hg' hgA, hAloc.2.1,
    hWloc.2.1] with ω ⟨u, hu, hur, hul⟩ hAo hWo v w hv hvr hw hwr z₀ hz₀ ⟨ε, hε, hWε⟩
  rw [union_comm (wallUnion Lw Rw ω) (A ω)] at hu hur hul
  have hO : IsOpen (H \ (A ω ∪ wallUnion Lw Rw ω)) := by
    have e : H \ (A ω ∪ wallUnion Lw Rw ω) = (H \ A ω) ∩ (H \ wallUnion Lw Rw ω) := by
      ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
    rw [e]
    exact hAo.2.inter hWo.2
  exact Sec7.tendsto_sub_of_union_means (g := g ω) (ua := fun _ => 0) hO subset_rfl
    (sdiff_subset_sdiff_right subset_union_left) hv hvr hw hwr (fun z _ => InnerProductSpace.harmonicAt_const 0)
    (fun φ _ => by simp) hu hur tendsto_const_nhds (hul z₀ (Or.inl hz₀) ⟨ε, hε, hWε⟩)

omit mΩ in
/-- The counterflow hull's lower union has only unbounded components (every sample). -/
theorem not_isBounded_lowerUnion_cfHull (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) :
    ∀ z ∈ lowerUnion (cfHull W' ζ' t ω), ¬ IsBounded (connectedComponentIn (lowerUnion (cfHull W' ζ' t ω)) z) :=
  Sec5.GlueCond.not_isBounded_lowerUnion_image_negInv (Sec5.GlueCond.isHPHull_hullAt _ _)

end Hull

/-! ### The flat clock -/

section FlatClock

variable {Ω : Type*}

/-- **(FC) The flat clock at two deterministic times** (Aux. lemma 37, p. 198), named input: for an exploration `E t`
and versions `g t` of the means of `E t` for the field `X`, almost surely, for all `r ≤ s` in a countable time set `Q`,
the harmonic representatives of `g r` (off `E r`) and `g s` (off `E s`) agree on every component of `ℍ ∖ E s` that is
also the component of `ℍ ∖ E r` through the same point. -/
def FlatClockStatement [MeasurableSpace Ω] (P : Measure Ω) (Q : Set ℝ≥0) (E : ℝ≥0 → Ω → Set ℂ)
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ r ∈ Q, ∀ s ∈ Q, r ≤ s → ∀ᵐ ω ∂P, ∀ vr vs : ℂ → ℝ,
    InnerProductSpace.HarmonicOnNhd vr (H \ E r ω) →
    (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ E r ω → g r ω φ = ∫ z, vr z * φ z) →
    InnerProductSpace.HarmonicOnNhd vs (H \ E s ω) →
    (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ E s ω → g s ω φ = ∫ z, vs z * φ z) →
    ∀ z ∈ H \ E s ω, connectedComponentIn (H \ E s ω) z = connectedComponentIn (H \ E r ω) z →
      ∀ w ∈ connectedComponentIn (H \ E s ω) z, vr w = vs w

/-- The strip exploration of Aux. lemma 37 at time `t`: the counterflow hull `m⁻¹(K′_t)` and the complete walls. -/
def stripExpl (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (β α : Ω → ℝ≥0 → ℂ) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  cfHull W' ζ' t ω ∪ wallUnion β α ω

/-- **The flat clock along an approach**: if the two representatives agree on a component (FC's pathwise conclusion
for a component unchanged since `r`) and an approach `F` eventually stays in it, they agree eventually along `F`. -/
theorem eventuallyEq_of_flatClock {Es : Set ℂ} {vr vs : ℂ → ℝ} {F : Filter ℂ} {z : ℂ}
    (hfc : ∀ w ∈ connectedComponentIn (H \ Es) z, vr w = vs w)
    (hF : ∀ᶠ w in F, w ∈ connectedComponentIn (H \ Es) z) : vr =ᶠ[F] vs := by
  filter_upwards [hF] with w hw using hfc w hw

end FlatClock

end InteractingSLE.Sec7.Aux37Germ
