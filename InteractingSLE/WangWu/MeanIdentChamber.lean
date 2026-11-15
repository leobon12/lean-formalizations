/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.MeanIdentArc
import InteractingSLE.WangWu.Adapted

/-!
# Wang–Wu Proposition 4.20: the wall values of the mean between ordered seed lines

Packet PROVE-WW-B5. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.4,
Proposition 4.20 (p. 29, text dump L1701–1745):

> **Proposition 4.20** (Conditional means between ordered seed lines). Let `h` in `ℍ` have boundary values `−a` on
> `ℝ₋` and `b` on `ℝ₊`, and let `u₁ < u₂` satisfy `λ − b ≤ u₁ < u₂ ≤ a − λ`. Suppose that the two corresponding
> non-boundary-intersecting level lines are ordered, with `γ_{u₂}` to the left of `γ_{u₁}`. Then their union is a
> local set. In each component between them, the conditional mean of `h` is the bounded harmonic function with values
> `λ − u₂` on the right side of `γ_{u₂}`, `−λ − u₁` on the left side of `γ_{u₁}`. (D2) …
>
> *Proof.* The single-line determinism proved in Proposition 4.18 and Lemma 4.5 give locality. The local-set union
> boundary lemma identifies the mean on the relative interior of every exposed arc. … The bounded harmonic extension of
> the values in (D2) is a candidate with the same boundary limits outside those two prime ends. Apply Corollary 4.8 to
> identify the mean with this candidate …

This file proves the first two steps for two ordered simple proper arcs `R = γ_{u₁}` (right wall) and `L = γ_{u₂}`
(left wall):

* **Locality and determination of the union** (`isLocalSet_union_of_aeDetermined`, Lemma 4.5 without adaptedness).
* **The wall values** (`ae_tendsto_unionMean_between`, deterministic core `exists_unionRep_tendsto_between`): almost
  surely the union mean `𝒞_{R∪L}` has a harmonic representative `w` on `ℍ \ (R ∪ L)` which tends, from the region
  between the walls (`leftSideOf R ∩ rightSideOf L`, which contains every component between them,
  `subset_between_of_mem_betweenComponents`), to the single-line value `ℓ_R(z)` at every point `z = R(s)` (`s > 0`) of
  the right wall off the left wall, and to `ℓ'_L(z)` at every point `z = L(s)` of the left wall off the right wall.
  Here `ℓ_R` is the left-side value of the single-line mean of `R` and `ℓ'_L` the right-side value of that of `L`
  (for seed lines of `F = h + m₀`: `ℓ_R = −λ − u₁ − m₀`, `ℓ'_L = λ − u₂ − m₀`, the zero-boundary form of (D2)).

The points excluded are the common points of the walls; on the boundary of a chamber these are exactly its opening
and closing points (`exists_contactGap_of_mem_betweenComponents`, PROVE-WW-B4), the two exceptional prime ends to
which the source then applies Corollary 4.8.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv IsZeroBoundaryGFF)
open InteractingSLE.LocalSets

universe u

namespace InteractingSLE.WangWu

/-- **A right-side boundary limit of a single-line mean** (the mirror of `HasLeftSideLimit`). -/
def HasRightSideLimit (g : DistOn upperHalfPlaneOpens) (γ : ℝ → ℂ) (ℓ : ℂ → ℝ) : Prop :=
  ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ arcRange γ) ∧
    (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcRange γ → g φ = ∫ z, v z * φ z) ∧
    ∀ s > 0, Tendsto v (𝓝[rightSideOf (arcRange γ)] (γ s)) (𝓝 (ℓ (γ s)))

/-! ### Components between the walls -/

/-- The left side of a set is a union of components of its complement in `ℍ`. -/
theorem mem_leftSideOf_of_mem_connectedComponentIn {A : Set ℂ} {z w : ℂ} (hz : z ∈ leftSideOf A)
    (hw : w ∈ connectedComponentIn (H \ A) z) : w ∈ leftSideOf A := by
  obtain ⟨-, x, hx, hxA, hxcl⟩ := hz
  refine ⟨connectedComponentIn_subset _ _ hw, x, hx, hxA, ?_⟩
  rwa [← connectedComponentIn_eq hw]

/-- The right side of a set is a union of components of its complement in `ℍ`. -/
theorem mem_rightSideOf_of_mem_connectedComponentIn {A : Set ℂ} {z w : ℂ} (hz : z ∈ rightSideOf A)
    (hw : w ∈ connectedComponentIn (H \ A) z) : w ∈ rightSideOf A := by
  obtain ⟨-, x, hx, hxA, hxcl⟩ := hz
  refine ⟨connectedComponentIn_subset _ _ hw, x, hx, hxA, ?_⟩
  rwa [← connectedComponentIn_eq hw]

/-- **Every component between two proper arcs lies on the left of the right wall and on the right of the left wall.** -/
theorem subset_between_of_mem_betweenComponents {R L : ℝ → ℂ} (hR : IsProperArc R) (hL : IsProperArc L)
    {C : Set ℂ} (hC : C ∈ betweenComponents (arcRange R) (arcRange L)) :
    C ⊆ leftSideOf (arcRange R) ∩ rightSideOf (arcRange L) := by
  obtain ⟨z, hz, hzR, hzL, rfl⟩ := hC
  have hzH : z ∈ H := hz.1
  have hzR' : z ∉ arcRange R := fun h => hz.2 (Or.inl h)
  have hzL' : z ∉ arcRange L := fun h => hz.2 (Or.inr h)
  have hl : z ∈ leftSideOf (arcRange R) :=
    (hR.mem_leftSideOf_or_mem_rightSideOf hzH hzR').resolve_right hzR
  have hr : z ∈ rightSideOf (arcRange L) :=
    (hL.mem_leftSideOf_or_mem_rightSideOf hzH hzL').resolve_left hzL
  intro w hw
  have hsubR : connectedComponentIn (H \ (arcRange R ∪ arcRange L)) z ⊆
      connectedComponentIn (H \ arcRange R) z :=
    connectedComponentIn_mono _ (sdiff_subset_sdiff_right subset_union_left)
  have hsubL : connectedComponentIn (H \ (arcRange R ∪ arcRange L)) z ⊆
      connectedComponentIn (H \ arcRange L) z :=
    connectedComponentIn_mono _ (sdiff_subset_sdiff_right subset_union_right)
  exact ⟨mem_leftSideOf_of_mem_connectedComponentIn hl (hsubR hw),
    mem_rightSideOf_of_mem_connectedComponentIn hr (hsubL hw)⟩

/-! ### The deterministic core -/

/-- **Deterministic core of the wall values (Proposition 4.20).** For two proper arcs (`R` the right wall, `L` the
left wall), single-line means with left-side values `ℓ_R` on `R` and right-side values `ℓ'_L` on `L`, and a union mean
`g` satisfying the conclusion of Proposition 3.8 for both orders, `g` has a harmonic representative `w` on
`ℍ \ (R ∪ L)` tending, from between the walls, to `ℓ_R(z)` at every point `z` of `R` off `L` and to `ℓ'_L(z)` at every
point `z` of `L` off `R`. -/
theorem exists_unionRep_tendsto_between {R L : ℝ → ℂ} (hR : IsProperArc R) (hL : IsProperArc L)
    {g gR gL : DistOn upperHalfPlaneOpens} {ℓR ℓL : ℂ → ℝ}
    (hgR : HasLeftSideLimit gR R ℓR) (hgL : HasRightSideLimit gL L ℓL)
    (h₁ : IsUnionBoundaryLimit (arcRange L) (arcRange R) g gR)
    (h₂ : IsUnionBoundaryLimit (arcRange R) (arcRange L) g gL) :
    ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (arcRange R ∪ arcRange L)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (arcRange R ∪ arcRange L) →
        g φ = ∫ z, w z * φ z) ∧
      (∀ s > 0, R s ∉ arcRange L →
        Tendsto w (𝓝[leftSideOf (arcRange R) ∩ rightSideOf (arcRange L)] (R s)) (𝓝 (ℓR (R s)))) ∧
      ∀ s > 0, L s ∉ arcRange R →
        Tendsto w (𝓝[leftSideOf (arcRange R) ∩ rightSideOf (arcRange L)] (L s)) (𝓝 (ℓL (L s))) := by
  set O : Set ℂ := H \ (arcRange R ∪ arcRange L) with hOdef
  have hO : IsOpen O := QuantumZipper.isOpen_H.sdiff (hR.isClosed_arcRange.union hL.isClosed_arcRange)
  have hO' : H \ (arcRange L ∪ arcRange R) = O := by rw [hOdef, union_comm]
  obtain ⟨vR, hvR, hvRg, hvRlim⟩ := hgR
  obtain ⟨vL, hvL, hvLg, hvLlim⟩ := hgL
  obtain ⟨u₁, hu₁, hu₁g, hu₁lim⟩ := h₁
  obtain ⟨u₂, hu₂, hu₂g, hu₂lim⟩ := h₂
  rw [hO'] at hu₁ hu₁g hu₁lim
  have hOR : O ⊆ H \ arcRange R := fun z hz => ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  have hOL : O ⊆ H \ arcRange L := fun z hz => ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  have hvRO : InnerProductSpace.HarmonicOnNhd vR O := fun z hz => hvR z (hOR hz)
  have hvLO : InnerProductSpace.HarmonicOnNhd vL O := fun z hz => hvL z (hOL hz)
  have hcont : ∀ {v : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd v O → ContinuousOn v O :=
    fun hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  -- the two representatives of `g` on `O`
  have hrep₁ : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O → g φ = ∫ z, (u₁ + vR) z * φ z := by
    intro φ hφ
    simp only [Pi.add_apply, add_mul]
    rw [integral_add (integrable_mul_test hO (hcont hu₁) φ hφ)
      (integrable_mul_test hO (hcont hvRO) φ hφ), ← hu₁g φ hφ, ← hvRg φ (hφ.trans hOR)]
    ring
  have hrep₂ : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O → g φ = ∫ z, (u₂ + vL) z * φ z := by
    intro φ hφ
    simp only [Pi.add_apply, add_mul]
    rw [integral_add (integrable_mul_test hO (hcont hu₂) φ hφ)
      (integrable_mul_test hO (hcont hvLO) φ hφ), ← hu₂g φ hφ, ← hvLg φ (hφ.trans hOL)]
    ring
  have heq := Sec6.eqOn_of_integral_mul_eq hO (fun z hz => hz.1) (hu₁.add hvRO) (hu₂.add hvLO)
    fun φ hφ => (hrep₁ φ hφ).symm.trans (hrep₂ φ hφ)
  set B := leftSideOf (arcRange R) ∩ rightSideOf (arcRange L) with hBdef
  have hBO : B ⊆ O := fun z hz =>
    ⟨hz.1.1.1, fun h => h.elim (fun h => hz.1.1.2 h) (fun h => hz.2.1.2 h)⟩
  -- a point off the other arc has a ball missing it
  have hball : ∀ {A A' : Set ℂ} {z₀ : ℂ}, IsClosed A' → z₀ ∉ A' → ∃ r > 0, A' ∩ ball z₀ r ⊆ A := by
    intro A A' z₀ hA' hz₀
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hA'.isOpen_compl z₀ hz₀
    exact ⟨r, hr, fun z hz => absurd hz.1 (hsub hz.2)⟩
  refine ⟨u₁ + vR, hu₁.add hvRO, hrep₁, ?_, ?_⟩
  · intro s hs hsL
    have l₁ : Tendsto u₁ (𝓝[B] (R s)) (𝓝 0) :=
      (hu₁lim (R s) (Or.inl ⟨s, mem_Ici.2 hs.le, rfl⟩) (hball hL.isClosed_arcRange hsL)).mono_left
        (nhdsWithin_mono _ hBO)
    have lR : Tendsto vR (𝓝[B] (R s)) (𝓝 (ℓR (R s))) :=
      (hvRlim s hs).mono_left (nhdsWithin_mono _ inter_subset_left)
    have := l₁.add lR
    rw [zero_add] at this
    exact this
  · intro s hs hsR
    have l₂ : Tendsto u₂ (𝓝[B] (L s)) (𝓝 0) :=
      (hu₂lim (L s) (Or.inl ⟨s, mem_Ici.2 hs.le, rfl⟩) (hball hR.isClosed_arcRange hsR)).mono_left
        (nhdsWithin_mono _ hBO)
    have lL : Tendsto vL (𝓝[B] (L s)) (𝓝 (ℓL (L s))) :=
      (hvLlim s hs).mono_left (nhdsWithin_mono _ inter_subset_right)
    have := l₂.add lL
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (heq (hBO hz)).symm

/-! ### Proposition 4.20: locality and wall values -/

section Probabilistic

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Wang–Wu Proposition 4.20: locality of the union and the wall values (D2).** Let `R, L` be random simple proper
arcs of `ℍ` (the right and left walls), whose ranges are local sets of the zero-boundary GFF `h` determined by `h`, and
let the single-line means `g_R`, `g_L` have left-side values `ℓ_R` on `R` and right-side values `ℓ'_L` on `L`. Then the
union `R ∪ L` is a local set determined by `h`, and for every version `g` of its mean, almost surely `g` has a harmonic
representative on `ℍ \ (R ∪ L)` tending, from between the walls, to `ℓ_R` at every point of `R` off `L` and to `ℓ'_L` at
every point of `L` off `R`. -/
theorem ae_tendsto_unionMean_between (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hRdet : LQGMetric.AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hLdet : LQGMetric.AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω)) h P)
    (hLloc : IsLocalSet (fun ω => arcRange (L ω)) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    {gR gL : Ω → DistOn upperHalfPlaneOpens}
    (hgR : IsLocalSetMean (fun ω => arcRange (R ω)) h P gR)
    (hgL : IsLocalSetMean (fun ω => arcRange (L ω)) h P gL) {ℓR ℓL : ℂ → ℝ}
    (hℓR : ∀ᵐ ω ∂P, HasLeftSideLimit (gR ω) (R ω) ℓR)
    (hℓL : ∀ᵐ ω ∂P, HasRightSideLimit (gL ω) (L ω) ℓL) :
    (IsLocalSet (fun ω => arcRange (R ω) ∪ arcRange (L ω)) h P ∧
      LQGMetric.AEDeterminedSigma
        (MeasurableSpace.comap (fun ω => arcRange (R ω) ∪ arcRange (L ω)) hittingSigma)
        (MeasurableSpace.comap h inferInstance) P) ∧
    ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun ω => arcRange (R ω) ∪ arcRange (L ω)) h P g →
      ∀ᵐ ω ∂P, ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (arcRange (R ω) ∪ arcRange (L ω))) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (arcRange (R ω) ∪ arcRange (L ω)) →
          g ω φ = ∫ z, w z * φ z) ∧
        (∀ s > 0, R ω s ∉ arcRange (L ω) →
          Tendsto w (𝓝[leftSideOf (arcRange (R ω)) ∩ rightSideOf (arcRange (L ω))] (R ω s))
            (𝓝 (ℓR (R ω s)))) ∧
        ∀ s > 0, L ω s ∉ arcRange (R ω) →
          Tendsto w (𝓝[leftSideOf (arcRange (R ω)) ∩ rightSideOf (arcRange (L ω))] (L ω s))
            (𝓝 (ℓL (L ω s))) := by
  refine ⟨isLocalSet_union_of_aeDetermined hh hRm hLm hRloc hLloc hRdet hLdet, fun g hg => ?_⟩
  have hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma) P :=
    Sec6.condIndepEv_of_le_aeSigma hh.measurable.comap_le hLm.comap_le fun s hs => hRdet s hs
  have e : (fun ω => arcRange (R ω) ∪ arcRange (L ω)) = fun ω => arcRange (L ω) ∪ arcRange (R ω) := by
    funext ω; exact union_comm _ _
  have hg' : IsLocalSetMean (fun ω => arcRange (L ω) ∪ arcRange (R ω)) h P g := e ▸ hg
  have hunbR : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (arcRange (R ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (arcRange (R ω))) z) := by
    filter_upwards [harc] with ω hω
    exact not_isBounded_of_isPreconnected_union_real hω.1.isPreconnected_union_real
  have hunbL : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (arcRange (L ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (arcRange (L ω))) z) := by
    filter_upwards [harc] with ω hω
    exact not_isBounded_of_isPreconnected_union_real hω.2.isPreconnected_union_real
  have p₁ := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh hLm hRm hci.symm hLloc hRloc hunbR hg' hgR
  have p₂ := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh hRm hLm hci hRloc hLloc hunbL hg hgL
  filter_upwards [harc, hℓR, hℓL, p₁, p₂] with ω hω hRω hLω h₁ h₂
  exact exists_unionRep_tendsto_between hω.1 hω.2 hRω hLω h₁ h₂

end Probabilistic

end InteractingSLE.WangWu
