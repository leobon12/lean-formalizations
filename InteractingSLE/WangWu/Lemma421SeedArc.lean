/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.PrefixLocalSides
import InteractingSLE.Spec.Sec5.Cond44RefSide

/-!
# Wang–Wu Lemma 4.21 without the order of the two lines

Packet PROVE-WW-B24. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Lemma 4.21
(text dump L1749–1757):

> **Lemma 4.21** (No common nontrivial arc). Two seed lines of different heights share no nontrivial subarc almost
> surely.
>
> *Proof.* If they share an arc, choose rational parameter intervals with closures strictly inside that arc.
> Simplicity and compactness separate an interior point of the smaller arc from the portions where the two curves
> differ. Approach the point from the same side. The local-set union boundary lemma then forces the union conditional
> mean to converge both to `−λ − u₁` and to `−λ − u₂`, or both to `λ − u₁` and `λ − u₂`. The limits differ.

The landed form (`WangWu.ae_interior_contact_eq_empty_inter`, PROVE-WW-B5/B8) assumes the order of the two lines
(Proposition 4.19), which it uses to know that the left side of one line is, near a common point, the left side of
the other ("approach the point from the same side"). This file removes that hypothesis by approaching the common point
from **both** sides of one line. Near a point of local coincidence each side of `L` lies (locally) in one of the two
sides of `R`, so the union mean forces, from the left of `L`, `ℓ_L = ℓ_R` or `ℓ_L = ℓ'_R`, and from the right of `L`,
`ℓ'_L = ℓ_R` or `ℓ'_L = ℓ'_R` (`ℓ` left, `ℓ'` right side values). For seed lines `ℓ ≠` on the same side (different
heights), and the crossed alternative `ℓ_L = ℓ'_R`, `ℓ'_L = ℓ_R` would make the jumps across the two lines opposite
(`ℓ_L − ℓ'_L = −2λ` but `ℓ'_R − ℓ_R = 2λ`).

## Main results

* `Lemma421Sides.eq_of_tendsto_union`: along any filter of points off both arcs converging to a point of local
  coincidence, the harmonic representatives of the two single-line means have the same limit (the union mean, the
  local-set union boundary lemma and uniqueness of harmonic representatives);
* `Lemma421Sides.mem_closure_inter_sides`: a set off `L` adherent to a point of local coincidence is adherent there to
  its part in the left side or in the right side of `R`;
* **`interior_contact_eq_empty_of_sides`**: the deterministic core without order;
* **`ae_interior_contact_eq_empty_sides`**: Lemma 4.21 for two random proper arcs that are local sets of one
  zero-boundary GFF, conditionally independent given it, with both side values (no order hypothesis).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv IsZeroBoundaryGFF)
open InteractingSLE.LocalSets

namespace InteractingSLE.WangWu

namespace Lemma421Sides

variable {R L : ℝ → ℂ}

/-- **The two single-line means have the same limit at a point of local coincidence.** If the union mean `g`
satisfies the conclusion of the local-set union boundary lemma (Proposition 3.8) for both orders, then along any
nontrivial filter of points off both arcs converging to a point `z₀` near which the two ranges coincide, harmonic
representatives `vR`, `vL` of the single-line means `gR`, `gL` with limits `a`, `b` have `a = b`. -/
theorem eq_of_tendsto_union (hR : IsProperArc R) (hL : IsProperArc L) {g gR gL : DistOn upperHalfPlaneOpens}
    (h₁ : IsUnionBoundaryLimit (arcRange L) (arcRange R) g gR)
    (h₂ : IsUnionBoundaryLimit (arcRange R) (arcRange L) g gL)
    {z₀ : ℂ} (hzR : z₀ ∈ arcRange R) (hzL : z₀ ∈ arcRange L) {r : ℝ} (hr : 0 < r)
    (hLR : arcRange L ∩ ball z₀ r ⊆ arcRange R) (hRL : arcRange R ∩ ball z₀ r ⊆ arcRange L)
    {vR vL : ℂ → ℝ} (hvR : InnerProductSpace.HarmonicOnNhd vR (H \ arcRange R))
    (hvRg : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcRange R → gR φ = ∫ z, vR z * φ z)
    (hvL : InnerProductSpace.HarmonicOnNhd vL (H \ arcRange L))
    (hvLg : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcRange L → gL φ = ∫ z, vL z * φ z)
    {F : Filter ℂ} [F.NeBot] (hF : F ≤ 𝓝[H \ (arcRange R ∪ arcRange L)] z₀) {a b : ℝ}
    (ha : Tendsto vR F (𝓝 a)) (hb : Tendsto vL F (𝓝 b)) : a = b := by
  set O : Set ℂ := H \ (arcRange R ∪ arcRange L) with hOdef
  have hO : IsOpen O := QuantumZipper.isOpen_H.sdiff (hR.isClosed_arcRange.union hL.isClosed_arcRange)
  have hO' : H \ (arcRange L ∪ arcRange R) = O := by rw [hOdef, union_comm]
  obtain ⟨u₁, hu₁, hu₁g, hu₁lim⟩ := h₁
  obtain ⟨u₂, hu₂, hu₂g, hu₂lim⟩ := h₂
  rw [hO'] at hu₁ hu₁g hu₁lim
  have l₁ : Tendsto u₁ F (𝓝 0) := (hu₁lim z₀ (Or.inl hzR) ⟨r, hr, hLR⟩).mono_left hF
  have l₂ : Tendsto u₂ F (𝓝 0) := (hu₂lim z₀ (Or.inl hzL) ⟨r, hr, hRL⟩).mono_left hF
  have hOR : O ⊆ H \ arcRange R := fun z hz => ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  have hOL : O ⊆ H \ arcRange L := fun z hz => ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  have hvRO : InnerProductSpace.HarmonicOnNhd vR O := fun z hz => hvR z (hOR hz)
  have hvLO : InnerProductSpace.HarmonicOnNhd vL O := fun z hz => hvL z (hOL hz)
  have hcont : ∀ {v : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd v O → ContinuousOn v O :=
    fun hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hrep : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      ∫ z, (u₁ + vR) z * φ z = ∫ z, (u₂ + vL) z * φ z := by
    intro φ hφ
    have i₁ := integrable_mul_test hO (hcont hu₁) φ hφ
    have i₂ := integrable_mul_test hO (hcont hu₂) φ hφ
    have iR := integrable_mul_test hO (hcont hvRO) φ hφ
    have iL := integrable_mul_test hO (hcont hvLO) φ hφ
    simp only [Pi.add_apply, add_mul]
    rw [integral_add i₁ iR, integral_add i₂ iL, ← hu₁g φ hφ, ← hu₂g φ hφ,
      ← hvRg φ (hφ.trans hOR), ← hvLg φ (hφ.trans hOL)]
    ring
  have heq := Sec6.eqOn_of_integral_mul_eq hO (fun z hz => hz.1) (hu₁.add hvRO) (hu₂.add hvLO) hrep
  have lA : Tendsto (u₁ + vR) F (𝓝 (0 + a)) := l₁.add ha
  have lB : Tendsto (u₁ + vR) F (𝓝 (0 + b)) := by
    refine (l₂.add hb).congr' ?_
    filter_upwards [hF self_mem_nhdsWithin] with z hz
    exact (heq hz).symm
  have := tendsto_nhds_unique lA lB
  simpa using this

/-- **Each side of `L` is locally in a side of `R`.** If the range of `R` near `z₀` lies in that of `L`, a set `S`
off `L` adherent to `z₀` is adherent to `z₀` through its part in the left side or through its part in the right side
of `R` (the two sides of a proper arc partition `ℍ ∖ R`). -/
theorem mem_closure_inter_sides (hR : IsProperArc R) {S : Set ℂ} (hS : S ⊆ H \ arcRange L) {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hRL : arcRange R ∩ ball z₀ r ⊆ arcRange L) (hz : z₀ ∈ closure S) :
    z₀ ∈ closure (S ∩ leftSideOf (arcRange R)) ∨ z₀ ∈ closure (S ∩ rightSideOf (arcRange R)) := by
  have h1 : z₀ ∈ closure (S ∩ ball z₀ r) := by
    rw [mem_closure_iff_nhdsWithin_neBot] at hz ⊢
    rwa [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z₀ hr))]
  have hsub : S ∩ ball z₀ r ⊆ (S ∩ leftSideOf (arcRange R)) ∪ (S ∩ rightSideOf (arcRange R)) := by
    rintro z ⟨hzS, hzB⟩
    have hzH : z ∈ H := (hS hzS).1
    have hzR : z ∉ arcRange R := fun h => (hS hzS).2 (hRL ⟨h, hzB⟩)
    rcases hR.mem_leftSideOf_or_mem_rightSideOf hzH hzR with h | h
    · exact Or.inl ⟨hzS, h⟩
    · exact Or.inr ⟨hzS, h⟩
  rw [← mem_union, ← closure_union]
  exact closure_mono hsub h1

end Lemma421Sides

open Lemma421Sides in
/-- **Deterministic core of Lemma 4.21 without the order of the lines.** Two proper arcs whose single-line means
have left-side limits `ℓR`, `ℓL` and right-side limits `ℓR'`, `ℓL'` with `ℓR ≠ ℓL`, `ℓR' ≠ ℓL'`, and without the
crossed coincidence `ℓL = ℓR'`, `ℓL' = ℓR`, and a union mean `g` satisfying the conclusion of Proposition 3.8 for both
orders, share no nontrivial subarc. -/
theorem interior_contact_eq_empty_of_sides {R L : ℝ → ℂ} (hR : IsProperArc R) (hL : IsProperArc L)
    {g gR gL : DistOn upperHalfPlaneOpens} {ℓR ℓR' ℓL ℓL' : ℂ → ℝ}
    (hgR : HasLeftSideLimit gR R ℓR) (hgR' : HasRightSideLimit gR R ℓR')
    (hgL : HasLeftSideLimit gL L ℓL) (hgL' : HasRightSideLimit gL L ℓL')
    (hℓ : ∀ z ∈ H, ℓR z ≠ ℓL z) (hℓ' : ∀ z ∈ H, ℓR' z ≠ ℓL' z)
    (hjump : ∀ z ∈ H, ℓL z = ℓR' z → ℓL' z ≠ ℓR z)
    (h₁ : IsUnionBoundaryLimit (arcRange L) (arcRange R) g gR)
    (h₂ : IsUnionBoundaryLimit (arcRange R) (arcRange L) g gL) :
    interior {t ∈ Ici (0 : ℝ) | L t ∈ arcRange R} = ∅ ∧
      interior {t ∈ Ici (0 : ℝ) | R t ∈ arcRange L} = ∅ := by
  -- a point of local coincidence contradicts the boundary limits
  suffices key : ∀ z₀ ∈ H, z₀ ∈ arcRange R → z₀ ∈ arcRange L → ∀ r > 0,
      arcRange L ∩ ball z₀ r ⊆ arcRange R → arcRange R ∩ ball z₀ r ⊆ arcRange L → False by
    constructor
    · by_contra hne
      obtain ⟨s, hs, r, hr, hzR, hLR, hRL⟩ := hR.exists_local_coincidence hL
        (nonempty_iff_ne_empty.2 hne)
      exact key (L s) (hL.mem_H s hs) hzR ⟨s, mem_Ici.2 hs.le, rfl⟩ r hr hLR hRL
    · by_contra hne
      obtain ⟨s, hs, r, hr, hzL, hRL, hLR⟩ := hL.exists_local_coincidence hR
        (nonempty_iff_ne_empty.2 hne)
      exact key (R s) (hR.mem_H s hs) ⟨s, mem_Ici.2 hs.le, rfl⟩ hzL r hr hLR hRL
  intro z₀ hz₀ hzR hzL r hr hLR hRL
  obtain ⟨t₀, ht₀, hRt₀⟩ := hzR
  obtain ⟨s₀, hs₀, hLs₀⟩ := hzL
  have hpos : ∀ {γ : ℝ → ℂ}, IsProperArc γ → ∀ {t : ℝ}, 0 ≤ t → γ t = z₀ → 0 < t := by
    intro γ hγ t ht he
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [← h0, hγ.zero] at he
      rw [← he] at hz₀
      exact absurd hz₀ (by simp [QuantumZipper.H])
    · exact h0
  have ht₀p := hpos hR (mem_Ici.1 ht₀) hRt₀
  have hs₀p := hpos hL (mem_Ici.1 hs₀) hLs₀
  have hzR : z₀ ∈ arcRange R := ⟨t₀, ht₀, hRt₀⟩
  have hzL : z₀ ∈ arcRange L := ⟨s₀, hs₀, hLs₀⟩
  obtain ⟨vR, hvR, hvRg, hvRlim⟩ := hgR
  obtain ⟨vR', hvR', hvR'g, hvR'lim⟩ := hgR'
  obtain ⟨vL, hvL, hvLg, hvLlim⟩ := hgL
  obtain ⟨vL', hvL', hvL'g, hvL'lim⟩ := hgL'
  -- the four one-sided limits at `z₀`
  have tR : Tendsto vR (𝓝[leftSideOf (arcRange R)] z₀) (𝓝 (ℓR z₀)) := by
    have := hvRlim t₀ ht₀p; rwa [hRt₀] at this
  have tR' : Tendsto vR' (𝓝[rightSideOf (arcRange R)] z₀) (𝓝 (ℓR' z₀)) := by
    have := hvR'lim t₀ ht₀p; rwa [hRt₀] at this
  have tL : Tendsto vL (𝓝[leftSideOf (arcRange L)] z₀) (𝓝 (ℓL z₀)) := by
    have := hvLlim s₀ hs₀p; rwa [hLs₀] at this
  have tL' : Tendsto vL' (𝓝[rightSideOf (arcRange L)] z₀) (𝓝 (ℓL' z₀)) := by
    have := hvL'lim s₀ hs₀p; rwa [hLs₀] at this
  -- a side of `L` meets a side of `R` near `z₀`: the two limits agree
  have hO : ∀ {S₁ S₂ : Set ℂ}, S₁ ⊆ H \ arcRange L → S₂ ⊆ H \ arcRange R →
      𝓝[S₁ ∩ S₂] z₀ ≤ 𝓝[H \ (arcRange R ∪ arcRange L)] z₀ := by
    intro S₁ S₂ h₁' h₂'
    refine nhdsWithin_mono _ fun z hz => ⟨(h₁' hz.1).1, ?_⟩
    rintro (h | h)
    · exact (h₂' hz.2).2 h
    · exact (h₁' hz.1).2 h
  have hlL : leftSideOf (arcRange L) ⊆ H \ arcRange L := fun z hz => hz.1
  have hrL : rightSideOf (arcRange L) ⊆ H \ arcRange L := fun z hz => hz.1
  have hlR : leftSideOf (arcRange R) ⊆ H \ arcRange R := fun z hz => hz.1
  have hrR : rightSideOf (arcRange R) ⊆ H \ arcRange R := fun z hz => hz.1
  have hclL : z₀ ∈ closure (leftSideOf (arcRange L)) := hLs₀ ▸ hL.mem_closure_leftSideOf hs₀p
  have hclL' : z₀ ∈ closure (rightSideOf (arcRange L)) := hLs₀ ▸ Sec5.Cond44Ref.mem_closure_rightSideOf hL hs₀p
  -- from the left side of `L`
  rcases mem_closure_inter_sides hR hlL hr hRL hclL with h | h
  · have := mem_closure_iff_nhdsWithin_neBot.1 h
    exact hℓ z₀ hz₀ (eq_of_tendsto_union hR hL h₁ h₂ hzR hzL hr hLR hRL hvR hvRg hvL hvLg (hO hlL hlR)
      (tR.mono_left (nhdsWithin_mono _ inter_subset_right))
      (tL.mono_left (nhdsWithin_mono _ inter_subset_left)))
  · have e₁ : ℓR' z₀ = ℓL z₀ := by
      have := mem_closure_iff_nhdsWithin_neBot.1 h
      exact eq_of_tendsto_union hR hL h₁ h₂ hzR hzL hr hLR hRL hvR' hvR'g hvL hvLg (hO hlL hrR)
        (tR'.mono_left (nhdsWithin_mono _ inter_subset_right))
        (tL.mono_left (nhdsWithin_mono _ inter_subset_left))
    -- from the right side of `L`
    rcases mem_closure_inter_sides hR hrL hr hRL hclL' with h' | h'
    · have e₂ : ℓR z₀ = ℓL' z₀ := by
        have := mem_closure_iff_nhdsWithin_neBot.1 h'
        exact eq_of_tendsto_union hR hL h₁ h₂ hzR hzL hr hLR hRL hvR hvRg hvL' hvL'g (hO hrL hlR)
          (tR.mono_left (nhdsWithin_mono _ inter_subset_right))
          (tL'.mono_left (nhdsWithin_mono _ inter_subset_left))
      exact hjump z₀ hz₀ e₁.symm e₂.symm
    · have := mem_closure_iff_nhdsWithin_neBot.1 h'
      exact hℓ' z₀ hz₀ (eq_of_tendsto_union hR hL h₁ h₂ hzR hzL hr hLR hRL hvR' hvR'g hvL' hvL'g (hO hrL hrR)
        (tR'.mono_left (nhdsWithin_mono _ inter_subset_right))
        (tL'.mono_left (nhdsWithin_mono _ inter_subset_left)))

section NoCommonArcSides

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Wang–Wu Lemma 4.21 (no common nontrivial arc) without the order of the lines.** Two random proper arcs `R`, `L`
whose ranges (with `∩ ℍ`) are local sets of one zero-boundary GFF `h`, conditionally independent given `h`, whose
single-line local-set means have left-side limits `ℓR`, `ℓL` and right-side limits `ℓR'`, `ℓL'` with `ℓR ≠ ℓL`,
`ℓR' ≠ ℓL'` and no crossed coincidence (`ℓL = ℓR'` and `ℓL' = ℓR` never both hold on `ℍ`), almost surely share no
nontrivial subarc. (`WangWu.ae_interior_contact_eq_empty_inter` with the order hypothesis replaced by the right-side
limits.) -/
theorem ae_interior_contact_eq_empty_sides (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω) ∩ H) h P)
    (hLloc : IsLocalSet (fun ω => arcRange (L ω) ∩ H) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    {gR gL : Ω → DistOn upperHalfPlaneOpens}
    (hgR : IsLocalSetMean (fun ω => arcRange (R ω)) h P gR)
    (hgL : IsLocalSetMean (fun ω => arcRange (L ω)) h P gL) {ℓR ℓR' ℓL ℓL' : ℂ → ℝ}
    (hℓR : ∀ᵐ ω ∂P, HasLeftSideLimit (gR ω) (R ω) ℓR)
    (hℓR' : ∀ᵐ ω ∂P, HasRightSideLimit (gR ω) (R ω) ℓR')
    (hℓL : ∀ᵐ ω ∂P, HasLeftSideLimit (gL ω) (L ω) ℓL)
    (hℓL' : ∀ᵐ ω ∂P, HasRightSideLimit (gL ω) (L ω) ℓL')
    (hℓ : ∀ z ∈ H, ℓR z ≠ ℓL z) (hℓ' : ∀ z ∈ H, ℓR' z ≠ ℓL' z)
    (hjump : ∀ z ∈ H, ℓL z = ℓR' z → ℓL' z ≠ ℓR z) :
    ∀ᵐ ω ∂P, interior {t ∈ Ici (0 : ℝ) | L ω t ∈ arcRange (R ω)} = ∅ ∧
      interior {t ∈ Ici (0 : ℝ) | R ω t ∈ arcRange (L ω)} = ∅ := by
  have hRm' := measurable_inter_H hRm
  have hLm' := measurable_inter_H hLm
  have hci' : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (R ω) ∩ H) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (L ω) ∩ H) hittingSigma) P := by
    rw [comap_inter_H, comap_inter_H]
    exact hci
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.isGermConditionalLaw_union hh hRm' hLm' hci' hRloc hLloc
  have e : (fun ω => arcRange (R ω) ∩ H ∪ arcRange (L ω) ∩ H) =
      fun ω => arcRange (L ω) ∩ H ∪ arcRange (R ω) ∩ H := by
    funext ω; exact union_comm _ _
  have hg' : IsLocalSetMean (fun ω => arcRange (L ω) ∩ H ∪ arcRange (R ω) ∩ H) h P g := e ▸ hg
  have hunbR : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (arcRange (R ω) ∩ H),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (arcRange (R ω) ∩ H)) z) := by
    filter_upwards [harc] with ω hω
    rw [lowerUnion_inter_H]
    exact not_isBounded_of_isPreconnected_union_real hω.1.isPreconnected_union_real
  have hunbL : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (arcRange (L ω) ∩ H),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (arcRange (L ω) ∩ H)) z) := by
    filter_upwards [harc] with ω hω
    rw [lowerUnion_inter_H]
    exact not_isBounded_of_isPreconnected_union_real hω.2.isPreconnected_union_real
  have p₁ := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh hLm' hRm' hci'.symm hLloc hRloc hunbR hg'
    (isLocalSetMean_inter_H_iff.2 hgR)
  have p₂ := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh hRm' hLm' hci' hRloc hLloc hunbL hg
    (isLocalSetMean_inter_H_iff.2 hgL)
  filter_upwards [harc, hℓR, hℓR', hℓL, hℓL', p₁, p₂] with ω hω hRω hRω' hLω hLω' h₁ h₂
  exact interior_contact_eq_empty_of_sides hω.1 hω.2 hRω hRω' hLω hLω' hℓ hℓ' hjump
    (IsUnionBoundaryLimit.of_inter_H (fun z hz hzH => hω.1.im_eq_zero_of_mem_arcRange hz hzH) h₁)
    (IsUnionBoundaryLimit.of_inter_H (fun z hz hzH => hω.2.im_eq_zero_of_mem_arcRange hz hzH) h₂)

end NoCommonArcSides

end InteractingSLE.WangWu
