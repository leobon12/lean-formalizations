/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberArcs
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# Wang–Wu Lemma 4.21: no common nontrivial arc

Packet PROVE-WW-B5. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.5, Lemma 4.21
(p. 30, text dump L1749–1757):

> **Lemma 4.21** (No common nontrivial arc). Two seed lines of different heights share no nontrivial subarc almost
> surely.
>
> *Proof.* If they share an arc, choose rational parameter intervals with closures strictly inside that arc.
> Simplicity and compactness separate an interior point of the smaller arc from the portions where the two curves
> differ. Approach the point from the same side. The local-set union boundary lemma then forces the union conditional
> mean to converge both to `−λ − u₁` and to `−λ − u₂`, or both to `λ − u₁` and `λ − u₂`. The limits differ.

## Statement

`ae_interior_contact_eq_empty`: two random simple proper arcs `R, L` of `ℍ` (`IsProperArc`, from `0` to `∞`) whose
ranges are local sets of the zero-boundary GFF `h`, conditionally independent given `h` (e.g. both determined by `h`),
with `L` to the left of `R` (`Disjoint (arcRange L) (rightSideOf (arcRange R))`, Proposition 4.19), and whose
single-line local-set means have left-side boundary limits `ℓ_R(z)`, `ℓ_L(z)` at every point `z` of the curve other
than its start, with `ℓ_R(z) ≠ ℓ_L(z)` on `ℍ`. Then almost surely neither arc spends a time interval on the other:
`interior {t ≥ 0 | L t ∈ R} = ∅` and `interior {t ≥ 0 | R t ∈ L} = ∅` (the form consumed by Lemma 4.22,
`IsOrderedArcs.lemma422`).

For seed lines of `F = h + m₀` at heights `u₁ < u₂` (Definition 1.9) the left-side values of `F` are `−λ − uᵢ`, so the
zero-boundary means have `ℓᵢ(z) = −λ − uᵢ − m₀(z)` (`m₀` the harmonic extension of the boundary data, continuous on
`ℍ`), and `ℓ₁ ≠ ℓ₂` everywhere.

## Proof

* *Geometry* (`IsProperArc.exists_local_coincidence`): a time interval of `L` on `R` gives a point `z₀ = L(s₀)`,
  `s₀ > 0`, near which the two ranges coincide. `R⁻¹ ∘ L` is continuous on a compact interval (images of closed time
  sets under a proper arc are closed) and injective, hence strictly monotone; its image is an interval around the
  `R`-time of `z₀`, and the rest of each arc is a closed set missing `z₀`.
* *Sides*: by the order, `leftSideOf L ⊆ leftSideOf R` (`IsDiscCrosscut.crossSide_pos_subset_of_disjoint` through the
  Cayley correspondence), and `z₀` is adherent to `leftSideOf L` (`IsProperArc.mem_closure_leftSideOf`).
* *Means*: Proposition 3.8 (`IsLocalSetMean.ae_tendsto_sub_of_union`), applied to `(L, R)` and to `(R, L)` at `z₀`,
  gives `𝒞_{R∪L} − 𝒞_R → 0` and `𝒞_{R∪L} − 𝒞_L → 0` at `z₀`; harmonic representatives are unique
  (`Sec6.eqOn_of_integral_mul_eq`), so along the left side of `L` the union mean tends both to `ℓ_R(z₀)` and to
  `ℓ_L(z₀)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open LQGMetric (DistOn TestOn CondIndepEv IsZeroBoundaryGFF)
open InteractingSLE.LocalSets

universe u

namespace InteractingSLE.WangWu

namespace IsProperArc

variable {γ R L : ℝ → ℂ}

/-- The image of a closed set of times under a proper arc is closed. -/
theorem isClosed_image (hγ : IsProperArc γ) {F : Set ℝ} (hF : IsClosed F) (hF0 : F ⊆ Ici 0) :
    IsClosed (γ '' F) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hγ.tendsto (‖z‖ + 1))
  have hcpt : IsClosed (γ '' (F ∩ Icc 0 T)) :=
    ((isCompact_Icc.inter_left hF).image_of_continuousOn
      (hγ.cont.mono fun t ht => mem_Ici.2 ht.2.1)).isClosed
  have hzT : z ∈ closure (γ '' (F ∩ Icc 0 T)) := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨b, hbA, hb⟩ := Metric.mem_closure_iff.1 hz (min ε 1) (lt_min hε one_pos)
    obtain ⟨t, ht, rfl⟩ := hbA
    refine ⟨γ t, ⟨t, ⟨ht, mem_Ici.1 (hF0 ht), ?_⟩, rfl⟩, lt_of_lt_of_le hb (min_le_left _ _)⟩
    by_contra htT
    push Not at htT
    have h1 := hT t htT.le
    have h2 : dist z (γ t) < 1 := lt_of_lt_of_le hb (min_le_right _ _)
    rw [dist_eq_norm] at h2
    have := norm_sub_norm_le (γ t) z
    rw [norm_sub_rev] at h2
    linarith
  rw [hcpt.closure_eq] at hzT
  obtain ⟨t, ht, rfl⟩ := hzT
  exact ⟨t, ht.1, rfl⟩

/-- Near the point at an interior time `s ∈ (a, b)` (`0 ≤ a`), a proper arc lies in its image of `(a, b)`. -/
theorem exists_ball_inter_subset (hγ : IsProperArc γ) {a b s : ℝ} (ha : 0 ≤ a) (hs : s ∈ Ioo a b) :
    ∃ r > 0, arcRange γ ∩ ball (γ s) r ⊆ γ '' Ioo a b := by
  have hF0 : Icc 0 a ∪ Ici b ⊆ Ici 0 := by
    rintro t (ht | ht)
    · exact mem_Ici.2 ht.1
    · exact mem_Ici.2 (ha.trans (hs.1.trans hs.2).le |>.trans ht)
  have hcl := hγ.isClosed_image (isClosed_Icc.union isClosed_Ici) hF0
  have hs0 : s ∈ Ici 0 := mem_Ici.2 (ha.trans hs.1.le)
  have hnot : γ s ∉ γ '' (Icc 0 a ∪ Ici b) := by
    rintro ⟨t, ht, he⟩
    have hts : t = s := hγ.inj (hF0 ht) hs0 he
    subst hts
    rcases ht with ht | ht
    · exact absurd ht.2 (not_le.2 hs.1)
    · exact absurd (mem_Ici.1 ht) (not_le.2 hs.2)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl _ hnot
  refine ⟨r, hr, ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, htb⟩
  have hnt : t ∉ Icc 0 a ∪ Ici b := fun h => hball htb ⟨t, h, rfl⟩
  simp only [mem_union, mem_Icc, mem_Ici, not_or, not_and, not_le] at hnt
  exact ⟨t, ⟨hnt.1 (mem_Ici.1 ht), hnt.2⟩, rfl⟩

/-- **Local coincidence.** If `L([a, b]) ⊆ R([0, ∞))` (`0 ≤ a`) and `a < s < b`, then near `L s` the arc `R` lies in
`L([a, b])`: `R⁻¹ ∘ L` is continuous and injective on `[a, b]`, hence strictly monotone, and its image is an interval
containing the `R`-time of `L s` in its interior. -/
theorem exists_ball_inter_arcRange_subset (hR : IsProperArc R) (hL : IsProperArc L) {a b s : ℝ}
    (ha : 0 ≤ a) (hab : L '' Icc a b ⊆ arcRange R) (hs : s ∈ Ioo a b) :
    ∃ r > 0, arcRange R ∩ ball (L s) r ⊆ L '' Icc a b := by
  have hab' : a ≤ b := (hs.1.trans hs.2).le
  have hIcc0 : Icc a b ⊆ Ici 0 := fun t ht => mem_Ici.2 (ha.trans ht.1)
  set φ : ℝ → ℝ := fun t => Function.invFunOn R (Ici 0) (L t) with hφdef
  have hex : ∀ t ∈ Icc a b, ∃ u ∈ Ici (0 : ℝ), R u = L t := fun t ht => hab ⟨t, ht, rfl⟩
  have hφ0 : ∀ t ∈ Icc a b, φ t ∈ Ici (0 : ℝ) := fun t ht => Function.invFunOn_mem (hex t ht)
  have hRφ : ∀ t ∈ Icc a b, R (φ t) = L t := fun t ht => Function.invFunOn_eq (hex t ht)
  have hφi : InjOn φ (Icc a b) := fun t ht t' ht' he =>
    hL.inj (hIcc0 ht) (hIcc0 ht') (by rw [← hRφ t ht, ← hRφ t' ht', he])
  have hφc : ContinuousOn φ (Icc a b) := by
    refine continuousOn_iff_isClosed.2 fun C hC => ?_
    refine ⟨Icc a b ∩ L ⁻¹' (R '' (C ∩ Ici 0)),
      (hL.cont.mono hIcc0).preimage_isClosed_of_isClosed isClosed_Icc
        (hR.isClosed_image (hC.inter isClosed_Ici) inter_subset_right), ?_⟩
    ext t
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨htC, ht⟩
      exact ⟨⟨ht, φ t, ⟨htC, hφ0 t ht⟩, hRφ t ht⟩, ht⟩
    · rintro ⟨⟨-, u, ⟨huC, hu0⟩, hu⟩, ht⟩
      have : u = φ t := hR.inj hu0 (hφ0 t ht) (by rw [hu, hRφ t ht])
      exact ⟨this ▸ huC, ht⟩
  have hsI : s ∈ Icc a b := Ioo_subset_Icc_self hs
  have haI : a ∈ Icc a b := left_mem_Icc.2 hab'
  have hbI : b ∈ Icc a b := right_mem_Icc.2 hab'
  -- the `R`-times of `L([a, b])` contain an open interval around `φ s`
  obtain ⟨p, q, hp0, hpq, hRpq⟩ : ∃ p q : ℝ, 0 ≤ p ∧ φ s ∈ Ioo p q ∧ R '' Ioo p q ⊆ L '' Icc a b := by
    rcases hφc.strictMonoOn_of_injOn_Icc' hab' hφi with hmono | hanti
    · refine ⟨φ a, φ b, hφ0 a haI, ⟨hmono haI hsI hs.1, hmono hsI hbI hs.2⟩, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc hab' hφc (Ioo_subset_Icc_self hu)
      exact ⟨t, ht, (hRφ t ht).symm⟩
    · refine ⟨φ b, φ a, hφ0 b hbI, ⟨hanti hsI hbI hs.2, hanti haI hsI hs.1⟩, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc' hab' hφc (Ioo_subset_Icc_self hu)
      exact ⟨t, ht, (hRφ t ht).symm⟩
  obtain ⟨r, hr, hball⟩ := hR.exists_ball_inter_subset hp0 hpq
  refine ⟨r, hr, ?_⟩
  rw [← hRφ s hsI]
  exact hball.trans hRpq

/-- **A shared time interval gives a point of local coincidence.** If `L` spends a nontrivial time interval on `R`,
there are `s > 0` and `r > 0` such that `L s ∈ R` and the two ranges agree in the ball of radius `r` around `L s`. -/
theorem exists_local_coincidence (hR : IsProperArc R) (hL : IsProperArc L)
    (hne : (interior {t ∈ Ici (0 : ℝ) | L t ∈ arcRange R}).Nonempty) :
    ∃ s > 0, ∃ r > 0, L s ∈ arcRange R ∧ arcRange L ∩ ball (L s) r ⊆ arcRange R ∧
      arcRange R ∩ ball (L s) r ⊆ arcRange L := by
  obtain ⟨t₁, ht₁⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 ht₁)
  set a := t₁ - ε / 2 with hadef
  set b := t₁ + ε / 2 with hbdef
  have hIcc : Icc a b ⊆ ball t₁ ε := by
    intro t ht
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, hadef, hbdef]
  have hsub : Icc a b ⊆ {t ∈ Ici (0 : ℝ) | L t ∈ arcRange R} := hIcc.trans hball
  have ha : 0 ≤ a := (hsub (left_mem_Icc.2 (by linarith [hadef, hbdef]))).1
  have hs : t₁ ∈ Ioo a b := ⟨by linarith [hadef], by linarith [hbdef]⟩
  have hLR : L '' Icc a b ⊆ arcRange R := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hsub ht).2
  obtain ⟨r₁, hr₁, h₁⟩ := hR.exists_ball_inter_arcRange_subset hL ha hLR hs
  obtain ⟨r₂, hr₂, h₂⟩ := hL.exists_ball_inter_subset ha hs
  refine ⟨t₁, ha.trans_lt hs.1, min r₁ r₂, lt_min hr₁ hr₂,
    hLR ⟨t₁, Ioo_subset_Icc_self hs, rfl⟩, ?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := h₂ ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩
    exact hLR ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := h₁ ⟨hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩
    exact ⟨t, mem_Ici.2 (ha.trans ht.1), rfl⟩

/-- Every point of a proper arc after its start is adherent to the left side of the arc. -/
theorem mem_closure_leftSideOf (hγ : IsProperArc γ) {s : ℝ} (hs : 0 < s) :
    γ s ∈ closure (leftSideOf (arcRange γ)) := by
  have hα := hγ.isDiscCrosscut_toDisc
  have hzH : γ s ∈ H := hγ.mem_H s hs
  have hzHb : γ s ∈ Hbar := le_of_lt (show (0 : ℝ) < (γ s).im from hzH)
  have hc : cayley (γ s) ∈ closure (crossSide (toDisc γ) 1) :=
    hα.crossRange_subset_closure_crossSide (Or.inl rfl)
      ((hγ.cayley_mem_crossRange_iff hzHb).2 ⟨s, mem_Ici.2 hs.le, rfl⟩)
  have hsub : cayleyInv '' crossSide (toDisc γ) 1 ⊆ leftSideOf (arcRange γ) := by
    rintro _ ⟨w, hw, rfl⟩
    have hwb := (hα.crossSide_subset (Or.inl rfl) hw).1
    have hzw : cayleyInv w ∈ H := QuantumZipper.CA.cayleyInv_mem_H hwb
    rw [hγ.mem_leftSideOf_iff hzw, cayley_cayleyInv_of_mem_ball hwb]
    exact hw
  have hcont : ContinuousAt cayleyInv (cayley (γ s)) := continuousAt_cayleyInv (cayley_ne_one_of_Hbar hzHb)
  have := mem_closure_image hcont hc
  rw [cayleyInv_cayley_of_mem_Hbar hzHb] at this
  exact closure_mono hsub this

/-- **The order of two proper arcs nests their left sides**: if `L` avoids the right side of `R`, the left side of `L`
lies in the left side of `R`. -/
theorem leftSideOf_subset_of_disjoint (hR : IsProperArc R) (hL : IsProperArc L)
    (hord : Disjoint (arcRange L) (rightSideOf (arcRange R))) :
    leftSideOf (arcRange L) ⊆ leftSideOf (arcRange R) := by
  have hα := hR.isDiscCrosscut_toDisc
  have hβ := hL.isDiscCrosscut_toDisc
  have h₁ := (disjoint_rightSideOf_iff hR hL).1 hord
  have h₂ := IsDiscCrosscut.disjoint_crossRange_crossSide_swap hα hβ h₁
  have h₃ := IsDiscCrosscut.crossSide_pos_subset_of_disjoint hα hβ h₂
  intro z hz
  have hzH : z ∈ H := hz.1.1
  rw [hL.mem_leftSideOf_iff hzH] at hz
  rw [hR.mem_leftSideOf_iff hzH]
  exact h₃ hz

end IsProperArc

/-! ### The deterministic core -/

/-- **A left-side boundary limit of a single-line mean.** `g` (a distribution on `ℍ`) is represented on `ℍ \ γ` by a
harmonic function `v` which tends to `ℓ(γ s)` from the left side of `γ` at every point `γ s`, `s > 0`. This is the
single-line identification of a seed line (proof of Proposition 4.19: "local-set boundary compatibility therefore
gives the boundary value"). -/
def HasLeftSideLimit (g : DistOn upperHalfPlaneOpens) (γ : ℝ → ℂ) (ℓ : ℂ → ℝ) : Prop :=
  ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ arcRange γ) ∧
    (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcRange γ → g φ = ∫ z, v z * φ z) ∧
    ∀ s > 0, Tendsto v (𝓝[leftSideOf (arcRange γ)] (γ s)) (𝓝 (ℓ (γ s)))

/-- The conclusion of Proposition 3.8 for the pair `(A₁, A₂)` and the union mean `g`, at one sample: a harmonic
representative `u` of `g − g₂` on `ℍ \ (A₁ ∪ A₂)` tending to `0` at every point of `A₂ ∪ ℝ` near which `A₁ ⊆ A₂`. -/
def IsUnionBoundaryLimit (A₁ A₂ : Set ℂ) (g g₂ : DistOn upperHalfPlaneOpens) : Prop :=
  ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ (A₁ ∪ A₂)) ∧
    (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ∪ A₂) → g φ - g₂ φ = ∫ z, u z * φ z) ∧
    ∀ z₀ ∈ A₂ ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A₁ ∩ ball z₀ r ⊆ A₂) →
      Tendsto u (𝓝[H \ (A₁ ∪ A₂)] z₀) (𝓝 0)

/-- **Deterministic core of Lemma 4.21.** Two ordered proper arcs (`L` left of `R`) whose single-line means have
left-side limits `ℓ_R ≠ ℓ_L`, and a union mean `g` satisfying the conclusion of Proposition 3.8 for both orders,
share no nontrivial subarc. -/
theorem interior_contact_eq_empty_of_means {R L : ℝ → ℂ} (hR : IsProperArc R) (hL : IsProperArc L)
    (hord : Disjoint (arcRange L) (rightSideOf (arcRange R)))
    {g gR gL : DistOn upperHalfPlaneOpens} {ℓR ℓL : ℂ → ℝ}
    (hgR : HasLeftSideLimit gR R ℓR) (hgL : HasLeftSideLimit gL L ℓL) (hℓ : ∀ z ∈ H, ℓR z ≠ ℓL z)
    (h₁ : IsUnionBoundaryLimit (arcRange L) (arcRange R) g gR)
    (h₂ : IsUnionBoundaryLimit (arcRange R) (arcRange L) g gL) :
    interior {t ∈ Ici (0 : ℝ) | L t ∈ arcRange R} = ∅ ∧
      interior {t ∈ Ici (0 : ℝ) | R t ∈ arcRange L} = ∅ := by
  -- a point of local coincidence contradicts the two boundary limits
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
  obtain ⟨u₀, hu₀, hRu₀⟩ := hzR
  obtain ⟨s₀, hs₀, hLs₀⟩ := hzL
  have hpos : ∀ {γ : ℝ → ℂ}, IsProperArc γ → ∀ {t : ℝ}, 0 ≤ t → γ t = z₀ → 0 < t := by
    intro γ hγ t ht he
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [← h0, hγ.zero] at he
      rw [← he] at hz₀
      exact absurd hz₀ (by simp [QuantumZipper.H])
    · exact h0
  have hu₀p := hpos hR (mem_Ici.1 hu₀) hRu₀
  have hs₀p := hpos hL (mem_Ici.1 hs₀) hLs₀
  -- the open set off both arcs, and the left side of `L` inside it
  set O : Set ℂ := H \ (arcRange R ∪ arcRange L) with hOdef
  have hO : IsOpen O := QuantumZipper.isOpen_H.sdiff (hR.isClosed_arcRange.union hL.isClosed_arcRange)
  have hO' : H \ (arcRange L ∪ arcRange R) = O := by rw [hOdef, union_comm]
  have hleftLR := hR.leftSideOf_subset_of_disjoint hL hord
  have hleftO : leftSideOf (arcRange L) ⊆ O := fun z hz =>
    ⟨hz.1.1, fun h => h.elim (fun h => (hleftLR hz).1.2 h) (fun h => hz.1.2 h)⟩
  set F := 𝓝[leftSideOf (arcRange L)] z₀ with hFdef
  have hFne : F.NeBot := by
    rw [hFdef, ← mem_closure_iff_nhdsWithin_neBot, ← hLs₀]
    exact hL.mem_closure_leftSideOf hs₀p
  have hFO : F ≤ 𝓝[O] z₀ := nhdsWithin_mono _ hleftO
  have hFR : F ≤ 𝓝[leftSideOf (arcRange R)] z₀ := nhdsWithin_mono _ hleftLR
  obtain ⟨vR, hvR, hvRg, hvRlim⟩ := hgR
  obtain ⟨vL, hvL, hvLg, hvLlim⟩ := hgL
  obtain ⟨u₁, hu₁, hu₁g, hu₁lim⟩ := h₁
  obtain ⟨u₂, hu₂, hu₂g, hu₂lim⟩ := h₂
  rw [hO'] at hu₁ hu₁g hu₁lim
  -- the four limits along `F`
  have l₁ : Tendsto u₁ F (𝓝 0) :=
    (hu₁lim z₀ (Or.inl ⟨u₀, hu₀, hRu₀⟩) ⟨r, hr, hLR⟩).mono_left hFO
  have l₂ : Tendsto u₂ F (𝓝 0) :=
    (hu₂lim z₀ (Or.inl ⟨s₀, hs₀, hLs₀⟩) ⟨r, hr, hRL⟩).mono_left hFO
  have lR : Tendsto vR F (𝓝 (ℓR z₀)) := by
    have := hvRlim u₀ hu₀p
    rw [hRu₀] at this
    exact this.mono_left hFR
  have lL : Tendsto vL F (𝓝 (ℓL z₀)) := by
    have := hvLlim s₀ hs₀p
    rw [hLs₀] at this
    exact this
  -- uniqueness of the harmonic representative of `g` on `O`
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
  have lA : Tendsto (u₁ + vR) F (𝓝 (0 + ℓR z₀)) := l₁.add lR
  have lB : Tendsto (u₁ + vR) F (𝓝 (0 + ℓL z₀)) := by
    refine (l₂.add lL).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (heq (hleftO hz)).symm
  have := tendsto_nhds_unique lA lB
  simp only [zero_add] at this
  exact hℓ z₀ hz₀ this

/-! ### Lemma 4.21 -/

/-- `ℝ ∪ γ([0, ∞))` is connected for a proper arc. -/
theorem IsProperArc.isPreconnected_union_real {γ : ℝ → ℂ} (hγ : IsProperArc γ) :
    IsPreconnected (arcRange γ ∪ {w : ℂ | w.im = 0}) := by
  have hreal : {w : ℂ | w.im = 0} = range (fun x : ℝ => (x : ℂ)) := by
    ext w
    constructor
    · intro hw
      exact ⟨w.re, Complex.ext (by simp) (by simpa using hw.symm)⟩
    · rintro ⟨x, rfl⟩
      simp
  refine IsPreconnected.union 0 ⟨0, mem_Ici.2 le_rfl, hγ.zero⟩ (by simp)
    (isPreconnected_Ici.image γ hγ.cont) ?_
  rw [hreal]
  exact isPreconnected_range Complex.continuous_ofReal

section Probabilistic

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Wang–Wu Lemma 4.21 (no common nontrivial arc).** Let `R, L` be random simple proper arcs of `ℍ` from `0` to `∞`
whose ranges are local sets of the zero-boundary GFF `h`, conditionally independent given `h` (for instance both
determined by `h`), with `L` to the left of `R` (Proposition 4.19), and let the single-line local-set means `g_R`, `g_L`
have left-side boundary limits `ℓ_R`, `ℓ_L` at every point of the arcs after their start, with `ℓ_R ≠ ℓ_L` on `ℍ`
(seed lines at different heights). Then almost surely neither arc spends a nontrivial time interval on the other. -/
theorem ae_interior_contact_eq_empty (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω)) h P)
    (hLloc : IsLocalSet (fun ω => arcRange (L ω)) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (arcRange (L ω)) (rightSideOf (arcRange (R ω))))
    {gR gL : Ω → DistOn upperHalfPlaneOpens}
    (hgR : IsLocalSetMean (fun ω => arcRange (R ω)) h P gR)
    (hgL : IsLocalSetMean (fun ω => arcRange (L ω)) h P gL) {ℓR ℓL : ℂ → ℝ}
    (hℓR : ∀ᵐ ω ∂P, HasLeftSideLimit (gR ω) (R ω) ℓR)
    (hℓL : ∀ᵐ ω ∂P, HasLeftSideLimit (gL ω) (L ω) ℓL) (hℓ : ∀ z ∈ H, ℓR z ≠ ℓL z) :
    ∀ᵐ ω ∂P, interior {t ∈ Ici (0 : ℝ) | L ω t ∈ arcRange (R ω)} = ∅ ∧
      interior {t ∈ Ici (0 : ℝ) | R ω t ∈ arcRange (L ω)} = ∅ := by
  -- the union mean
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.isGermConditionalLaw_union hh hRm hLm hci hRloc hLloc
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
  -- Proposition 3.8 for `(L, R)` and for `(R, L)`
  have p₁ := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh hLm hRm hci.symm hLloc hRloc hunbR hg' hgR
  have p₂ := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh hRm hLm hci hRloc hLloc hunbL hg hgL
  filter_upwards [harc, hord, hℓR, hℓL, p₁, p₂] with ω hω hoω hRω hLω h₁ h₂
  exact interior_contact_eq_empty_of_means hω.1 hω.2 hoω hRω hLω hℓ h₁ h₂

end Probabilistic

end InteractingSLE.WangWu
