/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.PrefixLocalLine
import InteractingSLE.WangWu.MeanIdentLine
import InteractingSLE.WangWu.Chamber2

/-!
# Single-line side values of a full level-line coupling (repair of PROVE-WW-B5/B7)

Packet PROVE-WW-B8. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), proof of
Proposition 4.19 (text dump L1660–1668): "The complete curve `β` is local by the terminal Gaussian-kernel limit. On a
compact subarc of `β`, compare with a sufficiently long finite prefix … Local-set boundary compatibility therefore gives
the boundary value `+λ` from `R`."

PROVE-WW-B5's `ae_hasLeftSideLimit_of_prefix` and PROVE-WW-B7's `ae_hasSideLimits_of_prefix_meanAt` assume
`IsLocalSet (arcRange γ)` and `IsLocalSet (arcPrefix γ (n + 1))`, which never hold (both sets contain `0 ∉ ℍ`;
`not_isLocalSet_arcRange`). Here the same arguments run with the local sets `arcRange γ ∩ ℍ` and `arcPrefix γ (n+1) ∩ ℍ`:
the hitting σ-algebra, the germ σ-algebra and the local-set mean do not see the real point (`comap_inter_H`,
`germSigma_inter_H`, `isLocalSetMean_inter_H_iff`).

## Main results

* `ae_isUnionBoundaryLimit_prefix_inter`, `ae_hasLeftSideLimit_of_prefix_inter`, `ae_hasRightSideLimit_of_prefix_inter`:
  B5's statements with satisfiable locality hypotheses;
* **`IsFullLevelLineCoupling.ae_hasSideLimits_line`**: for a full level-line coupling with an admissible seed and
  infinite lifetime whose trace is a simple proper arc `γ` determined by the field, the local-set mean of the complete
  line has the side values `−λ − u₀` on the left and `λ − u₀` on the right (`HasLeftSideLimit`, `HasRightSideLimit`:
  the inputs of Lemma 4.21 and Proposition 4.20). All of B7's remaining inputs (prefix locality, prefix means,
  complete-line locality) are discharged by `PrefixLocal*`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace QuantumZipper Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open LQGMetric (DistOn TestOn IsZeroBoundaryGFF AEDeterminedSigma CondIndepEv)
open LocalSets

/-! ### Random sets up to their real points -/

section Transfer

variable {Ω : Type*}

theorem relClosureH_inter_H (S : Set ℂ) : relClosureH (S ∩ H) = relClosureH S := by
  simp only [relClosureH, inter_assoc, inter_self]

/-- The hitting σ-algebra does not see the real points of a random set. -/
theorem comap_inter_H (A : Ω → Set ℂ) :
    MeasurableSpace.comap (fun ω => A ω ∩ H) hittingSigma = MeasurableSpace.comap A hittingSigma := by
  rw [← comap_relClosureH_comp (fun ω => A ω ∩ H), ← comap_relClosureH_comp A]
  simp only [relClosureH_inter_H]

theorem measurable_inter_H [mΩ : MeasurableSpace Ω] {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) : Measurable[mΩ, hittingSigma] fun ω => A ω ∩ H := by
  rw [measurable_iff_comap_le, comap_inter_H]
  exact hA.comap_le

theorem germNbhd_inter_H (δ : ℝ) (S : Set ℂ) : germNbhd δ (S ∩ H) = germNbhd δ S := by
  simp only [germNbhd, inter_assoc, inter_self]

/-- The germ σ-algebra does not see the real points of a random set. -/
theorem germSigma_inter_H (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    germSigma (fun ω => A ω ∩ H) h = germSigma A h := by
  simp only [germSigma, germSigmaAt, comap_inter_H, germNbhd_inter_H]

theorem H_diff_inter_H (S : Set ℂ) : H \ (S ∩ H) = H \ S := by
  ext z
  simp only [Set.mem_sdiff, mem_inter_iff]
  tauto

/-- The local-set mean does not see the real points of a random set. -/
theorem isLocalSetMean_inter_H_iff [MeasurableSpace Ω] {P : Measure Ω} {A : Ω → Set ℂ}
    {h g : Ω → DistOn upperHalfPlaneOpens} :
    IsLocalSetMean (fun ω => A ω ∩ H) h P g ↔ IsLocalSetMean A h P g := by
  unfold IsLocalSetMean
  rw [germSigma_inter_H]
  simp only [H_diff_inter_H]

/-- The conclusion of Proposition 3.8 for `(A₁ ∩ ℍ, A₂ ∩ ℍ)` gives it for `(A₁, A₂)` when the points of `A₂` off `ℍ`
are real. -/
theorem IsUnionBoundaryLimit.of_inter_H {A₁ A₂ : Set ℂ} (hA₂ : ∀ z ∈ A₂, z ∉ H → z.im = 0)
    {g g₂ : DistOn upperHalfPlaneOpens} (h : IsUnionBoundaryLimit (A₁ ∩ H) (A₂ ∩ H) g g₂) :
    IsUnionBoundaryLimit A₁ A₂ g g₂ := by
  obtain ⟨u, hu, hug, hlim⟩ := h
  have e : H \ (A₁ ∩ H ∪ A₂ ∩ H) = H \ (A₁ ∪ A₂) := by
    rw [← union_inter_distrib_right, H_diff_inter_H]
  rw [e] at hu hug hlim
  refine ⟨u, hu, hug, fun z₀ hz₀ ⟨r, hr, hsub⟩ => hlim z₀ ?_ ⟨r, hr, fun z hz => ⟨hsub ⟨hz.1.1, hz.2⟩, hz.1.2⟩⟩⟩
  rcases hz₀ with hz | hz
  · by_cases hzH : z₀ ∈ H
    · exact Or.inl ⟨hz, hzH⟩
    · exact Or.inr (hA₂ z₀ hz hzH)
  · exact Or.inr hz

theorem lowerUnion_inter_H (S : Set ℂ) : lowerUnion (S ∩ H) = lowerUnion S := by
  ext z
  simp only [lowerUnion, mem_union, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro (⟨h1, -⟩ | h2)
    · exact Or.inl h1
    · exact Or.inr h2
  · rintro (h1 | h2)
    · by_cases hz : z ∈ H
      · exact Or.inl ⟨h1, hz⟩
      · right
        simpa [H] using hz
    · exact Or.inr h2

theorem IsProperArc.im_eq_zero_of_mem_arcPrefix {γ : ℝ → ℂ} (hγ : IsProperArc γ) {t : ℝ} {z : ℂ}
    (hz : z ∈ arcPrefix γ t) (hzH : z ∉ H) : z.im = 0 := by
  obtain ⟨s, hs, rfl⟩ := hz
  rcases hs.1.lt_or_eq with h | h
  · exact absurd (hγ.mem_H s h) hzH
  · rw [← h, hγ.zero]
    simp

theorem IsProperArc.im_eq_zero_of_mem_arcRange {γ : ℝ → ℂ} (hγ : IsProperArc γ) {z : ℂ}
    (hz : z ∈ arcRange γ) (hzH : z ∉ H) : z.im = 0 := by
  obtain ⟨s, hs, rfl⟩ := hz
  rcases (mem_Ici.1 hs).lt_or_eq with h | h
  · exact absurd (hγ.mem_H s h) hzH
  · rw [← h, hγ.zero]
    simp

end Transfer

/-! ### PROVE-WW-B5's prefix comparison with satisfiable locality hypotheses -/

section Prefix

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 3.8 against every prefix** (PROVE-WW-B5's `ae_isUnionBoundaryLimit_prefix` with the local sets
`arcRange γ ∩ ℍ` and `arcPrefix γ (n + 1) ∩ ℍ`). -/
theorem ae_isUnionBoundaryLimit_prefix_inter (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {γ : Ω → ℝ → ℂ} (harc : ∀ᵐ ω ∂P, IsProperArc (γ ω))
    (hm : Measurable[mΩ, hittingSigma] fun ω => arcRange (γ ω))
    (hdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hloc : IsLocalSet (fun ω => arcRange (γ ω) ∩ H) h P)
    (hpm : ∀ n : ℕ, Measurable[mΩ, hittingSigma] fun ω => arcPrefix (γ ω) (n + 1))
    (hploc : ∀ n : ℕ, IsLocalSet (fun ω => arcPrefix (γ ω) (n + 1) ∩ H) h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) h P g)
    {gp : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgp : ∀ n : ℕ, IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1)) h P (gp n)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, IsUnionBoundaryLimit (arcRange (γ ω)) (arcPrefix (γ ω) (n + 1)) (g ω) (gp n ω) := by
  refine ae_all_iff.2 fun n => ?_
  have hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (γ ω) ∩ H) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcPrefix (γ ω) (n + 1) ∩ H) hittingSigma) P := by
    rw [comap_inter_H, comap_inter_H]
    exact Sec6.condIndepEv_of_le_aeSigma hh.measurable.comap_le (hpm n).comap_le fun s hs => hdet s hs
  have e : (fun ω => arcRange (γ ω) ∩ H ∪ arcPrefix (γ ω) (n + 1) ∩ H) = fun ω => arcRange (γ ω) ∩ H := by
    funext ω
    exact union_eq_left.2 (inter_subset_inter_left _ (arcPrefix_subset _ _))
  have hg' : IsLocalSetMean (fun ω => arcRange (γ ω) ∩ H ∪ arcPrefix (γ ω) (n + 1) ∩ H) h P g := by
    rw [e]
    exact isLocalSetMean_inter_H_iff.2 hg
  have hgp' : IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1) ∩ H) h P (gp n) :=
    isLocalSetMean_inter_H_iff.2 (hgp n)
  have hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (arcPrefix (γ ω) (n + 1) ∩ H),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (arcPrefix (γ ω) (n + 1) ∩ H)) z) := by
    filter_upwards [harc] with ω hω
    rw [lowerUnion_inter_H]
    exact not_isBounded_of_isPreconnected_union_real (hω.isPreconnected_prefix_union_real (by positivity))
  have hU := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh (measurable_inter_H hm)
    (measurable_inter_H (hpm n)) hci hloc (hploc n) hunb hg' hgp'
  filter_upwards [hU, harc] with ω hω hγ
  exact IsUnionBoundaryLimit.of_inter_H (fun z hz hzH => hγ.im_eq_zero_of_mem_arcPrefix hz hzH) hω

/-- **Left-side values of a complete seed line from those of its prefixes** (PROVE-WW-B5's
`ae_hasLeftSideLimit_of_prefix` with satisfiable locality hypotheses). -/
theorem ae_hasLeftSideLimit_of_prefix_inter (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {γ : Ω → ℝ → ℂ} (harc : ∀ᵐ ω ∂P, IsProperArc (γ ω))
    (hm : Measurable[mΩ, hittingSigma] fun ω => arcRange (γ ω))
    (hdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hloc : IsLocalSet (fun ω => arcRange (γ ω) ∩ H) h P)
    (hpm : ∀ n : ℕ, Measurable[mΩ, hittingSigma] fun ω => arcPrefix (γ ω) (n + 1))
    (hploc : ∀ n : ℕ, IsLocalSet (fun ω => arcPrefix (γ ω) (n + 1) ∩ H) h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) h P g)
    {gp : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgp : ∀ n : ℕ, IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1)) h P (gp n)) {ℓ : ℂ → ℝ}
    (hpℓ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ arcPrefix (γ ω) (n + 1)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix (γ ω) (n + 1) →
        gp n ω φ = ∫ z, v z * φ z) ∧
      ∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 →
        Tendsto v (𝓝[leftSideOf (arcRange (γ ω))] (γ ω s)) (𝓝 (ℓ (γ ω s)))) :
    ∀ᵐ ω ∂P, HasLeftSideLimit (g ω) (γ ω) ℓ := by
  filter_upwards [harc, hpℓ, ae_isUnionBoundaryLimit_prefix_inter hh harc hm hdet hloc hpm hploc hg hgp]
    with ω hω hpω huω
  exact exists_rep_tendsto_side_of_prefix hω (fun z hz => hz.1) hpω huω

/-- **Right-side values of a complete seed line from those of its prefixes** (mirror). -/
theorem ae_hasRightSideLimit_of_prefix_inter (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {γ : Ω → ℝ → ℂ} (harc : ∀ᵐ ω ∂P, IsProperArc (γ ω))
    (hm : Measurable[mΩ, hittingSigma] fun ω => arcRange (γ ω))
    (hdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hloc : IsLocalSet (fun ω => arcRange (γ ω) ∩ H) h P)
    (hpm : ∀ n : ℕ, Measurable[mΩ, hittingSigma] fun ω => arcPrefix (γ ω) (n + 1))
    (hploc : ∀ n : ℕ, IsLocalSet (fun ω => arcPrefix (γ ω) (n + 1) ∩ H) h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) h P g)
    {gp : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgp : ∀ n : ℕ, IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1)) h P (gp n)) {ℓ : ℂ → ℝ}
    (hpℓ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ arcPrefix (γ ω) (n + 1)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix (γ ω) (n + 1) →
        gp n ω φ = ∫ z, v z * φ z) ∧
      ∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 →
        Tendsto v (𝓝[rightSideOf (arcRange (γ ω))] (γ ω s)) (𝓝 (ℓ (γ ω s)))) :
    ∀ᵐ ω ∂P, HasRightSideLimit (g ω) (γ ω) ℓ := by
  filter_upwards [harc, hpℓ, ae_isUnionBoundaryLimit_prefix_inter hh harc hm hdet hloc hpm hploc hg hgp]
    with ω hω hpω huω
  exact exists_rep_tendsto_side_of_prefix hω (fun z hz => hz.1) hpω huω

end Prefix

/-! ### The full level-line coupling -/

section Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {F : Ω → DistOn upperHalfPlaneOpens}

/-- The positive-time part of a prefix of a proper arc. -/
theorem IsProperArc.arcPrefix_inter_H {γ : ℝ → ℂ} (hγ : IsProperArc γ) (t : ℝ) :
    arcPrefix γ t ∩ H = γ '' Ioc 0 t := by
  ext z
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hzH⟩
    rcases hs.1.lt_or_eq with h | h
    · exact ⟨s, ⟨h, hs.2⟩, rfl⟩
    · rw [← h, hγ.zero] at hzH
      simp [H] at hzH
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, Ioc_subset_Icc_self hs, rfl⟩, hγ.mem_H s hs.1⟩

/-- **Single-line side values of a full level-line coupling** (proof of Wang–Wu Proposition 4.19, "local-set boundary
compatibility therefore gives the boundary value `+λ` from `R`"; the inputs `HasLeftSideLimit`/`HasRightSideLimit` of
Lemma 4.21 and Proposition 4.20). Let a full level-line coupling (Definition 1.5) have an admissible seed, infinite
lifetime, a continuous generating trace (`htr`) and a Loewner trace `γ` that is almost surely a simple proper arc whose
range and prefixes are hitting-measurable and whose range is determined by the field. Then the local-set mean `g` of
the complete line for the centred field `F − u₀` has the side values `−λ − u₀` on the left and `λ − u₀` on the right of
`γ`. -/
theorem IsFullLevelLineCoupling.ae_hasSideLimits_line [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ᵐ ω ∂P, IsLoewnerTrace (Ito.rpath (W · ω)) (γ ω) ∧ IsProperArc (γ ω))
    (hm : Measurable[mΩ, hittingSigma] fun ω => arcRange (γ ω))
    (hpm : ∀ n : ℕ, Measurable[mΩ, hittingSigma] fun ω => arcPrefix (γ ω) (n + 1))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap (WholeField.centredField F u₀) inferInstance) P)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) (WholeField.centredField F u₀) P g) :
    (∀ᵐ ω ∂P, HasLeftSideLimit (g ω) (γ ω) fun z => -wwLambda - u₀ z) ∧
      ∀ᵐ ω ∂P, HasRightSideLimit (g ω) (γ ω) fun z => wwLambda - u₀ z := by
  have hE := hF.1
  obtain ⟨hX, -⟩ := hF.2.2
  have hh0 := hF.isZeroBoundaryGFF_centredField htr hseed hu₀
  set h0 := WholeField.centredField F u₀ with hh0def
  have hloc := hF.isLocalSet_line htr hseed hζ hγ hu₀
  have harc : ∀ᵐ ω ∂P, IsProperArc (γ ω) := hγ.mono fun ω h => h.2
  -- the prefixes at the integer times `n + 1`
  set τ : ℕ → Ω → WithTop ℝ≥0 := fun n _ => (((n : ℝ≥0) + 1 : ℝ≥0) : WithTop ℝ≥0) with hτdef
  have hτ : ∀ n : ℕ, IsStoppingTime (drivingFiltration P hX) (τ n) := fun n => isStoppingTime_const _ _
  have hτζ : ∀ n : ℕ, ∀ᵐ ω ∂P, (τ n ω : ℝ≥0∞) < ζ ω := fun n => by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact WithTop.coe_lt_top _
  have hτu : ∀ (n : ℕ) (ω : Ω), (τ n ω).untopD 0 = (n : ℝ≥0) + 1 := fun n ω => WithTop.untopD_coe _ _
  have hτn : ∀ (n : ℕ) (ω : Ω), (((τ n ω).untopD 0 : ℝ≥0) : ℝ) = (n : ℝ) + 1 := fun n ω => by
    rw [hτu n ω]; push_cast; ring
  have hKn : ∀ n : ℕ, ∀ᵐ ω ∂P, arcPrefix (γ ω) ((n : ℝ) + 1) ∩ H =
      fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ n ω).untopD 0 : ℝ≥0) := fun n => by
    filter_upwards [hγ] with ω hγω
    rw [hτn n ω, hγω.2.arcPrefix_inter_H]
    exact (fwdHull_eq_image_Ioc hγω.1 hγω.2 (by positivity)).symm
  have hploc : ∀ n : ℕ, IsLocalSet (fun ω => arcPrefix (γ ω) (n + 1) ∩ H) h0 P := fun n =>
    Coupling.IsLocalSet.congr_set (hF.isLocalSet_hull_centredField htr hu₀.1 hh0 hX (hτ n) (hτζ n)) (hKn n)
  have hgex : ∀ n : ℕ, ∃ g' : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1) ∩ H) h0 P g' := fun n =>
    IsLocalSet.exists_isLocalSetMean hh0 (measurable_inter_H (hpm n)) (hploc n)
  choose gp hgp using hgex
  have hrep : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ H \ (arcPrefix (γ ω) (n + 1) ∩ H) →
        gp n ω φ = ∫ z, (meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
          ((τ n ω).untopD 0) z - u₀ z) * φ z := fun n =>
    hF.ae_apply_eq_of_isLocalSetMean_hull htr hseed hu₀ hX (hτ n) (hτζ n) (measurable_inter_H (hpm n))
      (hKn n) (hgp n)
  -- the per-sample prefix representatives with their side values
  have hpre : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ arcPrefix (γ ω) (n + 1)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix (γ ω) (n + 1) →
        gp n ω φ = ∫ z, v z * φ z) ∧
      (∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 →
        Tendsto v (𝓝[leftSideOf (arcRange (γ ω))] (γ ω s)) (𝓝 (-wwLambda - u₀ (γ ω s)))) ∧
      ∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 →
        Tendsto v (𝓝[rightSideOf (arcRange (γ ω))] (γ ω s)) (𝓝 (wwLambda - u₀ (γ ω s))) := by
    filter_upwards [hE.2.2.2.2, hζ, hγ, ae_all_iff.2 hrep] with ω hp hz hγω hr n
    have hw : Continuous fun t => W t ω := by
      have h1 := hp.2.2.2.1
      rw [hz] at h1
      exact continuousOn_univ.1 (by simpa using h1)
    have ht : (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
    have hcast : (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
    have h1 := exists_rep_tendsto_sides_prefix_sub hp hw hγω.1 hγω.2 ht hu₀.1 (g := gp n ω)
      (fun φ hφ => by
        rw [hcast] at hφ
        have := hr n φ (by rwa [H_diff_inter_H])
        rw [hτu n ω] at this
        exact this)
    rw [hcast] at h1
    exact h1
  have hgp' : ∀ n : ℕ, IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1)) h0 P (gp n) := fun n =>
    isLocalSetMean_inter_H_iff.1 (hgp n)
  refine ⟨ae_hasLeftSideLimit_of_prefix_inter hh0 harc hm hdet hloc hpm hploc hg hgp' ?_,
    ae_hasRightSideLimit_of_prefix_inter hh0 harc hm hdet hloc hpm hploc hg hgp' ?_⟩
  · filter_upwards [hpre] with ω hω n
    obtain ⟨v, h1, h2, h3, -⟩ := hω n
    exact ⟨v, h1, h2, h3⟩
  · filter_upwards [hpre] with ω hω n
    obtain ⟨v, h1, h2, -, h4⟩ := hω n
    exact ⟨v, h1, h2, h4⟩

end Coupling

/-! ### PROVE-WW-B7's Proposition 4.20 exterior components with satisfiable locality hypotheses -/

section Exterior

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Wang–Wu Proposition 4.20, the left exterior component** (PROVE-WW-B7's `ae_eq_on_leftSideOf_union` with the local
sets `arcRange R ∩ ℍ`, `arcRange L ∩ ℍ`): for two ordered proper arcs (`L` left of `R`), almost surely the mean of the
union agrees with the single-line mean of `L` on every test function supported in the left side of `L`. -/
theorem ae_eq_on_leftSideOf_union_inter (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω) ∩ H) h P)
    (hLloc : IsLocalSet (fun ω => arcRange (L ω) ∩ H) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (arcRange (L ω)) (rightSideOf (arcRange (R ω))))
    {g gL : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => arcRange (R ω) ∪ arcRange (L ω)) h P g)
    (hgL : IsLocalSetMean (fun ω => arcRange (L ω)) h P gL) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ leftSideOf (arcRange (L ω)) → g ω φ = gL ω φ := by
  set C : Ω → Set ℂ := fun ω => leftSideOf (relClosureH (arcRange (L ω))) with hCdef
  have hCm : Measurable[MeasurableSpace.comap (fun ω => arcRange (L ω) ∩ H) hittingSigma, hittingSigma]
      fun ω => H \ C ω := by
    rw [comap_inter_H]
    exact measurable_compl_leftSideOf_relClosureH.comp (comap_measurable _)
  have hCeq : ∀ᵐ ω ∂P, C ω = leftSideOf (arcRange (L ω)) := by
    filter_upwards [harc] with ω hω
    exact hω.2.leftSideOf_relClosureH
  have hC : ∀ᵐ ω ∂P, C ω ⊆ H \ (arcRange (L ω) ∩ H) ∧
      ∀ z ∈ C ω, connectedComponentIn (H \ (arcRange (L ω) ∩ H)) z ⊆ C ω := by
    filter_upwards [hCeq] with ω hω
    rw [hω, H_diff_inter_H]
    exact ⟨fun z hz => hz.1, fun z hz w hw => mem_leftSideOf_of_mem_connectedComponentIn hz hw⟩
  have hCA₂ : ∀ᵐ ω ∂P, Disjoint (C ω) (arcRange (R ω) ∩ H) := by
    filter_upwards [hCeq, harc, hord] with ω hω hω' hord'
    rw [hω]
    exact Set.disjoint_left.2 fun z hz hzR =>
      (hω'.1.leftSideOf_subset_of_disjoint hω'.2 hord' hz).1.2 hzR.1
  have e : (fun ω => arcRange (L ω) ∩ H ∪ arcRange (R ω) ∩ H) =
      fun ω => (arcRange (R ω) ∪ arcRange (L ω)) ∩ H :=
    funext fun ω => by rw [← union_inter_distrib_right, union_comm]
  have hg' : IsLocalSetMean (fun ω => arcRange (L ω) ∩ H ∪ arcRange (R ω) ∩ H) h P g := by
    rw [e]
    exact isLocalSetMean_inter_H_iff.2 hg
  have hci' : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (L ω) ∩ H) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (R ω) ∩ H) hittingSigma) P := by
    rw [comap_inter_H, comap_inter_H]
    exact hci
  have key := IsLocalSetMean.ae_eq_on_of_union hh (measurable_inter_H hLm) (measurable_inter_H hRm) hci' hLloc
    hRloc hCm hC hCA₂ hg' (isLocalSetMean_inter_H_iff.2 hgL)
  filter_upwards [key, hCeq] with ω hω hCω φ hφ
  exact hω φ (hCω ▸ hφ)

/-- **Wang–Wu Proposition 4.20, the right exterior component** (PROVE-WW-B7's `ae_eq_on_rightSideOf_union` with
satisfiable locality hypotheses). -/
theorem ae_eq_on_rightSideOf_union_inter (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω) ∩ H) h P)
    (hLloc : IsLocalSet (fun ω => arcRange (L ω) ∩ H) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (arcRange (L ω)) (rightSideOf (arcRange (R ω))))
    {g gR : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => arcRange (R ω) ∪ arcRange (L ω)) h P g)
    (hgR : IsLocalSetMean (fun ω => arcRange (R ω)) h P gR) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ rightSideOf (arcRange (R ω)) → g ω φ = gR ω φ := by
  set C : Ω → Set ℂ := fun ω => rightSideOf (relClosureH (arcRange (R ω))) with hCdef
  have hCm : Measurable[MeasurableSpace.comap (fun ω => arcRange (R ω) ∩ H) hittingSigma, hittingSigma]
      fun ω => H \ C ω := by
    rw [comap_inter_H]
    exact measurable_compl_rightSideOf_relClosureH.comp (comap_measurable _)
  have hCeq : ∀ᵐ ω ∂P, C ω = rightSideOf (arcRange (R ω)) := by
    filter_upwards [harc] with ω hω
    exact hω.1.rightSideOf_relClosureH
  have hC : ∀ᵐ ω ∂P, C ω ⊆ H \ (arcRange (R ω) ∩ H) ∧
      ∀ z ∈ C ω, connectedComponentIn (H \ (arcRange (R ω) ∩ H)) z ⊆ C ω := by
    filter_upwards [hCeq] with ω hω
    rw [hω, H_diff_inter_H]
    exact ⟨fun z hz => hz.1, fun z hz w hw => mem_rightSideOf_of_mem_connectedComponentIn hz hw⟩
  have hCA₂ : ∀ᵐ ω ∂P, Disjoint (C ω) (arcRange (L ω) ∩ H) := by
    filter_upwards [hCeq, hord] with ω hω hord'
    rw [hω]
    exact hord'.symm.mono_right inter_subset_left
  have e : (fun ω => arcRange (R ω) ∩ H ∪ arcRange (L ω) ∩ H) =
      fun ω => (arcRange (R ω) ∪ arcRange (L ω)) ∩ H :=
    funext fun ω => by rw [← union_inter_distrib_right]
  have hg' : IsLocalSetMean (fun ω => arcRange (R ω) ∩ H ∪ arcRange (L ω) ∩ H) h P g := by
    rw [e]
    exact isLocalSetMean_inter_H_iff.2 hg
  have hci' : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (R ω) ∩ H) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (L ω) ∩ H) hittingSigma) P := by
    rw [comap_inter_H, comap_inter_H]
    exact hci
  have key := IsLocalSetMean.ae_eq_on_of_union hh (measurable_inter_H hRm) (measurable_inter_H hLm) hci' hRloc
    hLloc hCm hC hCA₂ hg' (isLocalSetMean_inter_H_iff.2 hgR)
  filter_upwards [key, hCeq] with ω hω hCω φ hφ
  exact hω φ (hCω ▸ hφ)

end Exterior

/-! ### PROVE-WW-B6's Lemma 4.21 with satisfiable locality hypotheses -/

section NoCommonArc

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Wang–Wu Lemma 4.21 (no common nontrivial arc)**, PROVE-WW-B6's `ae_interior_contact_eq_empty` with the local sets
`arcRange R ∩ ℍ`, `arcRange L ∩ ℍ`. -/
theorem ae_interior_contact_eq_empty_inter (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω) ∩ H) h P)
    (hLloc : IsLocalSet (fun ω => arcRange (L ω) ∩ H) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (arcRange (L ω)) (rightSideOf (arcRange (R ω))))
    {gR gL : Ω → DistOn upperHalfPlaneOpens}
    (hgR : IsLocalSetMean (fun ω => arcRange (R ω)) h P gR)
    (hgL : IsLocalSetMean (fun ω => arcRange (L ω)) h P gL) {ℓR ℓL : ℂ → ℝ}
    (hℓR : ∀ᵐ ω ∂P, HasLeftSideLimit (gR ω) (R ω) ℓR)
    (hℓL : ∀ᵐ ω ∂P, HasLeftSideLimit (gL ω) (L ω) ℓL) (hℓ : ∀ z ∈ H, ℓR z ≠ ℓL z) :
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
  filter_upwards [harc, hord, hℓR, hℓL, p₁, p₂] with ω hω hoω hRω hLω h₁ h₂
  exact interior_contact_eq_empty_of_means hω.1 hω.2 hoω hRω hLω hℓ
    (IsUnionBoundaryLimit.of_inter_H (fun z hz hzH => hω.1.im_eq_zero_of_mem_arcRange hz hzH) h₁)
    (IsUnionBoundaryLimit.of_inter_H (fun z hz hzH => hω.2.im_eq_zero_of_mem_arcRange hz hzH) h₂)

end NoCommonArc

/-! ### PROVE-WW-B5/B6's chamber identification with satisfiable locality hypotheses -/

section Chamber

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The union of two field-determined seed lines and its mean between the walls** (PROVE-WW-B5's
`ae_tendsto_unionMean_between` with the local sets `arcRange · ∩ ℍ`; the union local set is
`(arcRange R ∪ arcRange L) ∩ ℍ`). -/
theorem ae_tendsto_unionMean_between_inter (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hRdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hLdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω) ∩ H) h P)
    (hLloc : IsLocalSet (fun ω => arcRange (L ω) ∩ H) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    {gR gL : Ω → DistOn upperHalfPlaneOpens}
    (hgR : IsLocalSetMean (fun ω => arcRange (R ω)) h P gR)
    (hgL : IsLocalSetMean (fun ω => arcRange (L ω)) h P gL) {ℓR ℓL : ℂ → ℝ}
    (hℓR : ∀ᵐ ω ∂P, HasLeftSideLimit (gR ω) (R ω) ℓR)
    (hℓL : ∀ᵐ ω ∂P, HasRightSideLimit (gL ω) (L ω) ℓL) :
    (IsLocalSet (fun ω => (arcRange (R ω) ∪ arcRange (L ω)) ∩ H) h P ∧
      AEDeterminedSigma
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
  have hRm' := measurable_inter_H hRm
  have hLm' := measurable_inter_H hLm
  have hRdet' : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (R ω) ∩ H) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P := by
    rw [comap_inter_H]; exact hRdet
  have hLdet' : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (L ω) ∩ H) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P := by
    rw [comap_inter_H]; exact hLdet
  obtain ⟨hlocU, hdetU⟩ := isLocalSet_union_of_aeDetermined hh hRm' hLm' hRloc hLloc hRdet' hLdet'
  have eU : (fun ω => arcRange (R ω) ∩ H ∪ arcRange (L ω) ∩ H) =
      fun ω => (arcRange (R ω) ∪ arcRange (L ω)) ∩ H :=
    funext fun ω => (union_inter_distrib_right _ _ _).symm
  rw [eU] at hlocU hdetU
  rw [comap_inter_H] at hdetU
  refine ⟨⟨hlocU, hdetU⟩, fun g hg => ?_⟩
  have hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (R ω) ∩ H) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (L ω) ∩ H) hittingSigma) P := by
    rw [comap_inter_H, comap_inter_H]
    exact Sec6.condIndepEv_of_le_aeSigma hh.measurable.comap_le hLm.comap_le fun s hs => hRdet s hs
  have hgU : IsLocalSetMean (fun ω => arcRange (R ω) ∩ H ∪ arcRange (L ω) ∩ H) h P g := by
    rw [eU]; exact isLocalSetMean_inter_H_iff.2 hg
  have e : (fun ω => arcRange (R ω) ∩ H ∪ arcRange (L ω) ∩ H) =
      fun ω => arcRange (L ω) ∩ H ∪ arcRange (R ω) ∩ H := by
    funext ω; exact union_comm _ _
  have hg' : IsLocalSetMean (fun ω => arcRange (L ω) ∩ H ∪ arcRange (R ω) ∩ H) h P g := e ▸ hgU
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
  have p₁ := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh hLm' hRm' hci.symm hLloc hRloc hunbR hg'
    (isLocalSetMean_inter_H_iff.2 hgR)
  have p₂ := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hh hRm' hLm' hci hRloc hLloc hunbL hgU
    (isLocalSetMean_inter_H_iff.2 hgL)
  filter_upwards [harc, hℓR, hℓL, p₁, p₂] with ω hω hRω hLω h₁ h₂
  exact exists_unionRep_tendsto_between hω.1 hω.2 hRω hLω
    (IsUnionBoundaryLimit.of_inter_H (fun z hz hzH => hω.1.im_eq_zero_of_mem_arcRange hz hzH) h₁)
    (IsUnionBoundaryLimit.of_inter_H (fun z hz hzH => hω.2.im_eq_zero_of_mem_arcRange hz hzH) h₂)

/-- **The union mean on every chamber between two ordered seed lines** (PROVE-WW-B6's `ae_eqOn_chamber` with
satisfiable locality hypotheses). -/
theorem ae_eqOn_chamber_inter (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hRdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hLdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω) ∩ H) h P)
    (hLloc : IsLocalSet (fun ω => arcRange (L ω) ∩ H) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (arcRange (L ω)) (rightSideOf (arcRange (R ω))))
    {gR gL : Ω → DistOn upperHalfPlaneOpens}
    (hgR : IsLocalSetMean (fun ω => arcRange (R ω)) h P gR)
    (hgL : IsLocalSetMean (fun ω => arcRange (L ω)) h P gL) {ℓR ℓL : ℂ → ℝ}
    (hℓR : ∀ᵐ ω ∂P, HasLeftSideLimit (gR ω) (R ω) ℓR)
    (hℓL : ∀ᵐ ω ∂P, HasRightSideLimit (gL ω) (L ω) ℓL)
    (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean (fun ω => arcRange (R ω) ∪ arcRange (L ω)) h P g) :
    ∀ᵐ ω ∂P, ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (arcRange (R ω) ∪ arcRange (L ω))) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (arcRange (R ω) ∪ arcRange (L ω)) →
        g ω φ = ∫ z, w z * φ z) ∧
      ∀ C ∈ betweenComponents (arcRange (R ω)) (arcRange (L ω)),
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v C → (∃ M, ∀ z ∈ C, |v z| ≤ M) →
      (∀ s > 0, R ω s ∉ arcRange (L ω) → Tendsto v (𝓝[C] (R ω s)) (𝓝 (ℓR (R ω s)))) →
      (∀ s > 0, L ω s ∉ arcRange (R ω) → Tendsto v (𝓝[C] (L ω s)) (𝓝 (ℓL (L ω s)))) →
      EqOn w v C := by
  obtain ⟨⟨hloc, -⟩, hwall⟩ := ae_tendsto_unionMean_between_inter hh hRm hLm hRdet hLdet hRloc hLloc harc
    hgR hgL hℓR hℓL
  have hA : Measurable[mΩ, hittingSigma] fun ω => (arcRange (R ω) ∪ arcRange (L ω)) ∩ H :=
    measurable_inter_H (measurable_union_hitting hRm hLm)
  have hmean := Sec6.IsLocalSetMean.ae_eq_condExp_germSigma hh hA hloc (isLocalSetMean_inter_H_iff.2 hg)
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ ((arcRange (R ω) ∪ arcRange (L ω)) ∩ H)) := hloc.2.1.mono fun _ h => h.2
  filter_upwards [hwall g hg, ae_eqOn_of_condMean_global hh hmean hopen, harc, hord] with
    ω ⟨w, hw, hrep, hwR, hwL⟩ hcor hω hordω
  simp only [H_diff_inter_H] at hcor
  exact ⟨w, hw, hrep, fun C hC v hv hvb hvR hvL =>
    eqOn_chamber_of_cor48 hω.1 hω.2 hordω hwR hwL (hcor w hw hrep) hC hv hvb hvR hvL⟩

end Chamber

end InteractingSLE.WangWu
