import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lusin's continuity theorem (track CC, packet CC5, target T1)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D7** ("Lusin"). Mathlib (at the
pinned commit) has Lusin's *separation* theorem and the Lusin–Souslin theorem
(`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`), but not Lusin's *continuity* theorem, which is
proved here.

**Theorem** (`exists_isCompact_measure_compl_lt_continuousOn`). Let `S` be a Polish space with its Borel
σ-algebra, `μ` a finite measure on `S`, `T` a second-countable topological space whose open sets are
measurable, and `F : S → T` measurable. For every `ε > 0` there is a compact `K ⊆ S` with `μ Kᶜ < ε` such
that `F` is continuous on `K`.

*Proof* (D7). Let `b` be a countable basis of `T` and choose `δ_B > 0` (`B ∈ b`) with `∑ δ_B < ε / 2`.
1. `μ` is weakly regular (`Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure`), so for each
   `B ∈ b` there are a closed `C_B` and an open `U_B` with `C_B ⊆ F⁻¹ B ⊆ U_B` and
   `μ (U_B \ C_B) < δ_B`.
2. `G := ⋃_B (U_B \ C_B)` is open with `μ G < ε / 2`.
3. `μ` is tight (Polish space: `InnerRegularCompactLTTop`), so there is a compact `K₀` with
   `μ K₀ᶜ < ε / 2`. Put `K := K₀ \ G`: compact, with `μ Kᶜ ≤ μ K₀ᶜ + μ G < ε`.
4. For `x ∈ K`: `x ∈ U_B → x ∈ C_B ⊆ F⁻¹ B`, so `F⁻¹ B ∩ K = U_B ∩ K`. Every open `t ⊆ T` is a union
   of basic sets, so `F⁻¹ t ∩ K = (⋃_{B ⊆ t} U_B) ∩ K` is relatively open: `F` is continuous on `K`. ∎
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace SmallGammaGeodesics.CC

/-- Closed-inside/open-outside approximation of a measurable set of finite measure for a weakly
regular measure: `C ⊆ A ⊆ U`, `C` closed, `U` open, `μ (U \ C) < δ`. -/
theorem exists_isClosed_isOpen_sdiff_lt {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] {μ : Measure S} [μ.WeaklyRegular] {A : Set S} (hA : MeasurableSet A)
    (hAμ : μ A ≠ ∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ C U : Set S, IsClosed C ∧ IsOpen U ∧ C ⊆ A ∧ A ⊆ U ∧ μ (U \ C) < δ := by
  have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ).ne'
  obtain ⟨C, hCA, hCc, hC⟩ := hA.exists_isClosed_sdiff_lt hAμ hδ2
  obtain ⟨U, hAU, hUo, -, hU⟩ := hA.exists_isOpen_sdiff_lt hAμ hδ2
  refine ⟨C, U, hCc, hUo, hCA, hAU, ?_⟩
  calc μ (U \ C) ≤ μ ((U \ A) ∪ (A \ C)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxA : x ∈ A
        · exact Or.inr ⟨hxA, hx.2⟩
        · exact Or.inl ⟨hx.1, hxA⟩
    _ ≤ μ (U \ A) + μ (A \ C) := measure_union_le _ _
    _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hU hC
    _ = δ := ENNReal.add_halves δ

/-- **Lusin's continuity theorem** (CC0 D7; target T1 of packet CC5). A measurable map from a Polish
space to a second-countable space is continuous on a compact set of almost full measure. -/
theorem exists_isCompact_measure_compl_lt_continuousOn {S T : Type*} [TopologicalSpace S]
    [PolishSpace S] [MeasurableSpace S] [BorelSpace S] [TopologicalSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [OpensMeasurableSpace T] {F : S → T}
    (hF : Measurable F) (μ : Measure S) [IsFiniteMeasure μ] {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set S, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn F K := by
  classical
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  have : Countable (countableBasis T) := (countable_countableBasis T).to_subtype
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε2 (countableBasis T)
  -- step 1: closed/open approximations of the preimages of the basic open sets
  have happrox : ∀ B : countableBasis T, ∃ C U : Set S, IsClosed C ∧ IsOpen U ∧
      C ⊆ F ⁻¹' (B : Set T) ∧ F ⁻¹' (B : Set T) ⊆ U ∧ μ (U \ C) < δ B := fun B =>
    exists_isClosed_isOpen_sdiff_lt (hF (isOpen_of_mem_countableBasis B.2).measurableSet)
      (measure_ne_top μ _) (hδpos B).ne'
  choose C U hCc hUo hCA hAU hUC using happrox
  -- step 2: the bad open set
  set G : Set S := ⋃ B : countableBasis T, U B \ C B with hG
  have hGo : IsOpen G := isOpen_iUnion fun B => (hUo B).sdiff (hCc B)
  have hGμ : μ G < ε / 2 :=
    (measure_iUnion_le _).trans_lt ((ENNReal.tsum_le_tsum fun B => (hUC B).le).trans_lt hδsum)
  -- step 3: a tight compact set
  obtain ⟨K₀, -, hK₀, hK₀μ⟩ :=
    MeasurableSet.univ.exists_isCompact_sdiff_lt (measure_ne_top μ univ) hε2
  refine ⟨K₀ \ G, hK₀.diff hGo, ?_, ?_⟩
  · calc μ (K₀ \ G)ᶜ ≤ μ ((univ \ K₀) ∪ G) := by
          refine measure_mono fun x hx => ?_
          by_cases hxK : x ∈ K₀
          · exact Or.inr (by_contra fun hxG => hx ⟨hxK, hxG⟩)
          · exact Or.inl ⟨mem_univ x, hxK⟩
      _ ≤ μ (univ \ K₀) + μ G := measure_union_le _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hK₀μ hGμ
      _ = ε := ENNReal.add_halves ε
  -- step 4: continuity on `K₀ \ G`
  · rw [continuousOn_iff']
    intro t ht
    refine ⟨⋃ (B : countableBasis T) (_ : (B : Set T) ⊆ t), U B,
      isOpen_iUnion fun B => isOpen_iUnion fun _ => hUo B, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hxt, hxK⟩
      obtain ⟨B, hBb, hxB, hBt⟩ := (isBasis_countableBasis T).exists_subset_of_mem_open hxt ht
      exact ⟨⟨⟨B, hBb⟩, hBt, hAU ⟨B, hBb⟩ hxB⟩, hxK⟩
    · rintro ⟨⟨B, hBt, hxU⟩, hxK⟩
      refine ⟨hBt ?_, hxK⟩
      have hxC : x ∈ C B := by
        by_contra hxC
        exact hxK.2 (mem_iUnion.2 ⟨B, hxU, hxC⟩)
      exact hCA B hxC

end SmallGammaGeodesics.CC
