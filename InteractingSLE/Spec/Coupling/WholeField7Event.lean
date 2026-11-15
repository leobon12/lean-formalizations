/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField7Induct

/-!
# C.5 at `κ = 4`: label events are events of the stopped history

Packet PROVE-WHOLEFIELD7 (follow-up note C.5, `source/external/AstraIG1/ig1_followup_proofs.txt` L1705–1760; ruling
R38). The reconstruction across the trace (Proposition R1, `WangWu.ae_condExp_exp_eq_gaussCF`) needs a random closed set
`A ⊆ η[0,σ]` whose avoidance events are events of `𝓕_σ` and off which the C.4 kernel holds. It is built from the
rational closed balls that are labels at `σ`; this file shows that "a compact `C ⊆ ℍ` is a label at the driving stop
`σ`" is, up to a null set, an event of `𝓕_σ` (`exists_labelEvent`):

* `{C ∩ K_σ = ∅}` is landed (`exists_measurableSet_ae_iff_disjoint`);
* `{C ⊆ K_σ}` is the intersection over a countable dense subset of `C` (the hull is relatively closed in `ℍ`);
* `C` is a pocket at `σ` iff `C ⊆ K_σ` and, at every rational time `q`, `C` lies inside or outside `K_{q ∧ σ}`
  (`isPocketLabel_iff`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

/-! ### Pockets through rational times -/

section Pocket

variable {w : ℝ≥0 → ℝ} {C : Set ℂ} {t : ℝ≥0}

theorem mem_fwdHull_rpath_iff {z : ℂ} {u : ℝ≥0} :
    z ∈ fwdHull (Ito.rpath w) (u : ℝ) ↔ z ∈ H ∧ swallowTime (Ito.rpath w) z ≤ u := by
  show (z ∈ H ∧ swallowTime (Ito.rpath w) z ≤ ENNReal.ofReal (u : ℝ)) ↔ _
  rw [ENNReal.ofReal_coe_nnreal]

/-- **Pockets through rational times**: `C ⊆ ℍ` is a pocket at `t` iff `C ⊆ K_t` and at every rational `q`, `C` lies
inside or outside `K_{q ∧ t}`. -/
theorem isPocketLabel_iff (hCH : C ⊆ H) :
    IsPocketLabel w C t ↔ C ⊆ fwdHull (Ito.rpath w) (t : ℝ) ∧
      ∀ q : ℚ, C ⊆ fwdHull (Ito.rpath w) ((min (q : ℝ).toNNReal t : ℝ≥0) : ℝ) ∨
        Disjoint C (fwdHull (Ito.rpath w) ((min (q : ℝ).toNNReal t : ℝ≥0) : ℝ)) := by
  constructor
  · intro hp
    refine ⟨hp.subset_fwdHull hCH, fun q => ?_⟩
    obtain ⟨β, hβt, hs⟩ := hp
    by_cases hβ : β ≤ min (q : ℝ).toNNReal t
    · exact Or.inl fun z hz => mem_fwdHull_rpath_iff.2 ⟨hCH hz, by rw [hs z hz]; exact_mod_cast hβ⟩
    · exact Or.inr (isActiveLabel_of_lt_swallowTime fun z hz => by
        rw [hs z hz]; exact_mod_cast not_le.1 hβ)
  · rintro ⟨hsub, hq⟩
    rcases C.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
    · exact ⟨0, zero_le, fun z hz => hz.elim⟩
    have hle : ∀ z ∈ C, swallowTime (Ito.rpath w) z ≤ t := fun z hz => (mem_fwdHull_rpath_iff.1 (hsub hz)).2
    -- two points of `C` have the same swallowing time
    have key : ∀ z ∈ C, ∀ z' ∈ C, ¬ swallowTime (Ito.rpath w) z < swallowTime (Ito.rpath w) z' := by
      intro z hz z' hz' hlt
      have hne : swallowTime (Ito.rpath w) z' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hle z' hz')
      have hne' : swallowTime (Ito.rpath w) z ≠ ⊤ := ne_top_of_lt hlt
      have hlt' : (swallowTime (Ito.rpath w) z).toReal < (swallowTime (Ito.rpath w) z').toReal :=
        (ENNReal.toReal_lt_toReal hne' hne).2 hlt
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
      have hq0 : (0 : ℝ) ≤ q := ENNReal.toReal_nonneg.trans hq1.le
      have hqt : (q : ℝ).toNNReal ≤ t := by
        have h1 : (q : ℝ) ≤ (swallowTime (Ito.rpath w) z').toReal := hq2.le
        have h2 : (swallowTime (Ito.rpath w) z').toReal ≤ t := by
          have := ENNReal.toReal_mono ENNReal.coe_ne_top (hle z' hz')
          simpa using this
        exact Real.toNNReal_le_iff_le_coe.2 (h1.trans h2)
      have hqq := hq q
      rw [min_eq_left hqt] at hqq
      have hzq : swallowTime (Ito.rpath w) z ≤ ((q : ℝ).toNNReal : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal hne', ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hq0]
        exact ENNReal.ofReal_le_ofReal hq1.le
      have hz'q : ((q : ℝ).toNNReal : ℝ≥0∞) < swallowTime (Ito.rpath w) z' := by
        rw [← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hq0]
        exact (ENNReal.ofReal_lt_ofReal_iff (hq0.trans_lt hq2)).2 hq2
      rcases hqq with h | h
      · exact absurd (mem_fwdHull_rpath_iff.1 (h hz')).2 (not_le.2 hz'q)
      · exact Set.disjoint_left.1 h hz (mem_fwdHull_rpath_iff.2 ⟨hCH hz, hzq⟩)
    have hne₀ : swallowTime (Ito.rpath w) z₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hle z₀ hz₀)
    refine ⟨(swallowTime (Ito.rpath w) z₀).toNNReal, ?_, fun z hz => ?_⟩
    · have := hle z₀ hz₀
      rw [← ENNReal.coe_toNNReal hne₀] at this
      exact_mod_cast this
    · rw [ENNReal.coe_toNNReal hne₀]
      exact le_antisymm (not_lt.1 (key z₀ hz₀ z hz)) (not_lt.1 (key z hz z₀ hz₀))

end Pocket

/-! ### Events of the stopped history -/

section Events

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

omit [IsProbabilityMeasure P] in
theorem isStoppingTime_coe_const' {𝓖 : Filtration ℝ≥0 mΩ} (c : ℝ≥0) :
    IsStoppingTime 𝓖 fun _ : Ω => (c : WithTop ℝ≥0) := fun i => by
  by_cases hc : (c : WithTop ℝ≥0) ≤ i
  · simp only [hc, ofPred_true]; exact @MeasurableSet.univ _ (𝓖 i)
  · simp only [hc, ofPred_false]; exact @MeasurableSet.empty _ (𝓖 i)

/-- `{C ∩ K_τ = ∅}` at a real driving stop `τ < ζ`, up to a null set. -/
theorem exists_disjointEvent (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0))
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    ∃ G : Set Ω, MeasurableSet[hτ.measurableSpace] G ∧
      ∀ᵐ ω ∂P, (ω ∈ G ↔ Disjoint C (fwdHull (Ito.rpath (W · ω)) (τ ω : ℝ))) := by
  obtain ⟨σ₀, hσ₀⟩ := exists_isAnnouncingSeq_driving hE hκ hX (not_threshold_seed_of_ae_lt hE hτζ)
  obtain ⟨G, hG, hGe⟩ := exists_measurableSet_ae_iff_disjoint hE hX hσ₀ hτ hτζ hC hCH
  refine ⟨G, hG, hGe.mono fun ω hω => ?_⟩
  simp only [WithTop.untopD_coe] at hω
  exact hω

/-- `{C ⊆ K_τ}` at a real driving stop `τ < ζ`, up to a null set (a countable dense subset of `C` and the relative
closedness of the hull). -/
theorem exists_subsetEvent (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0))
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {C : Set ℂ} (hCH : C ⊆ H) :
    ∃ G : Set Ω, MeasurableSet[hτ.measurableSpace] G ∧
      ∀ᵐ ω ∂P, (ω ∈ G ↔ C ⊆ fwdHull (Ito.rpath (W · ω)) (τ ω : ℝ)) := by
  obtain ⟨D, hDC, hDc, hCD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace C).exists_countable_dense_subset
  have hG : ∀ z ∈ D, ∃ G : Set Ω, MeasurableSet[hτ.measurableSpace] G ∧
      ∀ᵐ ω ∂P, (ω ∈ G ↔ Disjoint {z} (fwdHull (Ito.rpath (W · ω)) (τ ω : ℝ))) := fun z hz =>
    exists_disjointEvent hE hκ hX hτ hτζ isCompact_singleton (singleton_subset_iff.2 (hCH (hDC hz)))
  choose! Gz hGzm hGz using hG
  refine ⟨⋂ z ∈ D, (Gz z)ᶜ, MeasurableSet.biInter hDc fun z hz => (hGzm z hz).compl, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ z ∈ D, (ω ∈ Gz z ↔ Disjoint {z} (fwdHull (Ito.rpath (W · ω)) (τ ω : ℝ))) :=
    (ae_ball_iff hDc).2 hGz
  filter_upwards [hall, hE.2.2.2.2, hτζ] with ω hω hp hlt
  have hopen : IsOpen (H \ fwdHull (Ito.rpath (W · ω)) (τ ω : ℝ)) :=
    MartMeans2.isOpen_H_diff_fwdHull_rpath hp.2.2.2.1 hlt
  constructor
  · intro hω' z hz
    by_contra hzK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen z ⟨hCH hz, hzK⟩
    obtain ⟨d, hdD, hdz⟩ := Metric.mem_closure_iff.1 (hCD hz) ε hε
    have hdK : d ∉ fwdHull (Ito.rpath (W · ω)) (τ ω : ℝ) :=
      (hball (mem_ball.2 (by rw [dist_comm]; exact hdz))).2
    have h1 : ω ∉ Gz d := mem_iInter₂.1 hω' d hdD
    exact h1 ((hω d hdD).2 (Set.disjoint_singleton_left.2 hdK))
  · intro hsub
    refine mem_iInter₂.2 fun z hz hG => ?_
    exact Set.disjoint_singleton_left.1 ((hω z hz).1 hG) (hsub (hDC hz))

/-- **"`C` is a label at `σ`" is an event of `𝓕_σ`**, up to a null set. -/
theorem exists_labelEvent (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    ∃ G : Set Ω, MeasurableSet[hσ.measurableSpace] G ∧ ∀ᵐ ω ∂P, (ω ∈ G ↔ IsLabel (W · ω) C (σ ω)) := by
  obtain ⟨G₁, hG₁, hG₁e⟩ := exists_disjointEvent hE hκ hX hσ hσζ hC hCH
  obtain ⟨G₂, hG₂, hG₂e⟩ := exists_subsetEvent hE hκ hX hσ hσζ hCH
  have hq : ∀ q : ℚ, IsStoppingTime (drivingFiltration P hX)
      fun ω => ((min (q : ℝ).toNNReal (σ ω) : ℝ≥0) : WithTop ℝ≥0) := fun q =>
    isStoppingTime_coe_min (isStoppingTime_coe_const' _) hσ
  have hqζ : ∀ q : ℚ, ∀ᵐ ω ∂P, ((min (q : ℝ).toNNReal (σ ω) : ℝ≥0) : ℝ≥0∞) < ζ ω := fun q =>
    hσζ.mono fun ω hω => lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hω
  have hqle : ∀ q : ℚ, (hq q).measurableSpace ≤ hσ.measurableSpace := fun q =>
    (hq q).measurableSpace_mono hσ fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)
  choose G₃ hG₃ hG₃e using fun q => exists_subsetEvent hE hκ hX (hq q) (hqζ q) hCH
  choose G₄ hG₄ hG₄e using fun q => exists_disjointEvent hE hκ hX (hq q) (hqζ q) hC hCH
  refine ⟨G₁ ∪ (G₂ ∩ ⋂ q, (G₃ q ∪ G₄ q)), hG₁.union (hG₂.inter (MeasurableSet.iInter fun q =>
    (hqle q _ (hG₃ q)).union (hqle q _ (hG₄ q)))), ?_⟩
  filter_upwards [hG₁e, hG₂e, ae_all_iff.2 hG₃e, ae_all_iff.2 hG₄e] with ω h1 h2 h3 h4
  rw [IsLabel, IsActiveLabel, isPocketLabel_iff hCH]
  simp only [mem_union, mem_inter_iff, mem_iInter, h1, h2, h3, h4]

end Events

end WholeField

end InteractingSLE
