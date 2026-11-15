/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsCore

/-!
# The hull's input of the union law: capped hitting times of a hull process

Packet PROVE-STRIPSYS37. The abstract union law `PocketStopWalls.isHistoryAvoidanceLocal_walls_hull` asks of the hull
process `K` its marked locality at every deterministic time and at a capped hitting time `σ_N ≤ N` of each open `U`.
For a monotone hull process adapted to a right-continuous filtration `𝓕` whose avoidance events are measurable at
bounded stopping times and which is marked local at every bounded stopping time with the stopped σ-algebra as marks
(the conclusion of the capacity coding theorem `WholeField.isHistoryAvoidanceLocal_of_capacity` for the frozen optional
hull coupling, `WholeField.isHistoryAvoidanceLocal_hull`, `WangWu.isHistoryAvoidanceLocal_reflect_hull`), these
hypotheses are supplied here:

* `hitCap K U N ω = inf ({t | K_t ∩ U ≠ ∅} ∪ {N})`, the hitting time of `U` capped at `N`;
* `hitCap_le`, `disjoint_of_lt_hitCap`, `not_disjoint_of_hitCap_lt`: `σ_N ≤ N`, `K_t ∩ U = ∅` before `σ_N`, and
  `K_t ∩ U ≠ ∅` for `σ_N < t ≤ N` (monotonicity);
* `isStoppingTime_hitCap`: `σ_N` is a stopping time (`{σ_N < i}` is a countable union of `𝓕`-events, and `𝓕` is
  right-continuous);
* **`isHistoryAvoidanceLocal_walls_hull_filtration`**: the union law of the walls with the hull at a raw stop `T`, with
  all the hull hypotheses discharged from the filtration form. The remaining hypotheses concern only the walls
  (`hW`, Lemma 6.2's output) and the stop with its marks (`hS0`, `hS1`, `hS2`: the marks restricted to `{T < r}` are
  `σ(X) ∨ 𝓕_r`-events, restricted to `{T = σ}` they are `σ(X) ∨ 𝓕_σ`-events for every bounded stopping time `σ`);
* **`isHistoryAvoidanceLocal_walls_hull_stoppingTime`**: at every stopping time `τ` of `𝓕` with the marks `σ(X) ∨ 𝓕_τ`
  (Aux. lemma 37's flat clock for the marked joint exploration walls ∪ counterflow hull), all stop hypotheses
  discharged.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopWalls

open QuantumZipper (H)
open LQGMetric (DistOn)
open LocalSets

/-! ### The capped hitting time -/

section Hit

variable {Ω : Type*}

/-- **The hitting time of `U` by the hull process, capped at `N`.** -/
def hitCap (K : ℝ≥0 → Ω → Set ℂ) (U : Set ℂ) (N : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf (insert N {t | ¬ Disjoint (K t ω) U})

variable {K : ℝ≥0 → Ω → Set ℂ} {U : Set ℂ} {N : ℝ≥0}

theorem hitCap_le (ω : Ω) : hitCap K U N ω ≤ N :=
  csInf_le (OrderBot.bddBelow _) (mem_insert _ _)

theorem disjoint_of_lt_hitCap {ω : Ω} {t : ℝ≥0} (ht : t < hitCap K U N ω) : Disjoint (K t ω) U := by
  by_contra hd
  exact absurd (csInf_le (OrderBot.bddBelow _) (mem_insert_of_mem _ hd)) (not_le.2 ht)

theorem not_disjoint_of_hitCap_lt (hKmono : ∀ ω, Monotone fun t => K t ω) {ω : Ω} {t : ℝ≥0}
    (ht : hitCap K U N ω < t) (htN : t ≤ N) : ¬ Disjoint (K t ω) U := by
  obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt (insert_nonempty _ _) ht
  rcases hs with rfl | hs
  · exact absurd htN (not_le.2 hst)
  · exact fun hd => hs (hd.mono_left (hKmono ω hst.le))

/-- `{σ_N < i}` through rational times. -/
theorem hitCap_lt_iff (hKmono : ∀ ω, Monotone fun t => K t ω) (ω : Ω) (i : ℝ≥0) :
    hitCap K U N ω < i ↔ N < i ∨ ∃ q : ℚ, (q : ℝ).toNNReal < i ∧ ¬ Disjoint (K (q : ℝ).toNNReal ω) U := by
  constructor
  · intro h
    obtain ⟨s, hs, hsi⟩ := exists_lt_of_csInf_lt (insert_nonempty _ _) h
    rcases hs with rfl | hs
    · exact Or.inl hsi
    · right
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (s : ℝ) < i from hsi)
      have hq0 : (0 : ℝ) ≤ q := s.2.trans hq1.le
      refine ⟨q, (Real.toNNReal_lt_iff_lt_coe hq0).2 hq2, fun hd => hs (hd.mono_left (hKmono ω ?_))⟩
      exact (Real.lt_toNNReal_iff_coe_lt.2 hq1).le
  · rintro (h | ⟨q, hq, hd⟩)
    · exact lt_of_le_of_lt (hitCap_le ω) h
    · exact lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) (mem_insert_of_mem _ hd)) hq

/-- **The capped hitting time is a stopping time** of a right-continuous filtration to which the hull's avoidance
events are adapted. -/
theorem isStoppingTime_hitCap [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (hKmono : ∀ ω, Monotone fun t => K t ω) (hKad : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | Disjoint (K t ω) U}) :
    IsStoppingTime 𝓕 fun ω => ((hitCap K U N ω : ℝ≥0) : WithTop ℝ≥0) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i => ?_
  have e : {ω | ((hitCap K U N ω : ℝ≥0) : WithTop ℝ≥0) < (i : WithTop ℝ≥0)} =
      {ω | N < i} ∪ ⋃ q : {q : ℚ // (q : ℝ).toNNReal < i}, {ω | Disjoint (K (q.1 : ℝ).toNNReal ω) U}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_lt_coe, hitCap_lt_iff hKmono, mem_union, mem_iUnion, mem_compl_iff]
    constructor
    · rintro (h | ⟨q, hq, hd⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨q, hq⟩, hd⟩
    · rintro (h | ⟨q, hd⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q.1, q.2, hd⟩
  rw [e]
  refine MeasurableSet.union (MeasurableSet.const _) (MeasurableSet.iUnion fun q => ?_)
  exact 𝓕.mono q.2.le _ (hKad _).compl

end Hit

/-! ### The union law with a filtration -/

section Filtration

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The walls ∪ hull law at a raw stop, hull hypotheses in filtration form.** Let `K` be a monotone hull process
adapted to the right-continuous filtration `𝓕` (`hKad`), whose avoidance events are `𝓕_τ`-measurable at bounded stopping
times (`hKst`), and which is marked local at every bounded stopping time with the marks `𝓕_τ` (`hloc`). Let the walls
`Γ` with information `X` be determined local (`hW`, Lemma 6.2 for the fully explored walls) and let the stop `T` and the
marks `ℳ` satisfy the raw stopping properties `hS0`, `hS1`, `hS2`. Then `wallsHullAt Γ K T` satisfies the
history-marked avoidance criterion for `ℳ`. -/
theorem isHistoryAvoidanceLocal_walls_hull_filtration {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {X : Ω → 𝒳} (hX : Measurable X) {Γ : Ω → Set ℂ} (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G → GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => markovCompl G (h ω)) ⁻¹' B')
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous] {K : ℝ≥0 → Ω → Set ℂ}
    (hKmono : ∀ ω, Monotone fun t => K t ω)
    (hKad : ∀ (t : ℝ≥0) (U : Set ℂ), IsOpen U → U ⊆ H → MeasurableSet[𝓕 t] {ω | Disjoint (K t ω) U})
    (hKst : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) → ∀ U : Set ℂ, IsOpen U →
      U ⊆ H → MeasurableSet[hτ.measurableSpace] {ω | Disjoint (K ((τ ω).untopD 0) ω) U})
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) →
      WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace (fun ω => K ((τ ω).untopD 0) ω) h P)
    {T : Ω → ℝ≥0∞}
    (hS1 : ∀ M, MeasurableSet[ℳ] M → ∀ r : ℝ≥0,
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 r] ({ω | T ω < r} ∩ M))
    (hS2 : ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) (N : ℕ),
      ∀ M, MeasurableSet[ℳ] M → MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
        ({ω | T ω = (σ ω : ℝ≥0∞)} ∩ ({ω | T ω < N} ∩ M)))
    (hS0 : ∀ M, MeasurableSet[ℳ] M → MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ r, 𝓕 r] M) :
    WholeField.IsHistoryAvoidanceLocal ℳ (wallsHullAt Γ K T) h P := by
  have hle : ∀ t, 𝓕 t ≤ mΩ := 𝓕.le
  refine isHistoryAvoidanceLocal_walls_hull (ℱ := fun r => 𝓕 r) hh hX hΓ hW hKmono
    (fun a b hab => 𝓕.mono hab) ?_ ?_ hS1 hS0
  · intro U G hUH hG hMD r F hF
    have hτ := isStoppingTime_const 𝓕 r
    obtain ⟨g, hg, hge⟩ := hloc (fun _ => (r : WithTop ℝ≥0)) hτ (fun _ => WithTop.coe_ne_top) U G hUH hG hMD F
      (by rw [IsStoppingTime.measurableSpace_const]; exact hF)
    refine ⟨(hle r _ (hKad r U U.isOpen hUH)).inter (hle r _ hF), g, hg, ?_⟩
    simpa only [WithTop.untopD_coe] using hge
  · intro U G hUH hG hMD
    have hKad' : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | Disjoint (K t ω) U} := fun t => hKad t U U.isOpen hUH
    refine ⟨fun N => hitCap K U N, fun N => (isStoppingTime_hitCap (N := (N : ℝ≥0)) hKmono hKad').measurableSpace,
      fun N => ⟨fun ω => hitCap_le ω, fun ω t ht => disjoint_of_lt_hitCap ht,
        fun ω t ht htN => not_disjoint_of_hitCap_lt hKmono ht htN, ?_, ?_⟩⟩
    · intro F hF
      set hτ := isStoppingTime_hitCap (N := (N : ℝ≥0)) (𝓕 := 𝓕) hKmono hKad' with hτdef
      obtain ⟨g, hg, hge⟩ := hloc _ hτ (fun _ => WithTop.coe_ne_top) U G hUH hG hMD F hF
      have hm := hKst _ hτ (fun _ => WithTop.coe_ne_top) U U.isOpen hUH
      refine ⟨hτ.measurableSpace_le _ (hm.inter hF), g, hg, ?_⟩
      simpa only [WithTop.untopD_coe] using hge
    · intro M hM
      exact hS2 (hitCap K U N) (isStoppingTime_hitCap hKmono hKad') N M hM

/-- **The walls ∪ hull law at a stopping time of the hull's filtration** (Aux. lemma 37's flat clock, PROVE-STRIPSYS34
§5 item 1: the marked joint exploration "walls ∪ counterflow hull" at every stopping time): for an `𝓕`-stopping time
`τ`,
`wallsHullAt Γ K τ` satisfies the history-marked avoidance criterion for the marks `σ(X) ∨ 𝓕_τ` (walls and stopped
hull history). The raw stopping properties of the filtration theorem are the standard facts on stopped σ-algebras. -/
theorem isHistoryAvoidanceLocal_walls_hull_stoppingTime [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {X : Ω → 𝒳} (hX : Measurable X) {Γ : Ω → Set ℂ} (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G → GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => markovCompl G (h ω)) ⁻¹' B')
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous] {K : ℝ≥0 → Ω → Set ℂ}
    (hKmono : ∀ ω, Monotone fun t => K t ω)
    (hKad : ∀ (t : ℝ≥0) (U : Set ℂ), IsOpen U → U ⊆ H → MeasurableSet[𝓕 t] {ω | Disjoint (K t ω) U})
    (hKst : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) → ∀ U : Set ℂ, IsOpen U →
      U ⊆ H → MeasurableSet[hτ.measurableSpace] {ω | Disjoint (K ((τ ω).untopD 0) ω) U})
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) →
      WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace (fun ω => K ((τ ω).untopD 0) ω) h P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) :
    WholeField.IsHistoryAvoidanceLocal (MeasurableSpace.comap X inferInstance ⊔ hτ.measurableSpace)
      (wallsHullAt Γ K fun ω => (τ ω : ℝ≥0∞)) h P := by
  have hXev : ∀ (𝒜 : MeasurableSpace Ω) (B : Set 𝒳), MeasurableSet B →
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝒜] (X ⁻¹' B) := fun 𝒜 B hB =>
    le_sup_left (a := MeasurableSpace.comap X inferInstance) _ (MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩)
  refine isHistoryAvoidanceLocal_walls_hull_filtration hh hX hΓ hW hKmono hKad hKst hloc ?_ ?_ ?_
  · intro M hM r
    have hlt : MeasurableSet[𝓕 r] {ω | (τ ω : ℝ≥0∞) < (r : ℝ≥0∞)} := hτ.measurableSet_lt r
    have hD : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝓕 r] {ω | (τ ω : ℝ≥0∞) < (r : ℝ≥0∞)} :=
      le_sup_right (b := 𝓕 r) _ hlt
    refine measurableSet_inter_of_sup hD (fun B hB => hD.inter (hXev _ B hB)) (fun F hF => ?_) hM
    have hG : MeasurableSet[hτ.measurableSpace] (F ∩ {ω | τ ω < r}) := hF.inter (hτ.measurableSet_lt' r)
    have e : {ω | (τ ω : ℝ≥0∞) < (r : ℝ≥0∞)} ∩ F = (F ∩ {ω | τ ω < r}) ∩ {ω | τ ω ≤ r} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h2, h1⟩, h1.le⟩
      · rintro ⟨⟨h2, h1⟩, -⟩
        exact ⟨h1, h2⟩
    rw [e]
    exact le_sup_right (b := 𝓕 r) _ (hG.2 r)
  · intro σ hσ N M hM
    have hD : MeasurableSet[hσ.measurableSpace]
        ({ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) = τ ω} ∩ {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) < ((N : ℝ≥0) : WithTop ℝ≥0)}) :=
      (IsStoppingTime.measurableSet_eq_stopping_time hσ hτ).inter (hσ.measurableSet_lt' _)
    have e : ∀ Q : Set Ω, {ω | (τ ω : ℝ≥0∞) = ((σ ω : ℝ≥0) : ℝ≥0∞)} ∩ ({ω | (τ ω : ℝ≥0∞) < (N : ℝ≥0∞)} ∩ Q) =
        ({ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) = τ ω} ∩
          {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) < ((N : ℝ≥0) : WithTop ℝ≥0)}) ∩ Q := fun Q => by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨h1.symm, ?_⟩, h3⟩
        have h2' : (τ ω : ℝ≥0∞) < ((N : ℝ≥0) : ℝ≥0∞) := by rwa [ENNReal.coe_natCast]
        rw [h1] at h2'
        exact h2'
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1.symm, ?_, h3⟩
        have h2' : (τ ω : ℝ≥0∞) < ((N : ℝ≥0) : ℝ≥0∞) := by rw [← h1]; exact h2
        rwa [ENNReal.coe_natCast] at h2'
    have hD' : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
        ({ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) = τ ω} ∩
          {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) < ((N : ℝ≥0) : WithTop ℝ≥0)}) :=
      le_sup_right (b := hσ.measurableSpace) _ hD
    have key : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ hσ.measurableSpace]
        (({ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) = τ ω} ∩
          {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) < ((N : ℝ≥0) : WithTop ℝ≥0)}) ∩ M) := by
      refine measurableSet_inter_of_sup hD' (fun B hB => hD'.inter (hXev _ B hB)) (fun F hF => ?_) hM
      have h1 : MeasurableSet[hσ.measurableSpace] (F ∩ {ω | τ ω ≤ (σ ω : WithTop ℝ≥0)}) :=
        IsStoppingTime.measurableSpace_mono (hτ.min hσ) hσ (fun ω => min_le_right _ _) _
          (IsStoppingTime.measurableSet_inter_le hτ hσ F hF)
      have e' : ({ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) = τ ω} ∩
          {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) < ((N : ℝ≥0) : WithTop ℝ≥0)}) ∩ F =
          (F ∩ {ω | τ ω ≤ (σ ω : WithTop ℝ≥0)}) ∩ ({ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) = τ ω} ∩
            {ω | ((σ ω : ℝ≥0) : WithTop ℝ≥0) < ((N : ℝ≥0) : WithTop ℝ≥0)}) := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨⟨h3, h1.symm.le⟩, h1, h2⟩
        · rintro ⟨⟨h3, -⟩, h1, h2⟩
          exact ⟨⟨h1, h2⟩, h3⟩
      rw [e']
      exact le_sup_right (b := hσ.measurableSpace) _ (h1.inter hD)
    convert key using 1
    exact e M
  · intro M hM
    exact sup_le_sup_left hτ.measurableSpace_le' _ M hM

end Filtration

end InteractingSLE.Sec7.PocketStopWalls
