/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72DPocket

/-!
# Lemma 7.1's joint law, last steps, I: the history-marked set `B_t` of the pocket chart

Packet PROVE-LEMMA72E. Specification §7.1, proof of Lemma 7.1 (`source/spec/p193-240.md` L598–L606, pp. 224–225):
"For each bounded stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies to the
revealed outer curves and the middle prefix."

For a driver `W` with lifetime `ζ` and random charts `c`, at a fixed time `t`:
* `openPart W ζ t ω` is `V_t = ℍ ∖ K_t` before the lifetime and `∅` after it;
* `markedSet W ζ c t ω` is `B_t = ℍ ∖ ψ⁻¹(V_t)` (`ψ⁻¹ = (c ω).2.1`), the complement of the pulled-back open region
  (the outside of the pocket, the outer curves and the pulled-back hull).

Results:
* `measurableSet_lt_subset_image`: `{t < ζ, K ⊆ ψ⁻¹(ℍ ∖ K_t)} ∈ 𝓐_t` for every compact `K` (the clause-event cover of
  `Lemma72D.exists_cover_clauseEvent` for a general compact set);
* `measurable_markedSet`: `B_t` is `𝓐_t`-measurable for the hitting σ-algebra;
* `isHistoryAvoidanceLocal_inter_H`, `isHistoryAvoidanceLocal_sup_nullSets`: the history-marked avoidance criterion
  is unchanged when the set is intersected with `ℍ` and when the null sets are added to the marks;
* `le_sup_nullSets_of_le_aeSigma`: a sub-σ-algebra of `mΩ` inside the completion of `ℋ` lies in `ℋ ∨ 𝒩`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.Lemma72E

open Coupling LocalSets WholeField

/-! ### The open part `V_t` and the marked set `B_t` -/

section Sets

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {t : ℝ≥0} {ω : Ω}

open Classical in
/-- `V_t = ℍ ∖ K_t` before the lifetime, `∅` after it. -/
def openPart (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  if (t : ℝ≥0∞) < ζ ω then H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) else ∅

/-- `B_t = ℍ ∖ ψ⁻¹(V_t)`. -/
def markedSet (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (c : Ω → Chart) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  H \ (c ω).2.1 '' openPart W ζ t ω

theorem openPart_of_lt (h : (t : ℝ≥0∞) < ζ ω) :
    openPart W ζ t ω = H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) := by
  classical
  simp only [openPart, h, ↓reduceIte]

theorem openPart_of_not_lt (h : ¬ (t : ℝ≥0∞) < ζ ω) : openPart W ζ t ω = ∅ := by
  classical
  simp only [openPart, h, ↓reduceIte]

theorem openPart_subset : openPart W ζ t ω ⊆ H := by
  by_cases h : (t : ℝ≥0∞) < ζ ω
  · rw [openPart_of_lt h]; exact sdiff_subset
  · rw [openPart_of_not_lt h]; exact empty_subset _

theorem isOpen_openPart (hc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) :
    IsOpen (openPart W ζ t ω) := by
  by_cases h : (t : ℝ≥0∞) < ζ ω
  · rw [openPart_of_lt h]; exact MartMeans2.isOpen_H_diff_fwdHull_rpath hc h
  · rw [openPart_of_not_lt h]; exact isOpen_empty

theorem image_openPart_subset (hcc : (c ω).IsConformal) : (c ω).2.1 '' openPart W ζ t ω ⊆ H :=
  (image_mono openPart_subset).trans hcc.2.1.image_subset

theorem markedSet_subset : markedSet W ζ c t ω ⊆ H := sdiff_subset

theorem H_diff_markedSet (hcc : (c ω).IsConformal) :
    H \ markedSet W ζ c t ω = (c ω).2.1 '' openPart W ζ t ω := by
  simp only [markedSet, sdiff_sdiff_right_self, inter_eq_right.2 (image_openPart_subset hcc)]

theorem isOpen_H_diff_markedSet (hcc : (c ω).IsConformal)
    (hc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) : IsOpen (H \ markedSet W ζ c t ω) := by
  rw [H_diff_markedSet hcc]
  exact hcc.isOpen_image_of_subset (isOpen_openPart hc) openPart_subset

/-- `ℍ ∖ C ⊆ B_t` for the chart domain `C = dom c`. -/
theorem H_diff_dom_subset_markedSet (hcc : (c ω).IsConformal) :
    H \ ((c ω).dom : Set ℂ) ⊆ markedSet W ζ c t ω :=
  sdiff_subset_sdiff_right (by rw [hcc.coe_dom]; exact image_mono openPart_subset)

/-- On the lifetime, `ℍ ∖ B_t = ψ⁻¹(ℍ ∖ K_t)`. -/
theorem H_diff_markedSet_of_lt (hcc : (c ω).IsConformal) (h : (t : ℝ≥0∞) < ζ ω) :
    H \ markedSet W ζ c t ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) := by
  rw [H_diff_markedSet hcc, openPart_of_lt h]

end Sets

/-! ### Measurability -/

section Meas

variable {Ω : Type*} {𝓐₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {𝓐 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : Ω → Chart}

/-- **`{t < ζ, K ⊆ ψ⁻¹(ℍ ∖ K_t)}` is an event of `𝓐_t`** for a compact `K` (the clause-event cover
`Lemma72D.exists_cover_clauseEvent` with `supp φ` replaced by `K`): for a dense sequence `dᵢ` of `K`, the event is the
countable union over finite families `F` of rational balls in `ℍ` and `m ∈ ℕ` of
`{t < ζ, ⋃F ∩ K_t = ∅} ∩ ⋂ᵢ {B̄(dᵢ, 1/(m+1)) ⊆ dom} ∩ ⋂ᵢ {ψ(dᵢ) ∈ ⋃F}`. -/
theorem measurableSet_lt_subset_image (hcc : ∀ ω, (c ω).IsConformal)
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet[𝓐₀] {ω | closedBall z r ⊆ (c ω).dom})
    (hfm : ∀ z, Measurable[𝓐₀] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hWa : AdaptedBefore 𝓐 ζ W) (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (t : ℝ≥0)
    (h₀ : 𝓐₀ ≤ 𝓐 t) (hζ : MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < ζ ω}) {K : Set ℂ} (hKc : IsCompact K) :
    MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < ζ ω ∧
      K ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))} := by
  classical
  set Kt : Ω → Set ℂ := fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) with hKt
  have hdom : ∀ ω, IsOpen ((c ω).dom : Set ℂ) := fun ω => (c ω).dom.isOpen
  have hmem : ∀ z, MeasurableSet[𝓐₀] {ω | z ∈ (c ω).dom} := fun z =>
    @Lemma71E.measurableSet_mem_of_closedBall Ω 𝓐₀ (fun ω => ((c ω).dom : Set ℂ)) hdom hCm z
  -- the empty set
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ K ⊆ (c ω).2.1 '' (H \ Kt ω)} = {ω | (t : ℝ≥0∞) < ζ ω} := by
      ext ω
      simp only [mem_ofPred_eq, hK0, empty_subset, and_true]
    rw [e]
    exact hζ
  -- a dense sequence of `K`
  obtain ⟨S, hSK, hSc, hKS⟩ := (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hSne : S.Nonempty := by
    obtain ⟨z, hz⟩ := hKne
    by_contra hS
    rw [not_nonempty_iff_eq_empty] at hS
    have := hKS hz
    rw [hS, closure_empty] at this
    exact this
  obtain ⟨d, rfl⟩ := hSc.exists_eq_range hSne
  -- the pieces
  set E' : Finset (ℚ × ℚ × ℚ) × ℕ → Set Ω := fun p =>
    if ballsK p.1 ⊆ H then
      {ω | (t : ℝ≥0∞) < ζ ω ∧ Disjoint (ballsK p.1) (Kt ω)} ∩
        ((⋂ i, {ω | closedBall (d i) (1 / ((p.2 : ℝ) + 1)) ⊆ (c ω).dom}) ∩
          ⋂ i, ({ω | d i ∈ (c ω).dom}ᶜ ∪
            ({ω | d i ∈ (c ω).dom} ∩ ({ω | d i ∈ (c ω).dom}.indicator fun ω => (c ω).1 (d i)) ⁻¹' ballsK p.1)))
    else ∅ with hE'def
  have hE'm : ∀ p, MeasurableSet[𝓐 t] (E' p) := fun p => by
    have hfw' : ∀ i, MeasurableSet[𝓐₀] ({ω | d i ∈ (c ω).dom}ᶜ ∪
        ({ω | d i ∈ (c ω).dom} ∩ ({ω | d i ∈ (c ω).dom}.indicator fun ω => (c ω).1 (d i)) ⁻¹' ballsK p.1)) :=
      fun i => by
        let _ : MeasurableSpace Ω := 𝓐₀
        exact (hmem (d i)).compl.union ((hmem (d i)).inter
          ((hfm (d i)) (isCompact_ballsK p.1).isClosed.measurableSet))
    let _ : MeasurableSpace Ω := 𝓐 t
    by_cases hp : ballsK p.1 ⊆ H
    · simp only [hE'def, hp, ↓reduceIte]
      exact (Lemma72D.measurableSet_lt_disjoint_ballsK hWa hc t hζ hp).inter ((MeasurableSet.iInter fun i =>
        h₀ _ (hCm (d i) _)).inter (MeasurableSet.iInter fun i => h₀ _ (hfw' i)))
    · simp only [hE'def, hp, ↓reduceIte]; exact MeasurableSet.empty
  -- the event is the union of the pieces
  have heq : {ω | (t : ℝ≥0∞) < ζ ω ∧ K ⊆ (c ω).2.1 '' (H \ Kt ω)} = ⋃ p, E' p := by
    ext ω
    constructor
    · rintro ⟨hlt, hsupp⟩
      rw [(hcc ω).image_eq_inter_preimage sdiff_subset] at hsupp
      have hKdom : K ⊆ (c ω).dom := fun z hz => (hsupp hz).1
      obtain ⟨δ, hδ, hδK⟩ := hKc.exists_thickening_subset_open (hdom ω) hKdom
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      have hopen : IsOpen (H \ Kt ω) := MartMeans2.isOpen_H_diff_fwdHull_rpath (hc ω) hlt
      have himc : IsCompact ((c ω).1 '' K) :=
        hKc.image_of_continuousOn ((hcc ω).differentiableOn_fwd.continuousOn.mono hKdom)
      obtain ⟨F, hF1, hF2⟩ := exists_rationalBalls himc hopen fun _ ⟨z, hz, hzw⟩ => hzw ▸ (hsupp hz).2
      have hFH : ballsK F ⊆ H := fun w hw => (hF2 hw).1
      refine mem_iUnion.2 ⟨(F, m), ?_⟩
      simp only [hE'def, hFH, ↓reduceIte, mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_union, mem_compl_iff,
        mem_preimage]
      refine ⟨⟨hlt, Set.disjoint_left.2 fun w hw hwK => (hF2 hw).2 hwK⟩, fun i => ?_, fun i => ?_⟩
      · intro w hw
        refine hδK (Metric.mem_thickening_iff.2 ⟨d i, hSK (mem_range_self i), ?_⟩)
        exact lt_of_le_of_lt (mem_closedBall.1 hw) hm
      · right
        have hdi : d i ∈ (c ω).dom := hKdom (hSK (mem_range_self i))
        refine ⟨hdi, ?_⟩
        rw [indicator_of_mem (show ω ∈ {ω | d i ∈ (c ω).dom} from hdi)]
        exact ballsU_subset_ballsK F (hF1 ⟨d i, hSK (mem_range_self i), rfl⟩)
    · intro hω
      obtain ⟨p, hω⟩ := mem_iUnion.1 hω
      by_cases hp : ballsK p.1 ⊆ H
      swap
      · simp only [hE'def, hp, ↓reduceIte] at hω; exact absurd hω (notMem_empty ω)
      simp only [hE'def, hp, ↓reduceIte, mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_union, mem_compl_iff,
        mem_preimage] at hω
      obtain ⟨⟨hlt, hdis⟩, hball, hfw⟩ := hω
      have hKdom : ∀ z ∈ K, z ∈ (c ω).dom := fun z hz => by
        obtain ⟨i, hi⟩ := Lemma72D.exists_dist_lt_of_denseSeq hKS hz (ε := 1 / ((p.2 : ℝ) + 1)) (by positivity)
        exact hball i (mem_closedBall.2 hi.le)
      have hfwd : ∀ i, (c ω).1 (d i) ∈ ballsK p.1 := fun i => by
        rcases hfw i with h | ⟨hmem', h⟩
        · exact absurd (hKdom _ (hSK (mem_range_self i))) h
        · rwa [indicator_of_mem (show ω ∈ {ω | d i ∈ (c ω).dom} from hmem')] at h
      refine ⟨hlt, fun z hz => ?_⟩
      rw [(hcc ω).image_eq_inter_preimage sdiff_subset]
      have hzd := hKdom z hz
      refine ⟨hzd, ?_⟩
      have hcont : ContinuousAt (c ω).1 z :=
        ((hcc ω).differentiableOn_fwd.continuousOn).continuousAt ((hdom ω).mem_nhds hzd)
      have hcl : (c ω).1 z ∈ closure ((c ω).1 '' range d) := mem_closure_image hcont (hKS hz)
      have hK : (c ω).1 z ∈ ballsK p.1 := by
        refine closure_minimal ?_ (isCompact_ballsK p.1).isClosed hcl
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        exact hfwd i
      exact ⟨hp hK, fun hzK => Set.disjoint_left.1 hdis hK hzK⟩
  rw [heq]
  let _ : MeasurableSpace Ω := 𝓐 t
  exact MeasurableSet.iUnion hE'm

/-- **`B_t` is `𝓐_t`-measurable for the hitting σ-algebra.** For `U ⊆ ℍ` open, `B_t ∩ U = ∅` iff `U ⊆ ψ⁻¹(V_t)`
iff every finite union of rational closed balls inside `U` lies in `ψ⁻¹(V_t)` (`exists_rationalBalls` at the points
of `U`); each of these is `{t < ζ, ⋃F ⊆ ψ⁻¹(ℍ ∖ K_t)}` or, after the lifetime, `{⋃F = ∅}`. -/
theorem measurable_markedSet (hcc : ∀ ω, (c ω).IsConformal)
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet[𝓐₀] {ω | closedBall z r ⊆ (c ω).dom})
    (hfm : ∀ z, Measurable[𝓐₀] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hWa : AdaptedBefore 𝓐 ζ W) (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (t : ℝ≥0)
    (h₀ : 𝓐₀ ≤ 𝓐 t) (hζ : MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < ζ ω}) :
    Measurable[𝓐 t, hittingSigma] (markedSet W ζ c t) := by
  classical
  let _ : MeasurableSpace Ω := 𝓐 t
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  -- one finite union of rational balls
  have hF : ∀ F : Finset (ℚ × ℚ × ℚ), MeasurableSet {ω | ballsK F ⊆ U → ballsK F ⊆ (c ω).2.1 '' openPart W ζ t ω} :=
    fun F => by
      by_cases hFU : ballsK F ⊆ U
      · have e : {ω | ballsK F ⊆ U → ballsK F ⊆ (c ω).2.1 '' openPart W ζ t ω} =
            {ω | (t : ℝ≥0∞) < ζ ω ∧ ballsK F ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))} ∪
              ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | ballsK F ⊆ ∅}) := by
          ext ω
          simp only [mem_ofPred_eq, hFU, forall_const, mem_union, mem_inter_iff, mem_compl_iff]
          by_cases h : (t : ℝ≥0∞) < ζ ω
          · rw [openPart_of_lt h]
            exact ⟨fun hs => Or.inl ⟨h, hs⟩, fun hs => hs.elim (fun h' => h'.2) fun h' => absurd h h'.1⟩
          · rw [openPart_of_not_lt h, image_empty]
            exact ⟨fun hs => Or.inr ⟨h, hs⟩, fun hs => hs.elim (fun h' => absurd h'.1 h) fun h' => h'.2⟩
        rw [e]
        exact (measurableSet_lt_subset_image (mΩ := mΩ) hcc hCm hfm hWa hc t h₀ hζ (isCompact_ballsK F)).union
          (hζ.compl.inter (MeasurableSet.const _))
      · have e : {ω | ballsK F ⊆ U → ballsK F ⊆ (c ω).2.1 '' openPart W ζ t ω} = univ := by
          ext ω
          simp only [mem_ofPred_eq, hFU, false_imp_iff, mem_univ]
        rw [e]
        exact MeasurableSet.univ
  -- the hitting event
  have e : markedSet W ζ c t ⁻¹' {A | (A ∩ U).Nonempty} =
      (⋂ F : Finset (ℚ × ℚ × ℚ), {ω | ballsK F ⊆ U → ballsK F ⊆ (c ω).2.1 '' openPart W ζ t ω})ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, mem_iInter]
    constructor
    · rintro ⟨z, hzB, hzU⟩ hall
      obtain ⟨F, hF1, hF2⟩ := exists_rationalBalls isCompact_singleton hUo (singleton_subset_iff.2 hzU)
      exact hzB.2 (hall F hF2 (ballsU_subset_ballsK F (hF1 rfl)))
    · intro hn
      by_contra hne
      refine hn fun F hFU w hw => ?_
      by_contra hwV
      exact hne ⟨w, ⟨hUH (hFU hw), hwV⟩, hFU hw⟩
  rw [e]
  exact (MeasurableSet.iInter hF).compl

end Meas

/-! ### The history-marked avoidance criterion: the trace in `ℍ` and null marks -/

section History

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The criterion only sees the trace in `ℍ`** (its avoidance events concern open `U ⊆ ℍ`). -/
theorem isHistoryAvoidanceLocal_inter_H {A : Ω → Set ℂ} (hloc : IsHistoryAvoidanceLocal ℋ A h P) :
    IsHistoryAvoidanceLocal ℋ (fun ω => A ω ∩ H) h P := by
  intro U G hUH hG hd F hF
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd F hF
  refine ⟨g, hg, ?_⟩
  have e : {ω | Disjoint (A ω ∩ H) (U : Set ℂ)} = {ω | Disjoint (A ω) (U : Set ℂ)} := by
    ext ω
    simp only [mem_ofPred_eq]
    exact ⟨fun hd' => Set.disjoint_left.2 fun z hzA hzU => Set.disjoint_left.1 hd' ⟨hzA, hUH hzU⟩ hzU,
      fun hd' => hd'.mono_left inter_subset_left⟩
  simp only [e]
  exact hge

/-- Every set of `ℋ ∨ 𝒩` is a.e. equal to a set of `ℋ`. -/
theorem exists_ae_eq_of_measurableSet_sup_nullSets {F : Set Ω} (hF : MeasurableSet[ℋ ⊔ Ito.nullSets P] F) :
    ∃ F', MeasurableSet[ℋ] F' ∧ F =ᵐ[P] F' :=
  (sup_le le_eventuallyMeasurableSpace (MeasurableSpace.generateFrom_le fun _ hu =>
      ⟨∅, @MeasurableSet.empty _ ℋ, ae_eq_empty.mpr hu.2⟩) :
    ℋ ⊔ Ito.nullSets P ≤ eventuallyMeasurableSpace ℋ (ae P)) F hF

/-- **Null sets may be added to the marks.** -/
theorem isHistoryAvoidanceLocal_sup_nullSets {A : Ω → Set ℂ} (hloc : IsHistoryAvoidanceLocal ℋ A h P) :
    IsHistoryAvoidanceLocal (ℋ ⊔ Ito.nullSets P) A h P := by
  intro U G hUH hG hd F hF
  obtain ⟨F', hF', hFF'⟩ := exists_ae_eq_of_measurableSet_sup_nullSets hF
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd F' hF'
  refine ⟨g, hg, Filter.EventuallyEq.trans ?_ hge⟩
  refine condExp_congr_ae (indicator_ae_eq_of_ae_eq_set ?_)
  filter_upwards [hFF'] with ω hω
  exact congrArg (fun p => (ω ∈ {ω | Disjoint (A ω) (U : Set ℂ)}) ∧ p) hω

/-- **A sub-σ-algebra of `mΩ` inside the completion of `ℋ` lies in `ℋ ∨ 𝒩`.** -/
theorem le_sup_nullSets_of_le_aeSigma {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hℋ : ℋ ≤ mΩ)
    (hle : m ≤ aeSigma ℋ P) : m ≤ ℋ ⊔ Ito.nullSets P := by
  intro s hs
  obtain ⟨s', hs', he⟩ := hle s hs
  have hsm : MeasurableSet[mΩ] s := hm s hs
  have hs'm : MeasurableSet[mΩ] s' := hℋ s' hs'
  obtain ⟨h1, h2⟩ := ae_eq_set.1 he
  have hn1 : MeasurableSet[Ito.nullSets P] (s \ s') :=
    MeasurableSpace.measurableSet_generateFrom ⟨hsm.diff hs'm, h1⟩
  have hn2 : MeasurableSet[Ito.nullSets P] (s' \ s) :=
    MeasurableSpace.measurableSet_generateFrom ⟨hs'm.diff hsm, h2⟩
  have e : s = (s' \ (s' \ s)) ∪ (s \ s') := by
    ext x
    simp only [mem_union, Set.mem_sdiff]
    tauto
  rw [e]
  let _ : MeasurableSpace Ω := ℋ ⊔ Ito.nullSets P
  exact ((le_sup_left : ℋ ≤ ℋ ⊔ Ito.nullSets P) _ hs').diff
    ((le_sup_right : Ito.nullSets P ≤ ℋ ⊔ Ito.nullSets P) _ hn2) |>.union
    ((le_sup_right : Ito.nullSets P ≤ ℋ ⊔ Ito.nullSets P) _ hn1)

end History

end InteractingSLE.Sec7.Lemma72E
