/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OLawAdded
import InteractingSLE.Spec.Sec7.R5EnlPocket

/-!
# R.5's enlarged-stop increment law in a component reference chart, from three pocket union laws

Packet PROVE-R5-OUTERLAW (ruling R88). The component twin of `R5Enl.hasOldChartIncrementLawOn_of_pocketLaws(_stop)`.
On a pocket test (`A`, traversal `γ`, base chart `c`, pocket `C`) at relative capacity `q` the three sets are

* the reference `B = liveExt A γ C Fs 0` (pocket exterior ∪ the counterflow hull `Fs` at the original time `s`),
* the current `K = activeCompl A γ c q` (pocket exterior ∪ `FT`; for an outer pocket `FT` is the relative hull),
* the enlarged set, the pocket exterior ∪ `FTs`, **cut to the event `E`** (`liveExt (A ∩ E) γ C FTs q`, which is `ℍ`
  off `E`; `E = {s ≤ T}` is a mark of the enlarged law),

each with a pocket union law. The reference chart `old` now uniformizes only one component of `ℍ ∖ B`: its domain
lies in `ℍ ∖ B`, the rest of `ℍ ∖ B` is open, its domain events and forward map are reference-record measurable, and
on `E` (live) the enlarged complement `C ∩ (ℍ ∖ FTs)` lies in its domain (`hNest`). Cutting the enlarged set to `E`
is what makes `hNest` a statement on `E` only: off `E` the enlarged complement is empty.

* **`hasOldChartIncrementLawOn_of_pocketLaws_comp`**, **`hasOldChartIncrementLawOn_of_pocketLaws_stop_comp`** — the
  conditioned increment law (clause 4 of `R5Out.R5ClausesCompOn` for one reference).

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5OLaw

open LocalSets WholeField PocketStop PocketCoupling PocketStopSide PocketTraversal PocketAdapt Lemma71C PocketUnionPt
  R5Enl

section Pocket

variable {Ω : Type*}

/-- The complement of the pocket-exterior set `extHullSet C F` in `ℍ` is `C ∩ (ℍ ∖ F)`. -/
theorem H_diff_extHullSet (C F : Set ℂ) : H \ extHullSet C F = C ∩ (H \ F) := by
  ext z
  simp only [extHullSet, mem_inter_iff, Set.mem_sdiff, mem_union, mem_compl_iff]
  tauto

/-- `liveExt_regular` with the openness of the hull complement asked only on the live event. -/
theorem liveExt_regular_live {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ} {q : ℝ≥0}
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F ω)) (ω : Ω) :
    liveExt A γ C F q ω ⊆ H ∧ IsOpen (H \ liveExt A γ C F q ω) := by
  by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
  · rw [liveExt_of_live hl]
    refine ⟨inter_subset_left, ?_⟩
    rw [H_diff_extHullSet]
    exact (hCo ω hl.1).inter (hFo ω hl.1 hl.2)
  · rw [liveExt_of_not_live hl, Set.sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩

variable {ℳB 𝓦c 𝓦e : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **R.5's enlarged-stop increment law in a component reference chart, from the three pocket union laws** (clause 4
of `R5Out.R5ClausesCompOn` for one reference). -/
theorem hasOldChartIncrementLawOn_of_pocketLaws_comp [IsProbabilityMeasure P]
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {C Fs FT FTs : Ω → Set ℂ} {q : ℝ≥0}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFso : ∀ ω ∈ A, IsOpen (H \ Fs ω))
    (hFTso : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ FTs ω))
    (hFTo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ FT ω))
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ FT ω))
    -- the three pocket union laws
    (hpreB : locPrefixSigma ℳB A γ 0 ≤ mΩ) (hRef : PocketStopUnionLaw ℳB P A γ C Fs h₀ 0)
    (hpreC : locPrefixSigma 𝓦c A γ q ≤ mΩ) (hCur : PocketStopUnionLaw 𝓦c P A γ C FT h₀ q)
    (hpreE : locPrefixSigma 𝓦e A γ q ≤ mΩ) (hEnl : PocketStopUnionLaw 𝓦e P A γ C FTs h₀ q)
    -- the records
    (hBrec : Measurable[locPrefixSigma ℳB A γ 0, hittingSigma] (liveExt A γ C Fs 0))
    (hRefInfo : locPrefixSigma ℳB A γ 0 ≤ locPrefixSigma 𝓦e A γ q)
    {E : Set Ω} (hEc : MeasurableSet[𝓦c] E) (hEe : MeasurableSet[𝓦e] E)
    (hmarks : MeasurableSpace.comap ((↑) : E → Ω) 𝓦c = MeasurableSpace.comap ((↑) : E → Ω) 𝓦e)
    (hcut : Measurable[locPrefixSigma 𝓦c A γ q, hittingSigma] (cutSet E (liveExt A γ C Fs 0)))
    -- the hulls
    (hsTs : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → Fs ω ⊆ FTs ω)
    (hsT : ∀ ω ∈ E, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → Fs ω ⊆ FT ω)
    (hTTs : ∀ ω ∈ E, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → FT ω = FTs ω)
    -- the reference chart of one component of the reference complement
    {G : Set Ω} (hG : MeasurableSet[germSigma (liveExt A γ C Fs 0) h₀ ⊔ locPrefixSigma ℳB A γ 0] G)
    {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[germSigma (liveExt A γ C Fs 0) h₀ ⊔ locPrefixSigma ℳB A γ 0]
      (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[germSigma (liveExt A γ C Fs 0) h₀ ⊔ locPrefixSigma ℳB A γ 0]
      ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldSub : ∀ ω ∈ G, ((old ω).dom : Set ℂ) ⊆ H \ liveExt A γ C Fs 0 ω)
    (hCut : ∀ ω ∈ G, IsOpen ((H \ liveExt A γ C Fs 0 ω) \ (old ω).dom))
    (hNest : ∀ ω ∈ G, ω ∈ E → ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → C ω ∩ (H \ FTs ω) ⊆ (old ω).dom)
    {M : Set Ω} (hMG : M ⊆ G) (hME : M ⊆ E) (hMlive : ∀ ω ∈ M, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A γ C Fs 0) h₀ P gOld →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
        HasOldChartIncrementLawOn P M old (relChart c γ q) gOld g := by
  have hhm := hh₀.measurable
  set B : Ω → Set ℂ := liveExt A γ C Fs 0 with hBdef
  -- the reference kernel
  obtain ⟨EB, hEBm, hEBloc, hEBeq⟩ := hRef
  have hLB := measurableSet_live (𝓦 := ℳB) A γ 0
  have hBloc : IsHistoryAvoidanceLocal (locPrefixSigma ℳB A γ 0) B h₀ P :=
    isHistoryAvoidanceLocal_liveExt hLB hEBloc hEBeq
  have hBm : Measurable[mΩ, hittingSigma] B := measurable_liveExt (hpreB _ hLB) hEBm hEBeq
  have hBreg : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω) := liveExt_regular hCo hFso
  obtain ⟨g₀, hg₀, hHarm₀, hK₀⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh₀ hBm hpreB hBloc
    (Eventually.of_forall hBreg)
  -- the enlarged law with the reference germ, cut to `E`
  have hpreE' : locPrefixSigma (𝓦e ⊔ germSigma B h₀) A γ q ≤ mΩ := by
    rw [locPrefixSigma_sup_info]
    exact sup_le hpreE (germSigma_le hBm hhm)
  have hEnl' := pocketStopUnionLaw_sup_germSigma hh₀ hpreE ((hBrec.mono hRefInfo le_rfl))
    (fun ω hω hq => by
      have hl0 : ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) := ⟨hω, lt_of_le_of_lt (by simp) hq⟩
      rw [hBdef, liveExt_of_live hl0]
      rintro z ⟨⟨hz, h1⟩, -⟩
      exact ⟨hz, h1.imp id fun h2 => hsTs ω hω hq h2⟩) hEnl
  obtain ⟨EK', hEK'm, hEK'loc, hEK'eq⟩ := hEnl'
  have hEpre : MeasurableSet[locPrefixSigma (𝓦e ⊔ germSigma B h₀) A γ q] E := by
    rw [locPrefixSigma_sup_info]
    exact le_sup_left (b := germSigma B h₀) _ (le_sup_left (b := MeasurableSpace.generateFrom _) _ hEe)
  have hLK' : MeasurableSet[locPrefixSigma (𝓦e ⊔ germSigma B h₀) A γ q]
      {ω | ω ∈ A ∩ E ∧ (q : ℝ≥0∞) < capLife (γ ω)} := by
    have e : {ω | ω ∈ A ∩ E ∧ (q : ℝ≥0∞) < capLife (γ ω)} =
        E ∩ {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff]
      tauto
    rw [e]
    exact hEpre.inter (measurableSet_live (𝓦 := 𝓦e ⊔ germSigma B h₀) A γ q)
  have hEK'eq' : ∀ ω ∈ A ∩ E, (q : ℝ≥0∞) < capLife (γ ω) → EK' ω = extHullSet (C ω) (FTs ω) :=
    fun ω hω hq => hEK'eq ω hω.1 hq
  have hK'loc := isHistoryAvoidanceLocal_liveExt (A := A ∩ E) (C := C) (F := FTs) hLK' hEK'loc hEK'eq'
  have hK'm : Measurable[mΩ, hittingSigma] (liveExt (A ∩ E) γ C FTs q) :=
    measurable_liveExt (hpreE' _ hLK') hEK'm hEK'eq'
  have hK'reg : ∀ ω, liveExt (A ∩ E) γ C FTs q ω ⊆ H ∧ IsOpen (H \ liveExt (A ∩ E) γ C FTs q ω) :=
    liveExt_regular_live (fun ω hω => hCo ω hω.1) fun ω hω hq => hFTso ω hω.1 hq
  -- the current law with the cut reference germ
  have hpreC' : locPrefixSigma (𝓦c ⊔ germSigma (cutSet E B) h₀) A γ q ≤ mΩ := by
    rw [locPrefixSigma_sup_info]
    exact sup_le hpreC (germSigma_le (hcut.mono hpreC le_rfl) hhm)
  have hCur' := pocketStopUnionLaw_sup_germSigma hh₀ hpreC hcut
    (fun ω hω hq => by
      by_cases hωE : ω ∈ E
      · have hl0 : ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) := ⟨hω, lt_of_le_of_lt (by simp) hq⟩
        rw [cutSet_of_mem hωE, hBdef, liveExt_of_live hl0]
        rintro z ⟨⟨hz, h1⟩, -⟩
        exact ⟨hz, h1.imp id fun h2 => hsT ω hωE hω hq h2⟩
      · rw [cutSet_of_notMem hωE, empty_inter]
        exact empty_subset _) hCur
  obtain ⟨EK, hEKm, hEKloc, hEKeq⟩ := hCur'
  have hLK := measurableSet_live (𝓦 := 𝓦c ⊔ germSigma (cutSet E B) h₀) A γ q
  have hKeq : activeCompl A γ c q = liveExt A γ C FT q := activeCompl_eq_liveExt hact
  have hKloc : IsHistoryAvoidanceLocal (locPrefixSigma (𝓦c ⊔ germSigma (cutSet E B) h₀) A γ q)
      (activeCompl A γ c q) h₀ P := by
    rw [hKeq]
    exact isHistoryAvoidanceLocal_liveExt hLK hEKloc hEKeq
  have hKm : Measurable[mΩ, hittingSigma] (activeCompl A γ c q) := by
    rw [hKeq]
    exact measurable_liveExt (hpreC' _ hLK) hEKm hEKeq
  have hKreg : ∀ ω, activeCompl A γ c q ω ⊆ H ∧ IsOpen (H \ activeCompl A γ c q ω) :=
    activeCompl_regular hact hCo hFTo
  -- the records
  have hInfo : germSigma B h₀ ⊔ locPrefixSigma ℳB A γ 0 ≤
      germSigma (liveExt (A ∩ E) γ C FTs q) h₀ ⊔ locPrefixSigma (𝓦e ⊔ germSigma B h₀) A γ q := by
    rw [locPrefixSigma_sup_info]
    exact sup_le (le_sup_right.trans le_sup_right) (hRefInfo.trans (le_sup_left.trans le_sup_right))
  have hEC : MeasurableSet[germSigma (activeCompl A γ c q) h₀ ⊔
      locPrefixSigma (𝓦c ⊔ germSigma (cutSet E B) h₀) A γ q] E := by
    refine le_sup_right (a := germSigma (activeCompl A γ c q) h₀) _ ?_
    rw [locPrefixSigma_sup_info]
    exact le_sup_left (b := germSigma (cutSet E B) h₀) _ (le_sup_left (b := MeasurableSpace.generateFrom _) _ hEc)
  have hEE : MeasurableSet[germSigma (liveExt (A ∩ E) γ C FTs q) h₀ ⊔
      locPrefixSigma (𝓦e ⊔ germSigma B h₀) A γ q] E :=
    le_sup_right (a := germSigma (liveExt (A ∩ E) γ C FTs q) h₀) _ hEpre
  have hKE : ∀ ω ∈ E, activeCompl A γ c q ω = liveExt (A ∩ E) γ C FTs q ω := by
    intro ω hωE
    rw [hKeq]
    by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
    · have hl' : ω ∈ A ∩ E ∧ (q : ℝ≥0∞) < capLife (γ ω) := ⟨⟨hl.1, hωE⟩, hl.2⟩
      rw [liveExt_of_live hl, liveExt_of_live hl', hTTs ω hωE hl.1 hl.2]
    · have hl' : ¬ (ω ∈ A ∩ E ∧ (q : ℝ≥0∞) < capLife (γ ω)) := fun h => hl ⟨h.1.1, h.2⟩
      rw [liveExt_of_not_live hl, liveExt_of_not_live hl']
  have hcutE : ∀ ω ∈ E, cutSet E B ω = B ω := fun ω hω => cutSet_of_mem hω
  have hmarks' : MeasurableSpace.comap ((↑) : E → Ω) (locPrefixSigma (𝓦c ⊔ germSigma (cutSet E B) h₀) A γ q) =
      MeasurableSpace.comap ((↑) : E → Ω) (locPrefixSigma (𝓦e ⊔ germSigma B h₀) A γ q) := by
    simp only [locPrefixSigma, MeasurableSpace.comap_sup]
    rw [hmarks, comap_val_germSigma_congr (h := h₀) hcutE]
  have hNest' : ∀ ω ∈ G, H \ liveExt (A ∩ E) γ C FTs q ω ⊆ (old ω).dom := by
    intro ω hωG
    by_cases hl : ω ∈ A ∩ E ∧ (q : ℝ≥0∞) < capLife (γ ω)
    · rw [liveExt_of_live hl, H_diff_extHullSet]
      exact hNest ω hωG hl.1.2 hl.1.1 hl.2
    · rw [liveExt_of_not_live hl, Set.sdiff_self]
      exact empty_subset _
  intro gOld hgOld g hg
  exact hasOldChartIncrementLawOn_of_enlarged_component_fwd hh₀ le_sup_left hg₀ hHarm₀ hK₀ hpreE' hpreC' hK'm
    (Eventually.of_forall hK'reg) hK'loc hKm (Eventually.of_forall hKreg) hKloc hInfo hEC hEE hKE hmarks' hG hOld
    hdom hfwd hOldSub (fun ω _ => (hBreg ω).2) hCut (fun ω _ => (hK'reg ω).2) hNest' hMG hME
    (fun ω hM => (H_diff_activeCompl_eq_relChart_dom (hMlive ω hM).1 (hMlive ω hM).2
      (hγ ω (hMlive ω hM).1) (hc ω (hMlive ω hM).1)).symm) gOld hgOld g hg

end Pocket

/-! ### The pocket law with the stopped information of `T` and `T ∨ s` -/

section PocketStop

open PocketStopWallsFin

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳] [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳}
  {P : Measure Ω}

/-- **R.5's enlarged-stop increment law in a component reference chart with the stopped records** (Aux. 35's
records; `E = {s ≤ T}`): the component twin of `R5Enl.hasOldChartIncrementLawOn_of_pocketLaws_stop`. -/
theorem hasOldChartIncrementLawOn_of_pocketLaws_stop_comp [IsProbabilityMeasure P]
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {C Fs FT FTs : Ω → Set ℂ} {q s : ℝ≥0} {T : Ω → ℝ≥0∞}
    (hT : IsMarkedStop ⊥ 𝓕 X T)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFso : ∀ ω ∈ A, IsOpen (H \ Fs ω))
    (hFTso : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ FTs ω))
    (hFTo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ FT ω))
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ FT ω))
    (hpreB : locPrefixSigma (MeasurableSpace.comap X inferInstance ⊔ 𝓕 s) A γ 0 ≤ mΩ)
    (hRef : PocketStopUnionLaw (MeasurableSpace.comap X inferInstance ⊔ 𝓕 s) P A γ C Fs h₀ 0)
    (hpreC : locPrefixSigma (markedStopSigma 𝓕 X T) A γ q ≤ mΩ)
    (hCur : PocketStopUnionLaw (markedStopSigma 𝓕 X T) P A γ C FT h₀ q)
    (hpreE : locPrefixSigma (markedStopSigma 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞))) A γ q ≤ mΩ)
    (hEnl : PocketStopUnionLaw (markedStopSigma 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞))) P A γ C FTs h₀ q)
    (hBs : Measurable[MeasurableSpace.comap X inferInstance ⊔ 𝓕 s, hittingSigma] (liveExt A γ C Fs 0))
    (hsTs : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → Fs ω ⊆ FTs ω)
    (hsT : ∀ ω, (s : ℝ≥0∞) ≤ T ω → ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → Fs ω ⊆ FT ω)
    (hTTs : ∀ ω, (s : ℝ≥0∞) ≤ T ω → ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → FT ω = FTs ω)
    {G : Set Ω} (hG : MeasurableSet[germSigma (liveExt A γ C Fs 0) h₀ ⊔
      locPrefixSigma (MeasurableSpace.comap X inferInstance ⊔ 𝓕 s) A γ 0] G)
    {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[germSigma (liveExt A γ C Fs 0) h₀ ⊔
      locPrefixSigma (MeasurableSpace.comap X inferInstance ⊔ 𝓕 s) A γ 0] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[germSigma (liveExt A γ C Fs 0) h₀ ⊔
      locPrefixSigma (MeasurableSpace.comap X inferInstance ⊔ 𝓕 s) A γ 0]
      ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldSub : ∀ ω ∈ G, ((old ω).dom : Set ℂ) ⊆ H \ liveExt A γ C Fs 0 ω)
    (hCut : ∀ ω ∈ G, IsOpen ((H \ liveExt A γ C Fs 0 ω) \ (old ω).dom))
    (hNest : ∀ ω ∈ G, (s : ℝ≥0∞) ≤ T ω → ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      C ω ∩ (H \ FTs ω) ⊆ (old ω).dom)
    {M : Set Ω} (hMG : M ⊆ G) (hME : ∀ ω ∈ M, (s : ℝ≥0∞) ≤ T ω)
    (hMlive : ∀ ω ∈ M, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A γ C Fs 0) h₀ P gOld →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
        HasOldChartIncrementLawOn P M old (relChart c γ q) gOld g := by
  have hTs : IsMarkedStop ⊥ 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞)) := fun σ hσ M hM =>
    PocketStopSide.isMarkedStop_max_ordinary hT (isStoppingTime_const 𝓕 s) σ hσ M
      ((bot_le : (⊥ : MeasurableSpace Ω) ≤ ⊥ ⊔ (isStoppingTime_const 𝓕 s).measurableSpace) M hM)
  have hBe : Measurable[markedStopSigma 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞)), hittingSigma]
      (liveExt A γ C Fs 0) :=
    hBs.mono (sup_le (comap_le_markedStopSigma hTs) (le_markedStopSigma_max hT s)) le_rfl
  exact hasOldChartIncrementLawOn_of_pocketLaws_comp hh₀ hγ hc hCo hFso hFTso hFTo hact hpreB hRef hpreC hCur
    hpreE hEnl (hBs.mono le_sup_left le_rfl) (locPrefixSigma_ref_le_max hT s A γ q)
    (measurableSet_le_markedStopSigma hT s).1 (measurableSet_le_markedStopSigma hT s).2
    (comap_val_markedStopSigma_max_eq hT s)
    ((measurable_cutSet_markedStopSigma hT s hBe).mono le_sup_left le_rfl) hsTs
    (fun ω hω => hsT ω hω) (fun ω hω => hTTs ω hω) hG hOld hdom hfwd hOldSub hCut
    (fun ω hωG hωE => hNest ω hωG hωE) hMG (fun ω hω => hME ω hω) hMlive

end PocketStop

end InteractingSLE.Sec7.R5OLaw
