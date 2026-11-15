/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlAdded
import InteractingSLE.Spec.Sec7.PocketStopSideEndLaws
import InteractingSLE.Spec.Sec7.PocketSideInRefLaws
import InteractingSLE.Spec.Sec7.SideLCGerm
import InteractingSLE.Spec.Sec7.R5EnlStop
import InteractingSLE.Spec.Sec7.PhaseContMeas

/-!
# R.5's enlarged-stop increment law on a pocket test, from three pocket union laws

Packet PROVE-R5-ENLARGED (continued). On a pocket test (`A`, traversal `γ`, base chart `c`, pocket `C`) at relative
capacity `q`, the three sets of Lemma R.5's proof are

* the reference `B = liveExt A γ C Fs 0` (pocket exterior ∪ the counterflow hull `Fs` at the reference time `s`),
* the current `K = activeCompl A γ c q` (pocket exterior ∪ the hull `FT` at the stop `T`),
* the enlarged `K' = liveExt A γ C FTs q` (pocket exterior ∪ the hull `FTs` at `T ∨ s`),

each with a pocket union law (`PocketStopUnionLaw`, Aux. 124/35's marked law) with marks `ℳB`, `𝓦c`, `𝓦e`. The germ
of the reference is added to the enlarged marks (the source: "the assumed marked law at `T_q` … retains … the germ of
`R_{q*}`") and, cut to the event `E = {s ≤ T}`, to the current marks, by the landed smaller-germ theorem
`PocketStopSide.pocketStopUnionLaw_sup_germSigma`. Then `hasOldChartIncrementLawOn_of_enlarged_marked_fwd` applies.

* `cutSet` (the reference cut to `E`), `liveExt_sub_mono`;
* **`hasOldChartIncrementLawOn_of_pocketLaws`** — clause 4 of `R5ClausesOn` for one reference: inputs are the three
  union laws, the record relations (`hRefInfo`: the reference record inside the enlarged marks; `hmarks`: the current
  and enlarged marks have the same trace on `E`; `E` in both marks; the cut reference measurable for the current marks),
  the hull relations (`Fs ⊆ FTs`, and on `E`: `Fs ⊆ FT = FTs`), and the reference chart (`hfwd` the only measurability).

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Enl

open LocalSets WholeField PocketStop PocketCoupling PocketStopSide PocketTraversal PocketAdapt Lemma71C PocketUnionPt

section Pocket

variable {Ω : Type*}

open Classical in
/-- The reference set cut to the event `E` (empty off `E`). -/
def cutSet (E : Set Ω) (B : Ω → Set ℂ) (ω : Ω) : Set ℂ :=
  if ω ∈ E then B ω else ∅

theorem cutSet_of_mem {E : Set Ω} {B : Ω → Set ℂ} {ω : Ω} (hω : ω ∈ E) : cutSet E B ω = B ω := by
  simp only [cutSet, hω, ↓reduceIte]

theorem cutSet_of_notMem {E : Set Ω} {B : Ω → Set ℂ} {ω : Ω} (hω : ω ∉ E) : cutSet E B ω = ∅ := by
  simp only [cutSet, hω, ↓reduceIte]

/-- A larger hull at a later live level has a smaller live complement. -/
theorem liveExt_sub_mono {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F F' : Ω → Set ℂ} {q : ℝ≥0}
    (hFF : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → F ω ⊆ F' ω) (ω : Ω) :
    H \ liveExt A γ C F' q ω ⊆ H \ liveExt A γ C F 0 ω := by
  by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
  · have hl0 : ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) :=
      ⟨hl.1, lt_of_le_of_lt (by simp) hl.2⟩
    rw [liveExt_of_live hl, liveExt_of_live hl0]
    rintro z ⟨hz, hn⟩
    refine ⟨hz, fun h' => hn ⟨h'.1, ?_⟩⟩
    rcases h'.2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (hFF ω hl.1 hl.2 h1)
  · rw [liveExt_of_not_live hl, sdiff_self]
    exact empty_subset _

variable {ℳB 𝓦c 𝓦e : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **R.5's enlarged-stop increment law on a pocket test from the three pocket union laws** (clause 4 of
`R5ClausesOn` for one reference). -/
theorem hasOldChartIncrementLawOn_of_pocketLaws [IsProbabilityMeasure P]
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {C Fs FT FTs : Ω → Set ℂ} {q : ℝ≥0}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFso : ∀ ω ∈ A, IsOpen (H \ Fs ω))
    (hFTso : ∀ ω ∈ A, IsOpen (H \ FTs ω))
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
    -- the reference chart
    {G : Set Ω} (hG : MeasurableSet[germSigma (liveExt A γ C Fs 0) h₀ ⊔ locPrefixSigma ℳB A γ 0] G)
    {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hfwd : ∀ z, Measurable[germSigma (liveExt A γ C Fs 0) h₀ ⊔ locPrefixSigma ℳB A γ 0]
      ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ liveExt A γ C Fs 0 ω)
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
  -- the enlarged law with the reference germ
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
  have hLK' := measurableSet_live (𝓦 := 𝓦e ⊔ germSigma B h₀) A γ q
  have hK'loc := isHistoryAvoidanceLocal_liveExt (C := C) (F := FTs) hLK' hEK'loc hEK'eq
  have hK'm : Measurable[mΩ, hittingSigma] (liveExt A γ C FTs q) :=
    measurable_liveExt (hpreE' _ hLK') hEK'm hEK'eq
  have hK'reg : ∀ ω, liveExt A γ C FTs q ω ⊆ H ∧ IsOpen (H \ liveExt A γ C FTs q ω) :=
    liveExt_regular hCo hFTso
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
      germSigma (liveExt A γ C FTs q) h₀ ⊔ locPrefixSigma (𝓦e ⊔ germSigma B h₀) A γ q := by
    rw [locPrefixSigma_sup_info]
    exact sup_le (le_sup_right.trans le_sup_right) (hRefInfo.trans (le_sup_left.trans le_sup_right))
  have hEC : MeasurableSet[germSigma (activeCompl A γ c q) h₀ ⊔
      locPrefixSigma (𝓦c ⊔ germSigma (cutSet E B) h₀) A γ q] E := by
    refine le_sup_right (a := germSigma (activeCompl A γ c q) h₀) _ ?_
    rw [locPrefixSigma_sup_info]
    exact le_sup_left (b := germSigma (cutSet E B) h₀) _ (le_sup_left (b := MeasurableSpace.generateFrom _) _ hEc)
  have hEE : MeasurableSet[germSigma (liveExt A γ C FTs q) h₀ ⊔
      locPrefixSigma (𝓦e ⊔ germSigma B h₀) A γ q] E := by
    refine le_sup_right (a := germSigma (liveExt A γ C FTs q) h₀) _ ?_
    rw [locPrefixSigma_sup_info]
    exact le_sup_left (b := germSigma B h₀) _ (le_sup_left (b := MeasurableSpace.generateFrom _) _ hEe)
  have hKE : ∀ ω ∈ E, activeCompl A γ c q ω = liveExt A γ C FTs q ω := by
    intro ω hωE
    rw [hKeq]
    by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
    · rw [liveExt_of_live hl, liveExt_of_live hl, hTTs ω hωE hl.1 hl.2]
    · rw [liveExt_of_not_live hl, liveExt_of_not_live hl]
  have hcutE : ∀ ω ∈ E, cutSet E B ω = B ω := fun ω hω => cutSet_of_mem hω
  have hmarks' : MeasurableSpace.comap ((↑) : E → Ω) (locPrefixSigma (𝓦c ⊔ germSigma (cutSet E B) h₀) A γ q) =
      MeasurableSpace.comap ((↑) : E → Ω) (locPrefixSigma (𝓦e ⊔ germSigma B h₀) A γ q) := by
    simp only [locPrefixSigma, MeasurableSpace.comap_sup]
    rw [hmarks, comap_val_germSigma_congr (h := h₀) hcutE]
  intro gOld hgOld g hg
  exact hasOldChartIncrementLawOn_of_enlarged_marked_fwd hh₀ le_sup_left hg₀ hHarm₀ hK₀ hpreE' hpreC' hK'm
    (Eventually.of_forall hK'reg) hK'loc hKm (Eventually.of_forall hKreg) hKloc hInfo hEC hEE hKE hmarks' hG hOld
    hfwd hOldDom (fun ω _ => (hBreg ω).2) (fun ω _ => (hK'reg ω).2) (fun ω _ => liveExt_sub_mono hsTs ω) hMG hME
    (fun ω hM => (H_diff_activeCompl_eq_relChart_dom (hMlive ω hM).1 (hMlive ω hM).2
      (hγ ω (hMlive ω hM).1) (hc ω (hMlive ω hM).1)).symm) gOld hgOld g hg

end Pocket

/-! ### The records at the stops `T` and `T ∨ s` -/

section Stops

open PocketStopWallsFin

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳] {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳}

/-- Marks of one stop cut to a common mark `E` on which the two stops agree are marks of the other. -/
theorem inter_mem_stopMarks_of_eqOn {T₁ T₂ : Ω → ℝ≥0∞} {E : Set Ω} (hE : E ∈ stopMarks 𝓕 X T₁)
    (h12 : ∀ ω ∈ E, T₁ ω = T₂ ω) {M : Set Ω} (hM : M ∈ stopMarks 𝓕 X T₁) : E ∩ M ∈ stopMarks 𝓕 X T₂ := by
  refine ⟨hE.1.inter hM.1, fun σ hσ => ?_⟩
  have e : {ω | T₂ ω ≤ (σ ω : ℝ≥0∞)} ∩ (E ∩ M) =
      ({ω | T₁ ω ≤ (σ ω : ℝ≥0∞)} ∩ E) ∩ ({ω | T₁ ω ≤ (σ ω : ℝ≥0∞)} ∩ M) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have h1' : T₁ ω ≤ (σ ω : ℝ≥0∞) := (h12 ω h2).symm ▸ h1
      exact ⟨⟨h1', h2⟩, h1', h3⟩
    · rintro ⟨⟨h1, h2⟩, -, h3⟩
      exact ⟨h12 ω h2 ▸ h1, h2, h3⟩
  rw [e]
  exact (hE.2 σ hσ).inter (hM.2 σ hσ)

/-- **A set measurable for the stopped information at `T ∨ s`, cut to `{s ≤ T}`, is measurable for the stopped
information at `T`.** -/
theorem measurable_cutSet_markedStopSigma {T : Ω → ℝ≥0∞} (hT : IsMarkedStop ⊥ 𝓕 X T) (s : ℝ≥0)
    {B : Ω → Set ℂ} (hB : Measurable[markedStopSigma 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞)), hittingSigma] B) :
    Measurable[markedStopSigma 𝓕 X T, hittingSigma] (cutSet {ω | (s : ℝ≥0∞) ≤ T ω} B) := by
  set E : Set Ω := {ω | (s : ℝ≥0∞) ≤ T ω}
  have hE : MeasurableSet[markedStopSigma 𝓕 X T] E := (measurableSet_le_markedStopSigma hT s).1
  have hEs : E ∈ stopMarks 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞)) :=
    mem_stopMarks_of_eqOn (mem_stopMarks_le hT s) fun _ω hω => (max_eq_left hω).symm
  have hle : markedStopSigma 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞)) ≤
      PocketStopMarked.traceSigma (markedStopSigma 𝓕 X T) E hE :=
    MeasurableSpace.generateFrom_le fun M hM => MeasurableSpace.measurableSet_generateFrom
      (inter_mem_stopMarks_of_eqOn hEs (fun ω hω => max_eq_left hω) hM)
  refine @measurable_generateFrom Ω (Set ℂ) (markedStopSigma 𝓕 X T) _ _ ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have e : cutSet E B ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} = E ∩ B ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} := by
    ext ω
    by_cases hω : ω ∈ E
    · simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, cutSet_of_mem hω, hω, true_and]
    · simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, cutSet_of_notMem hω, hω, false_and,
        empty_inter, Set.not_nonempty_empty]
  rw [e]
  exact hle _ (hB (measurableSet_hitting hUo hUH))

/-- **The reference record lies in the enlarged record**: the information `σ(X) ∨ 𝓕_s` with the level-`0` prefix
events is inside the stopped information at `T ∨ s` with the level-`q` prefix events. -/
theorem locPrefixSigma_ref_le_max {T : Ω → ℝ≥0∞} (hT : IsMarkedStop ⊥ 𝓕 X T) (s : ℝ≥0) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (q : ℝ≥0) :
    locPrefixSigma (MeasurableSpace.comap X inferInstance ⊔ 𝓕 s) A γ 0 ≤
      locPrefixSigma (markedStopSigma 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞))) A γ q := by
  have hTs : IsMarkedStop ⊥ 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞)) := by
    intro σ hσ M hM
    have h := PocketStopSide.isMarkedStop_max_ordinary hT (isStoppingTime_const 𝓕 s) σ hσ M
      ((bot_le : (⊥ : MeasurableSpace Ω) ≤ ⊥ ⊔ (isStoppingTime_const 𝓕 s).measurableSpace) M hM)
    exact h
  refine (PhaseCont.locPrefixSigma_mono _ A γ (show (0 : ℝ≥0) ≤ q from zero_le)).trans
    (sup_le_sup_right (sup_le ?_ ?_) _)
  · exact comap_le_markedStopSigma hTs
  · exact le_markedStopSigma_max hT s

end Stops

/-! ### The pocket law with the stopped information of `T` and `T ∨ s` -/

section PocketStop

open PocketStopWallsFin

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳] [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳}
  {P : Measure Ω}

/-- **R.5's enlarged-stop increment law on a pocket test with the stopped records** (Aux. 35's records): the reference
law with marks `σ(X) ∨ 𝓕_s`, the current law at the marked stop `T` with its stopped information, the enlarged law at
`T ∨ s` with its stopped information, `E = {s ≤ T}`. The record relations of `hasOldChartIncrementLawOn_of_pocketLaws`
are discharged from `IsMarkedStop ⊥ 𝓕 X T` and the `σ(X) ∨ 𝓕_s`-measurability of the reference set. -/
theorem hasOldChartIncrementLawOn_of_pocketLaws_stop [IsProbabilityMeasure P]
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {C Fs FT FTs : Ω → Set ℂ} {q s : ℝ≥0} {T : Ω → ℝ≥0∞}
    (hT : IsMarkedStop ⊥ 𝓕 X T)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hFso : ∀ ω ∈ A, IsOpen (H \ Fs ω))
    (hFTso : ∀ ω ∈ A, IsOpen (H \ FTs ω))
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
    (hfwd : ∀ z, Measurable[germSigma (liveExt A γ C Fs 0) h₀ ⊔
      locPrefixSigma (MeasurableSpace.comap X inferInstance ⊔ 𝓕 s) A γ 0]
      ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ liveExt A γ C Fs 0 ω)
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
  exact hasOldChartIncrementLawOn_of_pocketLaws hh₀ hγ hc hCo hFso hFTso hFTo hact hpreB hRef hpreC hCur hpreE hEnl
    (hBs.mono le_sup_left le_rfl) (locPrefixSigma_ref_le_max hT s A γ q)
    (measurableSet_le_markedStopSigma hT s).1 (measurableSet_le_markedStopSigma hT s).2
    (comap_val_markedStopSigma_max_eq hT s)
    ((measurable_cutSet_markedStopSigma hT s hBe).mono le_sup_left le_rfl) hsTs
    (fun ω hω => hsT ω hω) (fun ω hω => hTTs ω hω) hG hOld hfwd hOldDom hMG (fun ω hω => hME ω hω) hMlive

end PocketStop

end InteractingSLE.Sec7.R5Enl
