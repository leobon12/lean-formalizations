/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS6Word
import InteractingSLE.Spec.Sec5.StagedS5Filt

/-!
# Proposition 5.9 at depth `ℓ`, step S6 (b): the restarted word is adapted and its lifetime is announced

Packet PROVE-STAGED-S6 (`planning/handoffs/PROVE-STAGED-S5.md` §5.2, step 4). For PIECES' candidate on the glued space
and its Galmarino filtration `candFilt` (PROVE-STAGED-S4/S5):

* `stronglyAdapted_of_adaptedBefore`: a process adapted before `ζ`, vanishing from `ζ` on, with `{t < ζ} ∈ 𝓕 t`, is
  strongly adapted;
* **`measurableSet_lt_s3ζ_candFilt`**: `{r < s3ζ} ∈ candFilt r` (on every window `r` is before the restarted lifetime);
* **`stronglyAdapted_s3W_candFilt`**, **`stronglyAdapted_s6VL_candFilt`**, **`stronglyAdapted_s6VR_candFilt`**;
* the announcing times `s6Ann n = imgAnn n − S₀` (the template's away-from-the-hull times, read after the restart):
  `s6Ann_lt_s3ζ`, `monotone_s6Ann`, `exists_le_s6Ann`, and **`isStoppingTime_s6Ann_candFilt`** (on every window the
  event `{imgAnn n ≤ S₀ + r}` is read from Word49's stopped data through `imgAnn_le_iff'`, `isAway_iff_isAwayD`).

Conditional helpers with distinct names; they replace no source theorem. R48: only `h44` (R74) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS6

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)

/-! ### Strong adaptedness from adaptedness before a lifetime -/

section Gen

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}

/-- **A process adapted before `ζ` and vanishing from `ζ` on is strongly adapted**, if `{t < ζ} ∈ 𝓕 t`. -/
theorem stronglyAdapted_of_adaptedBefore (hX : AdaptedBefore 𝓕 ζ X)
    (hζ : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω})
    (h0 : ∀ (t : ℝ≥0) ω, ¬ (t : ℝ≥0∞) < ζ ω → X t ω = 0) : StronglyAdapted 𝓕 X := by
  intro t
  refine Measurable.stronglyMeasurable ?_
  intro B hB
  have e : X t ⁻¹' B = {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ B} ∪ ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ B}) := by
    ext ω
    by_cases h : (t : ℝ≥0∞) < ζ ω
    · simp only [mem_preimage, mem_union, mem_ofPred_eq, h, true_and, mem_inter_iff, mem_compl_iff,
        not_true_eq_false, false_and, or_false]
    · simp only [mem_preimage, mem_union, mem_ofPred_eq, h, false_and, mem_inter_iff, mem_compl_iff,
        not_false_eq_true, true_and, false_or, h0 t ω h]
  rw [e]
  exact (hX t B hB).union ((hζ t).compl.inter (MeasurableSet.const _))

theorem s3W_eq_zero {Ω : Type*} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {τ : ℝ} {r : ℝ≥0}
    {p : Ω × HistorySpace 0 0} (h : ¬ (r : ℝ≥0∞) < s3ζ s Wj E τ p) : s3W s Wj E τ r p = 0 := by
  classical
  have h' : ¬ (p ∈ univ ∧ ((s3Start s Wj E τ p + r : ℝ≥0) : WithTop ℝ≥0) <
      kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) := fun h'' => h (lt_arcζ_iff.2 h'')
  simp only [s3W, arcW, h', ↓reduceIte]

end Gen

/-! ### The candidate's restarted word is strongly adapted -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

include hκ4 in
/-- **The restarted lifetime is a stopping time of the Galmarino filtration**: `{r < s3ζ} ∈ candFilt r`. -/
theorem measurableSet_lt_s3ζ_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (r : ℝ≥0) :
    MeasurableSet[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r]
      {p | (r : ℝ≥0∞) < s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
        (lastO ℓ t : ℝ) p} := by
  have hW := adaptedBefore_candW x₀ h44 hκ hκ4 hb h hG.1 ℓ t
  have hE : MeasurableSet (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  refine measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
    (measurableSet_lt measurable_const (measurable_s3ζ hW hE hEg _)) fun q hq => ?_
  refine ⟨univ, MeasurableSet.univ, fun p hp hg hw => ?_⟩
  have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
  obtain ⟨hal, -, hqP, hlt⟩ := hw
  have hz := (lt_s3ζ_and_lt_s5ζ hqpos hEg hp hg hq hal hqP hlt le_rfl).1
  exact ⟨fun _ => mem_univ _, fun _ => hz⟩

include hκ4 in
theorem stronglyAdapted_s3W_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    StronglyAdapted (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
      (s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)) :=
  stronglyAdapted_of_adaptedBefore (adaptedBefore_s3W_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
    (measurableSet_lt_s3ζ_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs) fun _ _ h' => s3W_eq_zero h'

include hκ4 in
theorem stronglyAdapted_s6VL_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {nL : ℕ} (xL : Fin nL → ℝ) (i : Fin ((nL + 1) + ℓ)) :
    StronglyAdapted (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
      (s6VL xL (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
        (lastO ℓ t : ℝ) i) :=
  stronglyAdapted_of_adaptedBefore
    (adaptedBefore_s3VL_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs xL (treeIdx ℓ (nL + 1) i))
    (measurableSet_lt_s3ζ_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs) fun _ _ h' => by
      simp only [s6VL, s3VL, arcVL]
      exact ite_eq_right_iff.2 fun hc => absurd hc h'

include hκ4 in
theorem stronglyAdapted_s6VR_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {nR : ℕ} (xR : Fin nR → ℝ) (j : Fin ((nR + 1) + ℓ)) :
    StronglyAdapted (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
      (s6VR xR (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
        (lastO ℓ t : ℝ) j) :=
  stronglyAdapted_of_adaptedBefore
    (adaptedBefore_s3VR_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs xR (treeIdx ℓ (nR + 1) j))
    (measurableSet_lt_s3ζ_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs) fun _ _ h' => by
      simp only [s6VR, s3VR, arcVR]
      exact ite_eq_right_iff.2 fun hc => absurd hc h'

end Cand

/-! ### The announcing times of the restarted lifetime -/

section AnnDef

variable {Ω : Type*} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {τ : ℝ}

/-- **The announcing times of the restarted lifetime**: the template's away times (`Word49.imgAnn`: the image capacity
up to which the flow line stays `1/(n+1)` away from the counterflow hull, capped at own time `n`), after the
restart. -/
def s6Ann (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ) (n : ℕ)
    (p : Ω × HistorySpace 0 0) : ℝ≥0 :=
  imgAnn s (fun _ => ⊤) Wj E n p - s3Start s Wj E τ p

theorem s6Ann_lt_s3ζ (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (n : ℕ) (p : Ω × HistorySpace 0 0) :
    (s6Ann s Wj E τ n p : ℝ≥0∞) < s3ζ s Wj E τ p := by
  refine lt_arcζ_iff.2 ⟨mem_univ _, ?_⟩
  rw [s6Ann, add_tsub_eq_max]
  rcases le_total (s3Start s Wj E τ p) (imgAnn s (fun _ => ⊤) Wj E n p) with hle | hle
  · rw [max_eq_right hle]
    exact imgAnn_lt_imgT hEg n p
  · rw [max_eq_left hle]
    exact s3Start_lt_kLife' hEg τ p

theorem monotone_s6Ann (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (p : Ω × HistorySpace 0 0) :
    Monotone (s6Ann s Wj E τ · p) := fun _ _ hnm => tsub_le_tsub_right (monotone_imgAnn hEg p hnm) _

theorem exists_le_s6Ann (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < s3ζ s Wj E τ p) : ∃ n, u ≤ s6Ann s Wj E τ n p := by
  obtain ⟨-, hlt⟩ := lt_arcζ_iff.1 hu
  obtain ⟨n, hn⟩ := exists_le_imgAnn hEg hp (u := s3Start s Wj E τ p + u) hlt
  exact ⟨n, le_tsub_of_add_le_left hn⟩

end AnnDef

section AnnCand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

include hκ4 in
/-- **The announcing times are stopping times of the Galmarino filtration.** -/
theorem isStoppingTime_s6Ann_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (n : ℕ) :
    IsStoppingTime (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs) fun p =>
      ((s6Ann s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) n p :
        ℝ≥0) : WithTop ℝ≥0) := by
  intro r
  have hW := adaptedBefore_candW x₀ h44 hκ hκ4 hb h hG.1 ℓ t
  have hE : MeasurableSet (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  set Wc := candW x₀ h44 hκ hκ4 hb h ℓ t with hWc
  set Eg := candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s with hEgdef
  have e : {p | ((s6Ann s Wc Eg (lastO ℓ t : ℝ) n p : ℝ≥0) : WithTop ℝ≥0) ≤ r} =
      {p | imgAnn s (fun _ => ⊤) Wc Eg n p ≤ s3Start s Wc Eg (lastO ℓ t : ℝ) p + r} := by
    ext p
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, s6Ann, tsub_le_iff_left]
  rw [e]
  refine measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
    (measurableSet_le (measurable_imgAnn hW hE hEg n)
      ((StagedS4.measurable_s3Start hW hE hEg (lastO ℓ t)).add measurable_const)) fun q hq => ?_
  have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast hqpos.le
  set S : Set (XD s q) := (⋂ q' : ℚ, {x : XD s q | (q' : ℝ) < q → IsAwayD s n x.1 q' →
      capD s q q' x ≤ ((s5S₀ s q (lastO ℓ t) x + r : ℝ≥0) : ℝ)}) ∩ {x : XD s q | ¬ IsAwayD s n x.1 q} with hSdef
  have hSm : MeasurableSet S := by
    refine (MeasurableSet.iInter fun q' => ?_).inter
      (measurable_subtype_coe (measurableSet_isAwayD (nL := 0) (nR := 0) (s := s) n q)).compl
    by_cases hq' : (0 : ℝ) ≤ q' ∧ (q' : ℝ) < q
    · have e' : {x : XD s q | (q' : ℝ) < q → IsAwayD s n x.1 q' →
          capD s q q' x ≤ ((s5S₀ s q (lastO ℓ t) x + r : ℝ≥0) : ℝ)} =
          (Subtype.val ⁻¹' {y : Y49 0 0 | IsAwayD s n y q'})ᶜ ∪
            {x | capD s q q' x ≤ ((s5S₀ s q (lastO ℓ t) x + r : ℝ≥0) : ℝ)} := by
        ext x
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, hq'.2, true_imp_iff]
        tauto
      rw [e']
      exact (measurable_subtype_coe (measurableSet_isAwayD n q')).compl.union
        (measurableSet_le (measurable_indicator_capClock_gammaD q' hq'.1 hq'.2.le)
          (measurable_coe_nnreal_real.comp ((measurable_s5S₀ (lastO ℓ t)).add measurable_const)))
    · have e' : {x : XD s q | (q' : ℝ) < q → IsAwayD s n x.1 q' →
          capD s q q' x ≤ ((s5S₀ s q (lastO ℓ t) x + r : ℝ≥0) : ℝ)} = univ := by
        ext x
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro h1 h2
        exact absurd ⟨h2.1.1, h1⟩ hq'
      rw [e']
      exact MeasurableSet.univ
  obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD hSm
  refine ⟨C, hC, fun p hp hg hw => ?_⟩
  obtain ⟨hal, -, hqP, hlt⟩ := hw
  change _ ↔ (stopX hqpos hEg hp hg).1 ∈ C
  rw [← hCS (stopX hqpos hEg hp hg)]
  show imgAnn s (fun _ => ⊤) Wc Eg n p ≤ s3Start s Wc Eg (lastO ℓ t : ℝ) p + r ↔ _
  rw [imgAnn_le_iff' hEg hp hq0 hlt le_rfl n]
  simp only [hSdef, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [s5S₀_stopX hqpos hEg hp hg hq hal]
  refine and_congr (forall_congr' fun q' => imp_congr_right fun hq' => ?_)
    (not_congr (isAway_iff_isAwayD hg le_rfl))
  rw [isAway_iff_isAwayD hg hq'.le]
  refine imp_congr_right fun ha => ?_
  have hPc : (q' : ℝ) ∈ PcD s (stopX hqpos hEg hp hg).1 :=
    ((stopX hqpos hEg hp hg).2.rat q' ha.1.1 hq'.le).2 ⟨n, ha.2⟩
  have hcap : capD s q q' (stopX hqpos hEg hp hg) = capClock (gCurve s (fun _ => ⊤) Wc Eg p) q' := by
    rw [capD, indicator_of_mem (show stopX hqpos hEg hp hg ∈ {x : XD s q | (q' : ℝ) ∈ PcD s x.1} from hPc)]
    exact capClock_stopX hqpos hEg hp hg hq'.le
  rw [hcap]

include hκ4 in
/-- **The announcing sequence of the restarted lifetime** for the Galmarino filtration, under any measure for which
almost every glued sample is good. -/
theorem isAnnouncingSeq_s6Ann (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {μ : Measure (Ω × HistorySpace 0 0)}
    (hgood : ∀ᵐ p ∂μ, p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) :
    Coupling.IsAnnouncingSeq (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs) μ
      (s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s6Ann s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)) := by
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  refine ⟨fun n => isStoppingTime_s6Ann_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs n,
    fun p => monotone_s6Ann hEg p, fun n => Eventually.of_forall fun p => s6Ann_lt_s3ζ hEg n p, ?_⟩
  filter_upwards [hgood] with p hp
  exact fun u hu => exists_le_s6Ann hEg hp hu

end AnnCand

end InteractingSLE.Sec5.CrossCond.StagedS6
