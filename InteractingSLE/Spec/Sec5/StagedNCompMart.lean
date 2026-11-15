/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNCompFilt
import InteractingSLE.Spec.Sec5.StagedS6Mart

/-!
# The martingale and the word entrance after the last switch for a flag candidate

Packet PROVE-STAGED-NODECOMP. PROVE-STAGED-S6's `StagedS6Ann` and `StagedS6Mart` (candidate part) for the flag
candidate of arbitrary angle flags `fl` (first angle `θ₀ = flagAngle (fl 0)`, coupling field `qField + θ₀χ`); the
generic parts of S6 (tree order, killed words of arc pieces, `s6VL`/`s6VR`, `s6Ann`) are reused.

* `measurableSet_lt_s3ζ_candFiltF`, `stronglyAdapted_s3W/s6VL/s6VR_candFiltF`: Galmarino facts for `candFiltF`;
* `isStoppingTime_s6Ann_candFiltF`, **`isAnnouncingSeq_s6AnnF`**: the announcing sequence of the restarted lifetime;
* `monotone_candTsF`; **`isChartCouplingCharFunConst_candF`**: the chart clause under the conditioned measure;
* **`exists_isWordEntrance_candF`**: Wang–Wu Lemma 2.11 for the flag candidate's restarted word in tree order,
  conditioned on the alive event, driven by a Brownian motion of the usual augmentation of `candFiltF`.

For the node flags `nodeFlag s` this is the word entrance of every node candidate's tree piece. R48: the only named
input is `h44 : Theorem12ParamCond44Statement` (R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater Prop59NodeTree
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open StagedFinal (imgStageRhoL imgStageRhoR)

/-! ### Ported from `StagedS6Ann` -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

include hκ4 in
/-- **The restarted lifetime is a stopping time of the Galmarino filtration**: `{r < s3ζ} ∈ candFiltF r`. -/
theorem measurableSet_lt_s3ζ_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (r : ℝ≥0) :
    MeasurableSet[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r]
      {p | (r : ℝ≥0∞) < s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) p} := by
  have hW := adaptedBefore_candWF x₀ h44 hκ hκ4 hb h fl hG.1 ℓ t
  have hE : MeasurableSet (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  refine measurableSet_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
    (measurableSet_lt measurable_const (measurable_s3ζ hW hE hEg _)) fun q hq => ?_
  refine ⟨univ, MeasurableSet.univ, fun p hp hg hw => ?_⟩
  have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
  obtain ⟨hal, -, hqP, hlt⟩ := hw
  have hz := (lt_s3ζ_and_lt_s5ζ hqpos hEg hp hg hq hal hqP hlt le_rfl).1
  exact ⟨fun _ => mem_univ _, fun _ => hz⟩

include hκ4 in
theorem stronglyAdapted_s3W_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    StronglyAdapted (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
      (s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)) :=
  stronglyAdapted_of_adaptedBefore (adaptedBefore_s3W_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
    (measurableSet_lt_s3ζ_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs) fun _ _ h' => s3W_eq_zero h'

include hκ4 in
theorem stronglyAdapted_s6VL_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {nL : ℕ} (xL : Fin nL → ℝ) (i : Fin ((nL + 1) + ℓ)) :
    StronglyAdapted (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
      (s6VL xL (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) i) :=
  stronglyAdapted_of_adaptedBefore
    (adaptedBefore_s3VL_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs xL (treeIdx ℓ (nL + 1) i))
    (measurableSet_lt_s3ζ_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs) fun _ _ h' => by
      simp only [s6VL, s3VL, arcVL]
      exact ite_eq_right_iff.2 fun hc => absurd hc h'

include hκ4 in
theorem stronglyAdapted_s6VR_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {nR : ℕ} (xR : Fin nR → ℝ) (j : Fin ((nR + 1) + ℓ)) :
    StronglyAdapted (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
      (s6VR xR (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) j) :=
  stronglyAdapted_of_adaptedBefore
    (adaptedBefore_s3VR_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs xR (treeIdx ℓ (nR + 1) j))
    (measurableSet_lt_s3ζ_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs) fun _ _ h' => by
      simp only [s6VR, s3VR, arcVR]
      exact ite_eq_right_iff.2 fun hc => absurd hc h'

end Cand

section AnnCand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

include hκ4 in
/-- **The announcing times are stopping times of the Galmarino filtration.** -/
theorem isStoppingTime_s6Ann_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (n : ℕ) :
    IsStoppingTime (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs) fun p =>
      ((s6Ann s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) n
          p :
        ℝ≥0) : WithTop ℝ≥0) := by
  intro r
  have hW := adaptedBefore_candWF x₀ h44 hκ hκ4 hb h fl hG.1 ℓ t
  have hE : MeasurableSet (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) := measurableSet_glueGood
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  set Wc := candWF x₀ h44 hκ hκ4 hb h fl ℓ t with hWc
  set Eg := candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s with hEgdef
  have e : {p | ((s6Ann s Wc Eg (lastO ℓ t : ℝ) n p : ℝ≥0) : WithTop ℝ≥0) ≤ r} =
      {p | imgAnn s (fun _ => ⊤) Wc Eg n p ≤ s3Start s Wc Eg (lastO ℓ t : ℝ) p + r} := by
    ext p
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, s6Ann, tsub_le_iff_left]
  rw [e]
  refine measurableSet_candFiltF_of_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
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
theorem isAnnouncingSeq_s6AnnF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {μ : Measure (Ω × HistorySpace 0 0)}
    (hgood : ∀ᵐ p ∂μ, p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) :
    Coupling.IsAnnouncingSeq (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs) μ
      (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s6Ann s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ)) := by
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  refine ⟨fun n => isStoppingTime_s6Ann_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs n,
    fun p => monotone_s6Ann hEg p, fun n => Eventually.of_forall fun p => s6Ann_lt_s3ζ hEg n p, ?_⟩
  filter_upwards [hgood] with p hp
  exact fun u hu => exists_le_s6Ann hEg hp hu

end AnnCand

/-! ### Ported from `StagedS6Mart` -/

section Times

variable {fl : ℕ → Bool} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}

theorem monotone_candTsF (hv : IsValid ℓ t) : Monotone fun j : Fin ℓ => candTsF fl ℓ t (j + 1) := by
  intro j j' hjj
  simp only [candTsF_succ hv]
  rcases hjj.lt_or_eq with hlt | heq
  · rw [oTime_eq (hv.2 j).2.2, oTime_eq (hv.2 j').2.2]
    exact (decode_strictMono (hv.2 j').2.1 (hv.1 hlt)).le
  · rw [heq]

end Times

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

include hκ4 in
/-- **The candidate's chart clause at fixed restarted times, conditioned on the alive event.** -/
theorem isChartCouplingCharFunConst_candF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    Sec7.Lemma71D.IsChartCouplingCharFunConst κ
      (imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ
          hb).jumps
        0 (flagAngle (fl 0))) (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ)
      (imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ
          hb).jumps
        0 (flagAngle (fl 0))) (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ)
      ((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)])
      (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
      (s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTsF fl ℓ t) ℓ s
        (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTsF fl ℓ t) ℓ s
        (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3Chart s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (2 * Real.pi * chiC κ + (candAngF fl ℓ t ℓ - candAngF fl ℓ t 0) * chiC κ) (chiC κ)
      (fun p => rootFieldT κ x₀ (flagAngle (fl 0)) h p.1) := by
  intro r u hu φ
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set Wc := candWF x₀ h44 hκ hκ4 hb h fl ℓ t with hWc
  set Eg := candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s with hEgdef
  set A := s3Alive s Wc Eg (lastO ℓ t : ℝ) with hAdef
  set 𝓐 := candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs with h𝓐
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  have hAm : MeasurableSet[𝓐 r] A := measurableSet_s3Alive_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r
  set X : Ω × HistorySpace 0 0 → ℂ := fun p' =>
    Complex.exp (Complex.I * (rootFieldT κ x₀ (flagAngle (fl 0)) h p'.1 φ : ℂ)) with hXdef
  have hXm : Measurable X := Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    (((LQGMetric.measurable_distOn_apply φ).comp (measurable_rootFieldT hG.1 (flagAngle (fl 0)))).comp measurable_fst)))
  have hXb : ∀ p, ‖X p‖ ≤ 1 := fun p => by
    simp only [hXdef]
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hXi : Integrable X μ := Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  have h1 := ae_condExp_candFiltF_full x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hus hv hs φ r
  have h2 := Sec5.Aux61FibK.condExp_cond_ae_eq (𝓐.le r) hAm hXi
  have hAmeas : MeasurableSet A := 𝓐.le r _ hAm
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hK := isKilledWord_s6 (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0) hEg hF.2.1 hF.1
    hF.2.2.2 hF.2.2.1 (candTsF_bounds (fl := fl) hv) (monotone_candTsF (fl := fl) hv)
  filter_upwards [cond_absolutelyContinuous.ae_le h1, h2, ae_cond_mem hAmeas] with p hp1 hp2 hpA hlt hsupp
  have hmem : p ∈ candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r := ⟨hpA, hlt, hsupp⟩
  have e1 := hp2.trans (hp1 hmem)
  refine e1.trans ?_
  have hcc := isConformal_s3Chart hEg hpA
  have hvL : ∀ i, s3VL (flowLineXL c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) i r p ≤
      s3W s Wc Eg (lastO ℓ t : ℝ) r p := fun i => by
    have := hK.ordL p r ((treeIdx ℓ _).symm i) hlt
    simpa only [s6VL, Equiv.apply_symm_apply] using this
  have hvR : ∀ j, s3W s Wc Eg (lastO ℓ t : ℝ) r p ≤
      s3VR (flowLineXR c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) j r p := fun j => by
    have := hK.ordR p r ((treeIdx ℓ _).symm j) hlt
    simpa only [s6VR, Equiv.apply_symm_apply] using this
  have hav : Sec7.Lemma71D.IsChartAvoid (fun r' => s3W s Wc Eg (lastO ℓ t : ℝ) r' p)
      (s3ζ s Wc Eg (lastO ℓ t : ℝ) p) (s3Chart s Wc Eg (lastO ℓ t : ℝ) p) φ r := ⟨hlt, hsupp⟩
  have hI := Sec7.Lemma71D.integral_couplingMean_eq_chartMean (κ := κ)
    (ρL := imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ c.fn c.jumps 0 (flagAngle (fl 0))) (fun j => candAngF fl
        ℓ t j - candAngF fl ℓ t 0) ℓ)
    (ρR := imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ c.fn c.jumps 0 (flagAngle (fl 0))) (fun j => candAngF fl
        ℓ t j - candAngF fl ℓ t 0) ℓ)
    (w := fun r' => s3W s Wc Eg (lastO ℓ t : ℝ) r' p)
    (vL := fun i r' => s3VL (flowLineXL c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) i r' p)
    (vR := fun j r' => s3VR (flowLineXR c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) j r' p)
    (ζ := s3ζ s Wc Eg (lastO ℓ t : ℝ) p) (c := s3Chart s Wc Eg (lastO ℓ t : ℝ) p)
    (a := 2 * Real.pi * chiC κ + (candAngF fl ℓ t ℓ - candAngF fl ℓ t 0) * chiC κ) (k := chiC κ) (φ := φ) (t := r) hcc.1
    (StagedS4.continuousOn_s3W hEg p) hav hvL hvR (hu p)
  unfold candFF s4F
  rw [← hI]
  rfl

include hκ4 in
/-- **The word entrance of the candidate's restarted word after the last switch** (Wang–Wu Lemma 2.11 for the killed
word in tree order), conditioned on the alive event: on `(glued space) × (ℕ → ℝ)` there is a Brownian motion of the
usual augmentation of `candFiltF` (extended by an independent filtration) driving the integrated equations of the
restarted word before its lifetime. -/
theorem exists_isWordEntrance_candF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : candMu x₀ (κ := κ) P h W ζ hG.1 (s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
      (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)) ≠ 0) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)))
      (B : ℝ≥0 → (Ω × HistorySpace 0 0) × (ℕ → ℝ) → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration (usualAugmentation
        (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
        ((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
          (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)])) 𝓦) B
        (((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
          (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)]).prod P₀) ∧
      (∀ p, Continuous fun r => B r p) ∧
      ∀ᵐ p ∂(((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
          (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)]).prod P₀),
        Sec7.Aux117.IsWordEntrance κ
          (fun i => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
            (lastO ℓ t : ℝ) i 0 p.1)
          (fun j => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
            (lastO ℓ t : ℝ) j 0 p.1)
          (fun i => imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn
            (sourceWord (x₀ := x₀) hκ hb).jumps 0 (flagAngle (fl 0))) (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ
            (treeIdx ℓ _ i))
          (fun j => imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn
            (sourceWord (x₀ := x₀) hκ hb).jumps 0 (flagAngle (fl 0))) (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ
            (treeIdx ℓ _ j))
          (fun r => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
            (lastO ℓ t : ℝ) r p.1)
          (fun i r => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
            (lastO ℓ t : ℝ) i r p.1)
          (fun j r => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
            (lastO ℓ t : ℝ) j r p.1)
          (fun r => B r p)
          (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)
            p.1) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set Wc := candWF x₀ h44 hκ hκ4 hb h fl ℓ t with hWc
  set Eg := candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s with hEgdef
  set A := s3Alive s Wc Eg (lastO ℓ t : ℝ) with hAdef
  set μA := μ[|A] with hμA
  have : IsProbabilityMeasure μA := cond_isProbabilityMeasure hA0
  set 𝓐 := candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs with h𝓐
  set 𝓖 := usualAugmentation 𝓐 μA with h𝓖
  have h𝓐𝓖 : 𝓐 ≤ 𝓖 := Ito.le_usualAugmentation 𝓐 μA
  have : 𝓖.IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  have hnull : ∀ s', MeasurableSet s' → μA s' = 0 → MeasurableSet[𝓖 0] s' := fun s' hs' h0 =>
    Ito.measurableSet_usualAugmentation_of_null hs' h0 0
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hK := isKilledWord_s6 (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0) hEg hF.2.1 hF.1
    hF.2.2.2 hF.2.2.1 (candTsF_bounds (fl := fl) hv) (monotone_candTsF (fl := fl) hv)
  -- adaptedness
  have hWa : StronglyAdapted 𝓖 (s3W s Wc Eg (lastO ℓ t : ℝ)) := fun r =>
    (stronglyAdapted_s3W_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r).mono (h𝓐𝓖 r)
  have hVLa : ∀ i, StronglyAdapted 𝓖
      (s6VL (flowLineXL c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) i) := fun i r =>
    (stronglyAdapted_s6VL_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs _ i r).mono (h𝓐𝓖 r)
  have hVRa : ∀ j, StronglyAdapted 𝓖
      (s6VR (flowLineXR c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) j) := fun j r =>
    (stronglyAdapted_s6VR_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs _ j r).mono (h𝓐𝓖 r)
  have hζm : ∀ r : ℝ≥0, MeasurableSet[𝓖 r] {p | s3ζ s Wc Eg (lastO ℓ t : ℝ) p ≤ r} := fun r => by
    have h1 := (measurableSet_lt_s3ζ_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r).compl
    convert h𝓐𝓖 r _ h1 using 1
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
    exact Iff.rfl
  -- the announcing sequence
  have hgoodA : ∀ᵐ p ∂μA, p ∈ Eg := cond_absolutelyContinuous.ae_le
    ((ae_good_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf ℓ t hv hs).mono fun p hp => hp.1)
  obtain ⟨hσ0, hσm, hσT, hσlim⟩ := isAnnouncingSeq_s6AnnF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs hgoodA
  have hσ : ∀ n, IsStoppingTime 𝓖 fun p => (s6Ann s Wc Eg (lastO ℓ t : ℝ) n p : WithTop ℝ≥0) := fun n r =>
    h𝓐𝓖 r _ (hσ0 n r)
  have hT : Coupling.IsAnnouncingSeq 𝓖 μA (s3ζ s Wc Eg (lastO ℓ t : ℝ)) (s6Ann s Wc Eg (lastO ℓ t : ℝ)) :=
    ⟨hσ, hσm, hσT, hσlim⟩
  -- the chart clause at stopping times and its transport
  have hch := isMeasChart_s3Chart_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
  have hFm : Measurable fun p : Ω × HistorySpace 0 0 => rootFieldT κ x₀ (flagAngle (fl 0)) h p.1 :=
    (measurable_rootFieldT hG.1 (flagAngle (fl 0))).comp measurable_fst
  have hcf1 := isChartCouplingCharFunConst_comp_equiv
    (isChartCouplingCharFunConst_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hus hv hs) (treeIdx ℓ _) (treeIdx ℓ _)
  have hcfU := Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation (P := μA) hFm hch.conf hch.lift
    (fun p => hK.contW p) (fun i p => (hK.pathL p i).1) (fun j p => (hK.pathR p j).1)
    (fun p r hr => ⟨fun i => hK.ordL p r i hr, fun j => hK.ordR p r j hr⟩) hcf1
  set a₀ : ℝ := 2 * Real.pi * chiC κ + (candAngF fl ℓ t ℓ - candAngF fl ℓ t 0) * chiC κ with ha₀
  set h' : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p =>
    Sec7.Lemma71K.chartField (s3Chart s Wc Eg (lastO ℓ t : ℝ) p) a₀ (chiC κ) (rootFieldT κ x₀ (flagAngle (fl 0)) h p.1)
    with hh'
  have ht : ∀ p, IsChartTransport (s3Chart s Wc Eg (lastO ℓ t : ℝ) p) 1 a₀ (chiC κ)
      (rootFieldT κ x₀ (flagAngle (fl 0)) h p.1) (h' p) := fun p =>
    Sec7.Lemma71K.isChartTransport_chartField (hch.conf p) (hch.lift p) _ _ _
  have hdom0 : ∀ z, MeasurableSet[𝓐 0] {p | z ∈ (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).dom} := fun z =>
    hch.measurableSet_mem (mX := 𝓐 0) z
  have hdom : ∀ z, MeasurableSet[𝓖 0] {p | z ∈ (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).dom} := fun z =>
    h𝓐𝓖 0 _ (hdom0 z)
  have hfwd : ∀ z, Measurable[𝓖 0] ({p | z ∈ (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).dom}.indicator
      fun p => (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).1 z) := fun z => (hch.fwd z).mono (h𝓐𝓖 0) le_rfl
  have hliftm : ∀ z, Measurable[𝓖 0] ({p | z ∈ (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).dom}.indicator
      fun p => (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).2.2 z) := fun z => (hch.lft z).mono (h𝓐𝓖 0) le_rfl
  have hcf' := Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport (P := μA) hch.conf hdom hfwd hliftm
    hch.lift hFm (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p⟩) hcfU ht
  have hh'm : Measurable h' := by
    have hm := Chart.measurable_chartTransport_random' hch.conf (fun z => 𝓐.le 0 _ (hdom0 z))
      (fun z => (hch.fwd z).mono (𝓐.le 0) le_rfl) (fun z => (hch.lft z).mono (𝓐.le 0) le_rfl) hch.lift hFm 1
      a₀ (chiC κ)
    have e : h' = fun p => Chart.chartTransport (hch.conf p) 1 a₀ (chiC κ)
        (rootFieldT κ x₀ (flagAngle (fl 0)) h p.1) := by
      funext p
      simp only [hh', Sec7.Lemma71K.chartField]
      exact dite_eq_left_of_eq_true (eq_true (hch.conf p))
    rw [e]
    exact hm
  have hpos : ∀ p, (0 : ℝ≥0∞) < s3ζ s Wc Eg (lastO ℓ t : ℝ) p := fun p => by
    refine lt_arcζ_iff.2 ⟨mem_univ _, ?_⟩
    rw [add_zero]
    exact s3Start_lt_kLife' hEg (lastO ℓ t : ℝ) p
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun p => h' p φ) μA := fun φ =>
    integrable_apply_of_isCouplingCharFun_of_bounded hcf'
      (Eventually.of_forall fun p => ⟨hpos p, hK.contW p, hK.w_zero p⟩)
      φ ((LQGMetric.measurable_distOn_apply φ).comp hh'm)
  -- the martingale clause
  have hWb : AdaptedBefore 𝓖 (s3ζ s Wc Eg (lastO ℓ t : ℝ)) (s3W s Wc Eg (lastO ℓ t : ℝ)) :=
    MartChar.adaptedBefore_of_stronglyAdapted hζm hWa
  have hmart : ∀ z ∈ H, MartChar.IsLocalMartingaleBefore 𝓖 μA
      (fun p => min (QuantumZipper.swallowTime (MartChar.wpath (s3W s Wc Eg (lastO ℓ t : ℝ)) p) z : WithTop ℝ≥0)
        (s6T s Wc Eg (lastO ℓ t : ℝ) p))
      (MartChar.coupProc κ
        (fun i => imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ c.fn c.jumps 0 (flagAngle (fl 0)))
          (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ (treeIdx ℓ _ i))
        (fun j => imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ c.fn c.jumps 0 (flagAngle (fl 0)))
          (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ (treeIdx ℓ _ j))
        (s3W s Wc Eg (lastO ℓ t : ℝ)) (s6VL (flowLineXL c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ))
        (s6VR (flowLineXR c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ)) z) := by
    intro z hz
    obtain ⟨G, hG0, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull hWb
      (fun i => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVLa i))
      (fun j => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVRa j))
      (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p,
        ⟨fun i => (hK.pathL p i).1, fun j => (hK.pathR p j).1⟩,
        fun r hr => ⟨fun i => hK.ordL p r i hr, fun j => hK.ordR p r j hr⟩⟩)
      hT hint hcf' (fun p r => MartChar.meanExt κ _ _ (s3W s Wc Eg (lastO ℓ t : ℝ) r p)
        (fun i => s6VL (flowLineXL c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) i r p)
        (fun j => s6VR (flowLineXR c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) j r p))
      (fun p r => MartChar.isBoundedHarmonicExtension_meanExt κ _ _ _ _ _) hz
    exact Restart.ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG0 hGae
      (Restart.ConverseBefore.measurable_coupProc_zero hK.w_zero
        (fun i => ((hVLa i 0).measurable.mono (𝓖.le 0) le_rfl))
        (fun j => ((hVRa j 0).measurable.mono (𝓖.le 0) le_rfl)) hz) hloc
  exact StagedRepLater.exists_isWordEntrance_std hκ hnull hK hWa hVLa hVRa hσ hσm
    (fun n p => s6Ann_lt_s3ζ hEg n p) hσlim hmart

end Cand

end InteractingSLE.Sec5.CrossCond.StagedNComp
