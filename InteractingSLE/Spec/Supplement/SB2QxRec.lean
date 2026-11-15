/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxFlow
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Sec2.Assembly2Life

/-!
# Record matching: a record that is kernel-a.s. constant has a measurable regular driver

Worker REVIEW-FABLE-T14 (items 2–3 of PROVE-SB2-LCMEAN's handoff R13.8: the record matching of the step `ℓ → ℓ + 2`,
and the record clause of LCMEAN's `Mz.CanonIdentOn`). The record of B's piece read in the canonical chart must be,
almost surely on the stage event, the record of a driver measurable for the marks after B's stage (`Ms.stageMarks
(ℓ + 1)`, uncompleted). The route: under the regular conditional law given the marks, the record is almost surely the
conditioning sample's (it is determined by data the marks know); a map with that property has a measurable version;
and a record has a measurable decoding into a regular driver with the same record.

* **`exists_measurable_ae_eq_of_kernel_const`**: a map into a standard Borel space that is, for `P`-a.e. `ω₀ ∈ G`,
  almost surely constant under `condExpKernel P 𝓜 ω₀` agrees almost surely on `G` with an `𝓜`-measurable map;
* `recCode`, **`recDrvOf`** (measurable, regular at every record), **`recOf_recDrvOf`** (the decoded driver of the
  record of a regular driver continuous up to its lifetime has the same record);
* `continuousOn_of_good` (a regular driver with a good record is continuous up to its lifetime);
* **`exists_regular_rec_version`**.

All statements are standard (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Qx

open Exist Exist.Staged Exist.StagedLaw Sec2.Assembly

/-- **A kernel-a.s. constant map has a measurable version.** -/
theorem exists_measurable_ae_eq_of_kernel_const {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝓜 : 𝓜 ≤ mΩ)
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] {f : Ω → X} (hf : Measurable f)
    {G : Set Ω} (hconst : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), f ω = f ω₀) :
    ∃ g : Ω → X, Measurable[𝓜] g ∧ ∀ᵐ ω ∂P, ω ∈ G → f ω = g ω := by
  have hι := measurableEmbedding_embeddingReal X
  obtain ⟨ι', hι'm, hι'⟩ := hι.exists_measurable_extend (g := id) measurable_id fun _ => inferInstance
  set ψ : Ω → ℝ := fun ω => Real.arctan (embeddingReal X (f ω)) with hψ
  have hψm : Measurable ψ := Real.measurable_arctan.comp (hι.measurable.comp hf)
  have hψb : ∀ ω, ‖ψ ω‖ ≤ Real.pi / 2 := fun ω => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have hψi : Integrable ψ P :=
    Integrable.of_bound hψm.aestronglyMeasurable (Real.pi / 2) (Eventually.of_forall hψb)
  have htan : Measurable Real.tan := by
    have e : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
    rw [e]; exact Real.measurable_sin.div Real.measurable_cos
  refine ⟨fun ω => ι' (Real.tan ((P[ψ | 𝓜]) ω)), hι'm.comp (htan.comp stronglyMeasurable_condExp.measurable), ?_⟩
  filter_upwards [hconst, condExp_ae_eq_integral_condExpKernel h𝓜 hψi] with ω₀ hc hce hω₀
  have hint : ∫ ω, ψ ω ∂(condExpKernel P 𝓜 ω₀) = ψ ω₀ := by
    have hae : (fun ω => ψ ω) =ᵐ[condExpKernel P 𝓜 ω₀] fun _ => ψ ω₀ :=
      (hc hω₀).mono fun ω hω => by change Real.arctan _ = Real.arctan _; rw [hω]
    rw [integral_congr_ae hae]
    simp
  change f ω₀ = ι' (Real.tan ((P[ψ | 𝓜]) ω₀))
  rw [hce, hint, hψ]
  simp only [Real.tan_arctan]
  exact (congrFun hι' (f ω₀)).symm

/-- The dyadic code read from a record. -/
def recCode (r : RecData) : PCode := fun n k => r.1 ((k : ℚ) / 2 ^ n)

theorem measurable_recCode : Measurable recCode :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp measurable_fst

theorem toNNReal_dyadQ (n k : ℕ) : ((((k : ℚ) / 2 ^ n : ℚ) : ℝ)).toNNReal = dyad n k := by
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (by positivity)]
  simp [dyad]

theorem recCode_recOf (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : recCode (recOf ⊤ e) = enc (retOf ⊤ e).1 := by
  funext n k
  change (retOf ⊤ e).1 ((((k : ℚ) / 2 ^ n : ℚ) : ℝ)).toNNReal = (retOf ⊤ e).1 (dyad n k)
  rw [toNNReal_dyadQ]

/-- **The decoded driver of a record**: the regularization of the decoded dyadic path, with the recorded time. -/
def recDrvOf (r : RecData) : (ℝ≥0 → ℝ) × ℝ≥0∞ := StagedReg.regularize ⊤ (dec (recCode r), r.2.1)

theorem measurable_recDrvOf : Measurable recDrvOf := by
  have h1 : Measurable fun r : RecData => dec (recCode r) :=
    measurable_pi_iff.2 fun t => measurable_dec.comp (measurable_recCode.prodMk measurable_const)
  have h2 : Measurable fun r : RecData => r.2.1 := measurable_fst.comp measurable_snd
  have h := (StagedReg.measurable_regularize ⊤).comp (h1.prodMk h2)
  exact h

theorem isRegularDriver_recDrvOf (r : RecData) : IsRegularDriver (recDrvOf r) :=
  StagedReg.isRegularDriver_regularize _ _

/-- The record of a driver only sees the driver stopped at its lifetime. -/
theorem recOf_top_eq_of_canonDrv_eq {D D' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h : canonDrv ⊤ D = canonDrv ⊤ D') :
    recOf ⊤ D = recOf ⊤ D' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [canonDrv, le_top, ↓reduceIte] at h1 h2
  unfold recOf retOf readRec
  simp only [min_eq_right le_top, le_top, decide_true]
  rw [h2]
  refine Prod.ext (funext fun q => ?_) rfl
  have := congrFun h1 (q : ℝ).toNNReal
  simp only [min_eq_right le_top, h2] at this ⊢
  exact this

/-- A regular driver whose record is good (or whose lifetime is infinite) is continuous up to its lifetime. -/
theorem continuousOn_of_good {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : e.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ e))) :
    ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ e.2} := by
  by_cases htop : e.2 = ⊤
  · refine he.1.mono fun s hs => ?_
    simp only [mem_ofPred_eq, htop] at hs ⊢
    exact ENNReal.coe_lt_top
  have hc := continuous_retOf he (hg htop)
  refine hc.continuousOn.congr fun s hs => ?_
  change e.1 s = e.1 (min (s : ℝ≥0∞) (min ⊤ e.2)).toNNReal
  rw [min_eq_right le_top, min_eq_left hs, ENNReal.toNNReal_coe]

/-- **The decoded driver has the record**, for a regular driver continuous up to its lifetime. -/
theorem recOf_recDrvOf {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ e.2}) : recOf ⊤ (recDrvOf (recOf ⊤ e)) = recOf ⊤ e := by
  set f : ℝ≥0 → ℝ := (retOf ⊤ e).1 with hf
  have hfe : ∀ s : ℝ≥0, f s = e.1 (min (s : ℝ≥0∞) e.2).toNNReal := fun s => by
    rw [hf]; change e.1 _ = _; rw [min_eq_right (le_top : e.2 ≤ ⊤)]
  have hfc : Continuous f := by
    by_cases htop : e.2 = ⊤
    · have hc' : Continuous e.1 := continuousOn_univ.1 (hc.mono fun s _ => by
        simp only [mem_ofPred_eq, htop, le_top])
      refine hc'.congr fun s => ?_
      rw [hfe, htop, min_eq_left le_top, ENNReal.toNNReal_coe]
    · set T : ℝ≥0 := e.2.toNNReal with hT
      have hTe : (T : ℝ≥0∞) = e.2 := ENNReal.coe_toNNReal htop
      have hmin : Continuous fun s : ℝ≥0 => min s T := continuous_id.min continuous_const
      have hmaps : MapsTo (fun s : ℝ≥0 => min s T) univ {s | (s : ℝ≥0∞) ≤ e.2} := fun s _ => by
        simp only [mem_ofPred_eq, ← hTe, ENNReal.coe_le_coe]; exact min_le_right _ _
      refine (hc.comp_continuous hmin fun s => hmaps (mem_univ s)).congr fun s => ?_
      change e.1 (min s T) = f s
      rw [hfe, ← hTe, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  have hdec : dec (recCode (recOf ⊤ e)) = f := by
    rw [recCode_recOf]; exact Sec2.Assembly2.dec_enc_of_continuous hfc
  have h2 : (recOf ⊤ e).2.1 = e.2 := min_eq_right le_top
  have hdrv : recDrvOf (recOf ⊤ e) = StagedReg.regularize ⊤ (f, e.2) := by
    unfold recDrvOf; rw [hdec, h2]
  have hf0 : f 0 = 0 := by
    rw [hfe]; simp only [ENNReal.coe_zero, zero_le, min_eq_left, ENNReal.toNNReal_zero]; exact he.2.1
  have hreg := StagedReg.canonDrv_regularize (t := ⊤) (e := (f, e.2)) hf0 (hfc.continuousOn)
  rw [hdrv, recOf_top_eq_of_canonDrv_eq hreg]
  refine recOf_top_eq_of_canonDrv_eq ?_
  unfold canonDrv
  refine Prod.ext (funext fun r => ?_) rfl
  change f _ = e.1 _
  rw [hfe]
  simp only [min_eq_right (le_top : e.2 ≤ ⊤)]
  rcases le_total (r : ℝ≥0∞) e.2 with hr | hr
  · rw [min_eq_left hr, ENNReal.toNNReal_coe, min_eq_left hr, ENNReal.toNNReal_coe]
  · rw [min_eq_right hr]
    by_cases htop : e.2 = ⊤
    · rw [htop] at hr ⊢; simp
    · rw [ENNReal.coe_toNNReal htop, min_self]

/-- **Record matching from kernel constancy.** If the record of a measurable regular driver `e` is, for `P`-a.e.
`ω₀ ∈ G`, almost surely the conditioning sample's under `condExpKernel P 𝓜 ω₀`, and `e` is continuous up to its
lifetime almost surely on `G`, then a driver `Dr`, measurable for `𝓜` and regular at every sample, has almost surely
on `G` the record of `e`. -/
theorem exists_regular_rec_version {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝓜 : 𝓜 ≤ mΩ)
    {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (he : Measurable e) (hreg : ∀ ω, IsRegularDriver (e ω)) {G : Set Ω}
    (hc : ∀ᵐ ω ∂P, ω ∈ G → ContinuousOn (e ω).1 {s | (s : ℝ≥0∞) ≤ (e ω).2})
    (hconst : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), recOf ⊤ (e ω) = recOf ⊤ (e ω₀)) :
    ∃ Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable[𝓜] Dr ∧ (∀ ω, IsRegularDriver (Dr ω)) ∧
      ∀ᵐ ω ∂P, ω ∈ G → recOf ⊤ (Dr ω) = recOf ⊤ (e ω) := by
  obtain ⟨g, hgm, hg⟩ := exists_measurable_ae_eq_of_kernel_const h𝓜 (measurable_recOf he hreg ⊤) hconst
  refine ⟨fun ω => recDrvOf (g ω), measurable_recDrvOf.comp hgm, fun ω => isRegularDriver_recDrvOf _, ?_⟩
  filter_upwards [hg, hc] with ω hω hcω hωG
  rw [← hω hωG]
  exact recOf_recDrvOf (hreg ω) (hcω hωG)

end InteractingSLE.Theorem14.SB.Qx
