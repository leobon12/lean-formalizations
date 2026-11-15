/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndAsm
import InteractingSLE.Spec.Sec5.CrossCondMartPass

/-!
# Lemma 4.7 in the chart `Q`: the chart clause at fixed image times and the martingale clause (item D3)

Packet PROVE-CFRESTART5, item D3 (the Lemma 4.7 mirror of GLUECOND7's `CrossCondMartPass` and step B4 of
`CrossCondMart`). Given the stopped-history measurability of the image word (`hM1`, `hM3`: the image word before a
counterflow time is known from the two stopped histories, up to null sets — discharged in
`CrossRestartKernelQEndMarks`):

* `dyIdx_qTheta_and_mem_qAv_iff`: the dyadic pieces read through the capacity clock;
* **`ae_condExp_qRaw_eq_qF`**: the passage of step R1 (`ae_condExp_glue_eq_qF`) from deterministic dyadic counterflow
  times to a fixed image time `r` (Astra's E.4–E.6, WangWu's `setIntegral_eq_of_dyadic`);
* **`isChartCouplingCharFunConst_q`**: the chart coupling clause of the field `−h` at fixed image times of the raw
  image filtration (parameter `16/κ`, chart `fChart`, height shift `−πχ/2`, lift coefficient `−χ`);
* **`isLocalMartingaleBefore_q`**: the martingale clause of the killed image word in its filtration `qFilt` (Lemma
  7.1's pipeline: fixed times → stopping times of the usual augmentation → transport through the chart → local
  martingales of the explicit coupling means) — the hypothesis `hmart` of `exists_isWordEntrance_of_mart47`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar WholeField LocalSets CrossCond
open WangWu.ChartConst (dyq dyIdx dyF dyIdx_eq_iff setIntegral_eq_of_dyadic ae_condExp_eq_of_forall_setIntegral)
open CrossCond.Word49 (dyq_pos' div_le_dyq dyqR dyqR_pos dyqR_coe dyqR_toNNReal divR_coe divR_le_dyqR)

namespace Kill47

/-! ### The dyadic pieces -/

section Pieces

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}

/-- The pieces of the dyadic level sets, read through the capacity clock (deterministic, on a good sample alive at
the image time `r`). -/
theorem dyIdx_qTheta_and_mem_qAv_iff (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) {p : Ω × HistorySpace 0 0}
    {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p) (n k : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    (dyIdx n (qTheta W VL VR ζ s E r p) = k ∧ p ∈ qAv W VL VR ζ s E φ (dyq n k)) ↔
      (((dyq n k : ℝ≥0) : ℝ) ∈ qgPre W VL VR ζ s E p ∧ (r : ℝ) < capClock (qgCurve W s E p) (dyq n k)) ∧
        ¬ ((((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ qgPre W VL VR ζ s E p ∧
          (r : ℝ) < capClock (qgCurve W s E p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)) ∧
        p ∈ qAv W VL VR ζ s E φ (dyq n k) := by
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  obtain ⟨hθP, hθc⟩ := qTheta_spec hEg hr
  set θ := qTheta W VL VR ζ s E r p with hθdef
  have key : ∀ u : ℝ, u ∈ qgPre W VL VR ζ s E p →
      ((θ : ℝ) < u ↔ (r : ℝ) < capClock (qgCurve W s E p) u) := by
    intro u hu
    constructor
    · intro hlt
      rw [← hθc]
      exact hγ.strictMonoOn_capClock hθP hu hlt
    · intro hlt
      by_contra hle
      have := hγ.strictMonoOn_capClock.monotoneOn hu hθP (not_lt.1 hle)
      rw [hθc] at this
      linarith
  have hk0 : (0 : ℝ) ≤ (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hkt : (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ≤ ((dyq n k : ℝ≥0) : ℝ) := by exact_mod_cast div_le_dyq n k
  rw [dyIdx_eq_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, hAv⟩
    have hP : ((dyq n k : ℝ≥0) : ℝ) ∈ qgPre W VL VR ζ s E p := hAv.2.1
    have hP' := hγ.icc _ hP ⟨hk0, hkt⟩
    have h2' : (θ : ℝ) < ((dyq n k : ℝ≥0) : ℝ) := by exact_mod_cast h2
    refine ⟨⟨hP, (key _ hP).1 h2'⟩, fun hh => ?_, hAv⟩
    have h4 := (key _ hP').2 hh.2
    exact absurd (show θ < (k : ℝ≥0) / 2 ^ n by exact_mod_cast h4) (not_lt.2 h1)
  · rintro ⟨⟨hP, h2⟩, h3, hAv⟩
    have hP' := hγ.icc _ hP ⟨hk0, hkt⟩
    refine ⟨⟨?_, ?_⟩, hAv⟩
    · by_contra hlt
      have h5 : (θ : ℝ) < (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := by exact_mod_cast not_le.1 hlt
      exact h3 ⟨hP', (key _ hP').1 h5⟩
    · have := (key _ hP).2 h2
      exact_mod_cast this

end Pieces

/-! ### The clause at a fixed image time -/

section Main

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- The image marks of a chart-`Q` configuration are ordered. -/
theorem isOrderedForceWord_qx (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    IsOrderedForceWord (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) :=
  Theorem15.isOrderedForceWord_flowLine _ _ 0

/-- **The clause at a fixed image time** (Astra's E.4 with the passage of the characteristic functions along strict
upper dyadic counterflow times): almost surely on the validity event at the image time `r`,
`E[e^{i(−h,φ)} | qRaw r] = qF(r)`. -/
theorem ae_condExp_qRaw_eq_qF (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      IsGood47 W VL VR ζ p) {s : ℝ≥0} (hs : 0 < s)
    (hM1 : ∀ (r : ℝ≥0) (t' t : ℚ), (0 : ℝ) ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 0 0),
      MeasurableSet[qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k
        (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) r] A →
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
          A ∩ {p | (t' : ℝ) ∈ qgPre W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p ∧
            (r : ℝ) < capClock (qgCurve W s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p) t'})
    (hM3 : ∀ t : ℚ, 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
          qAv W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) φ (t : ℝ).toNNReal)
    (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      Sec7.Lemma71D.IsChartAvoid (fun t => qW W VL VR ζ s (glueGood47 (glueMeasure P k
          (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) t p)
        (qT W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p : ℝ≥0∞) (fChart W VL VR ζ s p) φ r →
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * ((-(h p'.1 φ) : ℝ) : ℂ)) |
          qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k
            (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) r] p =
        qF (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR) (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR)
          (-(π / 2 * chiC κ)) (-chiC κ) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) φ r p := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood47 μ W VL VR ζ with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood47
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  have hX := hC.2.2.2.1
  have hEae : ∀ᵐ p ∂μ, p ∈ E := ae_mem_glueGood47 hae
  have hxo := isOrderedForceWord_qx κ ρL ρR xL xR
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  have hFg := isZeroBoundaryGFF_cenT_glue (k := k) hC hu₀
  have hXm : Measurable fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * ((-(h p.1 φ) : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((((LQGMetric.measurable_distOn_apply φ).comp hC.2.1).comp measurable_fst).neg)))
  have hXb : ∀ p : Ω × HistorySpace 0 0, ‖Complex.exp (Complex.I * ((-(h p.1 φ) : ℝ) : ℂ))‖ ≤ 1 := fun p => by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hXi : Integrable (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * ((-(h p.1 φ) : ℝ) : ℂ))) μ :=
    Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  obtain ⟨hErm, hmeanm, hvarm⟩ := measurable_fChartAvoid_raw (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
    (-(π / 2 * chiC κ)) (-chiC κ) hxo hX hE hEg hs r φ
  set Er := {p : Ω × HistorySpace 0 0 | Sec7.Lemma71D.IsChartAvoid (fun t => qW W VL VR ζ s E t p)
    (qT W VL VR ζ s E p : ℝ≥0∞) (fChart W VL VR ζ s p) φ r} with hErdef
  set G := qF (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR) (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR)
    (-(π / 2 * chiC κ)) (-chiC κ) W VL VR ζ s E φ with hGdef
  have hGm : Measurable[qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s E r] (Er.indicator (G r)) := by
    have e : Er.indicator (G r) = Er.indicator (fun p => Complex.exp (Complex.I *
        ((Er.indicator (fun p => Sec7.Lemma71D.chartMean (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
          (fun t => qW W VL VR ζ s E t p) (fun i t => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E i t p)
          (fun j t => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E j t p) (fChart W VL VR ζ s p)
          (-(π / 2 * chiC κ)) (-chiC κ) φ r) p : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * Er.indicator (fun p => Sec7.Lemma71D.chartVar (fun t => qW W VL VR ζ s E t p)
          (fChart W VL VR ζ s p) φ r) p : ℝ) : ℂ))) := by
      refine Set.indicator_congr fun p hp => ?_
      simp only [hGdef, qF, indicator_of_mem hp]
    rw [e]
    refine Measurable.indicator ?_ hErm
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hmeanm).const_mul _ |>.sub
      (Complex.measurable_ofReal.comp (hvarm.const_mul _)))
  have hGi : Integrable (Er.indicator (G r)) μ := by
    refine Integrable.of_bound ((hGm.mono ((qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s E).le r)
      le_rfl).aestronglyMeasurable) 1 (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ Er
    · rw [indicator_of_mem hp]
      exact norm_qF_le_one hxo hEg hs φ hp.1
    · rw [indicator_of_notMem hp, norm_zero]
      exact zero_le_one
  refine ae_condExp_eq_of_forall_setIntegral
    ((qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s E).le r) hErm hXi hGm.stronglyMeasurable hGi ?_
  intro A hA
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hUm : ∀ t : ℝ≥0, Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 =>
      hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2 := fun t =>
    measurable_union_hitting (((measurable_hullAt s).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ t).comp measurable_snd)
  refine setIntegral_eq_of_dyadic hXi (Eventually.of_forall hXb)
    (fun n j => germSigma (fun p : Ω × HistorySpace 0 0 =>
      hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ (dyq n j) p.2)
        (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ s (dyq n j))
    (fun n j => sup_le (germSigma_le (hUm _) hFg.measurable) (cfGlueMarks_le _ _ hX))
    (Av := qAv W VL VR ζ s E φ)
    (F := fun q p => G (capClock (qgCurve W s E p) q).toNNReal p)
    (fun q p hp => norm_qF_le_one hxo hEg hs φ hp.2.2.1) ?_ (measurable_qTheta (s := s) hX hE hEg r)
    (((qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s E).le r _ hA).inter
      ((qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s E).le r _ hErm)) ?_ ?_
  · intro n j
    exact ae_condExp_glue_eq_qF hκ hκ4 hF h44 hC hcf hlaw k hk hu₀ hs (dyq_pos' n j) φ
  · intro n j
    have ht0 := dyqR_pos n j
    obtain ⟨B1, hB1m, hB1e⟩ := hM1 r (dyqR n j) (dyqR n j) (by exact_mod_cast ht0.le) le_rfl ht0 (A ∩ Er)
      (hA.inter hErm)
    obtain ⟨B2, hB2m, hB2e⟩ := hM1 r ((j : ℚ) / 2 ^ n) (dyqR n j) (by push_cast; positivity) (divR_le_dyqR n j) ht0
      univ MeasurableSet.univ
    obtain ⟨B3, hB3m, hB3e⟩ := hM3 (dyqR n j) ht0 φ
    rw [dyqR_toNNReal] at hB1m hB2m hB3m hB3e
    rw [dyqR_coe] at hB1e
    rw [divR_coe] at hB2e
    refine ⟨B1 ∩ B2ᶜ ∩ B3, le_sup_right (a := germSigma (fun p : Ω × HistorySpace 0 0 =>
      hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ (dyq n j) p.2)
        (fun p => cenT κ u₀ (cfField κ (h p.1)))) _ ((hB1m.inter hB2m.compl).inter hB3m), ?_⟩
    refine ((hB1e.inter hB2e.compl).inter hB3e).trans ?_
    refine Eventually.of_forall fun p => ?_
    simp only [mem_inter_iff, mem_compl_iff, mem_univ, true_and, eq_iff_iff]
    constructor
    · rintro ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
      have hh := (dyIdx_qTheta_and_mem_qAv_iff hEg hEr.1 n j φ).2 ⟨h1, h2, h3⟩
      exact ⟨⟨⟨hAp, hEr⟩, hh.1⟩, hh.2⟩
    · rintro ⟨⟨⟨hAp, hEr⟩, hd⟩, hav⟩
      obtain ⟨h1, h2, h3⟩ := (dyIdx_qTheta_and_mem_qAv_iff hEg hEr.1 n j φ).1 ⟨hd, hav⟩
      exact ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
  · filter_upwards [hEae] with p hpE hpD
    exact tendsto_qF_dyF hxo hEg hs hpE hpD.2

/-- **The chart coupling clause of the field `−h` at fixed image times of the raw image filtration** (steps R1–R6 of
the Lemma 4.7 direction, from the stopped-history measurability `hM1`, `hM3`). -/
theorem isChartCouplingCharFunConst_q (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      IsGood47 W VL VR ζ p) {s : ℝ≥0} (hs : 0 < s)
    (hM1 : ∀ (r : ℝ≥0) (t' t : ℚ), (0 : ℝ) ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 0 0),
      MeasurableSet[qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k
        (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) r] A →
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
          A ∩ {p | (t' : ℝ) ∈ qgPre W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p ∧
            (r : ℝ) < capClock (qgCurve W s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p) t'})
    (hM3 : ∀ t : ℚ, 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
          qAv W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) φ (t : ℝ).toNNReal) :
    Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
      (qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k
        (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
      (qW W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
      (qVL (qxL κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
      (qVR (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
      (fun p => (qT W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p : ℝ≥0∞))
      (fun p => fChart W VL VR ζ s p) (-(π / 2 * chiC κ)) (-chiC κ) (fun p => -h p.1) := by
  have hEg : ∀ p ∈ glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
      W VL VR ζ, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  have hkw := isKilledWord_q_of_ordered (isOrderedForceWord_qx κ ρL ρR xL xR) hEg hs
  intro r u hu φ
  filter_upwards [ae_condExp_qRaw_eq_qF hκ hκ4 hF h44 hC hcf hlaw k hk hae hs hM1 hM3 r φ] with p hp hr hsupp
  have hav : Sec7.Lemma71D.IsChartAvoid (fun t => qW W VL VR ζ s (glueGood47 (glueMeasure P k
      (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) t p)
      (qT W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
        W VL VR ζ) p : ℝ≥0∞) (fChart W VL VR ζ s p) φ r := ⟨hr, hsupp⟩
  have e : (fun ω' : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (((-h ω'.1) φ : ℝ) : ℂ))) =
      fun ω' => Complex.exp (Complex.I * ((-(h ω'.1 φ) : ℝ) : ℂ)) := rfl
  rw [e, hp hav, qF]
  have hint := Sec7.Lemma71D.integral_couplingMean_eq_chartMean (κ := 16 / κ) (ρL := iwL κ ρL ρR xL xR)
    (ρR := iwR κ ρL ρR xL xR) (a := -(π / 2 * chiC κ)) (k := -chiC κ) (isConformal_fChart p) (hkw.contW p) hav
    (fun i => hkw.ordL p r i hr) (fun j => hkw.ordR p r j hr) (hu p)
  congr 3
  exact congrArg Complex.ofReal hint.symm

/-- **The martingale clause of the counterflow's killed image word** (item D3; step B4 of the Lemma 4.7 direction):
for every `z ∈ ℍ`, the explicit coupling process of the image word (parameter `16/κ`, weights `iwL`, `iwR`) is a
local martingale before `min(swallowTime z, qT)` in the filtration `qFilt` of the image word. -/
theorem isLocalMartingaleBefore_q (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      IsGood47 W VL VR ζ p) {s : ℝ≥0} (hs : 0 < s)
    (hM1 : ∀ (r : ℝ≥0) (t' t : ℚ), (0 : ℝ) ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 0 0),
      MeasurableSet[qRaw (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k
        (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) r] A →
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
          A ∩ {p | (t' : ℝ) ∈ qgPre W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p ∧
            (r : ℝ) < capClock (qgCurve W s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p) t'})
    (hM3 : ∀ t : ℚ, 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
          qAv W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) φ (t : ℝ).toNNReal) :
    ∀ z ∈ H, IsLocalMartingaleBefore (qFilt (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s
        (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
      (fun p => min (QuantumZipper.swallowTime (wpath (qW W VL VR ζ s (glueGood47 (glueMeasure P k
          (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ)) p) z : WithTop ℝ≥0)
        (qT W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p))
      (coupProc (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
        (qW W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
        (qVL (qxL κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
        (qVR (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ)) z) := by
  intro z hz
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood47 μ W VL VR ζ with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood47
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  have hX := hC.2.2.2.1
  have hxo := isOrderedForceWord_qx κ ρL ρR xL xR
  obtain ⟨hnull, hK, hWa, hVLa, hVRa, hσ, hσm, hσT, hσlim, hζq⟩ :=
    filtClauses47 (μ := μ) hX hxo.2.1 hxo.1 hxo.2.2.2 hxo.2.2.1 hs hae
  set 𝓖 := qFilt μ (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s E with h𝓖
  have : 𝓖.IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  set ζ' : Ω × HistorySpace 0 0 → ℝ≥0∞ := fun p => (qT W VL VR ζ s E p : ℝ≥0∞) with hζ'
  set hF' : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => -h p.1 with hFdef
  have hFm : Measurable hF' := LQGMetric.measurable_distOn_iff.2 fun φ =>
    (((LQGMetric.measurable_distOn_apply φ).comp hC.2.1).comp measurable_fst).neg
  have hcc : ∀ p : Ω × HistorySpace 0 0, (fChart W VL VR ζ s p).IsConformal := fun p => isConformal_fChart p
  have hlc : ∀ p : Ω × HistorySpace 0 0,
      ContinuousOn (fChart W VL VR ζ s p).2.2 (fChart W VL VR ζ s p).dom := fun p => continuousOn_lift_fChart p
  have hcf0 := isChartCouplingCharFunConst_q hκ hκ4 hF h44 hC hcf hlaw k hk hae hs hM1 hM3
  have hcfU : Coupling.MartMeans2.IsChartCouplingCharFun (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR) μ 𝓖
      (qW W VL VR ζ s E) (qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E) (qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E) ζ'
      (fun p => fChart W VL VR ζ s p) (-(π / 2 * chiC κ)) (-chiC κ) hF' :=
    Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation hFm hcc hlc (fun p => hK.contW p)
      (fun i p => (hK.pathL p i).1) (fun j p => (hK.pathR p j).1)
      (fun p t ht => ⟨fun i => hK.ordL p t i ht, fun j => hK.ordR p t j ht⟩) hcf0
  set h' : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens :=
    fun p => Sec7.Lemma71K.chartField (fChart W VL VR ζ s p) (-(π / 2 * chiC κ)) (-chiC κ) (hF' p) with hh'
  have ht : ∀ p, IsChartTransport (fChart W VL VR ζ s p) 1 (-(π / 2 * chiC κ)) (-chiC κ) (hF' p) (h' p) :=
    fun p => Sec7.Lemma71K.isChartTransport_chartField (hcc p) (hlc p) _ _ (hF' p)
  have hY : Measurable[𝓖 0] (flowStop W VL VR ζ s) := measurable_flowStop_qFilt hX 0
  have hdom : ∀ z, MeasurableSet[𝓖 0] {p : Ω × HistorySpace 0 0 | z ∈ (fChart W VL VR ζ s p).dom} := fun z =>
    measurableSet_mem_dom_fChart_of hY z
  have hfwd : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 0 0 | z ∈ (fChart W VL VR ζ s p).dom}.indicator fun p => (fChart W VL VR ζ s p).1 z) :=
    fun z => measurable_indicator_fwd_fChart_of hY z
  have hliftm : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 0 0 | z ∈ (fChart W VL VR ζ s p).dom}.indicator
        fun p => (fChart W VL VR ζ s p).2.2 z) := fun z => measurable_indicator_lift_fChart_of hY z
  have hcf' : Coupling.MartMeans.IsCouplingCharFun (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR) μ 𝓖
      (qW W VL VR ζ s E) (qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E) (qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E) ζ' h' :=
    Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hcc hdom hfwd hliftm hlc hFm
      (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p⟩) hcfU ht
  have hh'm : Measurable h' := by
    have hm := Chart.measurable_chartTransport_random' hcc (fun z => 𝓖.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hlc hFm 1
      (-(π / 2 * chiC κ)) (-chiC κ)
    have e : h' = fun p => Chart.chartTransport (hcc p) 1 (-(π / 2 * chiC κ)) (-chiC κ) (hF' p) := by
      funext p
      simp only [hh', Sec7.Lemma71K.chartField, hcc p, ↓reduceDIte]
    rw [e]
    exact hm
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun p => h' p φ) μ := fun φ =>
    integrable_apply_of_isCouplingCharFun_of_bounded hcf'
      (Eventually.of_forall fun p => ⟨(isKilledCurve_qgCurve hEg p).zero_lt_kcLife, hK.contW p, hK.w_zero p⟩)
      φ ((LQGMetric.measurable_distOn_apply φ).comp hh'm)
  have hζm : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {p | ζ' p ≤ t} := by
    intro t
    have h1 := (hζq t).compl
    convert h1 using 1
    ext p
    simp only [hζ', mem_ofPred_eq, mem_compl_iff, not_lt]
    rfl
  have hT : Coupling.IsAnnouncingSeq 𝓖 μ ζ' (qAnn W VL VR ζ s E) :=
    ⟨hσ, hσm, fun n => Eventually.of_forall fun p => hσT n p, hσlim⟩
  obtain ⟨G, hG, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull
    (MartChar.adaptedBefore_of_stronglyAdapted hζm hWa)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVLa i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVRa j))
    (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p, ⟨fun i => (hK.pathL p i).1, fun j => (hK.pathR p j).1⟩,
      fun t ht => ⟨fun i => hK.ordL p t i ht, fun j => hK.ordR p t j ht⟩⟩)
    hT hint hcf' (fun p t => meanExt (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR) (qW W VL VR ζ s E t p)
      (fun i => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E i t p) (fun j => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E j t p))
    (fun p t => isBoundedHarmonicExtension_meanExt (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR) _ _ _) hz
  exact Restart.ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG hGae
    (Restart.ConverseBefore.measurable_coupProc_zero hK.w_zero
      (fun i => measurable_qVL (qxL κ ρL ρR xL xR) hX hE hEg i 0)
      (fun j => measurable_qVR (qxR κ ρL ρR xL xR) hX hE hEg j 0) hz) hloc

end Main

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
