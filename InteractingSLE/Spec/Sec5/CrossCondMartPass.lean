/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondMartFwd

/-!
# The chart clause at fixed image times (general `κ`) by the optional passage along upper dyadic forward times

Packet PROVE-GLUECOND7 (Astra's E.4 and E.6 at general `κ`; the general-`κ` form of PROVE-WW-B19's `ImgChartConst`).
The chart clause `ImgChartConst49Statement` (the conditional law of the field given the raw image filtration at a
fixed image time `r`) is derived from

* step R1 at the forward times (`ae_condExp_cfGlue_eq_cfF`, from the named mean identification
  `MeanIdent49Statement`);
* the measurability of the image word in the two stopped histories (`ImgMarks49Statement`: the image word before a
  rational forward time `t` is a function of the flow history stopped at `t` and the counterflow history stopped at
  `s`, up to null sets; proved in `CrossCondMartMarks`);
* PROVE-WW-B19's abstract optional passage `ChartConst.setIntegral_eq_of_dyadic` along the strict upper dyadic forward
  times `dyF n θ_r ↓ θ_r` of the forward time `θ_r = σ⁻¹(r)` of the image time, with the right limit
  `tendsto_cfF_dyF`;
* the measurability of the candidate in `imgRaw r` (`measurable_cfChartAvoid_raw`) and
  `Lemma71D.integral_couplingMean_eq_chartMean`.

## Main results

* `ImgMarks49Statement` (proved in `CrossCondMartMarks`); `dyqR` (rational dyadic times);
* `dyIdx_cfTheta_and_mem_cfAv_iff`: the dyadic pieces read through the capacity clock;
* **`ae_condExp_imgRaw_eq_cfF`**: `E[e^{i(h,φ)} | imgRaw r] = cfF(r)` on the validity event at the image time `r`;
* **`imgChartConst49Statement_of_ident_marks`**: `MeanIdent49Statement cL cR → ImgMarks49Statement →
  ImgChartConst49Statement cL cR` (any junction weights `cL`, `cR`);
* **`imageWord49FiltWStatement_of_ident_marks`**, `imageWord49FiltStatement_of_ident_marks`: the martingale clause
  from the same two inputs (for PROVE-GLUECOND5's weights, the case `cL5`, `cR5`).

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyIdx dyF dyIdx_eq_iff setIntegral_eq_of_dyadic ae_condExp_eq_of_forall_setIntegral)

namespace Word49

/-- **The image word before a forward time is known from the two stopped histories** (proved:
`CrossCondMartMarks.imgMarks49Statement`; forward times are rational). In the setting of
`Prop411Q.CfGlueAE` (glued measure `μ`, good set `E = glueGood μ s ζ W`), for each counterflow time `s > 0`:
(1) for every image time `r`, forward times `t' ≤ t`, `0 < t`, and every `A ∈ imgRaw r`, the event
`A ∩ {t' before contact, r < σ(t')}` is, up to a `μ`-null set, in the marks `cfGlueMarks t s` (flow history stopped at
`t`, counterflow history stopped at `s`); (2) for every forward time `t > 0` and test function `φ`, the forward
validity event `cfAv φ t` is, up to a null set, in the same marks (Astra's E.2 and E.6: "`R` and a mapped stopped
prefix recover its original geometric prefix … The capacity clock is adapted"). -/
def ImgMarks49Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfField κ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ s : ℝ≥0, 0 < s →
          (∀ (r : ℝ≥0) (t' t : ℚ), (0 : ℝ) ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 0 0),
            MeasurableSet[imgRaw xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) s ζ W) r] A →
            ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧
              B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
                A ∩ {p | (t' : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                    ((measurable_cfField κ).comp hC.2.1)) s ζ W) p ∧
                  (r : ℝ) < capClock (gCurve s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                    ((measurable_cfField κ).comp hC.2.1)) s ζ W) p) t'}) ∧
          ∀ t : ℚ, 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
            ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧
              B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
                cfAv s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                  ((measurable_cfField κ).comp hC.2.1)) s ζ W) φ (t : ℝ).toNNReal

/-! ### The dyadic pieces -/

section Pieces

variable {Ω : Type*} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}

theorem dyq_pos' (n k : ℕ) : 0 < dyq n k := by
  unfold dyq
  positivity

theorem div_le_dyq (n k : ℕ) : (k : ℝ≥0) / 2 ^ n ≤ dyq n k := by
  unfold dyq
  gcongr
  exact le_add_of_nonneg_right zero_le_one

/-- The rational dyadic point `(k + 1)/2ⁿ`. -/
def dyqR (n k : ℕ) : ℚ := ((k : ℚ) + 1) / 2 ^ n

theorem dyqR_pos (n k : ℕ) : 0 < dyqR n k := by
  unfold dyqR
  positivity

theorem dyqR_coe (n k : ℕ) : ((dyqR n k : ℚ) : ℝ) = ((dyq n k : ℝ≥0) : ℝ) := by
  rw [WangWu.ChartConst.dyq_coe, dyqR]
  push_cast
  ring

theorem dyqR_toNNReal (n k : ℕ) : ((dyqR n k : ℚ) : ℝ).toNNReal = dyq n k := by
  rw [dyqR_coe, Real.toNNReal_coe]

theorem divR_coe (n k : ℕ) : (((k : ℚ) / 2 ^ n : ℚ) : ℝ) = (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := by
  push_cast
  ring

theorem divR_le_dyqR (n k : ℕ) : (k : ℚ) / 2 ^ n ≤ dyqR n k := by
  unfold dyqR
  gcongr
  linarith

/-- The pieces of the dyadic level sets, read through the capacity clock (deterministic, on a good sample alive at
the image time `r`). -/
theorem dyIdx_cfTheta_and_mem_cfAv_iff (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0}
    {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) < imgT s ζ W E p) (n k : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    (dyIdx n (cfTheta s ζ W E r p) = k ∧ p ∈ cfAv s ζ W E φ (dyq n k)) ↔
      (((dyq n k : ℝ≥0) : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) (dyq n k)) ∧
        ¬ ((((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ gPre s ζ W E p ∧
          (r : ℝ) < capClock (gCurve s ζ W E p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)) ∧
        p ∈ cfAv s ζ W E φ (dyq n k) := by
  have hγ := isKilledArc_gCurve hEg p
  obtain ⟨hθP, hθc⟩ := cfTheta_spec hEg hr
  set θ := cfTheta s ζ W E r p with hθdef
  -- `θ < u ↔ r < σ(u)` for `u` before contact
  have key : ∀ u : ℝ, u ∈ gPre s ζ W E p → ((θ : ℝ) < u ↔ (r : ℝ) < capClock (gCurve s ζ W E p) u) := by
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
    have hP : ((dyq n k : ℝ≥0) : ℝ) ∈ gPre s ζ W E p := hAv.2.1
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

/-- **The clause at a fixed image time** (Astra's E.4 with the passage of the characteristic functions along strict
upper dyadic forward times): almost surely on the validity event at the image time `r`,
`E[e^{i(h,φ)} | imgRaw r] = cfF(r)`. -/
theorem ae_condExp_imgRaw_eq_cfF {cL cR : ℝ → ℝ → ℝ} (hMI : MeanIdent49Statement.{u} cL cR) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s)
    (hM1 : ∀ (r : ℝ≥0) (t' t : ℚ), (0 : ℝ) ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 0 0),
      MeasurableSet[imgRaw xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W) r] A →
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
          A ∩ {p | (t' : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) s ζ W) p ∧
            (r : ℝ) < capClock (gCurve s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) s ζ W) p) t'})
    (hM3 : ∀ t : ℚ, 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)]
          cfAv s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) φ (t : ℝ).toNNReal)
    (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) t p)
        (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) p : ℝ≥0∞) (cfChart s p.2) φ r →
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          imgRaw xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) r] p =
        cfF cL cR κ ρL ρR xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) φ r p := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hX := hC.2.2.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
      hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  have hEae : ∀ᵐ p ∂μ, p ∈ E := ae_mem_glueGood hae
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  have hFg := isZeroBoundaryGFF_cenT_glue (k := k) hC hu₀
  have hXm : Measurable fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (((LQGMetric.measurable_distOn_apply φ).comp hC.2.1).comp measurable_fst)))
  have hXb : ∀ p : Ω × HistorySpace 0 0, ‖Complex.exp (Complex.I * (h p.1 φ : ℂ))‖ ≤ 1 := fun p => by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hXi : Integrable (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) μ :=
    Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  obtain ⟨hErm, hmeanm, hvarm⟩ := measurable_cfChartAvoid_raw (xL := xL) (xR := xR) cL cR κ ρL ρR hF hWad hE hEg r φ
  set Er := {p : Ω × HistorySpace 0 0 | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
    (imgT s ζ W E p : ℝ≥0∞) (cfChart s p.2) φ r} with hErdef
  -- the candidate is `imgRaw r`-measurable on `Er`
  have hGm : Measurable[imgRaw xL xR s ζ W E r] (Er.indicator (cfF cL cR κ ρL ρR xL xR s ζ W E φ r)) := by
    have e : Er.indicator (cfF cL cR κ ρL ρR xL xR s ζ W E φ r) = Er.indicator (fun p => Complex.exp (Complex.I *
        ((Er.indicator (fun p => Sec7.Lemma71D.chartMean κ (jwL cL κ ρL) (jwR cR κ ρR) (fun t => imgW s ζ W E t p)
          (fun i t => imgVL xL s ζ W E i t p) (fun j t => imgVR xR s ζ W E j t p) (cfChart s p.2)
          (2 * Real.pi * chiC κ) (chiC κ) φ r) p : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * Er.indicator (fun p => Sec7.Lemma71D.chartVar (fun t => imgW s ζ W E t p)
          (cfChart s p.2) φ r) p : ℝ) : ℂ))) := by
      refine Set.indicator_congr fun p hp => ?_
      simp only [cfF, indicator_of_mem hp]
    rw [e]
    refine Measurable.indicator ?_ hErm
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hmeanm).const_mul _ |>.sub
      (Complex.measurable_ofReal.comp (hvarm.const_mul _)))
  have hGi : Integrable (Er.indicator (cfF cL cR κ ρL ρR xL xR s ζ W E φ r)) μ := by
    refine Integrable.of_bound ((hGm.mono ((imgRaw xL xR s ζ W E).le r) le_rfl).aestronglyMeasurable) 1
      (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ Er
    · rw [indicator_of_mem hp]
      exact norm_cfF_le_one hF hEg φ hp.1
    · rw [indicator_of_notMem hp, norm_zero]
      exact zero_le_one
  refine ae_condExp_eq_of_forall_setIntegral ((imgRaw xL xR s ζ W E).le r) hErm hXi hGm.stronglyMeasurable hGi ?_
  intro A hA
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hUm : ∀ t : ℝ≥0, Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 =>
      hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2 := fun t =>
    measurable_union_hitting (((measurable_hullAt t).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ s).comp measurable_snd)
  refine setIntegral_eq_of_dyadic hXi (Eventually.of_forall hXb)
    (fun n j => germSigma (fun p : Ω × HistorySpace 0 0 =>
      hullAt (dyq n j) (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)
        (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ (dyq n j) s)
    (fun n j => sup_le (germSigma_le (hUm _) hFg.measurable) (cfGlueMarks_le _ _ hX))
    (Av := cfAv s ζ W E φ)
    (F := fun q p => cfF cL cR κ ρL ρR xL xR s ζ W E φ (capClock (gCurve s ζ W E p) q).toNNReal p)
    (fun q p hp => norm_cfF_le_one hF hEg φ hp.2.2.1) ?_ (measurable_cfTheta hWad hE hEg r)
    (((imgRaw xL xR s ζ W E).le r _ hA).inter ((imgRaw xL xR s ζ W E).le r _ hErm)) ?_ ?_
  · -- the clause at the dyadic forward times
    intro n j
    exact ae_condExp_cfGlue_eq_cfF hMI hκ hκ4 hF h44 hC hcf hlaw k hk hu₀ hs (dyq_pos' n j) φ
  · -- the pieces are in the marks
    intro n j
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
      hullAt (dyq n j) (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)
        (fun p => cenT κ u₀ (cfField κ (h p.1)))) _ ((hB1m.inter hB2m.compl).inter hB3m), ?_⟩
    refine ((hB1e.inter hB2e.compl).inter hB3e).trans ?_
    refine Eventually.of_forall fun p => ?_
    simp only [mem_inter_iff, mem_compl_iff, mem_univ, true_and, eq_iff_iff]
    constructor
    · rintro ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
      have hh := (dyIdx_cfTheta_and_mem_cfAv_iff hEg hEr.1 n j φ).2 ⟨h1, h2, h3⟩
      exact ⟨⟨⟨hAp, hEr⟩, hh.1⟩, hh.2⟩
    · rintro ⟨⟨⟨hAp, hEr⟩, hd⟩, hav⟩
      obtain ⟨h1, h2, h3⟩ := (dyIdx_cfTheta_and_mem_cfAv_iff hEg hEr.1 n j φ).1 ⟨hd, hav⟩
      exact ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
  · -- the right limit
    filter_upwards [hEae] with p hpE hpD
    exact tendsto_cfF_dyF hF hEg hpE hpD.2

end Main

/-- **`ImgChartConst49Statement` from the mean identification and the stopped-history measurability of the image
word** (steps R1–R6 at general `κ`). -/
theorem imgChartConst49Statement_of_ident_marks {cL cR : ℝ → ℝ → ℝ} (hMI : MeanIdent49Statement.{u} cL cR)
    (hM : ImgMarks49Statement.{u}) : ImgChartConst49Statement.{u} cL cR := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  obtain ⟨hM1, hM3⟩ := hM κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  have hEg : ∀ p ∈ glueGood (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) s ζ W,
      IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hkw := isKilledWord_img (ζ := ζ) (W := W) (xL := xL) (xR := xR) hF hEg
  intro r u hu φ
  filter_upwards [ae_condExp_imgRaw_eq_cfF hMI hκ hκ4 hF h44 hC hcf hlaw k hk hs hM1 hM3 r φ] with p hp hr hsupp
  have hav : Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W (glueGood (glueMeasure P k
      (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) s ζ W) t p)
      (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
        s ζ W) p : ℝ≥0∞) (cfChart s p.2) φ r := ⟨hr, hsupp⟩
  rw [hp hav, cfF]
  have hint := Sec7.Lemma71D.integral_couplingMean_eq_chartMean (κ := κ) (ρL := jwL cL κ ρL) (ρR := jwR cR κ ρR)
    (a := 2 * Real.pi * chiC κ) (k := chiC κ) (isConformal_cfChart p.2) (hkw.contW p) hav
    (fun i => hkw.ordL p r i hr) (fun j => hkw.ordR p r j hr) (hu p)
  congr 3
  exact congrArg Complex.ofReal hint.symm

/-- **The martingale clause of PROVE-GLUECOND5 (`ImageWord49FiltStatement`) from the mean identification and the
stopped-history measurability of the image word.** -/
theorem imageWord49FiltWStatement_of_ident_marks {cL cR : ℝ → ℝ → ℝ} (hMI : MeanIdent49Statement.{u} cL cR)
    (hM : ImgMarks49Statement.{u}) : ImageWord49FiltWStatement.{u} cL cR :=
  imageWord49FiltWStatement_of_chartConst (imgChartConst49Statement_of_ident_marks hMI hM)

/-- PROVE-GLUECOND5's martingale clause (junction weights `cL5`, `cR5`) from the same two inputs with these weights. -/
theorem imageWord49FiltStatement_of_ident_marks (hMI : MeanIdent49Statement.{u} cL5 cR5)
    (hM : ImgMarks49Statement.{u}) : ImageWord49FiltStatement.{u} :=
  imageWord49FiltWStatement_of_ident_marks hMI hM

/-- **The corrected martingale clause (`cL6`, `cR6`) from the mean identification and the stopped-history
measurability.** -/
theorem imageWord49FiltCStatement_of_ident_marks (hMI : MeanIdent49Statement.{u} cL6 cR6)
    (hM : ImgMarks49Statement.{u}) : ImageWord49FiltCStatement.{u} :=
  imageWord49FiltWStatement_of_ident_marks hMI hM

end Word49

end InteractingSLE.Sec5.CrossCond
