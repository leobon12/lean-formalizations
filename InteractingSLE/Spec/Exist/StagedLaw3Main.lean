/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Adm
import InteractingSLE.Spec.Coupling.Lemma311
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71
import InteractingSLE.Spec.Sec7.LocalExtILoc
import InteractingSLE.Spec.Theorem14

/-!
# `StopCondLawStatement` holds

Packet PROVE-STAGEDLAW3. The conditional-law conjunct of the single-stage law (`StopCondLawStatement`,
PROVE-STAGEDLAW2):

* an admissible flow-line seed: `ae_condExp_recField_of_admissible` (the announced kernel at the stop, read in the
  record chart, and the tower property);
* an inadmissible seed: the lifetime vanishes almost surely, the record is almost surely the zero record
  (`recOf_of_zero`), the record σ-algebra is trivial, and the field read in the time-`0` chart has the GFF law of the
  initial word (`integral_cexp_recField_zeroRec`, through the one-dimensional laws
  `Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess`).

Main results: **`stopCondLawStatement`**, **`stopLawStatement`**, **`stagedCondLawStatement`**, and the companion's
construction statement from Theorems 1.2–1.3 alone, **`stagedHistoryConstructionStatement_of_param`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged Restart LQGMetric

/-! ### The zero record -/

/-- The record of a piece killed at time `0`. -/
def zeroRec : RecData := (fun _ => 0, 0, true)

theorem recOf_of_zero {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (h0 : e.2 = 0) :
    recOf t e = zeroRec := by
  have hmin : min t e.2 = 0 := by rw [h0]; exact min_eq_right bot_le
  refine Prod.ext (funext fun q => ?_) (Prod.ext ?_ ?_)
  · change e.1 (min (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal = 0
    rw [hmin, min_eq_right (zero_le (a := (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞))), ENNReal.toNNReal_zero]
    exact he.2.1
  · change min t e.2 = 0
    exact hmin
  · change decide (e.2 ≤ t) = true
    rw [h0]
    exact decide_eq_true bot_le

theorem rtime_zeroRec : rtime zeroRec = 0 := by
  simp [rtime, zeroRec]

theorem stopHull_zeroRec : stopHull zeroRec = ∅ := by
  unfold stopHull
  rw [rtime_zeroRec]
  exact RS.fwdHull_zero_eq_empty (continuous_rdrv _)

/-- A constant mark on `[0, 0]`. -/
theorem isMark_const_zero {w : ℝ → ℝ} (hw0 : w 0 = 0) {x : ℝ} (hx : 0 ≤ x) : IsMark w 0 x fun _ => x := by
  refine ⟨fun _ _ => hx, fun s hs => ?_, intervalIntegrable_const, ?_⟩
  · have : s = 0 := le_antisymm hs.2 hs.1
    rw [this, hw0, intervalIntegral.integral_same]
    ring
  · refine measure_mono_null (fun s (hs : s ∈ Icc (0 : ℝ) 0 ∧ x = 0) => ?_) (measure_singleton (0 : ℝ))
    exact le_antisymm hs.1.2 hs.1.1

theorem markPos_time_zero {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : 0 ≤ x) :
    markPos w 0 x = x :=
  markPos_eq hw hw0 le_rfl (isMark_const_zero hw0 hx)

theorem markPosL_time_zero {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : x ≤ 0) :
    markPosL w 0 x = x := by
  unfold markPosL
  rw [markPos_time_zero (w := fun s => -w s) hw.neg (by simp [hw0]) (neg_nonneg.2 hx), neg_neg]

/-! ### The field in the time-`0` chart -/

/-- **The characteristic value of the flow-line field at a test function** (`h' − 𝔥₀` a zero-boundary GFF):
`E[exp(i h'(ψ))] = exp(i ∫ 𝔥₀ ψ − ½ G_ℍ(ψ, ψ))`. -/
theorem integral_cexp_of_isZBGFFProcess {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {h' : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (hh : IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h' ω φ - ∫ z, u₀ z * φ z) Q)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (h' ω ψ : ℂ)) ∂Q =
      Complex.exp (Complex.I * ((∫ z, u₀ z * ψ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ : ℝ) : ℂ)) := by
  have hlaw := Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess hh ψ
  have hm : Measurable fun ω => h' ω ψ := by
    have := hh.measurable ψ
    simpa using this.add_const (∫ z, u₀ z * ψ z)
  have hG : 0 ≤ zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ := by
    rw [← hh.covariance_eq ψ ψ, covariance_self ((hh.measurable ψ).aemeasurable)]
    exact variance_nonneg _ _
  have hf : AEStronglyMeasurable (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) (Q.map fun ω => h' ω ψ) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  have h1 : (∫ ω, Complex.exp (Complex.I * (h' ω ψ : ℂ)) ∂Q) =
      ∫ x, Complex.exp (Complex.I * (x : ℂ)) ∂(Q.map fun ω => h' ω ψ) :=
    (integral_map hm.aemeasurable hf).symm
  rw [h1, hlaw]
  have h2 := charFun_gaussianReal (μ := ∫ z, u₀ z * ψ z)
    (v := (zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ).toNNReal) 1
  rw [charFun_apply_real] at h2
  have e : ∀ x : ℝ, Complex.exp (Complex.I * (x : ℂ)) = Complex.exp (((1 : ℝ) : ℂ) * x * Complex.I) :=
    fun x => by congr 1; push_cast; ring
  simp only [e]
  rw [h2, Real.coe_toNNReal _ hG]
  congr 1
  push_cast
  ring

/-! ### An inadmissible seed -/

/-- **The conditional law at the stop for an inadmissible seed** (the lifetime vanishes almost surely). -/
theorem ae_condExp_recField_of_inadmissible {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (t : ℝ≥0∞)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (g : Ω → DistOn upperHalfPlaneOpens) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hE : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω))
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ Q g (fun s ω => (E ω).1 s) (fun ω => (E ω).2))
    (hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q,
      Q[fun ω' => Complex.exp (Complex.I * (recField κ (recOf t (E ω')) (g ω') φ : ℂ)) |
          MeasurableSpace.comap (fun ω' => recOf t (E ω')) inferInstance] ω =
        gaussCF (stopWord κ (c, θ, recOf t (E ω))) φ := by
  classical
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  set R : Ω → RecData := fun ω => recOf t (E ω) with hRdef
  have hRm : Measurable R := measurable_recOf hE hreg t
  have hR0 : ∀ᵐ ω ∂Q, R ω = zeroRec := by
    filter_upwards [LocalExt.ae_zeta_eq_zero_of_thresholdCondition hC.1 hκ hseed] with ω hω
    exact recOf_of_zero (hreg ω) hω
  -- the data of the flow-line word
  set nL := flowLineNL c.fn c.jumps 0
  set nR := flowLineNR c.fn c.jumps 0
  set xLp := (padFL 0 0 c.fn c.jumps).1.1
  set xRp := (padFL 0 0 c.fn c.jumps).1.2
  set ρLp := (padFL κ θ c.fn c.jumps).2.1
  set ρRp := (padFL κ θ c.fn c.jumps).2.2
  obtain ⟨u₀, hu₀⟩ := WholeField.exists_bhe κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
    (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  have hord := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hxL0 : ∀ i, xLp i ≤ 0 := fun i => by
    by_cases hi : i < nL
    · rw [show xLp i = flowLineXL c.fn c.jumps 0 ⟨i, hi⟩ from padFL_fst_fst_fin c.fn c.jumps ⟨i, hi⟩]
      exact hord.2.1 _
    · have hi' : ¬ i < flowLineNL c.fn c.jumps 0 := hi
      simp only [xLp, padFL, hi', ↓reduceDIte, le_refl]
  have hxR0 : ∀ j, 0 ≤ xRp j := fun j => by
    by_cases hj : j < nR
    · rw [show xRp j = flowLineXR c.fn c.jumps 0 ⟨j, hj⟩ from padFL_fst_snd_fin c.fn c.jumps ⟨j, hj⟩]
      exact hord.2.2.2 _
    · have hj' : ¬ j < flowLineNR c.fn c.jumps 0 := hj
      simp only [xRp, padFL, hj', ↓reduceDIte, le_refl]
  have hposL : (fun i => markPosL (rdrv zeroRec) (rtime zeroRec) (xLp i)) = xLp := by
    funext i
    rw [rtime_zeroRec]
    exact markPosL_time_zero (continuous_rdrv _) (rdrv_zero _) (hxL0 i)
  have hposR : (fun j => markPos (rdrv zeroRec) (rtime zeroRec) (xRp j)) = xRp := by
    funext j
    rw [rtime_zeroRec]
    exact markPos_time_zero (continuous_rdrv _) (rdrv_zero _) (hxR0 j)
  have horder : IsMarkOrder nL nR xLp xRp := by
    refine ⟨fun i j hij hj => ?_, fun i _ => hxL0 i, fun i j hij hj => ?_, fun i _ => hxR0 i⟩
    · have h1 : xLp i = flowLineXL c.fn c.jumps 0 ⟨i, by omega⟩ := padFL_fst_fst_fin c.fn c.jumps ⟨i, by omega⟩
      have h2 : xLp j = flowLineXL c.fn c.jumps 0 ⟨j, hj⟩ := padFL_fst_fst_fin c.fn c.jumps ⟨j, hj⟩
      rw [h1, h2]
      exact hord.1 (show (⟨i, by omega⟩ : Fin nL) ≤ ⟨j, hj⟩ from hij)
    · have h1 : xRp i = flowLineXR c.fn c.jumps 0 ⟨i, by omega⟩ := padFL_fst_snd_fin c.fn c.jumps ⟨i, by omega⟩
      have h2 : xRp j = flowLineXR c.fn c.jumps 0 ⟨j, hj⟩ := padFL_fst_snd_fin c.fn c.jumps ⟨j, hj⟩
      rw [h1, h2]
      exact hord.2.2.1 (show (⟨i, by omega⟩ : Fin nR) ≤ ⟨j, hj⟩ from hij)
  have hmeanEq : EqOn u₀ (fun z => (forceWord κ nL nR xLp xRp ρLp ρRp (θ * chiC κ)).mean z + θ * chiC κ) H := by
    refine eqOn_mean_forceWord κ ρLp ρRp (θ * chiC κ) horder ?_
    have e1 : (fun i : Fin nL => ρLp i) = flowLineRhoL κ c.fn c.jumps 0 θ :=
      funext (padFL_snd_fst_fin κ θ c.fn c.jumps)
    have e2 : (fun j : Fin nR => ρRp j) = flowLineRhoR κ c.fn c.jumps 0 θ :=
      funext (padFL_snd_snd_fin κ θ c.fn c.jumps)
    have e3 : (fun i : Fin nL => xLp i) = flowLineXL c.fn c.jumps 0 := funext (padFL_fst_fst_fin c.fn c.jumps)
    have e4 : (fun j : Fin nR => xRp j) = flowLineXR c.fn c.jumps 0 := funext (padFL_fst_snd_fin c.fn c.jumps)
    rw [e1, e2, e3, e4]
    exact hu₀
  -- the expectation
  set ψ₀ := Chart.pushTest (isConformal_recChart zeroRec) φ with hψ₀
  set c₀ := gaussCF (stopWord κ (c, θ, zeroRec)) φ with hc₀
  have hstop : ∀ z, ψ₀ z ≠ 0 →
      stopMean κ nL nR xLp xRp ρLp ρRp (θ * chiC κ) zeroRec z = u₀ z := by
    intro z hz
    have hzD : z ∈ (recChart zeroRec).dom := by
      by_contra hn
      exact hz (Chart.pushTest_apply_of_notMem _ φ hn)
    rw [← SetLike.mem_coe, coe_dom_recChart, stopHull_zeroRec, sdiff_empty] at hzD
    unfold stopMean
    rw [hposL, hposR]
    unfold couplingMean
    rw [rtime_zeroRec, fwdMap_zero_time (rdrv_zero _) z, Coupling.MartMeans2.logDerivFwd_zero, Complex.zero_im,
      mul_zero, sub_zero, hmeanEq hzD]
  have hint : (∫ z, stopMean κ nL nR xLp xRp ρLp ρRp (θ * chiC κ) zeroRec z * ψ₀ z) = ∫ z, u₀ z * ψ₀ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : ψ₀ z = 0
    · simp only [hz, mul_zero]
    · simp only [hstop z hz]
  have hvar : zeroGFFTestCov (H \ stopHull zeroRec) ψ₀ ψ₀ = zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ₀ ψ₀ := by
    rw [stopHull_zeroRec, sdiff_empty, coe_upperHalfPlaneOpens]
  have hEX : (∫ ω, Complex.exp (Complex.I * (recField κ zeroRec (g ω) φ : ℂ)) ∂Q) = c₀ := by
    have e : ∀ ω, Complex.exp (Complex.I * (recField κ zeroRec (g ω) φ : ℂ)) =
        Complex.exp (Complex.I * (chartShift κ θ zeroRec φ : ℂ)) * Complex.exp (Complex.I * (h' ω ψ₀ : ℂ)) := by
      intro ω
      rw [recField_apply_eq (htr ω) zeroRec φ, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [e]
    rw [integral_const_mul, integral_cexp_of_isZBGFFProcess (hC.2.2.1 u₀ hu₀) ψ₀, ← hint, ← hvar]
    exact cexp_chartShift_mul_eq_gaussCF κ θ nL nR xLp xRp ρLp ρRp zeroRec φ
  -- the record σ-algebra is trivial
  set X : Ω → ℂ := fun ω => Complex.exp (Complex.I * (recField κ (R ω) (g ω) φ : ℂ)) with hXdef
  have hg : Measurable g := by
    refine LQGMetric.measurable_distOn_iff.2 fun ψ => ?_
    have e : (fun ω => g ω ψ) = fun ω => h' ω ψ - θ * chiC κ * ∫ z, ψ z := by
      funext ω
      have := htr ω ψ ψ (fun z => by rw [Complex.ofReal_zero, add_zero])
      linarith
    rw [e]
    exact ((measurable_distOn_apply ψ).comp hC.2.1).sub_const _
  have hXr : Measurable fun ω => recField κ (R ω) (g ω) φ := by
    have h1 := (measurable_recField κ).comp (hRm.prodMk hg)
    have h2 := (measurable_distOn_apply φ).comp h1
    exact h2
  have hXi : Integrable X Q := by
    have h3 := GFF.integrable_exp_I_mul (P := Q) hXr
    exact h3
  have hXint : ∫ ω, X ω ∂Q = c₀ := by
    rw [← hEX]
    refine integral_congr_ae ?_
    filter_upwards [hR0] with ω hω
    simp only [hXdef, hω]
  have hRle : MeasurableSpace.comap R inferInstance ≤ mΩ := hRm.comap_le
  have hce : (fun _ => c₀) =ᵐ[Q] Q[X|MeasurableSpace.comap R inferInstance] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hRle hXi (fun s _ _ => integrableOn_const ?_)
      (fun s hs _ => ?_) stronglyMeasurable_const.aestronglyMeasurable
    · exact measure_ne_top _ _
    obtain ⟨S0, -, rfl⟩ := hs
    by_cases h0 : zeroRec ∈ S0
    · have hset : (R ⁻¹' S0 : Set Ω) =ᵐ[Q] (univ : Set Ω) := by
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [hR0] with ω hω
        simp only [mem_preimage, hω, h0, mem_univ]
      rw [setIntegral_congr_set hset, setIntegral_congr_set hset]
      simp only [Measure.restrict_univ]
      rw [hXint, integral_const, probReal_univ, one_smul]
    · have hset : (R ⁻¹' S0 : Set Ω) =ᵐ[Q] (∅ : Set Ω) := by
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [hR0] with ω hω
        simp only [mem_preimage, hω, h0, mem_empty_iff_false]
      rw [setIntegral_congr_set hset, setIntegral_congr_set hset]
      simp only [Measure.restrict_empty, integral_zero_measure]
  filter_upwards [hce, hR0] with ω h1 h2
  change Q[X|MeasurableSpace.comap R inferInstance] ω = gaussCF (stopWord κ (c, θ, R ω)) φ
  rw [← h1, h2]

/-! ### The statement and its consequences -/

/-- **`StopCondLawStatement` holds**: conditionally on the record of a finite stop, the field of a flow-line piece read
in the record chart has the Gaussian characteristic functional of the stop word `stopWord κ (c, θ, record)` (jointly
measurable, sorted). -/
theorem stopCondLawStatement : StopCondLawStatement.{u} := by
  intro κ hκ _
  refine ⟨stopWord κ, measurable_stopWord κ, isSorted_stopWord κ, ?_⟩
  intro c θ t Ω _ _ Q _ g E hE hreg hfl φ
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · filter_upwards [ae_condExp_recField_of_inadmissible hκ c θ t Q g E hE hreg hfl hseed φ] with ω h _ using h
  · exact ae_condExp_recField_of_admissible hκ c θ t Q g E hE hreg hfl hseed φ

/-- **The single-stage law `StopLawStatement` holds.** -/
theorem stopLawStatement : StopLawStatement.{u} := stopLawStatement_of_stopCondLaw stopCondLawStatement

/-- **The staged conditional law `StagedCondLawStatement` holds.** -/
theorem stagedCondLawStatement : StagedCondLawStatement.{u} :=
  stagedCondLawStatement_of_stopCondLaw stopCondLawStatement

/-- **Theorem 1.4's companion construction from Theorems 1.2 (parametric) and 1.3 alone.** -/
theorem stagedHistoryConstructionStatement_of_param (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) : Theorem14.StagedHistoryConstructionStatement.{u} :=
  stagedHistoryConstructionStatement_of_stopLaw' h12p h13 stopLawStatement

theorem regularStagedHistoryConstructionStatement_of_param (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) : RegularStagedHistoryConstructionStatement.{u} :=
  regularStagedHistoryConstructionStatement_of_stopLaw' h12p h13 stopLawStatement

/-- **The conclusion of Theorem 1.4's companion `exists_isStagedHistory` from Theorems 1.2 (parametric) and 1.3.** -/
theorem exists_isStagedHistory_of_param (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec,
      IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec) :=
  Theorem14.exists_isStagedHistory_of_inputs (stagedHistoryConstructionStatement_of_param h12p h13) hκ hκ4 b jumps
    hb hh

end StagedLaw

end Exist

end InteractingSLE
