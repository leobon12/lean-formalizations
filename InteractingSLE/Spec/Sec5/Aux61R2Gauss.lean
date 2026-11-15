/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R2Fibre

/-!
# The fibre's field at time `0`: a Gaussian free field with mean `M^c + q`

Packet PROVE-AUX61-R2, piece R2e (the comparison data of the corrected fibre). At time `0` the hull is empty, the
reference word's marks are at their initial positions, and the fibre's mean `meanF κ u₀ q Fq` is `u₀ + q` on `ℍ`
(`u₀` the reference word's initial extension: the canonical mean `M^c` at the restart): the Green potential of the
cutoff's source is the cutoff itself (Green inversion). Integrating the kernel at the stop `0` (where `e > 0`):
`E[e^{i h(φ)}] = exp(i ∫ (u₀ + q) φ − ½ E_ℍ(φ))`, so `h − (u₀ + q)` is a zero-boundary GFF on `ℍ`.

* `RefFibre.u0`, `RefFibre.u0_ext`, `RefFibre.refExt_zero`: the reference word's initial extension, the frame of the
  kernel at time `0`;
* `RefFibre.mean0 = u0 + q`, `continuousOn_mean0`;
* `greenCross_zero_eq`, **`integral_meanF_zero`**: `∫ meanF κ u q Fq w 0 · φ = ∫ (u + q) φ`;
* **`RefFibre.integral_cexp`**: the integrated time-0 kernel;
* **`RefFibre.isZBGFFProcess`**: the centred pairings `h(φ) − ∫ (u0 + q) φ` form a zero-boundary GFF process on `ℍ`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61R2

open QuantumZipper (H fwdHull fwdMap)
open LQGMetric (TestOn DistOn)
open LocalExt (IsGreenTest greenCross cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Aux61Win (meanF IsCutoffOn)
open Sec7.PocketTraversal

universe u

/-! ### The mean at time `0` -/

/-- **The cross Green energy at time `0`** (driver started at `0`): it does not see the driver. -/
theorem greenCross_zero_eq {w : ℝ → ℝ} (hw0 : w 0 = 0) (φ : TestOn upperHalfPlaneOpens) (F : CMCut) :
    greenCross w 0 φ F.src = greenCross (fun _ => 0) 0 φ F.src := by
  have hfix : ∀ (v : ℝ → ℝ), v 0 = 0 → ∀ y : ℂ, y ∈ H → fwdMap v 0 y = y := fun v hv0 y hy => by
    have hy0 : y ≠ ((v 0 : ℝ) : ℂ) := by
      rw [hv0, Complex.ofReal_zero]
      intro h0
      have hyH : (0 : ℝ) < y.im := hy
      rw [h0] at hyH
      simp at hyH
    rw [QuantumZipper.B5.fwdMap_zero_time v hy0, hv0, Complex.ofReal_zero, sub_zero]
  unfold greenCross
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  by_cases hy : φ y = 0
  · simp only [hy, zero_mul, integral_zero]
  have hyH : y ∈ H := φ.tsupport_subset (subset_tsupport _ hy)
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : F.src z = 0
  · simp only [hz, mul_zero]
  have hzH : z ∈ H := (F.mem_of_src_ne_zero hz).1
  simp only
  rw [hfix w hw0 y hyH, hfix w hw0 z hzH, hfix (fun _ => 0) rfl y hyH, hfix (fun _ => 0) rfl z hzH]

/-- **The mean at time `0`**: `∫ meanF κ u q Fq w 0 · φ = ∫ (u + q) φ` (the Green potential of the cutoff's source
is the cutoff, by Green inversion). -/
theorem integral_meanF_zero {κ : ℝ} {u q : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hq : ContinuousOn q H) {Fq : CMCut} {w' : ℝ≥0 → ℝ} (hw' : Continuous w') (hw0 : w' 0 = 0)
    (φ : TestOn upperHalfPlaneOpens) :
    (∫ z, meanF κ u q Fq (Ito.rpath w') ((0 : ℝ≥0) : ℝ) z * φ z) = ∫ z, (u z + q z) * φ z := by
  set w : ℝ → ℝ := Ito.rpath w' with hwdef
  have hw : Continuous w := hw'.comp continuous_real_toNNReal
  have hw00 : w 0 = 0 := by simp [hwdef, Ito.rpath, hw0]
  have hK0 : fwdHull w 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty hw
  have hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w') ((0 : ℝ≥0) : ℝ)) := by
    rw [NNReal.coe_zero, ← hwdef, hK0]; exact disjoint_empty _
  have hcut : IsCutoffOn Fq (fun z => Fq.f z) ∅ univ :=
    ⟨isOpen_empty, fun _ h _ => h.elim, fun _ h _ => h.elim, fun _ h => h.elim⟩
  have hG : IsGreenTest (Ito.rpath w') ((0 : ℝ≥0) : ℝ) Fq.src := by
    refine hcut.isGreenTest_src ?_
    rw [NNReal.coe_zero, ← hwdef, hK0, closure_empty]
  have huc : ContinuousOn u H := fun z hz => ((hu z hz).1.continuousAt).continuousWithinAt
  rw [Aux61Win.integral_meanF_eq hu hq hw' hG φ hφ, NNReal.coe_zero, ← hwdef, greenCross_zero_eq hw00,
    Restart.FlowStopIdentCMI.CMCut.greenCross_zero_src]
  have e₁ : ∫ z, couplingMean κ w 0 u z * φ z = ∫ z, u z * φ z := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : φ z = 0
    · simp only [hz, mul_zero]
    have hzH : z ∈ H := φ.tsupport_subset (subset_tsupport _ hz)
    have hz0 : z ≠ 0 := fun h => by
      have : (0 : ℝ) < z.im := hzH
      rw [h, Complex.zero_im] at this
      exact lt_irrefl _ this
    simp only
    rw [Coupling.MartMeans2.couplingMean_zero κ hw00 u hz0]
  have hFc : ContinuousOn Fq.f H := Fq.smooth.continuous.continuousOn
  have i₁ := LocalExt.integrable_mul_testOn huc φ
  have i₂ := LocalExt.integrable_mul_testOn hq φ
  have i₃ := LocalExt.integrable_mul_testOn hFc φ
  have e₂ : ∫ z, φ z * Fq.f z = ∫ z, Fq.f z * φ z := integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have e₃ : ∫ z, (q z - Fq.f z) * φ z = (∫ z, q z * φ z) - ∫ z, Fq.f z * φ z := by
    rw [← integral_sub i₂ i₃]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only; ring)
  have e₄ : ∫ z, (u z + q z) * φ z = (∫ z, u z * φ z) + ∫ z, q z * φ z := by
    rw [← integral_add i₁ i₂]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only; ring)
  rw [e₁, e₂, e₃, e₄]
  ring

namespace RefFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : RefFibre S)

/-- **The reference word's initial extension** (the canonical reference mean `M^c` at the restart). -/
def u0 : ℂ → ℝ :=
  MartChar.meanExt D.κ (flowLineRhoL D.κ D.bR D.JR 0 0) (flowLineRhoR D.κ D.bR D.JR 0 0) 0
    (flowLineXL D.bR D.JR 0) (flowLineXR D.bR D.JR 0)

theorem u0_ext : IsBoundedHarmonicExtension
    (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR 0 0) (flowLineRhoR D.κ D.bR D.JR 0 0)
      (fun i => flowLineXL D.bR D.JR 0 i - 0) (fun j => flowLineXR D.bR D.JR 0 j - 0))
    (forceJumpSet (fun i => flowLineXL D.bR D.JR 0 i - 0) (fun j => flowLineXR D.bR D.JR 0 j - 0)) D.u0 :=
  MartChar.isBoundedHarmonicExtension_meanExt _ _ _ 0 _ _

/-- At time `0` the reference marks are at their initial positions: `u0` is a reference extension at time `0`. -/
theorem refExt_zero (ω : S) : RefExt D.κ D.bR D.JR D.W 0 ω D.u0 := by
  have hF := Theorem15.isOrderedForceWord_flowLine D.bR D.JR 0
  have hL : (fun i => geomLW D.W (fun _ => flowLineXL D.bR D.JR 0) i 0 ω - D.W 0 ω) =
      fun i => flowLineXL D.bR D.JR 0 i - 0 := funext fun i => by
    rw [geomLW_zero D.continuous D.zero (hF.2.1 i), D.zero ω]
  have hR : (fun j => geomRW D.W (fun _ => flowLineXR D.bR D.JR 0) j 0 ω - D.W 0 ω) =
      fun j => flowLineXR D.bR D.JR 0 j - 0 := funext fun j => by
    rw [geomRW_zero D.continuous D.zero (hF.2.2.2 j), D.zero ω]
  unfold RefExt
  rw [hL, hR]
  exact D.u0_ext

/-- **The fibre's mean at time `0`**: `M^c + q`. -/
def mean0 (z : ℂ) : ℝ := D.u0 z + D.q z

theorem continuousOn_u0 : ContinuousOn D.u0 H := fun z hz => ((D.u0_ext.1 z hz).1.continuousAt).continuousWithinAt

theorem continuousOn_mean0 : ContinuousOn D.mean0 H := D.continuousOn_u0.add D.q_cont

/-- **The integrated time-0 kernel** (the clock is positive): `E[e^{i h(φ)}] = cfVal(∫ (u0 + q) φ, E_ℍ(φ))`. -/
theorem integral_cexp (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (D.field ω φ : ℂ)) ∂D.P =
      cfVal (∫ z, D.mean0 z * φ z) (QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens φ φ) := by
  let _ := D.prob
  have hτ : IsStoppingTime D.filt fun _ : S => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const _ _
  have hτe : ∀ᵐ ω ∂D.P, ((((0 : ℝ≥0) : WithTop ℝ≥0)) : ℝ≥0∞) < D.e ω := he0
  have hker := D.kernel _ hτ hτe (fun _ => D.u0) D.refExt_zero φ
  refine LocalExt.integral_eq_of_condExp_ae_eq_const hτ.measurableSpace_le ?_
  filter_upwards [hker] with ω hω
  have hw : Continuous (Ito.rpath (D.W · ω)) := (D.continuous ω).comp continuous_real_toNNReal
  have hw00 : Ito.rpath (D.W · ω) 0 = 0 := by simp [Ito.rpath, D.zero ω]
  have hK0 : fwdHull (Ito.rpath (D.W · ω)) 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty hw
  have h0 : (((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : ℝ) = 0 := by simp
  have hd : Disjoint (tsupport φ) (fwdHull (Ito.rpath (D.W · ω))
      ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) := by
    rw [h0, hK0]; exact disjoint_empty _
  rw [hω hd]
  have hm := integral_meanF_zero (κ := D.κ) D.u0_ext.1 D.q_cont (Fq := D.Fq) (D.continuous ω) (D.zero ω) φ
  have hu : (((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 = 0 := by simp
  simp only [hu]
  rw [hm, NNReal.coe_zero, Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hw00,
    Sec7.Lemma71J.loewnerGreenEnergy_const_zero]
  rfl

/-- **The fibre's field is a Gaussian free field with mean `u0 + q`** (the clock is positive). -/
theorem isZBGFFProcess (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => D.field ω φ - ∫ z, D.mean0 z * φ z) D.P := by
  let _ := D.prob
  have hmc := D.continuousOn_mean0
  have href := Coupling.isZBGFFProcess_fieldLaw0 hmc
  have e₁ : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, D.mean0 z * φ z = smoothDist upperHalfPlaneOpens D.mean0 φ :=
    fun φ => by
      rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hmc]
      exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have eP : (fun φ ω => D.field ω φ - ∫ z, D.mean0 z * φ z) = fun φ ω =>
      D.field ω φ - smoothDist upperHalfPlaneOpens D.mean0 φ := by
    funext φ ω; rw [e₁ φ]
  have eR : (fun φ (x : DistOn upperHalfPlaneOpens) => x φ - ∫ z, D.mean0 z * φ z) = fun φ x =>
      x φ - smoothDist upperHalfPlaneOpens D.mean0 φ := by
    funext φ x; rw [e₁ φ]
  rw [eR] at href
  rw [eP]
  refine LocalExt.isZBGFFProcess_of_integral_cexp_eq (X := D.field) D.measurable_field _ (X' := fun x => x) _ href
    fun φ => ?_
  rw [← e₁ φ]
  set c : ℝ := ∫ z, D.mean0 z * φ z
  have hsplit : ∀ y : ℝ, Complex.exp (Complex.I * ((y - c : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * (c : ℂ))) * Complex.exp (Complex.I * (y : ℂ)) := fun y => by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [hsplit]
  rw [integral_const_mul, integral_const_mul, D.integral_cexp he0 φ, Coupling.integral_cexp_fieldLaw0 hmc φ, cfVal]
  congr 2
  push_cast
  ring

end RefFibre

end InteractingSLE.Sec5.Aux61R2
