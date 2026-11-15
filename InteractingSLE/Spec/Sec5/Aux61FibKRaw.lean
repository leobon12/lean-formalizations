/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ActCut

/-!
# A restart fibre whose kernel is known at deterministic dyadic times only

Packet PROVE-AUX61-FIB2 (Theorem 1.2's Prop 5.1 (E1), pieces (F2)–(F3) of `planning/handoffs/PROVE-AUX61-ACT.md`).
`Aux61Act.DyActFibre` asks for the actual kernel (Aux. lemma 61 relative to the reference word) at the stops
`min(T_N, k/2ⁿ)` **of the fibre's completed right-continuous filtration**. A fibre is a regular conditional law of the
glued space; from the glued space only countably many identities pass to almost every fibre, and the stopped σ-algebras
of a completed filtration (whose null sets depend on the fibre) are not of that kind. This file removes the last stops:

* `RawActFibre`: the data of `DyActFibre` with, in place of `dyKernel`, the kernel at the **deterministic** dyadic
  times `q = k/2ⁿ` on the pre-clock event `{q < e}`, given any σ-algebra `𝓜 q` between the null-augmented raw killed
  σ-algebra at `q` and the ambient one (`rawKernel`). Nothing about stops, completions or right limits is asked;
* its time-0 law (`RawActFibre.isZBGFFProcess`, from `rawKernel` at `q = 0`), the chosen cutoff `Fq` of `q`, and the
  Cameron–Martin tilt `tilt = k e^{−Λ} · P` (the construction of `DyActFibre`, copied because there it depends on
  `dyKernel`).

`Aux61FibKTilt` derives `dyKernel` from `rawKernel` (`RawActFibre.toDyActFibre`): under the tilt restricted to `{q < e}`
the shifted field has the reference kernel at `q`, hence the dyadic law `IsDyadicSampled` of the reference word, and the
landed `StoppedK2.isCouplingCharFun_of_dyadic_reg` and the reverse tilt give the kernel at every stop.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61FibK

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Aux61Win (meanF IsCutoffOn)
open Aux61R2 (RefExt)
open Aux61Act (shiftField)
open Sec7.PocketTraversal

universe u

/-- **A restart fibre with the kernel at the deterministic dyadic times** (see the module docstring): the data of
`Aux61Act.DyActFibre`, with `dyKernel` replaced by `rawKernel`: for every cutoff `(F, N)` of `q` near the buffer, at
each dyadic time `q = k/2ⁿ`, for every reference extension `u` at `q` and every test `ψ`, almost surely on the
pre-clock event `{q < e}` with `ψ` off the hull at `q`, the conditional characteristic functional of the field given
`𝓜 q` is the `meanF` Gaussian kernel. `𝓜 q` is any σ-algebra containing the null-augmented raw killed σ-algebra at
`q`. -/
structure RawActFibre (S : Type u) [m : MeasurableSpace S] where
  κ : ℝ
  κ_pos : 0 < κ
  bR : ℝ → ℝ
  JR : Finset ℝ
  bR_pc : IsPiecewiseConstantBoundaryData bR JR
  CS : Aux61R45.ClockSource S
  y_zero : CS.y = 0
  V : Set ℂ
  RC : Aux61R45.ReferenceClock CS κ bR JR 0 V
  driving_eq : CS.driving = drivingFiltration CS.P RC.killed
  field : S → DistOn upperHalfPlaneOpens
  measurable_field : Measurable field
  q : ℂ → ℝ
  q_harm : InnerProductSpace.HarmonicOnNhd q H
  O₀ : Set ℝ
  O₀_open : IsOpen O₀
  q_zero : ∀ x ∈ O₀, Tendsto q (𝓝[H] (x : ℂ)) (𝓝 0)
  buffer : Set ℂ
  buffer_open : IsOpen buffer
  zero_mem : (0 : ℂ) ∈ buffer
  buffer_compact : IsCompact (closure buffer)
  buffer_real : ∀ z ∈ closure buffer, z.im = 0 → z.re ∈ O₀
  hull_buffer : ∀ᵐ ω ∂CS.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < RC.e ω →
    closure (fwdHull (Ito.rpath (RC.W · ω)) t) ⊆ buffer
  𝓜 : ℝ≥0 → MeasurableSpace S
  𝓜_le : ∀ t, 𝓜 t ≤ m
  raw_le : ∀ t, Ito.nullAugmented (killedDrivingFiltration RC.killed) CS.P t ≤ 𝓜 t
  rawKernel : ∀ (F : CMCut) (N : Set ℂ), IsCutoffOn F q N O₀ → buffer ⊆ N → ∀ n k : ℕ,
    ∀ u : S → ℂ → ℝ, (∀ ω, RefExt κ bR JR RC.W (Restart.DomainMarkov.dyT n k) ω (u ω)) →
    ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂CS.P,
      ((Restart.DomainMarkov.dyT n k : ℝ≥0) : ℝ≥0∞) < RC.e ω →
      Disjoint (tsupport ψ) (fwdHull (Ito.rpath (RC.W · ω)) (Restart.DomainMarkov.dyT n k : ℝ≥0)) →
      CS.P[fun ω' => Complex.exp (Complex.I * (field ω' ψ : ℂ)) | 𝓜 (Restart.DomainMarkov.dyT n k)] ω =
        cfVal (∫ z, meanF κ (u ω) q F (Ito.rpath (RC.W · ω)) (Restart.DomainMarkov.dyT n k : ℝ≥0) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (RC.W · ω)) (Restart.DomainMarkov.dyT n k : ℝ≥0) ψ)
  members : Restart.DomainMarkov.HasRatMembers CS.P (killedDrivingFiltration RC.killed) RC.W RC.e
    (WholeField.centredField field fun z =>
      MartChar.meanExt κ (flowLineRhoL κ bR JR 0 0) (flowLineRhoR κ bR JR 0 0) 0 (flowLineXL bR JR 0)
        (flowLineXR bR JR 0) z + q z)
  injective : ∀ᵐ ω ∂CS.P, InjOn (CS.Γ ω) {t | (t : ℝ≥0∞) ≤ RC.e ω}

namespace RawActFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : RawActFibre S)

instance : IsProbabilityMeasure D.CS.P := D.CS.prob

/-- The pre-clock event `{q < e}` is an event of `𝓜 q`. -/
theorem measurableSet_lt_e (t : ℝ≥0) : MeasurableSet[D.𝓜 t] {ω | (t : ℝ≥0∞) < D.RC.e ω} := by
  refine D.raw_le t _ (Ito.le_nullAugmented _ _ t _ ?_)
  refine MeasurableSpace.measurableSet_generateFrom ⟨t, le_rfl, univ, MeasurableSet.univ, ?_⟩
  ext ω
  simp

/-! ### The time-0 law -/

/-- The reference word's initial extension (the canonical mean `M^c` at the restart). -/
def u0 : ℂ → ℝ :=
  MartChar.meanExt D.κ (flowLineRhoL D.κ D.bR D.JR 0 0) (flowLineRhoR D.κ D.bR D.JR 0 0) 0
    (flowLineXL D.bR D.JR 0) (flowLineXR D.bR D.JR 0)

theorem u0_ext : IsBoundedHarmonicExtension
    (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR 0 0) (flowLineRhoR D.κ D.bR D.JR 0 0)
      (fun i => flowLineXL D.bR D.JR 0 i - 0) (fun j => flowLineXR D.bR D.JR 0 j - 0))
    (forceJumpSet (fun i => flowLineXL D.bR D.JR 0 i - 0) (fun j => flowLineXR D.bR D.JR 0 j - 0)) D.u0 :=
  MartChar.isBoundedHarmonicExtension_meanExt _ _ _ 0 _ _

/-- At time `0`, `u0` is a reference extension. -/
theorem refExt_zero (ω : S) : RefExt D.κ D.bR D.JR D.RC.W 0 ω D.u0 := by
  have hF := Theorem15.isOrderedForceWord_flowLine D.bR D.JR 0
  have hL : (fun i => geomLW D.RC.W (fun _ => flowLineXL D.bR D.JR 0) i 0 ω - D.RC.W 0 ω) =
      fun i => flowLineXL D.bR D.JR 0 i - 0 := funext fun i => by
    rw [geomLW_zero D.RC.continuous D.RC.zero (hF.2.1 i), D.RC.zero ω]
  have hR : (fun j => geomRW D.RC.W (fun _ => flowLineXR D.bR D.JR 0) j 0 ω - D.RC.W 0 ω) =
      fun j => flowLineXR D.bR D.JR 0 j - 0 := funext fun j => by
    rw [geomRW_zero D.RC.continuous D.RC.zero (hF.2.2.2 j), D.RC.zero ω]
  unfold RefExt
  rw [hL, hR]
  exact D.u0_ext

/-- The fibre's mean at time `0`: `M^c + q`. -/
def mean0 (z : ℂ) : ℝ := D.u0 z + D.q z

theorem continuousOn_q : ContinuousOn D.q H := D.q_harm.contDiffOn.continuousOn

theorem continuousOn_u0 : ContinuousOn D.u0 H := fun z hz => ((D.u0_ext.1 z hz).1.continuousAt).continuousWithinAt

theorem continuousOn_mean0 : ContinuousOn D.mean0 H := ContinuousOn.add D.continuousOn_u0 D.continuousOn_q

/-- The clock is positive (it is announced). -/
theorem ae_e_pos : ∀ᵐ ω ∂D.CS.P, 0 < D.RC.e ω :=
  (D.RC.announcing.2.2.1 0).mono fun _ h => lt_of_le_of_lt bot_le h

/-- **The integrated time-0 kernel** (`rawKernel` at `q = 0`, where `{0 < e}` is almost sure and the hull is
empty): for any cutoff of `q` near the buffer, `E[e^{i h(φ)}] = cfVal(∫ (u0 + q) φ, E_ℍ(φ))`. -/
theorem integral_cexp {F : CMCut} {N : Set ℂ} (hF : IsCutoffOn F D.q N D.O₀) (hbN : D.buffer ⊆ N)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (D.field ω φ : ℂ)) ∂D.CS.P =
      cfVal (∫ z, D.mean0 z * φ z) (QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens φ φ) := by
  have h0 : Restart.DomainMarkov.dyT 0 0 = 0 := by simp [Restart.DomainMarkov.dyT]
  have hu : ∀ ω, RefExt D.κ D.bR D.JR D.RC.W (Restart.DomainMarkov.dyT 0 0) ω D.u0 := fun ω => by
    rw [h0]; exact D.refExt_zero ω
  have hker := D.rawKernel F N hF hbN 0 0 (fun _ => D.u0) hu φ
  rw [h0] at hker
  refine LocalExt.integral_eq_of_condExp_ae_eq_const (D.𝓜_le 0) ?_
  filter_upwards [hker, D.ae_e_pos] with ω hω hpos
  have hw : Continuous (Ito.rpath (D.RC.W · ω)) := (D.RC.continuous ω).comp continuous_real_toNNReal
  have hw00 : Ito.rpath (D.RC.W · ω) 0 = 0 := by simp [Ito.rpath, D.RC.zero ω]
  have hK0 : fwdHull (Ito.rpath (D.RC.W · ω)) 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty hw
  have hd : Disjoint (tsupport φ) (fwdHull (Ito.rpath (D.RC.W · ω)) ((0 : ℝ≥0) : ℝ)) := by
    rw [NNReal.coe_zero, hK0]; exact disjoint_empty _
  rw [hω (by simpa using hpos) hd]
  have hm := Aux61R2.integral_meanF_zero (κ := D.κ) D.u0_ext.1 D.continuousOn_q (Fq := F) (D.RC.continuous ω)
    (D.RC.zero ω) φ
  rw [NNReal.coe_zero] at hm ⊢
  rw [hm, Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hw00, Sec7.Lemma71J.loewnerGreenEnergy_const_zero]
  rfl

/-- **The fibre's field is a Gaussian free field with mean `u0 + q`** (given one cutoff of `q` near the buffer). -/
theorem isZBGFFProcess {F : CMCut} {N : Set ℂ} (hF : IsCutoffOn F D.q N D.O₀) (hbN : D.buffer ⊆ N) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => D.field ω φ - ∫ z, D.mean0 z * φ z) D.CS.P := by
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
  rw [integral_const_mul, integral_const_mul, D.integral_cexp hF hbN φ, Coupling.integral_cexp_fieldLaw0 hmc φ,
    cfVal]
  congr 2
  push_cast
  ring

/-! ### The chosen cutoff and the Cameron–Martin tilt (as for `DyActFibre`) -/

theorem exists_cut : ∃ (N : Set ℂ) (F : CMCut) (C : ℝ), closure D.buffer ⊆ N ∧ IsCutoffOn F D.q N D.O₀ ∧
    ∀ z, F.src z ≠ 0 → |D.q z| ≤ C :=
  Aux61Cov.exists_cmCut_of_harmonic D.O₀_open D.q_harm D.q_zero D.buffer_compact D.buffer_real

/-- The chosen neighbourhood of the buffer. -/
def Nq : Set ℂ := D.exists_cut.choose

/-- The chosen cutoff of `q`. -/
def Fq : CMCut := D.exists_cut.choose_spec.choose

/-- The chosen bound of `q` on the source of the cutoff. -/
def Cq : ℝ := D.exists_cut.choose_spec.choose_spec.choose

theorem cut_spec : closure D.buffer ⊆ D.Nq ∧ IsCutoffOn D.Fq D.q D.Nq D.O₀ ∧
    ∀ z, D.Fq.src z ≠ 0 → |D.q z| ≤ D.Cq :=
  D.exists_cut.choose_spec.choose_spec.choose_spec

theorem buffer_sub : D.buffer ⊆ D.Nq := subset_closure.trans D.cut_spec.1

theorem exists_tilt : ∃ Λ : S → ℝ, Measurable Λ ∧
    (∀ᵐ ω ∂D.CS.P, Tendsto (fun n => D.field ω (D.Fq.neg.testSeq n)) atTop (𝓝 (Λ ω))) ∧
    Integrable (fun ω => Real.exp (-Λ ω)) D.CS.P := by
  obtain ⟨Cu, hCu⟩ := D.u0_ext.2.1
  refine Aux61Act.exists_tiltΛ D.measurable_field D.continuousOn_mean0
    (D.isZBGFFProcess D.cut_spec.2.1 D.buffer_sub) D.Fq.neg (C := Cu + D.Cq) fun z hz => ?_
  have hz' : D.Fq.src z ≠ 0 := fun h0 => hz (by rw [CMCut.src_neg, h0, neg_zero])
  have hzH : z ∈ H := (D.Fq.mem_of_src_ne_zero hz').1
  exact (abs_add_le _ _).trans (add_le_add (hCu z hzH) (D.cut_spec.2.2 z hz'))

/-- The pairing limit. -/
def Λ : S → ℝ := D.exists_tilt.choose

theorem measurable_Λ : Measurable D.Λ := D.exists_tilt.choose_spec.1

theorem ae_tendsto_Λ : ∀ᵐ ω ∂D.CS.P, Tendsto (fun n => D.field ω (D.Fq.neg.testSeq n)) atTop (𝓝 (D.Λ ω)) :=
  D.exists_tilt.choose_spec.2.1

theorem integrable_exp_neg_Λ : Integrable (fun ω => Real.exp (-D.Λ ω)) D.CS.P := D.exists_tilt.choose_spec.2.2

theorem integral_exp_neg_Λ_pos : 0 < ∫ ω, Real.exp (-D.Λ ω) ∂D.CS.P := by
  refine (integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos _).le) D.integrable_exp_neg_Λ).2 ?_
  have hs : Function.support (fun ω => Real.exp (-D.Λ ω)) = univ :=
    eq_univ_of_forall fun ω => (Real.exp_pos _).ne'
  rw [hs, measure_univ]
  exact one_pos

/-- The normalizing constant. -/
def kc : ℝ := (∫ ω, Real.exp (-D.Λ ω) ∂D.CS.P)⁻¹

theorem kc_pos : 0 < D.kc := inv_pos.2 D.integral_exp_neg_Λ_pos

/-- **The tilted law** `k e^{−Λ} · P`. -/
def tilt : Measure S := D.CS.P.withDensity fun ω => ENNReal.ofReal (D.kc * Real.exp (-D.Λ ω))

instance isProbabilityMeasure_tilt : IsProbabilityMeasure D.tilt := by
  constructor
  have hint := D.integrable_exp_neg_Λ
  have hpos := D.integral_exp_neg_Λ_pos
  change (D.CS.P.withDensity fun ω => ENNReal.ofReal ((∫ ω, Real.exp (-D.Λ ω) ∂D.CS.P)⁻¹ *
    Real.exp (-D.Λ ω))) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
      (ae_of_all _ fun ω => mul_nonneg (inv_pos.2 hpos).le (Real.exp_pos _).le),
    integral_const_mul, inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]

theorem tilt_ac : D.tilt ≪ D.CS.P := withDensity_absolutelyContinuous _ _

theorem ac_tilt : D.CS.P ≪ D.tilt :=
  Restart.FlowStopIdentCMI.absolutelyContinuous_withDensity_exp D.measurable_Λ D.kc_pos

/-! ### The reference processes -/

/-- The reference marks' processes (from the fibre's seed `y = 0`). -/
def VL : Fin (flowLineNL D.bR D.JR D.CS.y) → ℝ≥0 → S → ℝ := geomLW D.RC.W (fun _ => flowLineXL D.bR D.JR D.CS.y)

/-- The reference marks' processes (right). -/
def VR : Fin (flowLineNR D.bR D.JR D.CS.y) → ℝ≥0 → S → ℝ := geomRW D.RC.W (fun _ => flowLineXR D.bR D.JR D.CS.y)

/-- The reference extension process. -/
def ucf : S → ℝ≥0 → ℂ → ℝ :=
  Restart.DomainMarkov.bheProc D.κ (flowLineRhoL D.κ D.bR D.JR D.CS.y 0) (flowLineRhoR D.κ D.bR D.JR D.CS.y 0)
    D.RC.W D.VL D.VR

theorem refExt_ucf (ω : S) (t : ℝ≥0) : RefExt D.κ D.bR D.JR D.RC.W t ω (D.ucf ω t) :=
  Aux61Act.refExt_of_bhe D.y_zero (Restart.DomainMarkov.isBoundedHarmonicExtension_bheProc ω t)

/-- The completed filtration of the fibre is the reference word's, under the fibre law and under the tilt. -/
theorem driving_eq_tilt : D.CS.driving = drivingFiltration D.tilt D.RC.killed :=
  D.driving_eq.trans (Aux61R2.drivingFiltration_congr D.ac_tilt D.tilt_ac D.RC.killed)

/-- The hulls before the clock lie in the buffer, at any time below the clock. -/
theorem ae_hull_buffer_of_lt {t : S → ℝ≥0} (ht : ∀ᵐ ω ∂D.CS.P, (t ω : ℝ≥0∞) < D.RC.e ω) :
    ∀ᵐ ω ∂D.CS.P, closure (fwdHull (Ito.rpath (D.RC.W · ω)) (t ω)) ⊆ D.buffer := by
  filter_upwards [D.hull_buffer, ht] with ω hb htω using hb _ htω

/-- The reference processes are regular before the clock (`IsForceReg`). -/
theorem isForceReg (ω : S) : Restart.DomainMarkov.Aux79.IsForceReg D.RC.W D.VL D.VR D.RC.e ω :=
  ⟨D.RC.zero ω, (D.RC.continuous ω).continuousOn,
    fun i => (isForcePath_geomLW D.RC.continuous _ ω i).1.continuousOn,
    fun j => (isForcePath_geomRW D.RC.continuous _ ω j).1.continuousOn,
    fun t _ => ⟨fun i => geomLW_le D.RC.continuous _ ω t i, fun j => le_geomRW D.RC.continuous _ ω t j⟩⟩

end RawActFibre

end InteractingSLE.Sec5.Aux61FibK
