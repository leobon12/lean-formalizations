/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ActTilt
import InteractingSLE.Spec.Restart.StoppedK2Dyadic

/-!
# A restart fibre whose kernel is known at countably many stops

Packet PROVE-AUX61-ACT (Theorem 1.2's Prop 5.1 (E1), the disintegration and the per-fibre kernel). PROVE-AUX61-R2C's
`Aux61Cov.ActFibre` asks for the actual kernel (Aux. lemma 61 relative to the reference word) at **every** stop of the
fibre's own completed driving filtration. A fibre is a regular conditional law of the glued space; only countably many
identities can be carried from the glued space to almost every fibre, and a stop of one fibre's completed filtration
does not come from a stop of the glued space. This file removes that obstruction: the kernel at the countable family of
stops `min(T_N, k/2ⁿ)` (`T_N` the reference clock's announcing sequence) gives the kernel at every stop before the
clock.

Route (no new probability): the kernel at `τ = 0` makes the field a Gaussian free field with mean `M^c + q`
(`isZBGFFProcess`), which gives the Cameron–Martin data `Λ`, `k` of the cutoff `−Fq` (`Aux61ActTilt.exists_tiltΛ`).
Under the tilt `Q = k e^{−Λ} · P` the shifted field has the reference kernel at each `min(T_N, k/2ⁿ)`
(`Aux61ActTilt.ae_condExp_tilt_fwd`), hence the dyadic protected-kernel law `IsDyadicSampled` of the reference word
(`isDyadicSampled_tilt`: an event at a dyadic time `q` inside the avoidance event is exhausted by its parts on
`{q ≤ T_N}`, which are events at the stop `min(T_N, q)`); the landed `StoppedK2.isCouplingCharFun_of_dyadic_reg` gives
the
reference kernel at every stop under `Q`, and the reverse tilt (`Aux61ActTilt.ae_condExp_tilt_rev`) brings it back.

* `DyActFibre`: the data of `Aux61Cov.ActFibre` with the kernel only at the stops `min(T_N, k/2ⁿ)`, the clock source
  killed at the clock (`driving_eq`: the fibre's completed filtration is the reference word's) and a piecewise constant
  reference word (as in `Aux61Cov.RefWin`);
* `DyActFibre.u0`, `refExt_zero`, `mean0`, **`isZBGFFProcess`** (the time-0 law), the chosen cutoff `Fq` with its bound;
* **`DyActFibre.locality`**: locality of the hulls at every stop before the clock, from the member identities at
  rational times (the landed `DomainMarkov.isLocalSet_hull_of_members`);
* **`DyActFibre.kernel_Fq`**: the kernel for the chosen cutoff at every stop before the clock.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Act

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (IsGreenTest greenCross cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Aux61Win (meanF IsCutoffOn)
open Aux61R2 (RefExt)
open Sec7.PocketTraversal

universe u

/-- The stop `min(T_N, k/2ⁿ)` of a reference clock. -/
def dyStop {S : Type u} [MeasurableSpace S] {CS : Aux61R45.ClockSource S} {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {V : Set ℂ} (RC : Aux61R45.ReferenceClock CS κ b J θ V) (n k N : ℕ) : S → WithTop ℝ≥0 :=
  fun ω => min ((RC.T N ω : ℝ≥0) : WithTop ℝ≥0) ((Restart.DomainMarkov.dyT n k : ℝ≥0) : WithTop ℝ≥0)

/-- **A restart fibre with the kernel at the stops `min(T_N, k/2ⁿ)`** (see the module docstring): the data of
`Aux61Cov.ActFibre`, the clock source killed at the clock (`driving_eq`), the kernel only at the countably many
stops `dyStop RC n k N`, and, in place of locality at every stop, the member identities at rational times
(`DomainMarkov.HasRatMembers`) of the field centred by its time-0 mean `M^c + q`. -/
structure DyActFibre (S : Type u) [m : MeasurableSpace S] where
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
  dyKernel : ∀ (F : CMCut) (N : Set ℂ), IsCutoffOn F q N O₀ → buffer ⊆ N →
    ∀ (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime CS.driving τ), (∃ n k N' : ℕ, τ = dyStop RC n k N') →
    ∀ u : S → ℂ → ℝ, (∀ ω, RefExt κ bR JR RC.W ((τ ω).untopD 0) ω (u ω)) →
    ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂CS.P,
      Disjoint (tsupport ψ) (fwdHull (Ito.rpath (RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) →
      CS.P[fun ω' => Complex.exp (Complex.I * (field ω' ψ : ℂ)) | hτ.measurableSpace] ω =
        cfVal (∫ z, meanF κ (u ω) q F (Ito.rpath (RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) ψ)
  members : Restart.DomainMarkov.HasRatMembers CS.P (killedDrivingFiltration RC.killed) RC.W RC.e
    (WholeField.centredField field fun z =>
      MartChar.meanExt κ (flowLineRhoL κ bR JR 0 0) (flowLineRhoR κ bR JR 0 0) 0 (flowLineXL bR JR 0)
        (flowLineXR bR JR 0) z + q z)
  injective : ∀ᵐ ω ∂CS.P, InjOn (CS.Γ ω) {t | (t : ℝ≥0∞) ≤ RC.e ω}

namespace DyActFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : DyActFibre S)

instance : IsProbabilityMeasure D.CS.P := D.CS.prob

/-! ### The stops `min(T_N, k/2ⁿ)` -/

theorem isStoppingTime_dyStop (n k N : ℕ) : IsStoppingTime D.CS.driving (dyStop D.RC n k N) :=
  (D.RC.announcing.1 N).min_const _

theorem dyStop_untopD (n k N : ℕ) (ω : S) :
    (dyStop D.RC n k N ω).untopD 0 = min (D.RC.T N ω) (Restart.DomainMarkov.dyT n k) := by
  simp only [dyStop, ← WithTop.coe_min, WithTop.untopD_coe]

/-- The clock is positive (it is announced). -/
theorem ae_e_pos : ∀ᵐ ω ∂D.CS.P, 0 < D.RC.e ω :=
  (D.RC.announcing.2.2.1 0).mono fun _ h => lt_of_le_of_lt bot_le h

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

/-- **The integrated time-0 kernel**: for any cutoff of `q` near the buffer,
`E[e^{i h(φ)}] = cfVal(∫ (u0 + q) φ, E_ℍ(φ))`. -/
theorem integral_cexp {F : CMCut} {N : Set ℂ} (hF : IsCutoffOn F D.q N D.O₀) (hbN : D.buffer ⊆ N)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (D.field ω φ : ℂ)) ∂D.CS.P =
      cfVal (∫ z, D.mean0 z * φ z) (QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens φ φ) := by
  have hτ := D.isStoppingTime_dyStop 0 0 0
  have h0 : ∀ ω, (dyStop D.RC 0 0 0 ω).untopD 0 = 0 := fun ω => by
    rw [D.dyStop_untopD]
    simp [Restart.DomainMarkov.dyT]
  have hu : ∀ ω, RefExt D.κ D.bR D.JR D.RC.W ((dyStop D.RC 0 0 0 ω).untopD 0) ω D.u0 := fun ω => by
    rw [h0]; exact D.refExt_zero ω
  have hker := D.dyKernel F N hF hbN _ hτ ⟨0, 0, 0, rfl⟩ (fun _ => D.u0) hu φ
  refine LocalExt.integral_eq_of_condExp_ae_eq_const hτ.measurableSpace_le ?_
  filter_upwards [hker] with ω hω
  have hw : Continuous (Ito.rpath (D.RC.W · ω)) := (D.RC.continuous ω).comp continuous_real_toNNReal
  have hw00 : Ito.rpath (D.RC.W · ω) 0 = 0 := by simp [Ito.rpath, D.RC.zero ω]
  have hK0 : fwdHull (Ito.rpath (D.RC.W · ω)) 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty hw
  have hd : Disjoint (tsupport φ) (fwdHull (Ito.rpath (D.RC.W · ω))
      ((dyStop D.RC 0 0 0 ω).untopD 0 : ℝ≥0)) := by
    rw [h0, NNReal.coe_zero, hK0]; exact disjoint_empty _
  rw [hω hd, h0]
  have hm := Aux61R2.integral_meanF_zero (κ := D.κ) D.u0_ext.1 D.continuousOn_q (Fq := F) (D.RC.continuous ω)
    (D.RC.zero ω) φ
  rw [hm, NNReal.coe_zero, Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hw00,
    Sec7.Lemma71J.loewnerGreenEnergy_const_zero]
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

/-! ### The chosen cutoff -/

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

/-! ### The Cameron–Martin data of the cutoff `−Fq` -/

theorem exists_tilt : ∃ Λ : S → ℝ, Measurable Λ ∧
    (∀ᵐ ω ∂D.CS.P, Tendsto (fun n => D.field ω (D.Fq.neg.testSeq n)) atTop (𝓝 (Λ ω))) ∧
    Integrable (fun ω => Real.exp (-Λ ω)) D.CS.P := by
  obtain ⟨Cu, hCu⟩ := D.u0_ext.2.1
  refine exists_tiltΛ D.measurable_field D.continuousOn_mean0 (D.isZBGFFProcess D.cut_spec.2.1 D.buffer_sub)
    D.Fq.neg (C := Cu + D.Cq) fun z hz => ?_
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

/-! ### Locality at every stop from the member identities -/

theorem harmonic_mean0 : InnerProductSpace.HarmonicOnNhd D.mean0 H := fun z hz =>
  (D.u0_ext.1 z hz).add (D.q_harm z hz)

/-- The field centred by its time-0 mean is a zero-boundary GFF. -/
theorem isZeroBoundaryGFF_centred :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField D.field D.mean0) D.CS.P := by
  refine ⟨WholeField.measurable_centredField D.measurable_field D.mean0, ?_⟩
  have he : (fun φ ω => WholeField.centredField D.field D.mean0 ω φ) =
      fun φ ω => D.field ω φ - ∫ z, D.mean0 z * φ z := by
    funext φ ω
    exact WholeField.centredField_apply D.field D.harmonic_mean0 ω φ
  rw [he]
  exact D.isZBGFFProcess D.cut_spec.2.1 D.buffer_sub

/-- **Locality of the hulls at every stop before the clock**, from the member identities at rational times. -/
theorem locality (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime D.CS.driving τ)
    (hτe : ∀ᵐ ω ∂D.CS.P, (τ ω : ℝ≥0∞) < D.RC.e ω) :
    IsLocalSet (fun ω => fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.field D.CS.P := by
  have hτ' : IsStoppingTime (usualAugmentation (killedDrivingFiltration D.RC.killed) D.CS.P) τ := by
    have h := D.driving_eq
    rw [drivingFiltration] at h
    exact h ▸ hτ
  have hpath : ∀ᵐ ω ∂D.CS.P, ContinuousOn (fun t => D.RC.W t ω) {t | (t : ℝ≥0∞) < D.RC.e ω} ∧
      D.RC.W 0 ω = 0 := ae_of_all _ fun ω => ⟨(D.RC.continuous ω).continuousOn, D.RC.zero ω⟩
  have hl := Restart.DomainMarkov.isLocalSet_hull_of_members D.isZeroBoundaryGFF_centred
    (Coupling.adaptedBefore_killedDriving_W D.RC.killed) hpath D.members hτ' hτe
  have hadd := Coupling.IsLocalSet.add_dist hl (WholeField.isHarmonicDistOn_smoothDist D.harmonic_mean0)
  simp only [WholeField.centredField, sub_add_cancel] at hadd
  exact hadd

end DyActFibre

/-! ### The reference word's processes -/

section Ref

variable {S : Type u} [mS : MeasurableSpace S]

omit mS in
/-- A bounded harmonic extension of the reference data with marks from `y = 0` is a reference extension. -/
theorem refExt_of_bhe {κ : ℝ} {bR : ℝ → ℝ} {JR : Finset ℝ} {W : ℝ≥0 → S → ℝ} {t : ℝ≥0} {ω : S}
    {u : ℂ → ℝ} {y : ℝ} (hy : y = 0)
    (h : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR JR y 0) (flowLineRhoR κ bR JR y 0)
        (fun i => geomLW W (fun _ => flowLineXL bR JR y) i t ω - W t ω)
        (fun j => geomRW W (fun _ => flowLineXR bR JR y) j t ω - W t ω))
      (forceJumpSet (fun i => geomLW W (fun _ => flowLineXL bR JR y) i t ω - W t ω)
        (fun j => geomRW W (fun _ => flowLineXR bR JR y) j t ω - W t ω)) u) :
    RefExt κ bR JR W t ω u := by
  subst hy; exact h

omit mS in
/-- A reference extension is a bounded harmonic extension of the reference data with marks from `y = 0`. -/
theorem bhe_of_refExt {κ : ℝ} {bR : ℝ → ℝ} {JR : Finset ℝ} {W : ℝ≥0 → S → ℝ} {t : ℝ≥0} {ω : S}
    {u : ℂ → ℝ} {y : ℝ} (hy : y = 0) (h : RefExt κ bR JR W t ω u) :
    IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR JR y 0) (flowLineRhoR κ bR JR y 0)
        (fun i => geomLW W (fun _ => flowLineXL bR JR y) i t ω - W t ω)
        (fun j => geomRW W (fun _ => flowLineXR bR JR y) j t ω - W t ω))
      (forceJumpSet (fun i => geomLW W (fun _ => flowLineXL bR JR y) i t ω - W t ω)
        (fun j => geomRW W (fun _ => flowLineXR bR JR y) j t ω - W t ω)) u := by
  subst hy; exact h

/-- The stopping-time σ-algebra only depends on the filtration. -/
theorem measurableSpace_congr {f g : Filtration ℝ≥0 mS} (h : f = g) {τ : S → WithTop ℝ≥0}
    (hτ : IsStoppingTime f τ) (hτ' : IsStoppingTime g τ) : hτ.measurableSpace = hτ'.measurableSpace := by
  subst h; rfl

omit mS in
/-- `cfAt` at a deterministic time with `θ = 1` is `cfVal`. -/
theorem cfAt_one_eq_cfVal {κ : ℝ} {W : ℝ≥0 → S → ℝ} (u : S → ℝ≥0 → ℂ → ℝ) (ψ : ℂ → ℝ) (r : ℝ≥0) (ω : S) :
    Coupling.cfAt κ W u ψ 1 (fun _ => r) ω =
      cfVal (∫ z, couplingMean κ (Ito.rpath (W · ω)) r (u ω r) z * ψ z)
        (loewnerGreenEnergy (Ito.rpath (W · ω)) r ψ) := by
  simp only [Coupling.cfAt, cfVal]
  congr 1
  push_cast
  ring_nf
  rfl

end Ref

namespace DyActFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : DyActFibre S)

/-- The reference marks' processes (from the fibre's seed `y = 0`). -/
def VL : Fin (flowLineNL D.bR D.JR D.CS.y) → ℝ≥0 → S → ℝ := geomLW D.RC.W (fun _ => flowLineXL D.bR D.JR D.CS.y)

/-- The reference marks' processes (right). -/
def VR : Fin (flowLineNR D.bR D.JR D.CS.y) → ℝ≥0 → S → ℝ := geomRW D.RC.W (fun _ => flowLineXR D.bR D.JR D.CS.y)

/-- The reference extension process. -/
def ucf : S → ℝ≥0 → ℂ → ℝ :=
  Restart.DomainMarkov.bheProc D.κ (flowLineRhoL D.κ D.bR D.JR D.CS.y 0) (flowLineRhoR D.κ D.bR D.JR D.CS.y 0)
    D.RC.W D.VL D.VR

theorem refExt_ucf (ω : S) (t : ℝ≥0) : RefExt D.κ D.bR D.JR D.RC.W t ω (D.ucf ω t) :=
  refExt_of_bhe D.y_zero (Restart.DomainMarkov.isBoundedHarmonicExtension_bheProc ω t)

/-- The completed filtration of the fibre is the reference word's, under the fibre law and under the tilt. -/
theorem driving_eq_tilt : D.CS.driving = drivingFiltration D.tilt D.RC.killed :=
  D.driving_eq.trans (Aux61R2.drivingFiltration_congr D.ac_tilt D.tilt_ac D.RC.killed)

/-- The hulls before the clock lie in the buffer, at any time below the clock. -/
theorem ae_hull_buffer_of_lt {t : S → ℝ≥0} (ht : ∀ᵐ ω ∂D.CS.P, (t ω : ℝ≥0∞) < D.RC.e ω) :
    ∀ᵐ ω ∂D.CS.P, closure (fwdHull (Ito.rpath (D.RC.W · ω)) (t ω)) ⊆ D.buffer := by
  filter_upwards [D.hull_buffer, ht] with ω hb htω using hb _ htω

/-- The stop `min(T_N, k/2ⁿ)` is before the clock. -/
theorem ae_dyStop_lt (n k N : ℕ) :
    ∀ᵐ ω ∂D.CS.P, (((dyStop D.RC n k N ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < D.RC.e ω := by
  filter_upwards [D.RC.announcing.2.2.1 N] with ω hω
  rw [D.dyStop_untopD]
  exact lt_of_le_of_lt (by exact_mod_cast min_le_left _ _) hω

/-- **The reference kernel under the tilt at the stops `min(T_N, k/2ⁿ)`** (the forward tilt of `dyKernel`). -/
theorem ae_condExp_tilt_dyStop (n k N : ℕ) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂D.tilt, Disjoint (tsupport ψ)
        (fwdHull (Ito.rpath (D.RC.W · ω)) ((dyStop D.RC n k N ω).untopD 0 : ℝ≥0)) →
      D.tilt[fun ω' => Complex.exp (Complex.I * (shiftField D.field D.q D.Fq ω' ψ : ℂ)) |
          (D.isStoppingTime_dyStop n k N).measurableSpace] ω =
        cfVal (∫ z, couplingMean D.κ (Ito.rpath (D.RC.W · ω)) ((dyStop D.RC n k N ω).untopD 0 : ℝ≥0)
            (D.ucf ω ((dyStop D.RC n k N ω).untopD 0)) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (D.RC.W · ω)) ((dyStop D.RC n k N ω).untopD 0 : ℝ≥0) ψ) := by
  have hτ := D.isStoppingTime_dyStop n k N
  have hcut := D.cut_spec.2.1
  have hker := D.dyKernel D.Fq D.Nq hcut D.buffer_sub _ hτ ⟨n, k, N, rfl⟩
    (fun ω => D.ucf ω ((dyStop D.RC n k N ω).untopD 0)) (fun ω => D.refExt_ucf ω _)
  exact ae_condExp_tilt_fwd (t := fun ω => (dyStop D.RC n k N ω).untopD 0) hτ.measurableSpace_le
    D.measurable_field D.continuousOn_q hcut D.cut_spec.2.2 D.buffer_open D.zero_mem D.buffer_sub D.RC.zero
    D.RC.continuous (D.ae_hull_buffer_of_lt (D.ae_dyStop_lt n k N))
    (fun ω => (D.refExt_ucf ω _).1) (fun ω => (D.refExt_ucf ω _).2.1) hker D.measurable_Λ D.ae_tendsto_Λ
    D.integrable_exp_neg_Λ D.kc_pos ψ

/-- **The dyadic protected-kernel law of the reference word under the tilt**: an event `A` at the dyadic time
`q = k/2ⁿ` inside the avoidance event is exhausted by its parts on `{q ≤ T_N}`, which are events at the stop
`min(T_N, q)` where the tilted kernel holds with the stop equal to `q`. -/
theorem isDyadicSampled_tilt : Restart.DomainMarkov.IsDyadicSampled D.κ D.RC.W D.ucf D.tilt D.RC.killed
    (shiftField D.field D.q D.Fq) := by
  intro ψ n k A hA hAav
  set q : ℝ≥0 := Restart.DomainMarkov.dyT n k with hqdef
  set 𝓖 := D.CS.driving with h𝓖
  have hA𝓖 : MeasurableSet[𝓖 q] A := by
    have h1 : Ito.nullAugmented (killedDrivingFiltration D.RC.killed) D.tilt ≤ drivingFiltration D.tilt D.RC.killed :=
      Ito.nullAugmented_le_usualAugmentation _ _
    rw [h𝓖, D.driving_eq_tilt]; exact h1 q _ hA
  set f : S → ℂ := fun ω => Complex.exp (Complex.I * (shiftField D.field D.q D.Fq ω ψ : ℂ)) with hf
  set g : S → ℂ := Coupling.cfAt D.κ D.RC.W D.ucf ψ 1 (fun _ => q) with hg
  set B : ℕ → Set S := fun N => A ∩ {ω | q ≤ D.RC.T N ω} with hB
  have hTq : ∀ N, MeasurableSet[𝓖 q] {ω | q ≤ D.RC.T N ω} := fun N => by
    have h := (D.RC.announcing.1 N).measurableSet_lt q
    have e : {ω | q ≤ D.RC.T N ω} = {ω | ((D.RC.T N ω : ℝ≥0) : WithTop ℝ≥0) < (q : WithTop ℝ≥0)}ᶜ := by
      ext ω; simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_lt_coe, not_lt]
    rw [e]; exact h.compl
  have hB𝓖 : ∀ N, MeasurableSet[𝓖 q] (B N) := fun N => hA𝓖.inter (hTq N)
  have hBm : ∀ N, MeasurableSet (B N) := fun N => 𝓖.le q _ (hB𝓖 N)
  have hBτ : ∀ N, MeasurableSet[(D.isStoppingTime_dyStop n k N).measurableSpace] (B N) := by
    intro N
    refine ⟨(le_iSup (fun t => (𝓖 t : MeasurableSpace S)) q) _ (hB𝓖 N), fun i => ?_⟩
    by_cases hqi : q ≤ i
    · have e : B N ∩ {ω | dyStop D.RC n k N ω ≤ (i : WithTop ℝ≥0)} = B N := inter_eq_left.2 fun ω _ => by
        change min ((D.RC.T N ω : ℝ≥0) : WithTop ℝ≥0) (q : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)
        exact (min_le_right _ _).trans (by exact_mod_cast hqi)
      rw [e]; exact 𝓖.mono hqi _ (hB𝓖 N)
    · have e : B N ∩ {ω | dyStop D.RC n k N ω ≤ (i : WithTop ℝ≥0)} = ∅ := by
        refine eq_empty_of_forall_notMem fun ω hω => hqi ?_
        have h1 : dyStop D.RC n k N ω ≤ (i : WithTop ℝ≥0) := hω.2
        have h2 : (dyStop D.RC n k N ω) = (q : WithTop ℝ≥0) := by
          change min ((D.RC.T N ω : ℝ≥0) : WithTop ℝ≥0) (q : WithTop ℝ≥0) = (q : WithTop ℝ≥0)
          exact min_eq_right (by exact_mod_cast hω.1.2)
        rw [h2] at h1
        exact_mod_cast h1
      rw [e]; exact @MeasurableSet.empty _ (𝓖 i)
  have hBq : ∀ N, ∀ ω ∈ B N, (dyStop D.RC n k N ω).untopD 0 = q := fun N ω hω => by
    rw [D.dyStop_untopD]; exact min_eq_right hω.2
  -- `f` is bounded and measurable
  have hfm : Measurable f := Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    ((LQGMetric.measurable_distOn_apply ψ).comp (measurable_shiftField D.measurable_field))))
  have hfint : Integrable f D.tilt :=
    Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  -- the identity on each part
  have hpart : ∀ N, ∀ᵐ ω ∂D.tilt, ω ∈ B N →
      D.tilt[f | (D.isStoppingTime_dyStop n k N).measurableSpace] ω = g ω := by
    intro N
    filter_upwards [D.ae_condExp_tilt_dyStop n k N ψ] with ω hω hωB
    have hq := hBq N ω hωB
    have hdis : Disjoint (tsupport ψ) (fwdHull (Ito.rpath (D.RC.W · ω)) ((dyStop D.RC n k N ω).untopD 0 : ℝ≥0)) := by
      rw [hq]; exact (hAav hωB.1).2
    rw [hω hdis, hq, hg, cfAt_one_eq_cfVal]
  have heqN : ∀ N, ∫ ω in B N, f ω ∂D.tilt = ∫ ω in B N, g ω ∂D.tilt := by
    intro N
    have hτ := D.isStoppingTime_dyStop n k N
    rw [← setIntegral_condExp hτ.measurableSpace_le hfint (hBτ N)]
    exact setIntegral_congr_ae (hBm N) (hpart N)
  -- `g` is integrable on the union
  have hmono : Monotone B := fun N N' hNN' ω hω =>
    ⟨hω.1, hω.2.trans (D.RC.announcing.2.1 ω hNN')⟩
  have hgm : AEStronglyMeasurable g (D.tilt.restrict (⋃ N, B N)) := by
    refine aestronglyMeasurable_iUnion_iff.2 fun N => ?_
    have hτ := D.isStoppingTime_dyStop n k N
    have hc : AEStronglyMeasurable (D.tilt[f | hτ.measurableSpace]) (D.tilt.restrict (B N)) :=
      (stronglyMeasurable_condExp.mono hτ.measurableSpace_le).aestronglyMeasurable
    refine hc.congr ?_
    rw [EventuallyEq, ae_restrict_iff' (hBm N)]
    exact hpart N
  have hgb : ∀ ω ∈ A, ‖g ω‖ ≤ 1 := fun ω hω => by
    rw [hg, cfAt_one_eq_cfVal, LocalExt.norm_cfVal]
    have hw : Continuous (Ito.rpath (D.RC.W · ω)) := (D.RC.continuous ω).comp continuous_real_toNNReal
    have hw0 : Ito.rpath (D.RC.W · ω) 0 = 0 := by simp [Ito.rpath, D.RC.zero ω]
    have hE := Coupling.loewnerGreenEnergy_nonneg hw hw0 q.coe_nonneg ψ (hAav hω).2
    rw [Real.exp_le_one_iff]
    linarith
  have hBA : (⋃ N, B N) ⊆ A := iUnion_subset fun N => inter_subset_left
  have hgint : IntegrableOn g (⋃ N, B N) D.tilt := by
    refine Integrable.of_bound hgm 1 ?_
    rw [ae_restrict_iff' (MeasurableSet.iUnion hBm)]
    exact ae_of_all _ fun ω hω => hgb ω (hBA hω)
  have hlimf := tendsto_setIntegral_of_monotone hBm hmono hfint.integrableOn
  have hlimg := tendsto_setIntegral_of_monotone hBm hmono hgint
  have hU : ∫ ω in ⋃ N, B N, f ω ∂D.tilt = ∫ ω in ⋃ N, B N, g ω ∂D.tilt :=
    tendsto_nhds_unique (hlimf.congr heqN) hlimg
  -- the union is `A` up to a null set
  have hAU : (⋃ N, B N : Set S) =ᵐ[D.tilt] A := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [D.tilt_ac.ae_le D.RC.announcing.2.2.2] with ω hω
    refine ⟨fun h => hBA h, fun h => ?_⟩
    obtain ⟨N, hN⟩ := hω q (hAav h).1
    exact mem_iUnion.2 ⟨N, h, hN⟩
  rw [← setIntegral_congr_set hAU, ← setIntegral_congr_set hAU]
  exact hU

/-- The reference processes are regular before the clock (`IsForceReg`). -/
theorem isForceReg (ω : S) : Restart.DomainMarkov.Aux79.IsForceReg D.RC.W D.VL D.VR D.RC.e ω :=
  ⟨D.RC.zero ω, (D.RC.continuous ω).continuousOn,
    fun i => (isForcePath_geomLW D.RC.continuous _ ω i).1.continuousOn,
    fun j => (isForcePath_geomRW D.RC.continuous _ ω j).1.continuousOn,
    fun t _ => ⟨fun i => geomLW_le D.RC.continuous _ ω t i, fun j => le_geomRW D.RC.continuous _ ω t j⟩⟩

/-- **The reference kernel at every stop under the tilt** (the landed dyadic argument,
`StoppedK2.isCouplingCharFun_of_dyadic_reg`). -/
theorem isCouplingCharFun_tilt : Coupling.MartMeans.IsCouplingCharFun D.κ (flowLineRhoL D.κ D.bR D.JR D.CS.y 0)
    (flowLineRhoR D.κ D.bR D.JR D.CS.y 0) D.tilt (drivingFiltration D.tilt D.RC.killed) D.RC.W D.VL D.VR D.RC.e
    (shiftField D.field D.q D.Fq) :=
  Restart.StoppedK2.isCouplingCharFun_of_dyadic_reg D.RC.killed _
    (fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp (measurable_shiftField D.measurable_field))
    D.isDyadicSampled_tilt (ae_of_all _ D.isForceReg)

/-- **The actual kernel for the chosen cutoff at every stop before the clock** (the reverse tilt of
`isCouplingCharFun_tilt`). -/
theorem kernel_Fq (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime D.CS.driving τ)
    (hτe : ∀ᵐ ω ∂D.CS.P, (τ ω : ℝ≥0∞) < D.RC.e ω) (u : S → ℂ → ℝ)
    (hu : ∀ ω, RefExt D.κ D.bR D.JR D.RC.W ((τ ω).untopD 0) ω (u ω)) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂D.CS.P, Disjoint (tsupport ψ) (fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) →
      D.CS.P[fun ω' => Complex.exp (Complex.I * (D.field ω' ψ : ℂ)) | hτ.measurableSpace] ω =
        cfVal (∫ z, meanF D.κ (u ω) D.q D.Fq (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) ψ) := by
  have hτ' : IsStoppingTime (drivingFiltration D.tilt D.RC.killed) τ := D.driving_eq_tilt ▸ hτ
  have hms : hτ.measurableSpace = hτ'.measurableSpace := measurableSpace_congr D.driving_eq_tilt hτ hτ'
  have hτeQ : ∀ᵐ ω ∂D.tilt, (τ ω : ℝ≥0∞) < D.RC.e ω := D.tilt_ac.ae_le hτe
  have hcf := D.isCouplingCharFun_tilt τ hτ' hτeQ u (fun ω => bhe_of_refExt D.y_zero (hu ω))
  have hKb : ∀ᵐ ω ∂D.CS.P, closure (fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) ⊆ D.buffer :=
    D.ae_hull_buffer_of_lt (hτe.mono fun ω h => Restart.FlowStopIdentCM.coe_untopD_lt h)
  have : IsProbabilityMeasure (D.CS.P.withDensity fun ω => ENNReal.ofReal (D.kc * Real.exp (-D.Λ ω))) :=
    D.isProbabilityMeasure_tilt
  refine ae_condExp_tilt_rev (t := fun ω => (τ ω).untopD 0) hτ.measurableSpace_le D.measurable_field
    D.continuousOn_q D.cut_spec.2.1 D.cut_spec.2.2 D.buffer_open D.zero_mem D.buffer_sub D.RC.zero D.RC.continuous
    hKb (fun ω => (hu ω).1) (fun ω => (hu ω).2.1) D.measurable_Λ D.ae_tendsto_Λ D.kc_pos (fun φ => ?_) ψ
  filter_upwards [hcf φ] with ω hω hdis
  have h1 := hω hdis
  rw [← hms] at h1
  exact h1

end DyActFibre

end InteractingSLE.Sec5.Aux61Act
