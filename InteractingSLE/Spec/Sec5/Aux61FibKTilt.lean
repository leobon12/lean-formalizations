/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibKRaw

/-!
# The kernel at deterministic dyadic times gives the kernel at every stop

Packet PROVE-AUX61-FIB2. For a `RawActFibre` (the kernel only at the deterministic dyadic times `q` on `{q < e}`):

* `condExp_cond_ae_eq`: conditioning on an event `D ∈ m` does not change the conditional expectation given `m` on `D`;
* **`setIntegral_tilt_eq_of_restrict`** (the Cameron–Martin tilt restricted to an event): if the actual kernel
  `meanF κ u q Fq` holds at `(m, t)` only on an event `D ∈ m` on which the hulls up to `t` lie in the buffer, then under
  `k e^{−Λ} · P` the shifted field `h + (Fq − q)` satisfies the reference-kernel identity on every `A ∈ m` inside
  `D ∩ {supp φ ∩ K_t = ∅}` (proof: `Aux61Act.ae_condExp_tilt_fwd` under the conditioned law `P[·|D]`);
* **`RawActFibre.isDyadicSampled_tilt`**: under the tilt, the reference word's dyadic law `IsDyadicSampled` (an event
  `A` at the dyadic time `q` inside the avoidance event lies in `{q < e}`, where the restricted tilt applies with the
  deterministic time `q` — no announcing stops, no exhaustion);
* `RawActFibre.isCouplingCharFun_tilt` (the landed `StoppedK2.isCouplingCharFun_of_dyadic_reg`), **`kernel_Fq`** (the
  reverse tilt `Aux61Act.ae_condExp_tilt_rev`), **`kernel`** (every cutoff, `Aux61Act.integral_meanF_congr_cut`);
* **`RawActFibre.toDyActFibre`**: a `RawActFibre` is an `Aux61Act.DyActFibre` with the same law, word, path and clock.

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
open Restart.FlowStopIdentCMI (CMCut geomL geomR)
open Aux61Win (meanF IsCutoffOn)
open Aux61R2 (RefExt)
open Aux61Act (shiftField)
open Sec7.PocketTraversal

universe u

/-! ### Conditioning on an event of the σ-algebra -/

section Cond

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Conditioning on an event `D` of `m` does not change the conditional expectation given `m` on `D`.** -/
theorem condExp_cond_ae_eq [IsFiniteMeasure P] (hm : m ≤ mΩ) {D : Set Ω} (hD : MeasurableSet[m] D)
    {f : Ω → ℂ} (hf : Integrable f P) : (P[|D])[f | m] =ᵐ[P[|D]] P[f | m] := by
  by_cases h0 : P D = 0
  · rw [cond_eq_zero_of_meas_eq_zero h0, EventuallyEq, ae_zero]
    exact eventually_bot
  have hc : (P D)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 h0
  have : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure h0
  have hPD : P[|D] = (P D)⁻¹ • P.restrict D := rfl
  set μ' := P.restrict D with hμ'
  have h1 : μ'[f | m] =ᵐ[μ'] P[f | m] := condExp_restrict_ae_eq_restrict hm hD hf
  have hint : Integrable f (P[|D]) := by rw [hPD]; exact hf.restrict.smul_measure hc
  have h2 : μ'[f | m] =ᵐ[P[|D]] (P[|D])[f | m] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hint (fun s _ _ => ?_) (fun s hs _ => ?_) ?_
    · rw [hPD]; exact (integrable_condExp.smul_measure hc).integrableOn
    · rw [hPD, Measure.restrict_smul, integral_smul_measure, integral_smul_measure,
        setIntegral_condExp hm hf.restrict hs]
    · exact stronglyMeasurable_condExp.aestronglyMeasurable
  have hac : P[|D] ≪ μ' := by rw [hPD]; exact Measure.smul_absolutelyContinuous
  exact h2.symm.trans (hac.ae_le h1)

end Cond

/-! ### The Cameron–Martin tilt restricted to an event -/

section Restrict

variable {S : Type*} {m : MeasurableSpace S} [mS : MeasurableSpace S] {P : Measure S} [IsProbabilityMeasure P]
  {κ : ℝ} {field : S → DistOn upperHalfPlaneOpens}
  {q : ℂ → ℝ} {O₀ : Set ℝ} {Fq : CMCut} {Nq : Set ℂ} {Cq : ℝ} {buffer : Set ℂ}
  {W : ℝ≥0 → S → ℝ} {t : S → ℝ≥0} {u : S → ℂ → ℝ}

omit [IsProbabilityMeasure P] in
/-- Set integrals over a part of `D` under a density with respect to the conditioned law. -/
theorem setIntegral_withDensity_cond {D A : Set S} (hD : MeasurableSet D) (hAD : A ⊆ D) (ρ : S → ℝ≥0∞)
    (g : S → ℂ) :
    ∫ ω in A, g ω ∂((P[|D]).withDensity ρ) = ((P D)⁻¹).toReal • ∫ ω in A, g ω ∂(P.withDensity ρ) := by
  have e : (P[|D]).withDensity ρ = (P D)⁻¹ • (P.withDensity ρ).restrict D := by
    have hPD : P[|D] = (P D)⁻¹ • P.restrict D := rfl
    rw [hPD, withDensity_smul_measure, restrict_withDensity hD]
  rw [e, Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict' hD, inter_eq_left.2 hAD]

/-- **The Cameron–Martin tilt of a kernel known on an event** (`Aux61Act.ae_condExp_tilt_fwd` under the conditioned
law `P[·|D]`): if the actual kernel `meanF κ u q Fq` holds at `(m, t)` almost surely on an event `D ∈ m` on which the
hulls up to `t` lie in the buffer, then under `k e^{−Λ} · P` the shifted field `h + (Fq − q)` has, on every event
`A ∈ m` inside `D` on which `φ` avoids the hull, the set integral of the reference kernel `couplingMean κ · t u`. -/
theorem setIntegral_tilt_eq_of_restrict (hm : m ≤ mS) (hfm : Measurable field) (hq : ContinuousOn q H)
    (hcut : IsCutoffOn Fq q Nq O₀) (hqb : ∀ z, Fq.src z ≠ 0 → |q z| ≤ Cq) (hbo : IsOpen buffer)
    (hb0 : (0 : ℂ) ∈ buffer) (hbN : buffer ⊆ Nq) (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous (W · ω))
    {D : Set S} (hD : MeasurableSet[m] D)
    (hKb : ∀ᵐ ω ∂P, ω ∈ D → closure (fwdHull (Ito.rpath (W · ω)) (t ω)) ⊆ buffer)
    (hu : ∀ ω, InnerProductSpace.HarmonicOnNhd (u ω) H) (hub : ∀ ω, ∃ C : ℝ, ∀ z ∈ H, |u ω z| ≤ C)
    (hker : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ D →
      Disjoint (tsupport ψ) (fwdHull (Ito.rpath (W · ω)) (t ω)) →
      P[fun ω' => Complex.exp (Complex.I * (field ω' ψ : ℂ)) | m] ω =
        cfVal (∫ z, meanF κ (u ω) q Fq (Ito.rpath (W · ω)) (t ω) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (W · ω)) (t ω) ψ))
    {Λ : S → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ ω ∂P, Tendsto (fun n => field ω (Fq.neg.testSeq n)) atTop (𝓝 (Λ ω)))
    (hint : Integrable (fun ω => Real.exp (-Λ ω)) P) {k : ℝ} (hk : 0 < k) (φ : TestOn upperHalfPlaneOpens)
    {A : Set S} (hA : MeasurableSet[m] A) (hAD : A ⊆ D)
    (hAφ : ∀ ω ∈ A, Disjoint (tsupport φ) (fwdHull (Ito.rpath (W · ω)) (t ω))) :
    ∫ ω in A, Complex.exp (Complex.I * (shiftField field q Fq ω φ : ℂ))
        ∂(P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))) =
      ∫ ω in A, cfVal (∫ z, couplingMean κ (Ito.rpath (W · ω)) (t ω) (u ω) z * φ z)
          (loewnerGreenEnergy (Ito.rpath (W · ω)) (t ω) φ)
        ∂(P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))) := by
  have hDm : MeasurableSet D := hm _ hD
  have hAm : MeasurableSet A := hm _ hA
  set ρ : S → ℝ≥0∞ := fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)) with hρ
  by_cases h0 : P D = 0
  · have hA0 : (P.withDensity ρ) A = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_mono_null hAD h0)
    rw [Measure.restrict_eq_zero.2 hA0, integral_zero_measure, integral_zero_measure]
  have hP' : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure h0
  have hcP : P[|D] ≪ P := cond_absolutelyContinuous
  have hDae : ∀ᵐ ω ∂(P[|D]), ω ∈ D := ae_cond_mem hDm
  have hKb' : ∀ᵐ ω ∂(P[|D]), closure (fwdHull (Ito.rpath (W · ω)) (t ω)) ⊆ buffer := by
    filter_upwards [hcP.ae_le hKb, hDae] with ω h1 h2 using h1 h2
  have hfint : ∀ ψ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω' => Complex.exp (Complex.I * (field ω' ψ : ℂ))) P := fun ψ =>
    Integrable.of_bound ((Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((LQGMetric.measurable_distOn_apply ψ).comp hfm)))).aestronglyMeasurable) 1
      (ae_of_all _ fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hker' : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂(P[|D]),
      Disjoint (tsupport ψ) (fwdHull (Ito.rpath (W · ω)) (t ω)) →
      (P[|D])[fun ω' => Complex.exp (Complex.I * (field ω' ψ : ℂ)) | m] ω =
        cfVal (∫ z, meanF κ (u ω) q Fq (Ito.rpath (W · ω)) (t ω) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (W · ω)) (t ω) ψ) := fun ψ => by
    filter_upwards [condExp_cond_ae_eq hm hD (hfint ψ), hcP.ae_le (hker ψ), hDae] with ω h1 h2 h3 hdis
    rw [h1, h2 h3 hdis]
  have hint' : Integrable (fun ω => Real.exp (-Λ ω)) (P[|D]) := by
    have hPD : P[|D] = (P D)⁻¹ • P.restrict D := rfl
    rw [hPD]
    exact hint.restrict.smul_measure (ENNReal.inv_ne_top.2 h0)
  have hfwd := Aux61Act.ae_condExp_tilt_fwd (P := P[|D]) (κ := κ) (t := t) (u := u) hm hfm hq hcut hqb hbo hb0
    hbN hW0 hWc hKb' hu hub hker' hΛm (hcP.ae_le hΛ) hint' hk φ
  have hQfin : IsFiniteMeasure ((P[|D]).withDensity ρ) :=
    isFiniteMeasure_withDensity_ofReal (hint'.const_mul k).2
  set f' : S → ℂ := fun ω => Complex.exp (Complex.I * (shiftField field q Fq ω φ : ℂ)) with hf'
  have hf'm : Measurable f' := Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    ((LQGMetric.measurable_distOn_apply φ).comp (Aux61Act.measurable_shiftField hfm))))
  have hf'int : Integrable f' ((P[|D]).withDensity ρ) :=
    Integrable.of_bound hf'm.aestronglyMeasurable 1 (ae_of_all _ fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have e1 : ∫ ω in A, f' ω ∂((P[|D]).withDensity ρ) =
      ∫ ω in A, cfVal (∫ z, couplingMean κ (Ito.rpath (W · ω)) (t ω) (u ω) z * φ z)
          (loewnerGreenEnergy (Ito.rpath (W · ω)) (t ω) φ) ∂((P[|D]).withDensity ρ) := by
    rw [← setIntegral_condExp hm hf'int hA]
    refine setIntegral_congr_ae hAm ?_
    filter_upwards [hfwd] with ω hω hωA using hω (hAφ ω hωA)
  rw [setIntegral_withDensity_cond hDm hAD, setIntegral_withDensity_cond hDm hAD] at e1
  have hc0 : ((P D)⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 (measure_ne_top _ _), ENNReal.inv_ne_top.2 h0⟩
  exact smul_right_injective ℂ hc0 e1

end Restrict

/-! ### The fibre: the dyadic law under the tilt, the kernel at every stop -/

/-- Equivalent laws have the same null sets. -/
theorem nullSets_congr {S : Type*} [MeasurableSpace S] {P Q : Measure S} (h1 : P ≪ Q) (h2 : Q ≪ P) :
    Ito.nullSets P = Ito.nullSets Q := by
  unfold Ito.nullSets
  congr 1
  ext s
  exact ⟨fun h => ⟨h.1, h2 h.2⟩, fun h => ⟨h.1, h1 h.2⟩⟩

namespace RawActFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : RawActFibre S)

/-- **The dyadic protected-kernel law of the reference word under the tilt**: an event `A` at the dyadic time
`q = k/2ⁿ` inside the avoidance event lies in `{q < e}` and in `𝓜 q`, where the restricted tilt of `rawKernel`
applies at the deterministic time `q`. -/
theorem isDyadicSampled_tilt : Restart.DomainMarkov.IsDyadicSampled D.κ D.RC.W D.ucf D.tilt D.RC.killed
    (shiftField D.field D.q D.Fq) := by
  intro ψ n k A hA hAav
  set q : ℝ≥0 := Restart.DomainMarkov.dyT n k with hqdef
  have hA𝓜 : MeasurableSet[D.𝓜 q] A := by
    refine D.raw_le q _ ?_
    rw [Ito.nullAugmented_apply] at hA ⊢
    rwa [nullSets_congr D.ac_tilt D.tilt_ac]
  have hcut := D.cut_spec.2.1
  have hker : ∀ ψ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂D.CS.P, ω ∈ {ω | (q : ℝ≥0∞) < D.RC.e ω} →
      Disjoint (tsupport ψ') (fwdHull (Ito.rpath (D.RC.W · ω)) ((fun _ => q) ω)) →
      D.CS.P[fun ω' => Complex.exp (Complex.I * (D.field ω' ψ' : ℂ)) | D.𝓜 q] ω =
        cfVal (∫ z, meanF D.κ (D.ucf ω q) D.q D.Fq (Ito.rpath (D.RC.W · ω)) ((fun _ => q) ω) z * ψ' z)
          (loewnerGreenEnergy (Ito.rpath (D.RC.W · ω)) ((fun _ => q) ω) ψ') := fun ψ' =>
    D.rawKernel D.Fq D.Nq hcut D.buffer_sub n k (fun ω => D.ucf ω q) (fun ω => D.refExt_ucf ω q) ψ'
  have hKb : ∀ᵐ ω ∂D.CS.P, ω ∈ {ω | (q : ℝ≥0∞) < D.RC.e ω} →
      closure (fwdHull (Ito.rpath (D.RC.W · ω)) ((fun _ => q) ω)) ⊆ D.buffer :=
    D.hull_buffer.mono fun ω h hω => h q hω
  have e := setIntegral_tilt_eq_of_restrict (m := D.𝓜 q) (P := D.CS.P) (t := fun _ => q)
    (u := fun ω => D.ucf ω q) (D.𝓜_le q) D.measurable_field D.continuousOn_q hcut D.cut_spec.2.2 D.buffer_open
    D.zero_mem D.buffer_sub D.RC.zero D.RC.continuous (D.measurableSet_lt_e q) hKb
    (fun ω => (D.refExt_ucf ω q).1) (fun ω => (D.refExt_ucf ω q).2.1) hker D.measurable_Λ D.ae_tendsto_Λ
    D.integrable_exp_neg_Λ D.kc_pos ψ hA𝓜 (fun ω hω => (hAav hω).1) (fun ω hω => (hAav hω).2)
  simp only [Aux61Act.cfAt_one_eq_cfVal]
  exact e

/-- **The reference kernel at every stop under the tilt** (the landed `StoppedK2.isCouplingCharFun_of_dyadic_reg`). -/
theorem isCouplingCharFun_tilt : Coupling.MartMeans.IsCouplingCharFun D.κ (flowLineRhoL D.κ D.bR D.JR D.CS.y 0)
    (flowLineRhoR D.κ D.bR D.JR D.CS.y 0) D.tilt (drivingFiltration D.tilt D.RC.killed) D.RC.W D.VL D.VR D.RC.e
    (shiftField D.field D.q D.Fq) :=
  Restart.StoppedK2.isCouplingCharFun_of_dyadic_reg D.RC.killed _
    (fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp (Aux61Act.measurable_shiftField D.measurable_field))
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
  have hms : hτ.measurableSpace = hτ'.measurableSpace :=
    Aux61Act.measurableSpace_congr D.driving_eq_tilt hτ hτ'
  have hτeQ : ∀ᵐ ω ∂D.tilt, (τ ω : ℝ≥0∞) < D.RC.e ω := D.tilt_ac.ae_le hτe
  have hcf := D.isCouplingCharFun_tilt τ hτ' hτeQ u (fun ω => Aux61Act.bhe_of_refExt D.y_zero (hu ω))
  have hKb : ∀ᵐ ω ∂D.CS.P, closure (fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) ⊆ D.buffer :=
    D.ae_hull_buffer_of_lt (hτe.mono fun ω h => Restart.FlowStopIdentCM.coe_untopD_lt h)
  have : IsProbabilityMeasure (D.CS.P.withDensity fun ω => ENNReal.ofReal (D.kc * Real.exp (-D.Λ ω))) :=
    D.isProbabilityMeasure_tilt
  refine Aux61Act.ae_condExp_tilt_rev (t := fun ω => (τ ω).untopD 0) hτ.measurableSpace_le D.measurable_field
    D.continuousOn_q D.cut_spec.2.1 D.cut_spec.2.2 D.buffer_open D.zero_mem D.buffer_sub D.RC.zero D.RC.continuous
    hKb (fun ω => (hu ω).1) (fun ω => (hu ω).2.1) D.measurable_Λ D.ae_tendsto_Λ D.kc_pos (fun φ => ?_) ψ
  filter_upwards [hcf φ] with ω hω hdis
  have h1 := hω hdis
  rw [← hms] at h1
  exact h1

/-- A reference extension in the geometric (`geomL`) form of the frozen (PC1). -/
theorem bhe_geomL_of_refExt {t : ℝ≥0} {ω : S} {u : ℂ → ℝ} (hu : RefExt D.κ D.bR D.JR D.RC.W t ω u) :
    IsBoundedHarmonicExtension
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR 0 0) (flowLineRhoR D.κ D.bR D.JR 0 0)
        (fun i => geomL (Ito.rpath (D.RC.W · ω)) t (flowLineXL D.bR D.JR 0 i))
        (fun j => geomR (Ito.rpath (D.RC.W · ω)) t (flowLineXR D.bR D.JR 0 j)))
      (forceJumpSet (fun i => geomL (Ito.rpath (D.RC.W · ω)) t (flowLineXL D.bR D.JR 0 i))
        (fun j => geomR (Ito.rpath (D.RC.W · ω)) t (flowLineXR D.bR D.JR 0 j))) u := by
  have e1 : (fun i => geomL (Ito.rpath (D.RC.W · ω)) t (flowLineXL D.bR D.JR 0 i)) =
      fun i => geomLW D.RC.W (fun _ => flowLineXL D.bR D.JR 0) i t ω - D.RC.W t ω :=
    funext fun i => Restart.FlowStopIdentCMI.geomL_rpath_eq_geomLW_sub D.RC.W _ i t ω
  have e2 : (fun j => geomR (Ito.rpath (D.RC.W · ω)) t (flowLineXR D.bR D.JR 0 j)) =
      fun j => geomRW D.RC.W (fun _ => flowLineXR D.bR D.JR 0) j t ω - D.RC.W t ω :=
    funext fun j => Restart.FlowStopIdentCMI.geomR_rpath_eq_geomRW_sub D.RC.W _ j t ω
  rw [e1, e2]
  exact hu

/-- **The kernel of a `RawActFibre` for every cutoff** of `q` near the buffer, at every stop before the clock
(`kernel_Fq` and the independence of the cutoff). -/
theorem kernel (F : CMCut) (N : Set ℂ) (hF : IsCutoffOn F D.q N D.O₀) (hbN : D.buffer ⊆ N)
    (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime D.CS.driving τ) (hτe : ∀ᵐ ω ∂D.CS.P, (τ ω : ℝ≥0∞) < D.RC.e ω)
    (u : S → ℂ → ℝ) (hu : ∀ ω, RefExt D.κ D.bR D.JR D.RC.W ((τ ω).untopD 0) ω (u ω))
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂D.CS.P, Disjoint (tsupport ψ) (fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) →
      D.CS.P[fun ω' => Complex.exp (Complex.I * (D.field ω' ψ : ℂ)) | hτ.measurableSpace] ω =
        cfVal (∫ z, meanF D.κ (u ω) D.q F (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0) ψ) := by
  have hKb : ∀ᵐ ω ∂D.CS.P, closure (fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) ⊆ D.buffer :=
    D.ae_hull_buffer_of_lt (hτe.mono fun ω h => Restart.FlowStopIdentCM.coe_untopD_lt h)
  filter_upwards [D.kernel_Fq τ hτ hτe u hu ψ, hKb, hτe, D.RC.trace] with ω h1 hK hlt htr hdis
  rw [h1 hdis]
  have htr' : IsGeneratingTrace (D.RC.W · ω) (D.RC.e ω) (D.CS.Γ ω) := by
    simpa only [D.y_zero, Complex.ofReal_zero, sub_zero] using htr
  have hlt' := Restart.FlowStopIdentCM.coe_untopD_lt hlt
  have hK' : closure (fwdHull (Ito.rpath (D.RC.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) ⊆ D.Nq ∩ N :=
    subset_inter (hK.trans D.buffer_sub) (hK.trans hbN)
  rw [Aux61Act.integral_meanF_congr_cut D.κ_pos D.bR_pc (D.RC.continuous ω) (D.RC.zero ω)
    (fun _ => Aux61Act.exists_trace_real htr' hlt') (D.bhe_geomL_of_refExt (hu ω)) D.continuousOn_q
    D.cut_spec.2.1 hF ⟨D.buffer_sub D.zero_mem, hbN D.zero_mem⟩ hK' ψ hdis]

/-- **A `RawActFibre` is a `DyActFibre`** (with the same law, word, clock source, reference clock and field): the
kernel at the stops `min(T_N, k/2ⁿ)` is the kernel at every stop before the clock. -/
def toDyActFibre : Aux61Act.DyActFibre S where
  κ := D.κ
  κ_pos := D.κ_pos
  bR := D.bR
  JR := D.JR
  bR_pc := D.bR_pc
  CS := D.CS
  y_zero := D.y_zero
  V := D.V
  RC := D.RC
  driving_eq := D.driving_eq
  field := D.field
  measurable_field := D.measurable_field
  q := D.q
  q_harm := D.q_harm
  O₀ := D.O₀
  O₀_open := D.O₀_open
  q_zero := D.q_zero
  buffer := D.buffer
  buffer_open := D.buffer_open
  zero_mem := D.zero_mem
  buffer_compact := D.buffer_compact
  buffer_real := D.buffer_real
  hull_buffer := D.hull_buffer
  dyKernel := by
    intro F N hF hbN τ hτ hτform u hu ψ
    obtain ⟨n, k, N', rfl⟩ := hτform
    refine D.kernel F N hF hbN _ hτ ?_ u hu ψ
    filter_upwards [D.RC.announcing.2.2.1 N'] with ω hω
    exact lt_of_le_of_lt (min_le_left _ _) hω
  members := D.members
  injective := D.injective

end RawActFibre

end InteractingSLE.Sec5.Aux61FibK
