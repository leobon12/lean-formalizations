/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowLocalityGenKernelL1

/-!
# Flow locality with a general agreement set: the conditional tilt with retained pockets at a bounded stop

Packet PROVE-G7A-LOC (PROVE-G3RESTART §5.2, steps 1–4 and 6, and §6.4). At a bounded stop `τ` of the original
driving filtration before the buffer exit, under the tilt `Q* = k e^{−Λ} · Q₀`, the shifted chart field has, off the
filled hull, the kernel with mean `∫ M^b_τ φ − greenCross_τ(φ, 1_{ℍ∖K_τ} F_y.src) + T_y(φ)` and the frozen Green
variance. Only the ALIVE part of the source enters (the pocket part has zero covariance with `φ`), and the in-pocket
conditional means cancel:

1. the retained-range kernel (`WholeField.retainedRangeKernelTraceStatement`, Aux. lemma 16 for `κ < 4`) along the
   trace `Γ − y`, hence the joint Gaussian law of `(h'(φ), h'(s'_k))` (`RLC.G7aTilt.ae_condExp_joint_of_rangeKer`);
2. the tilt limit without the in-pocket means (`RLC.G7aTilt.ae_condExp_tilt_of_joint_limit`), with `L¹` convergence
   of the densities (`GSetting.tendsto_eLpNorm_exp_neg_chart`) and of the cross covariances
   (`tendsto_zeroGFFTestCov_of_alive`);
3. Bayes with an unknown normalizer (`ae_condExp_withDensity_eq_of_tilt`);
4. the mean of the retained kernel against `φ` agrees (mod `2π`, which is all `cfVal` sees) with the frozen coupling
   mean, by comparing with the frozen off-hull kernel; the variance is the frozen energy
   (`zeroGFFTestCov_self_eq_of_alive`).

Main result: **`GSetting.ae_condExp_chart_tilt_bdd`**.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowLocalityGen
open QuantumZipper (H Hbar fwdHull)
open LQGMetric (TestOn DistOn)
open FlowStopIdentCMI

namespace GSetting
variable {S : Type u} [MeasurableSpace S] (D : GSetting S)

/-- The `b`-word's bounded harmonic extension at the actual mark positions at time `t`. -/
def ubAt (t : S → ℝ≥0) (ω : S) : ℂ → ℝ :=
  MartChar.meanExt D.κ (flowLineRhoL D.κ D.b D.J D.y D.θ) (flowLineRhoR D.κ D.b D.J D.y D.θ)
    (D.W₀ (t ω) ω) (fun i => D.VL₀ i (t ω) ω) (fun j => D.VR₀ j (t ω) ω)

/-- **The conditional tilt with retained pockets, at a bounded stop.** -/
theorem ae_condExp_chart_tilt_bdd (τ : S → ℝ≥0) (hτ : IsStoppingTime D.driving fun ω => (τ ω : WithTop ℝ≥0))
    (hN : ∃ N : ℝ≥0, ∀ ω, τ ω ≤ N)
    (hτx : ∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω)) {W₁ : ℝ≥0 → S → ℝ}
    (hW₁ : ∀ᵐ ω ∂D.Q₀, Continuous (W₁ · ω) ∧ ∃ t₂ : ℝ, (τ ω : ℝ) < t₂ ∧
      ∀ r ∈ Icc (0 : ℝ) t₂, Ito.rpath (W₁ · ω) r = Ito.rpath (D.W₀ · ω) r)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂D.tilt, Disjoint (tsupport φ) (fwdHull (Ito.rpath (W₁ · ω)) (τ ω)) →
      D.tilt[fun ω' => Complex.exp (Complex.I * (D.chartField ω' φ : ℂ)) | hτ.measurableSpace] ω =
        LocalExt.cfVal ((∫ z, couplingMean D.κ (Ito.rpath (D.W₀ · ω)) (τ ω) (D.ubAt τ ω) z * φ z) -
          LocalExt.greenCross (Ito.rpath (W₁ · ω)) (τ ω) φ
            ((H \ fwdHull (Ito.rpath (W₁ · ω)) (τ ω)).indicator (D.F.shift D.y).src) +
          chartShift D.F D.q D.y φ) (loewnerGreenEnergy (Ito.rpath (D.W₀ · ω)) (τ ω) φ) := by
  classical
  let _ := D.Q₀_prob
  set P := D.Q₀ with hP
  have hm : hτ.measurableSpace ≤ _ := hτ.measurableSpace_le
  set c : ℝ := D.θ * QuantumZipper.chiC D.κ with hc
  set I₀ : ℝ := ∫ z, D.F.src z with hI₀
  set s' : ℕ → TestOn upperHalfPlaneOpens := fun n => chartTest D.y (D.s n) with hs'
  set Λ' : S → ℝ := fun x => D.Λ x + c * I₀ with hΛ'def
  set k' : ℝ := D.k * Real.exp (c * I₀) with hk'def
  have hΛ'm : Measurable Λ' := D.Λ_measurable.add_const _
  have hk' : 0 < k' := mul_pos D.k_pos (Real.exp_pos _)
  have hdens : (fun x => ENNReal.ofReal (k' * Real.exp (-Λ' x))) =
      fun x => ENNReal.ofReal (D.k * Real.exp (-D.Λ x)) := by
    funext x
    congr 1
    simp only [hk'def, hΛ'def, neg_add, Real.exp_add]
    rw [show D.k * Real.exp (c * I₀) * (Real.exp (-D.Λ x) * Real.exp (-(c * I₀))) =
      D.k * Real.exp (-D.Λ x) * (Real.exp (c * I₀) * Real.exp (-(c * I₀))) by ring, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, mul_one]
  have hint' : Integrable (fun x => Real.exp (-Λ' x)) P := by
    refine ((integrable_exp_neg_of_prob D.Λ_measurable D.k_pos D.tilt_prob).const_mul
      (Real.exp (-(c * I₀)))).congr (ae_of_all _ fun x => ?_)
    simp only [hΛ'def, neg_add, Real.exp_add]; ring
  -- integrability of the approximating densities
  have hints : ∀ n, ∫ z, s' n z = ∫ z, D.s n z := fun n => by
    simp only [hs', chartTest_apply]
    exact integral_add_right_eq_self (fun z => D.s n z) (D.y : ℂ)
  have htr : ∀ x n, D.h' x (s' n) = D.H₀ x (D.s n) + c * ∫ z, D.s n z := fun x n => by
    rw [D.translate x (D.s n) (s' n) fun z => chartTest_apply D.y (D.s n) z, hints]
  obtain ⟨B, hB⟩ := exists_integral_exp_neg_two_le D.b_pc D.H₀_gff D.F D.s_bound
  have hYm : ∀ n, Measurable fun x => D.h' x (s' n) := fun n =>
    (LQGMetric.measurable_distOn_apply _).comp D.coupling.2.1
  have hintk : ∀ n, Integrable (fun x => Real.exp (-D.h' x (s' n))) P := by
    intro n
    have h2 : Integrable (fun x => 1 + Real.exp (-2 * D.H₀ x (D.s n)) * Real.exp (-2 * (c * ∫ z, D.s n z))) P :=
      (integrable_const 1).add ((hB n).1.mul_const _)
    refine h2.mono' (Real.measurable_exp.comp (hYm n).neg).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, htr]
    rcases le_or_gt 0 (D.H₀ x (D.s n) + c * ∫ z, D.s n z) with h | h
    · have : Real.exp (-(D.H₀ x (D.s n) + c * ∫ z, D.s n z)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      linarith [Real.exp_pos (-2 * D.H₀ x (D.s n) + -2 * (c * ∫ z, D.s n z))]
    · have : Real.exp (-(D.H₀ x (D.s n) + c * ∫ z, D.s n z)) ≤
          Real.exp (-2 * D.H₀ x (D.s n) + -2 * (c * ∫ z, D.s n z)) := Real.exp_le_exp.2 (by linarith)
      linarith
  have hL1 := D.tendsto_eLpNorm_exp_neg_chart
  -- the trace, the area and the retained-range kernel
  have hτU : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < D.U ω := hτx.mono fun ω h => h.trans_le (min_le_left _ _)
  have hRK := WholeField.retainedRangeKernelTraceStatement D.κ D.κ_pos D.κ_lt_four _ _ _ _
    (Theorem15.isOrderedForceWord_flowLine D.b D.J D.y) D.Q₀ D.filt D.W₀ D.VL₀ D.VR₀ D.B₀ D.U D.h' D.coupling
    (D.trace.mono fun ω h => ⟨_, h⟩) D.killed
  obtain ⟨M, -, hMk⟩ := hRK τ hτ hN hτU
  set V : S → Set ℂ := fun ω => H \ (fun t => D.Γ ω t - D.y) '' Icc 0 (τ ω) with hVdef
  have hker : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      P[fun ω' => Complex.exp (Complex.I * (D.h' ω' χ : ℂ)) | hτ.measurableSpace] ω =
        WholeField.rangeKerCF (M ω) (V ω) χ := fun χ => by
    filter_upwards [hMk χ, D.trace, hτU] with ω h1 h2 h3
    exact h1 _ (LP.isGeneratingTrace_mono h2 h3.le)
  have hV : ∀ᵐ ω ∂P, IsOpen (V ω) ∧ V ω ⊆ H := by
    filter_upwards [D.trace, hτU] with ω hg hlt
    have hcpt : IsCompact ((fun t => D.Γ ω t - D.y) '' Icc 0 (τ ω)) :=
      isCompact_Icc.image_of_continuousOn (hg.2.1.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hlt.le)
    exact ⟨(isOpen_lt continuous_const Complex.continuous_im).sdiff hcpt.isClosed, sdiff_subset⟩
  have harea : ∀ᵐ ω ∂P, volume ((fun t => D.Γ ω t - D.y) '' Icc 0 (τ ω) ∩ H) = 0 := by
    filter_upwards [D.trace, hτU, D.coupling.1.ae_dimH_image_inter_H_le D.κ_pos
      (by linarith [D.κ_lt_four])] with ω hg hlt hdim
    refine InteractingSLE.volume_eq_zero_of_dimH_lt_two (lt_of_le_of_lt (hdim _ hg (Icc 0 (τ ω))
      fun s hs => le_trans (ENNReal.coe_le_coe.2 hs.2) hlt.le) ?_)
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (Dimension.interiorDimBound_lt_two
      (by linarith [D.κ_lt_four]))
  -- the alive part of the source
  set Dφ : Set S := {ω | Disjoint (tsupport φ) (fwdHull (Ito.rpath (W₁ · ω)) (τ ω))} with hDφ
  set src' : ℂ → ℝ := (D.F.shift D.y).src with hsrc'
  set s₁₂ : S → ℝ := fun ω => LocalExt.greenCross (Ito.rpath (W₁ · ω)) (τ ω) φ
    ((H \ fwdHull (Ito.rpath (W₁ · ω)) (τ ω)).indicator src') with hs₁₂
  have hs'le : ∀ n z, |s' n z| ≤ |src' z| := fun n z => by
    rw [hs', chartTest_apply, hsrc', CMCut.src_shift]; exact D.s_bound n _
  have hs'lim : ∀ z, Tendsto (fun n => s' n z) atTop (𝓝 (src' z)) := fun z => by
    simp only [hs', chartTest_apply, hsrc', CMCut.src_shift]; exact D.s_limit _
  obtain ⟨Cs, -, hCs⟩ := (D.F.shift D.y).exists_abs_src_le
  have hsK : ∀ z, src' z ≠ 0 →
      z ∈ tsupport (QuantumZipper.K3.greenDensity (D.F.shift D.y).f) ∩ Hbar := fun z hz => by
    obtain ⟨hzH, hzt⟩ := (D.F.shift D.y).mem_of_src_ne_zero hz
    exact ⟨hzt, show (0 : ℝ) ≤ z.im from le_of_lt hzH⟩
  have hs : ∀ᵐ ω ∂P, ω ∈ Dφ → Tendsto (fun k => QuantumZipper.zeroGFFTestCov (V ω) φ (s' k)) atTop (𝓝 (s₁₂ ω)) := by
    filter_upwards [D.trace, hτU, harea, hW₁, D.coupling.1.ae_isIntegratedSLEPath] with ω hg hlt ha hw hp hωD
    obtain ⟨hc, t₂, ht₂, hag⟩ := hw
    exact tendsto_zeroGFFTestCov_of_alive hg hp.2.2.2.1 hp.1 hlt ha (hc.comp continuous_real_toNNReal) ht₂ hag φ
      hωD (D.F.shift D.y).measurable_src hCs
      ((D.F.shift D.y).hasCompactSupport_greenDensity.isCompact.inter_right
        (isClosed_le continuous_const Complex.continuous_im)) inter_subset_right hsK hs'le hs'lim
  -- the tilt identity and Bayes
  have hjoint := fun k (a b : ℝ) => (RLC.G7aTilt.ae_condExp_joint_of_rangeKer hV hker φ (s' k) a b).mono
    fun ω h (_ : ω ∈ Dφ) => h
  have hXm : Measurable fun x => D.h' x φ := (LQGMetric.measurable_distOn_apply φ).comp D.coupling.2.1
  have htl := RLC.G7aTilt.ae_condExp_tilt_of_joint_limit (Y := fun k x => D.h' x (s' k)) hm hXm hYm hΛ'm hintk
    hint' hL1 hjoint hs
  have hXcm : AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (D.h' ω φ : ℂ))) P :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hXm))).aestronglyMeasurable
  have hXb : ∀ ω, ‖Complex.exp (Complex.I * (D.h' ω φ : ℂ))‖ ≤ 1 := fun ω => by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hbayes := ae_condExp_withDensity_eq_of_tilt hm hΛ'm hint' hk' hXcm hXb htl
  rw [hdens] at hbayes
  -- the frozen off-hull kernel
  obtain ⟨hX', hcf⟩ := D.coupling.exists_isCouplingCharFun
  have hubH : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.b D.J D.y D.θ) (flowLineRhoR D.κ D.b D.J D.y D.θ)
        (fun i => D.VL₀ i (((τ ω : WithTop ℝ≥0)).untopD 0) ω - D.W₀ (((τ ω : WithTop ℝ≥0)).untopD 0) ω)
        (fun j => D.VR₀ j (((τ ω : WithTop ℝ≥0)).untopD 0) ω - D.W₀ (((τ ω : WithTop ℝ≥0)).untopD 0) ω))
      (forceJumpSet
        (fun i => D.VL₀ i (((τ ω : WithTop ℝ≥0)).untopD 0) ω - D.W₀ (((τ ω : WithTop ℝ≥0)).untopD 0) ω)
        (fun j => D.VR₀ j (((τ ω : WithTop ℝ≥0)).untopD 0) ω - D.W₀ (((τ ω : WithTop ℝ≥0)).untopD 0) ω))
      (D.ubAt τ ω) := fun ω => MartChar.isBoundedHarmonicExtension_meanExt D.κ _ _ _ _ _
  have hfr := hcf (fun ω => (τ ω : WithTop ℝ≥0)) hτ hτU (D.ubAt τ) hubH φ
  -- assembly
  have hQP : D.tilt ≪ P := D.tilt_equivalent.1
  have hsm : D.tilt[fun ω' => Complex.exp (Complex.I * (D.chartField ω' φ : ℂ)) | hτ.measurableSpace] =ᵐ[D.tilt]
      fun ω => Complex.exp (Complex.I * (chartShift D.F D.q D.y φ : ℂ)) •
        D.tilt[fun ω' => Complex.exp (Complex.I * (D.h' ω' φ : ℂ)) | hτ.measurableSpace] ω := by
    have e := condExp_smul (μ := D.tilt) (m := hτ.measurableSpace)
      (Complex.exp (Complex.I * (chartShift D.F D.q D.y φ : ℂ))) fun ω' => Complex.exp (Complex.I * (D.h' ω' φ : ℂ))
    have hf : (fun ω' => Complex.exp (Complex.I * (D.chartField ω' φ : ℂ))) =
        Complex.exp (Complex.I * (chartShift D.F D.q D.y φ : ℂ)) •
          fun ω' => Complex.exp (Complex.I * (D.h' ω' φ : ℂ)) := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
      congr 1
      show Complex.I * ((D.h' ω' φ + chartShift D.F D.q D.y φ : ℝ) : ℂ) = _
      push_cast; ring
    rw [hf]
    exact e
  filter_upwards [hsm, hbayes, hQP.ae_le hfr, hQP.ae_le (hker φ), hQP.ae_le D.trace, hQP.ae_le hτU,
    hQP.ae_le harea, hQP.ae_le hW₁, hQP.ae_le D.coupling.1.ae_isIntegratedSLEPath] with ω e1 e2 e3 e4 hg hlt ha hw hp
    hωD
  obtain ⟨hc, t₂, ht₂, hag⟩ := hw
  have ht0 : (0 : ℝ) ≤ τ ω := NNReal.coe_nonneg _
  have hK : fwdHull (Ito.rpath (D.W₀ · ω)) (τ ω) = fwdHull (Ito.rpath (W₁ · ω)) (τ ω) :=
    (InteractingSLE.fwdHull_eq_of_eqOn ht0 ht₂ hag).symm
  have hωD' : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => D.W₀ s.toNNReal ω) (τ ω)) := by
    change Disjoint (tsupport φ) (fwdHull (Ito.rpath (D.W₀ · ω)) (τ ω))
    rw [hK]; exact hωD
  have hE : QuantumZipper.zeroGFFTestCov (V ω) φ φ = loewnerGreenEnergy (Ito.rpath (D.W₀ · ω)) (τ ω) φ := by
    rw [zeroGFFTestCov_self_eq_of_alive hg hp.2.2.2.1 hp.1 hlt ha (hc.comp continuous_real_toNNReal) ht₂ hag φ hωD]
    exact StoppedK2.loewnerGreenEnergy_congr_Icc (fun r hr => hag r ⟨hr.1, hr.2.trans ht₂.le⟩) φ
  -- the means agree modulo `2π`
  have hcf1 : LocalExt.cfVal (M ω φ) (loewnerGreenEnergy (Ito.rpath (D.W₀ · ω)) (τ ω) φ) =
      LocalExt.cfVal (∫ z, couplingMean D.κ (Ito.rpath (D.W₀ · ω)) (τ ω) (D.ubAt τ ω) z * φ z)
        (loewnerGreenEnergy (Ito.rpath (D.W₀ · ω)) (τ ω) φ) := by
    rw [← hE, ← RLC.G7aTilt.rangeKerCF_eq_cfVal, ← e4, hE]
    exact e3 hωD'
  have e2' : D.tilt[fun ω' => Complex.exp (Complex.I * (D.h' ω' φ : ℂ)) | hτ.measurableSpace] ω =
      LocalExt.cfVal (M ω φ - s₁₂ ω) (QuantumZipper.zeroGFFTestCov (V ω) φ φ) := e2 hωD
  rw [e1, e2', hE]
  have hsplit : ∀ a s q : ℝ, LocalExt.cfVal (a - s) q =
      Complex.exp (Complex.I * ((-s : ℝ) : ℂ)) * LocalExt.cfVal a q := fun a s q => by
    rw [FlowStopIdentCM.cexp_mul_cfVal, sub_eq_add_neg]
  rw [hsplit, hcf1, ← hsplit, smul_eq_mul, FlowStopIdentCM.cexp_mul_cfVal]

end GSetting

end InteractingSLE.Restart.FlowLocalityGen
