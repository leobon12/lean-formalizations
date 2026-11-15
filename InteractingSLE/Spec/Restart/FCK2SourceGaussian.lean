/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2SourceWord
import InteractingSLE.Spec.Sec7.LocalExtKJoint

/-!
# Initial Gaussian data from retained conditional characteristic functions

At zero, the concrete retained-driver filtration is exactly the retained sigma
algebra. Clamping a Gaussian observable to an initial measurable event gives a
conditional Gaussian observable, with zero mean and variance off that event.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A zero-start driver adds no information to the retained past at time zero. -/
theorem fcRetainedDriverFiltration_zero {d : PairData Ω} (hd : d.IsMeasGood)
    (W : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (W t)) (h0 : ∀ ω, W 0 ω = 0) :
    fcRetainedDriverFiltration P hd W hm 0 = retSigma d P := by
  have he : fcDriverFiltration (retHist d) W hd.measurable_retHist hm 0 =
      MeasurableSpace.comap (retHist d) inferInstance := by
    apply le_antisymm
    · apply sup_le le_rfl
      refine iSup₂_le fun r hr => ?_
      have er : r = 0 := le_antisymm hr zero_le
      subst r
      rw [show W 0 = fun _ => 0 from funext h0, MeasurableSpace.comap_const]
      exact bot_le
    · exact le_sup_left
  change mΩ ⊓ LocalSets.aeSigma
    (fcDriverFiltration (retHist d) W hd.measurable_retHist hm 0) P = _
  rw [he]
  rfl

/-- A conditional Gaussian identity on an initial event gives the complete
conditional law of the event-clamped observable. No integrability of the
original observable is assumed. -/
theorem isCondGaussian_indicator_of_condCharFun [IsProbabilityMeasure P]
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) {B : Set Ω} (hB : MeasurableSet[𝒢] B)
    {X μ : Ω → ℝ} (hX : Measurable[mΩ] X) (hμ : Measurable[𝒢] μ)
    {v : ℝ} (hv : 0 ≤ v)
    (hc : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ B →
      P[fun ω => Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * ((t * μ ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (t ^ 2 * v)) : ℝ) : ℂ)) :
    @Sec6.Prop65.IsCondGaussian Ω 𝒢 mΩ P (B.indicator X) (B.indicator μ)
      (B.indicator fun _ => v) v := by
  classical
  let _ : MeasurableSpace Ω := mΩ
  refine ⟨h𝒢, hX.indicator (h𝒢 _ hB), hμ.indicator hB,
    measurable_const.indicator hB, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ B
    · rw [indicator_of_mem hω]; exact hv
    · rw [indicator_of_notMem hω]
  · intro ω
    by_cases hω : ω ∈ B
    · rw [indicator_of_mem hω]
    · rw [indicator_of_notMem hω]; exact hv
  · intro t
    let f : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ))
    have hf : Integrable f P := GFF.integrable_exp_I_mul (hX.const_mul t)
    have he : (fun ω => Complex.exp (Complex.I * ((t * B.indicator X ω : ℝ) : ℂ))) =
        B.indicator f + Bᶜ.indicator (fun _ => (1 : ℂ)) := by
      funext ω
      by_cases hω : ω ∈ B <;> simp [hω, f]
    rw [he]
    filter_upwards [condExp_add (hf.indicator (h𝒢 _ hB))
        ((integrable_const (1 : ℂ)).indicator (h𝒢 _ hB.compl)) 𝒢,
      condExp_indicator hf hB, condExp_indicator (integrable_const (1 : ℂ)) hB.compl,
      hc t] with ω hadd hind hind' hcω
    rw [hadd, Pi.add_apply, hind, hind', condExp_const h𝒢]
    by_cases hω : ω ∈ B
    · have hωc : ω ∉ Bᶜ := not_not_intro hω
      simpa only [Pi.add_apply, indicator_of_mem hω, indicator_of_notMem hωc,
        add_zero, f] using hcω hω
    · simp [hω]

/-- The harmonic mean of a fixed flow type has a position-independent bound
after its angle shift, by the existing finite-force harmonic extension bound. -/
theorem abs_mean_add_le_of_mem_typeSet {κ θ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    (hs : c.IsSorted) {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hc : c ∈ FCDet.typeSet κ θ nL nR ρL ρR) {z : ℂ} (hz : z ∈ H) :
    |c.mean z + θ * chiC κ| ≤ LocalExt.bheBound κ ρL ρR := by
  obtain ⟨eL, eR, hxL, hxR, heL, heR⟩ := FCDet.isFlowType_of_mem_typeSet hc
  subst nL nR
  change ρL = flowLineRhoL κ c.fn c.jumps 0 θ at heL
  change ρR = flowLineRhoR κ c.fn c.jumps 0 θ at heR
  subst ρL ρR
  have he := Exist.eqOn_flowLine_harmonicExtension hκ c.isPiecewiseConstantBoundaryData 0 θ
    (c.isBoundedHarmonicExtension_mean hs)
    (LocalExt.isBoundedHarmonicExtension_bheAt κ _ _ (flowLineXL c.fn c.jumps 0)
      (flowLineXR c.fn c.jumps 0)) hz
  simp only [Complex.ofReal_zero, add_zero] at he
  rw [← he]
  exact LocalExt.abs_bheAt_le _ _ _ _ _ hz

/-- The shifted mean pairing is bounded uniformly over the sorted words of a
fixed force type. The test's norm is integrated only against ordinary area. -/
theorem norm_integral_mean_add_le_of_mem_typeSet {κ θ : ℝ} (hκ : 0 < κ)
    {c : BoundaryWord} (hs : c.IsSorted) {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hc : c ∈ FCDet.typeSet κ θ nL nR ρL ρR) (φ : TestOn upperHalfPlaneOpens) :
    ‖(∫ z, c.mean z * φ z) + θ * chiC κ * (∫ z, φ z)‖ ≤
      LocalExt.bheBound κ ρL ρR * (∫ z, ‖φ z‖) := by
  have hi : Integrable (fun z => c.mean z * φ z) := by
    simpa only [mul_comm] using SupercriticalConformalCovariance.GM24.integrable_test_mul
      (BoundaryWord.continuousOn_mean c) φ
  have hφ : Integrable (fun z : ℂ => φ z) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have he : (∫ z, c.mean z * φ z) + θ * chiC κ * (∫ z, φ z) =
      ∫ z, (c.mean z + θ * chiC κ) * φ z := by
    simp_rw [add_mul]
    rw [integral_add hi (hφ.const_mul _), integral_const_mul]
  rw [he, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hφ.norm.const_mul _)
  refine ae_of_all _ fun z => ?_
  by_cases hφz : φ z = 0
  · simp only [hφz, mul_zero, norm_zero, le_refl]
  · rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (abs_mean_add_le_of_mem_typeSet hκ hs hc
        (φ.tsupport_subset (subset_tsupport _ (Function.mem_support.2 hφz)))) (norm_nonneg _)

/-- At seed zero the flow-field coordinate change only adds a constant. -/
theorem flowField_zero_apply (a : ℝ) (Hc : DistOn upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) :
    Exist.flowField 0 a Hc φ = Hc φ + a * (∫ z, φ z) :=
  Exist.isTranslateAddConst_flowField 0 a Hc φ φ (by intro z; simp only [Complex.ofReal_zero, add_zero])

/-- R1's word characteristic functional supplies a bounded-mean conditional
Gaussian law for every clamped fixed-type pairing. Sortedness is needed only
almost surely on the live event; the mean is set to zero on exceptional words. -/
theorem initialPairingGaussian_of_wordCF [IsProbabilityMeasure P]
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} (hM : MeasurableSet[𝒢] M)
    {β : Ω → BoundaryWord} (hβ : Measurable[𝒢] β)
    (hs : ∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable[mΩ] Hc)
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω => Complex.exp (Complex.I * (Hc ω φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ)
    {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) (a : RetAux79.ForceWordType) (φ : TestOn upperHalfPlaneOpens) :
    ∃ (μ V : Ω → ℝ) (K C : ℝ),
      @Sec6.Prop65.IsCondGaussian Ω 𝒢 mΩ P
        ((fcTypeBranch κ θ M β a).indicator
          (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ)) μ V K ∧
      ∀ ω, ‖μ ω‖ ≤ C := by
  classical
  let _ : MeasurableSpace Ω := mΩ
  let B := fcTypeBranch κ θ M β a
  let X := fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ
  let m₀ := fun ω => (∫ z, (β ω).mean z * φ z) + θ * chiC κ * (∫ z, φ z)
  let μ := fun ω => if (β ω).IsSorted then m₀ ω else 0
  let v := QuantumZipper.zeroGFFTestCov H φ φ
  let C := LocalExt.bheBound κ a.rhoL a.rhoR * (∫ z, ‖φ z‖)
  have hB : MeasurableSet[𝒢] B :=
    hM.inter (hβ (RetAux79.measurableSet_forceTypeSet κ θ a))
  have hμ : Measurable[𝒢] μ := Measurable.ite
    (hβ BoundaryWord.measurableSet_isSorted)
    (((BoundaryWord.measurable_integral_mean_mul φ).comp hβ).add_const _) measurable_const
  have hX : Measurable[mΩ] X := (LQGMetric.measurable_distOn_apply φ).comp
    ((Exist.measurable_flowField 0 _).comp hHc)
  have hv : 0 ≤ v := LocalSets.zeroGFFTestCov_self_nonneg QuantumZipper.isOpen_H subset_rfl φ
  have hc (t : ℝ) : ∀ᵐ ω ∂P, ω ∈ B →
      P[fun ω => Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * ((t * μ ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (t ^ 2 * v)) : ℝ) : ℂ) := by
    let f := fun ω => Complex.exp (Complex.I * (Hc ω (t • φ) : ℂ))
    let c : ℂ := Complex.exp (Complex.I * ((t * (θ * chiC κ * (∫ z, φ z)) : ℝ) : ℂ))
    have he : (fun ω => Complex.exp (Complex.I * ((t * X ω : ℝ) : ℂ))) =
        fun ω => c * f ω := by
      funext ω
      dsimp [X, c, f]
      rw [flowField_zero_apply, map_smul, smul_eq_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    have hp := condExp_smul c f 𝒢 (μ := P)
    filter_upwards [hcf (t • φ), hs, hp] with ω hcω hsω hpω hω
    have hωM : ω ∈ M := hω.1
    have hm : μ ω = m₀ ω := ite_eq_left_iff.2 fun hn => False.elim (hn (hsω hωM))
    rw [show (fun ω => c * f ω) = c • f from rfl, hpω]
    change c * P[f | 𝒢] ω = _
    rw [hcω hωM, hm]
    have hmean : (∫ z, (β ω).mean z * (t • φ) z) = t * (∫ z, (β ω).mean z * φ z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by change _ * (t * _) = _; ring
    have hvar : QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ⇑(t • φ) ⇑(t • φ) =
        t ^ 2 * QuantumZipper.zeroGFFTestCov H φ φ :=
      LocalSets.zeroGFFTestCov_smul_self QuantumZipper.isOpen_H subset_rfl t φ
    dsimp only [c, gaussCF, m₀, v]
    rw [hmean, hvar, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  refine ⟨B.indicator μ, B.indicator (fun _ => v), v, C,
    isCondGaussian_indicator_of_condCharFun h𝒢 hB hX hμ hv hc, ?_⟩
  have hC : 0 ≤ C := mul_nonneg (by unfold LocalExt.bheBound; positivity)
    (integral_nonneg fun _ => norm_nonneg _)
  intro ω
  by_cases hω : ω ∈ B
  · rw [indicator_of_mem hω]
    by_cases hsω : (β ω).IsSorted
    · rw [show μ ω = m₀ ω from ite_eq_left_iff.2 fun hn => False.elim (hn hsω)]
      exact norm_integral_mean_add_le_of_mem_typeSet hκ hsω hω.2 φ
    · simpa only [μ, hsω, ↓reduceIte, norm_zero] using hC
  · simpa only [indicator_of_notMem hω, norm_zero] using hC

end InteractingSLE.Restart.FCPlumb
