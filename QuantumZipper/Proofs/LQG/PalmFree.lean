import QuantumZipper.Proofs.LQG.PalmFormula
import QuantumZipper.Proofs.LQG.BoundaryExistenceAS
import QuantumZipper.Proofs.LQG.GoodSample
import QuantumZipper.Proofs.LQG.RegularSample
import QuantumZipper.Proofs.LQG.KernelIdentities
import QuantumZipper.Proofs.LQG.MeasurabilityAE

/-!
# Blueprint D1 (instantiation): the Palm formula for the free field

Task D1-INST. Three parts.

1. `palm_formula_weight`: the abstract Palm identity of `PalmFormula.lean` with a continuous,
   nonnegative, compactly supported weight `w` (vanishing off `[a,b]`) in place of the indicator
   of `[a,b]`; the `L¹` hypothesis is only needed for continuous compactly supported test
   functions vanishing off `[a,b]` (`BdryL1ConvCc`), so no atomlessness at `a, b` is needed.
2. The free field: `zG X R` is the normalized free field `zField X R` with the coordinates at
   non-admissible measures set to `0`; it is a genuine centered Gaussian field
   (`isCenteredGaussianField_zG`) and agrees with `zField X R` on every admissible measure, in
   particular on every folded circle, so it has the same boundary measures. All hypotheses of
   part 1 are discharged for `Y = ofFun m + zG X R` (`m` continuous), with the explicit kernel
   `freeKernel R x z = neumannH x z − fcPot R 0 z` and `c̃ = 2 log R` (`ae_avgReg_zG`,
   `variance_zG_fc`, `tendsto_covariance_zG`, `lintegral_qBoundaryMeasure_zG_lt_top`,
   `bdryL1ConvCc_zG`, `aemeasurable_qBoundaryMeasure_free`), giving `palm_formula_free`,
   stated for `zField X R` itself and admissible coordinates `μ_j`.
3. `half_freeKernel_eq`: `(γ/2) c(x,·) = γ (−log ‖· − x‖) + (continuous function)` for real `x`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

set_option linter.unusedSectionVars false

namespace QuantumZipper
namespace PalmFree

open Palm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Z : Ω → FieldSample} {m : ℂ → ℝ} {μ : ℕ → Measure ℂ} {γ : ℝ}

/-! ## 1. The weighted Palm formula -/

/-- `L¹` convergence of the approximating boundary measures of `ofFun m + Z` to `ν`, tested
against continuous compactly supported functions vanishing off `[a,b]` (the form provided by
`BdryExist.integral_abs_bdryApprox_sub_qBoundaryMeasure_le`). -/
def BdryL1ConvCc (γ : ℝ) (m : ℂ → ℝ) (Z : Ω → FieldSample) (P : Measure Ω)
    (ν : Ω → Measure ℝ) (a b : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → (∀ x ∉ Icc a b, f x = 0) →
    Tendsto (fun k => ∫ ω, |∫ x, f x ∂(bdryApprox γ (ofFun m + Z ω) k) -
      ∫ x, f x ∂(ν ω)| ∂P) atTop (𝓝 0)

section Weighted

variable {a b : ℝ} {ν : Ω → Measure ℝ}

/-- `tendsto_lhs` with the `L¹` hypothesis for a single test function. -/
lemma tendsto_lhs_single (hZ : IsCenteredGaussianField P Z) (hm : Continuous m) {Cv : ℝ}
    {ctil : ℝ → ℝ}
    (hreg : ∀ k, ∀ x ∈ Icc a b, ∀ᵐ ω ∂P,
      avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k))
    (hvarbd : ∀ k, ∀ x ∈ Icc a b, varK Z P x k + 2 * Real.log (radius k) ≤ Cv)
    (hvar : ∀ x ∈ Icc a b, Tendsto (fun k => varK Z P x k + 2 * Real.log (radius k)) atTop
      (𝓝 (ctil x)))
    (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ∞)
    {g : (ℕ → ℝ) → ℝ} {Cg : ℝ} (hg : Measurable g) (hgb : ∀ y, |g y| ≤ Cg) (h : ℝ →ᵇ ℝ)
    (hL1 : Tendsto (fun k => ∫ ω, |∫ x in Icc a b, h x ∂(bdryApprox γ (ofFun m + Z ω) k) -
      ∫ x in Icc a b, h x ∂(ν ω)| ∂P) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, g (coords m Z μ ω) *
        ∫ x in Icc a b, h x ∂(bdryApprox γ (ofFun m + Z ω) k) ∂P) atTop
      (𝓝 (∫ ω, g (coords m Z μ ω) * ∫ x in Icc a b, h x ∂(ν ω) ∂P)) := by
  have hA := integrable_setIntegral_nu hν hfin h
  have hAk : ∀ k, Integrable
      (fun ω => ∫ x in Icc a b, h x ∂(bdryApprox γ (ofFun m + Z ω) k)) P := by
    intro k
    have hint := (integrable_prod_F_dens (μ := μ) (γ := γ) (F := fun _ x => h x) (CF := ‖h‖) hZ hm
      hreg hvarbd hvar (h.continuous.measurable.comp measurable_snd)
      (fun _ x => by rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm x) k).integral_prod_left
    refine hint.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [setIntegral_bdryApprox _ k measurableSet_Icc]
    rfl
  have hgm : AEStronglyMeasurable (fun ω => g (coords m Z μ ω)) P :=
    (hg.comp (measurable_coords hZ)).aestronglyMeasurable
  have hgb' : ∀ᵐ ω ∂P, ‖g (coords m Z μ ω)‖ ≤ Cg :=
    ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
    (by simpa using hL1.const_mul Cg)
  rw [← integral_sub ((hAk k).bdd_mul hgm hgb') (hA.bdd_mul hgm hgb'), ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((hAk k).sub hA).abs.const_mul Cg)
    (ae_of_all _ fun ω => ?_)
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)

/-- The Palm identity for products `w(x) g(coords) h(x)` (bounded continuous `g, h`). -/
lemma palm_core_weight (hZ : IsCenteredGaussianField P Z) (hm : Continuous m) {Cv : ℝ}
    {ctil : ℝ → ℝ} {c : ℝ → ℂ → ℝ}
    (hreg : ∀ k, ∀ x ∈ Icc a b, ∀ᵐ ω ∂P,
      avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k))
    (hvarbd : ∀ k, ∀ x ∈ Icc a b, varK Z P x k + 2 * Real.log (radius k) ≤ Cv)
    (hvar : ∀ x ∈ Icc a b, Tendsto (fun k => varK Z P x k + 2 * Real.log (radius k)) atTop
      (𝓝 (ctil x)))
    (hcov : ∀ x ∈ Icc a b, ∀ j, Tendsto
      (fun k => cov[fun ω => Z ω (μ j), fun ω => Z ω (fcK x k); P]) atTop
      (𝓝 (∫ z, c x z ∂(μ j))))
    (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ∞)
    (hL1 : BdryL1ConvCc γ m Z P ν a b) (w : ℝ →ᵇ ℝ) (hwc : HasCompactSupport w)
    (hwab : ∀ x ∉ Icc a b, w x = 0) (g : (ℕ → ℝ) →ᵇ ℝ) (h : ℝ →ᵇ ℝ) :
    ∫ ω, ∫ x in Icc a b, w x * (g (coords m Z μ ω) * h x) ∂(ν ω) ∂P =
      ∫ x in Icc a b, rhoLim γ m ctil x *
        ∫ ω, w x * (g (coords m Z μ ω + shiftLim γ c μ x) * h x) ∂P := by
  set wh : ℝ →ᵇ ℝ := w * h with hwh
  have hwh_apply : ∀ x, wh x = w x * h x := fun x => rfl
  have hgb : ∀ y, |g y| ≤ ‖g‖ := fun y => by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm y
  have hhb : ∀ x, |wh x| ≤ ‖wh‖ := fun x => by
    rw [← Real.norm_eq_abs]; exact wh.norm_coe_le_norm x
  have hFm : Measurable (Function.uncurry fun (y : ℕ → ℝ) (x : ℝ) => g y * wh x) :=
    (g.continuous.measurable.comp measurable_fst).mul
      (wh.continuous.measurable.comp measurable_snd)
  have hFb : ∀ y x, |g y * wh x| ≤ ‖g‖ * ‖wh‖ := fun y x => by
    rw [abs_mul]; exact mul_le_mul (hgb y) (hhb x) (abs_nonneg _) (norm_nonneg _)
  have hvan : ∀ x ∉ Icc a b, wh x = 0 := fun x hx => by rw [hwh_apply, hwab x hx, zero_mul]
  have hL1' : Tendsto (fun k => ∫ ω, |∫ x in Icc a b, wh x ∂(bdryApprox γ (ofFun m + Z ω) k) -
      ∫ x in Icc a b, wh x ∂(ν ω)| ∂P) atTop (𝓝 0) := by
    have hc : HasCompactSupport (fun x => wh x) := by
      have : (fun x => wh x) = (⇑w) * (⇑h) := by funext x; rfl
      rw [this]; exact hwc.mul_right
    have := hL1 (fun x => wh x) wh.continuous hc hvan
    refine this.congr fun k => ?_
    congr 1; funext ω
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvan,
      setIntegral_eq_integral_of_forall_compl_eq_zero hvan]
  have hl := tendsto_lhs_single (μ := μ) hZ hm hreg hvarbd hvar hν hfin g.continuous.measurable
    hgb wh hL1'
  have hr := tendsto_rhs (γ := γ) (μ := μ) (F := fun y x => g y * wh x) hZ hm hreg hvarbd hvar
    hcov hFm hFb (fun x => g.continuous.mul continuous_const)
  have heq : ∀ k, ∫ x in Icc a b, rhoK γ m Z P x k *
      ∫ ω, g (coords m Z μ ω + shiftK γ Z P μ x k) * wh x ∂P =
      ∫ ω, g (coords m Z μ ω) * ∫ x in Icc a b, wh x ∂(bdryApprox γ (ofFun m + Z ω) k) ∂P := by
    intro k
    have := palm_levelK (γ := γ) (μ := μ) (F := fun y x => g y * wh x) hZ hm hreg hvarbd hvar
      hFm hFb k
    simp_rw [integral_const_mul] at this
    exact this.symm
  have key := tendsto_nhds_unique hl (hr.congr heq)
  have e1 : ∀ ω, ∫ x in Icc a b, w x * (g (coords m Z μ ω) * h x) ∂(ν ω) =
      g (coords m Z μ ω) * ∫ x in Icc a b, wh x ∂(ν ω) := by
    intro ω
    rw [← integral_const_mul]
    congr 1; funext x; rw [hwh_apply]; ring
  have e2 : ∀ x, ∫ ω, w x * (g (coords m Z μ ω + shiftLim γ c μ x) * h x) ∂P =
      ∫ ω, g (coords m Z μ ω + shiftLim γ c μ x) * wh x ∂P := by
    intro x
    congr 1; funext ω; rw [hwh_apply]; ring
  simp_rw [e1, e2]
  exact key

/-- **Weighted Palm formula (abstract, coordinates form).** -/
theorem palm_formula_weight_coords (hZ : IsCenteredGaussianField P Z)
    (hm : Continuous m) {Cv : ℝ} {ctil : ℝ → ℝ} (hctil : Measurable ctil) {c : ℝ → ℂ → ℝ}
    (hc : Measurable (Function.uncurry c)) [∀ j, IsFiniteMeasure (μ j)]
    (hreg : ∀ k, ∀ x ∈ Icc a b, ∀ᵐ ω ∂P,
      avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k))
    (hvarbd : ∀ k, ∀ x ∈ Icc a b, varK Z P x k + 2 * Real.log (radius k) ≤ Cv)
    (hvar : ∀ x ∈ Icc a b, Tendsto (fun k => varK Z P x k + 2 * Real.log (radius k)) atTop
      (𝓝 (ctil x)))
    (hcov : ∀ x ∈ Icc a b, ∀ j, Tendsto
      (fun k => cov[fun ω => Z ω (μ j), fun ω => Z ω (fcK x k); P]) atTop
      (𝓝 (∫ z, c x z ∂(μ j))))
    (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ∞)
    (hL1 : BdryL1ConvCc γ m Z P ν a b)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hwab : ∀ x ∉ Icc a b, w x = 0)
    {φ : (ℕ → ℝ) → ℝ → ℝ} (hφ : Measurable (Function.uncurry φ)) {Cφ : ℝ}
    (hφb : ∀ y x, |φ y x| ≤ Cφ) :
    ∫ ω, ∫ x, w x * φ (coords m Z μ ω) x ∂(ν ω) ∂P =
      ∫ x, w x * rhoLim γ m ctil x *
        ∫ ω, φ (coords m Z μ ω + shiftLim γ c μ x) x ∂P := by
  have := hZ.gauss.isProbabilityMeasure
  have hI : MeasurableSet (Icc a b) := measurableSet_Icc
  obtain ⟨Cw, hCw⟩ := hw.bounded_above_of_compact_support hwc
  set wB : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup w hw Cw hCw with hwB
  have hwB_apply : ∀ x, wB x = w x := fun x => rfl
  have hCw' : ∀ x, |w x| ≤ Cw := fun x => by rw [← Real.norm_eq_abs]; exact hCw x
  set κ := kerI hν hI with hκ
  obtain ⟨B, hB0, hB⟩ := exists_bound_rho (γ := γ) hm hvarbd hvar
  -- measurability
  have hρ : Measurable (rhoLim γ m ctil) := by
    unfold rhoLim
    exact Real.measurable_exp.comp ((((hm.measurable.comp Complex.measurable_ofReal).const_mul
      γ).div_const 2).add ((hctil.const_mul (γ ^ 2)).div_const 8))
  have hs : Measurable (shiftLim γ c μ) := measurable_pi_iff.mpr fun j =>
    (hc.stronglyMeasurable.integral_prod_right (ν := μ j)).measurable.const_mul _
  have hmapL : Measurable fun p : Ω × ℝ => (coords m Z μ p.1, p.2) :=
    ((measurable_coords hZ).comp measurable_fst).prodMk measurable_snd
  have hmapR : Measurable fun p : ℝ × Ω => (coords m Z μ p.2 + shiftLim γ c μ p.1, p.1) :=
    (((measurable_coords hZ).comp measurable_snd).add (hs.comp measurable_fst)).prodMk
      measurable_fst
  -- the two finite measures
  have hfinL : IsFiniteMeasure (P ⊗ₘ κ) := by
    constructor
    rw [Measure.compProd_apply MeasurableSet.univ]
    simpa only [preimage_univ] using lintegral_kerI hν hI hfin
  set ρN : ℝ → ℝ≥0 := fun x => (rhoLim γ m ctil x).toNNReal with hρN
  have hρNm : Measurable ρN := hρ.real_toNNReal
  set D := (volume.restrict (Icc a b)).withDensity fun x => (ρN x : ℝ≥0∞) with hD
  have hfinD : IsFiniteMeasure D := by
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ x in Icc a b, (ρN x : ℝ≥0∞) ≤ ∫⁻ _ in Icc a b, ENNReal.ofReal B := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hI] with x hx
          exact ENNReal.ofReal_le_ofReal (hB x hx).2
      _ < ∞ := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  set wN : ℝ → ℝ≥0 := fun x => (w x).toNNReal with hwN
  have hwNm : Measurable wN := hw.measurable.real_toNNReal
  have hwNm' : Measurable fun p : (ℕ → ℝ) × ℝ => (wN p.2 : ℝ≥0∞) :=
    (hwNm.comp measurable_snd).coe_nnreal_ennreal
  set ML0 := (P ⊗ₘ κ).map fun p : Ω × ℝ => (coords m Z μ p.1, p.2) with hML0
  set MR0 := (D.prod P).map fun p : ℝ × Ω => (coords m Z μ p.2 + shiftLim γ c μ p.1, p.1)
    with hMR0
  have hfinML0 : IsFiniteMeasure ML0 := by rw [hML0]; infer_instance
  have hfinMR0 : IsFiniteMeasure MR0 := by rw [hMR0]; infer_instance
  set ML := ML0.withDensity fun p => (wN p.2 : ℝ≥0∞) with hML
  set MR := MR0.withDensity fun p => (wN p.2 : ℝ≥0∞) with hMR
  have hwNle : ∀ p : (ℕ → ℝ) × ℝ, (wN p.2 : ℝ≥0∞) ≤ ENNReal.ofReal Cw := fun p => by
    show ENNReal.ofReal (w p.2) ≤ _
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hCw' _))
  have hfinW : ∀ M : Measure ((ℕ → ℝ) × ℝ), IsFiniteMeasure M →
      IsFiniteMeasure (M.withDensity fun p => (wN p.2 : ℝ≥0∞)) := by
    intro M hM
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ p, (wN p.2 : ℝ≥0∞) ∂M ≤ ∫⁻ _, ENNReal.ofReal Cw ∂M := lintegral_mono hwNle
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hfinML : IsFiniteMeasure ML := hfinW _ hfinML0
  have hfinMR : IsFiniteMeasure MR := hfinW _ hfinMR0
  have hwint : ∀ (M : Measure ((ℕ → ℝ) × ℝ)) (G : (ℕ → ℝ) × ℝ → ℝ),
      ∫ p, G p ∂(M.withDensity fun p => (wN p.2 : ℝ≥0∞)) = ∫ p, w p.2 * G p ∂M := by
    intro M G
    rw [integral_withDensity_eq_integral_smul (f := fun p : (ℕ → ℝ) × ℝ => wN p.2)
      (hwNm.comp measurable_snd)]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hwN, NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (hw0 _)]
  -- integrals against the two measures
  have hLint : ∀ G : (ℕ → ℝ) × ℝ → ℝ, Measurable G → ∀ C, (∀ p, |G p| ≤ C) →
      ∫ p, G p ∂ML = ∫ ω, ∫ x in Icc a b, w x * G (coords m Z μ ω, x) ∂(ν ω) ∂P := by
    intro G hG C hC
    have hG' : Measurable fun p : (ℕ → ℝ) × ℝ => w p.2 * G p :=
      (hw.measurable.comp measurable_snd).mul hG
    rw [hML, hwint, hML0, integral_map hmapL.aemeasurable hG'.aestronglyMeasurable,
      Measure.integral_compProd (Integrable.of_bound
        (f := fun p : Ω × ℝ => w p.2 * G (coords m Z μ p.1, p.2))
        (hG'.comp hmapL).aestronglyMeasurable (Cw * C)
        (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hCw' _) (hC _) (abs_nonneg _) ((abs_nonneg _).trans (hCw' 0))))]
    refine integral_congr_ae ((nuMod_ae_eq hν hI hfin).mono fun ω hω => ?_)
    simp only [hκ, kerI_apply, hω]
  have hRint : ∀ G : (ℕ → ℝ) × ℝ → ℝ, Measurable G → ∀ C, (∀ p, |G p| ≤ C) →
      ∫ p, G p ∂MR = ∫ x in Icc a b, rhoLim γ m ctil x *
        ∫ ω, w x * G (coords m Z μ ω + shiftLim γ c μ x, x) ∂P := by
    intro G hG C hC
    have hG' : Measurable fun p : (ℕ → ℝ) × ℝ => w p.2 * G p :=
      (hw.measurable.comp measurable_snd).mul hG
    rw [hMR, hwint, hMR0, integral_map hmapR.aemeasurable hG'.aestronglyMeasurable,
      integral_prod _ (Integrable.of_bound
        (f := fun p : ℝ × Ω => w p.1 * G (coords m Z μ p.2 + shiftLim γ c μ p.1, p.1))
        (hG'.comp hmapR).aestronglyMeasurable (Cw * C)
        (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hCw' _) (hC _) (abs_nonneg _) ((abs_nonneg _).trans (hCw' 0)))),
      hD, integral_withDensity_eq_integral_smul hρNm]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hρN, NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (show 0 ≤ rhoLim γ m ctil x from (Real.exp_pos _).le)]
  -- the measures agree
  have hM : ML = MR := by
    refine _root_.Measure.ext_of_integral_mul_boundedContinuousFunction fun g h => ?_
    have hGm : Measurable fun p : (ℕ → ℝ) × ℝ => g p.1 * h p.2 :=
      (g.continuous.measurable.comp measurable_fst).mul
        (h.continuous.measurable.comp measurable_snd)
    have hGb : ∀ p : (ℕ → ℝ) × ℝ, |g p.1 * h p.2| ≤ ‖g‖ * ‖h‖ := fun p => by
      rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul (g.norm_coe_le_norm _) (h.norm_coe_le_norm _) (norm_nonneg _)
        (norm_nonneg _)
    rw [hLint _ hGm _ hGb, hRint _ hGm _ hGb]
    have := palm_core_weight hZ hm hreg hvarbd hvar hcov hν hfin hL1 wB hwc hwab g h
    simpa only [hwB_apply] using this
  have hφb' : ∀ p : (ℕ → ℝ) × ℝ, |Function.uncurry φ p| ≤ Cφ := fun p => hφb _ _
  have h1 := hLint _ hφ _ hφb'
  rw [hM, hRint _ hφ _ hφb'] at h1
  simp only [Function.uncurry_apply_pair] at h1
  -- remove the restriction to `[a,b]`
  have hL : ∀ ω, ∫ x, w x * φ (coords m Z μ ω) x ∂(ν ω) =
      ∫ x in Icc a b, w x * φ (coords m Z μ ω) x ∂(ν ω) := fun ω =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hwab x hx, zero_mul]).symm
  have hR : ∫ x, w x * rhoLim γ m ctil x * ∫ ω, φ (coords m Z μ ω + shiftLim γ c μ x) x ∂P =
      ∫ x in Icc a b, rhoLim γ m ctil x *
        ∫ ω, w x * φ (coords m Z μ ω + shiftLim γ c μ x) x ∂P := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hwab x hx, zero_mul, zero_mul]]
    refine setIntegral_congr_fun hI fun x _ => ?_
    rw [integral_const_mul]; ring
  simp_rw [hL]
  rw [hR]
  exact h1.symm

/-- `coords + shiftLim` are the coordinates of the shifted field. -/
lemma coords_add_shiftLim' (c : ℝ → ℂ → ℝ) (ω : Ω) (x : ℝ) :
    coords m Z μ ω + shiftLim γ c μ x =
      fun j => (ofFun m + Z ω + ofFun (fun z => γ / 2 * c x z)) (μ j) := by
  funext j
  simp only [coords, shiftLim, Pi.add_apply, ofFun, integral_const_mul]

/-- **Weighted Palm formula (Blueprint D1 with a `C_c` weight).** For a continuous,
nonnegative, compactly supported weight `w` vanishing off `[a,b]` and bounded measurable `φ`:
`E ∫ w(x) φ(Y,x) ν(dx) = ∫ w(x) ρ(x) E φ(Y + ofFun((γ/2)c(x,·)), x) dx`,
`ρ(x) = exp(γ m(x)/2 + γ² c̃(x)/8)`. The `L¹` hypothesis is only needed in the `C_c` form. -/
theorem palm_formula_weight (hZ : IsCenteredGaussianField P Z)
    (hm : Continuous m) {Cv : ℝ} {ctil : ℝ → ℝ} (hctil : Measurable ctil) {c : ℝ → ℂ → ℝ}
    (hc : Measurable (Function.uncurry c)) [∀ j, IsFiniteMeasure (μ j)]
    (hreg : ∀ k, ∀ x ∈ Icc a b, ∀ᵐ ω ∂P,
      avgReg (ofFun m + Z ω) k (x : ℂ) = (ofFun m + Z ω) (fcK x k))
    (hvarbd : ∀ k, ∀ x ∈ Icc a b,
      Var[fun ω => Z ω (fcK x k); P] + 2 * Real.log (radius k) ≤ Cv)
    (hvar : ∀ x ∈ Icc a b, Tendsto
      (fun k => Var[fun ω => Z ω (fcK x k); P] + 2 * Real.log (radius k)) atTop (𝓝 (ctil x)))
    (hcov : ∀ x ∈ Icc a b, ∀ j, Tendsto
      (fun k => cov[fun ω => Z ω (μ j), fun ω => Z ω (fcK x k); P]) atTop
      (𝓝 (∫ z, c x z ∂(μ j))))
    (hν : AEMeasurable ν P) (hfin : ∫⁻ ω, ν ω (Icc a b) ∂P < ∞)
    (hL1 : BdryL1ConvCc γ m Z P ν a b)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hwab : ∀ x ∉ Icc a b, w x = 0)
    {φ : (ℕ → ℝ) → ℝ → ℝ} (hφ : Measurable (Function.uncurry φ)) {Cφ : ℝ}
    (hφb : ∀ y x, |φ y x| ≤ Cφ) :
    ∫ ω, ∫ x, w x * φ (fun j => (ofFun m + Z ω) (μ j)) x ∂(ν ω) ∂P =
      ∫ x, w x * Real.exp (γ * m x / 2 + γ ^ 2 * ctil x / 8) *
        ∫ ω, φ (fun j => (ofFun m + Z ω + ofFun (fun z => γ / 2 * c x z)) (μ j)) x ∂P := by
  have H := palm_formula_weight_coords (γ := γ) hZ hm hctil hc hreg hvarbd hvar hcov hν hfin
    hL1 hw hwc hw0 hwab hφ hφb
  simp only [coords_add_shiftLim'] at H
  exact H

end Weighted

/-! ## 2. The free field: a genuine Gaussian field agreeing with `zField` -/

section FreeGauss

variable {X : Ω → FieldSample}

open BdryExist

open Classical in
/-- The normalized free field `zField X R` with its coordinates at non-admissible measures set
to `0`. On admissible measures (in particular on all folded circles) it is `zField X R`. -/
def zG (X : Ω → FieldSample) (R : ℝ) (ω : Ω) : FieldSample :=
  fun ν => if IsAdmissibleH ν then zField X R ω ν else 0

lemma zG_of_adm {R : ℝ} {ν : Measure ℂ} (hν : IsAdmissibleH ν) (ω : Ω) :
    zG X R ω ν = zField X R ω ν := by
  unfold zG; rw [ite_eq_left hν]

lemma zG_of_not_adm {R : ℝ} {ν : Measure ℂ} (hν : ¬ IsAdmissibleH ν) (ω : Ω) :
    zG X R ω ν = 0 := by
  unfold zG; rw [ite_eq_right hν]

lemma zG_fc {R : ℝ} {z : ℂ} (hz : z ∈ Hbar) {r : ℝ} (hr : 0 < r) (ω : Ω) :
    zG X R ω (foldedCircle z r) = zField X R ω (foldedCircle z r) :=
  zG_of_adm (isAdmissibleH_foldedCircle hz hr) ω

/-- The mass of `ν` as an `ℝ≥0`. -/
abbrev massN (ν : Measure ℂ) : ℝ≥0 := (ν univ).toNNReal

lemma adm_smul_fc {R : ℝ} (hR : 0 < R) (c : ℝ≥0) : IsAdmissibleH (c • foldedCircle 0 R) :=
  isAdmissibleH_smul (c := (c : ℝ≥0∞)) (isAdmissibleH_foldedCircle (by simp [Hbar]) hR)
    ENNReal.coe_lt_top

lemma mass_smul_fc (R : ℝ) {ν : Measure ℂ} (hν : IsAdmissibleH ν) :
    ν univ = (massN ν • foldedCircle 0 R) univ := by
  have := hν.1
  show ν univ = ((massN ν : ℝ≥0∞) • foldedCircle 0 R) univ
  rw [Measure.smul_apply, smul_eq_mul, measure_univ (μ := foldedCircle 0 R), mul_one,
    ENNReal.coe_toNNReal (measure_ne_top ν univ)]

/-- The balanced admissible pair `(ν, |ν| fc(0,R))`. -/
def pairN (R : ℝ) (hR : 0 < R) (ν : {ν : Measure ℂ // IsAdmissibleH ν}) :
    {q : Measure ℂ × Measure ℂ // IsAdmissibleH q.1 ∧ IsAdmissibleH q.2 ∧ q.1 univ = q.2 univ} :=
  ⟨(ν.1, massN ν.1 • foldedCircle 0 R), ν.2, adm_smul_fc hR _, mass_smul_fc R ν.2⟩

lemma X_smul_fc_ae (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR : 0 < R) (c : ℝ≥0) :
    (fun ω => X ω (c • foldedCircle 0 R)) =ᵐ[P] fun ω => (c : ℝ) * X ω (foldedCircle 0 R) := by
  have hF := isAdmissibleH_foldedCircle (by simp [Hbar] : (0 : ℂ) ∈ Hbar) hR
  have := hX.linear _ _ hF hF c 0
  simpa using this

/-- On an admissible `ν`, `zField X R ω ν` is a.s. the balanced difference `X ν − X(|ν| fc(0,R))`. -/
lemma zField_ae_eq_pair (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR : 0 < R) (ν : Measure ℂ) :
    (fun ω => X ω ν - X ω (massN ν • foldedCircle 0 R)) =ᵐ[P] fun ω => zField X R ω ν := by
  filter_upwards [X_smul_fc_ae hX hR (massN ν)] with ω hω
  rw [hω]
  simp only [zField, addConst, massN, ENNReal.coe_toNNReal_eq_toReal]
  ring

lemma measurable_zG (hX : IsFreeGFFModConstH X P) (R : ℝ) (ν : Measure ℂ) :
    Measurable fun ω => zG X R ω ν := by
  by_cases hν : IsAdmissibleH ν
  · simp_rw [zG_of_adm hν]
    exact (measurable_pi_apply ν).comp (measurable_zField hX R)
  · simp_rw [zG_of_not_adm hν]; exact measurable_const

/-- **`zG X R` is a centered Gaussian field.** -/
theorem isCenteredGaussianField_zG (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR : 0 < R) :
    IsCenteredGaussianField P (zG X R) := by
  have hW0 : IsGaussianProcess (fun (ν : {ν : Measure ℂ // IsAdmissibleH ν}) (ω : Ω) =>
      X ω ν.1 - X ω (massN ν.1 • foldedCircle 0 R)) P :=
    hX.gaussian.comp_right (pairN R hR)
  have hW : IsGaussianProcess (fun (ν : {ν : Measure ℂ // IsAdmissibleH ν}) (ω : Ω) =>
      zField X R ω ν.1) P :=
    hW0.congr fun ν => zField_ae_eq_pair hX hR ν.1
  refine ⟨?_, measurable_zG hX R, fun ν => ?_⟩
  · refine hW.of_isGaussianProcess fun ν => ?_
    by_cases hν : IsAdmissibleH ν
    · let t : {ν : Measure ℂ // IsAdmissibleH ν} := ⟨ν, hν⟩
      refine ⟨{t}, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({t} : Finset _) => ℝ)
        ⟨t, Finset.mem_singleton_self t⟩, fun ω => ?_⟩
      simp only [ContinuousLinearMap.proj_apply, Finset.restrict]
      exact zG_of_adm hν ω
    · exact ⟨∅, 0, fun ω => by simp only [zero_apply]; exact zG_of_not_adm hν ω⟩
  · by_cases hν : IsAdmissibleH ν
    · simp_rw [zG_of_adm hν]
      rw [← integral_congr_ae (zField_ae_eq_pair hX hR ν)]
      exact hX.centered _ _ hν (adm_smul_fc hR _) (mass_smul_fc R hν)
    · simp_rw [zG_of_not_adm hν]; simp

lemma covariance_congr_ae' {U U' V V' : Ω → ℝ} (hU : U =ᵐ[P] U') (hV : V =ᵐ[P] V') :
    cov[U, V; P] = cov[U', V'; P] := by
  unfold covariance
  rw [integral_congr_ae hU, integral_congr_ae hV]
  refine integral_congr_ae ?_
  filter_upwards [hU, hV] with ω h1 h2
  rw [h1, h2]

/-- Covariance of `zG` on admissible measures. -/
lemma covariance_zG (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR : 0 < R) {ν₁ ν₂ : Measure ℂ}
    (h₁ : IsAdmissibleH ν₁) (h₂ : IsAdmissibleH ν₂) :
    cov[fun ω => zG X R ω ν₁, fun ω => zG X R ω ν₂; P] =
      kernelCov2 neumannH (ν₁, massN ν₁ • foldedCircle 0 R)
        (ν₂, massN ν₂ • foldedCircle 0 R) := by
  simp_rw [zG_of_adm h₁, zG_of_adm h₂]
  rw [← covariance_congr_ae' (zField_ae_eq_pair hX hR ν₁) (zField_ae_eq_pair hX hR ν₂)]
  exact hX.covariance_eq (ν₁, _) (ν₂, _) h₁ (adm_smul_fc hR _) (mass_smul_fc R h₁)
    h₂ (adm_smul_fc hR _) (mass_smul_fc R h₂)

lemma kernelCov_smul_left (G : ℂ → ℂ → ℝ) (c : ℝ≥0) (μ ν : Measure ℂ) :
    kernelCov G (c • μ) ν = c * kernelCov G μ ν := by
  unfold kernelCov
  rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

lemma kernelCov_fc_right' (μ : Measure ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    kernelCov neumannH μ (foldedCircle a r) = ∫ y, KernelId.fcPot r a y ∂μ := by
  unfold kernelCov
  simp_rw [KernelId.integral_neumannH_foldedCircle_right' a _ hr]

/-- Covariance of `zG` against a folded circle centred on `ℝ` inside `B(0,R)`. -/
lemma covariance_zG_fc (hX : IsFreeGFFModConstH X P) {R : ℝ} {ν : Measure ℂ}
    (hν : IsAdmissibleH ν) {x r : ℝ} (hr : 0 < r) (hxr : |x| + r ≤ R) :
    cov[fun ω => zG X R ω ν, fun ω => zG X R ω (foldedCircle (x : ℂ) r); P] =
      ∫ y, KernelId.fcPot r x y ∂ν - ∫ y, KernelId.fcPot R 0 y ∂ν := by
  have hR : 0 < R := by linarith [abs_nonneg x]
  have hfc := isAdmissibleH_foldedCircle (GaussTK.ofReal_mem_Hbar x) hr
  rw [covariance_zG hX hR hν hfc]
  have hm1 : massN (foldedCircle (x : ℂ) r) = 1 := by simp [massN]
  have hxn : ‖(x : ℂ)‖ + r ≤ R := by rwa [GaussTK.norm_ofReal']
  simp only [kernelCov2, hm1, one_smul, kernelCov_smul_left]
  rw [kernelCov_fc_bigCircle_left hr hxn, kernelCov_fc_bigCircle_left hR (by simp),
    kernelCov_fc_right' _ _ hr, kernelCov_fc_right' _ _ hR]
  ring

/-- Variance of `zG` at a folded circle centred on `ℝ`. -/
lemma variance_zG_fc (hX : IsFreeGFFModConstH X P) {R : ℝ} {x r : ℝ} (hr : 0 < r)
    (hxr : |x| + r ≤ R) :
    Var[fun ω => zG X R ω (foldedCircle (x : ℂ) r); P] + 2 * Real.log r = 2 * Real.log R := by
  have hxn : ‖(x : ℂ)‖ + r ≤ R := by rwa [GaussTK.norm_ofReal']
  rw [← covariance_self (measurable_zG hX R _).aemeasurable]
  simp_rw [zG_fc (GaussTK.ofReal_mem_Hbar x) hr]
  rw [show (fun ω => zField X R ω (foldedCircle (x : ℂ) r)) = fun ω =>
    addConst (X ω) (-X ω (foldedCircle 0 R)) (foldedCircle (x : ℂ) r) from rfl]
  rw [GaussTK.covariance_Z_fc hX (GaussTK.ofReal_mem_Hbar x) (GaussTK.ofReal_mem_Hbar x) hr hr
    hxn hxn, kernelCov_fc_real_sameCenter hr hr, max_self]
  ring

/-! ### The covariance kernel of the normalized free field -/

/-- The covariance kernel `c(x,z) = G_N(x,z) − ∫ G_N(z,·) d fc(0,R)` of `zField X R` (for
`|x| < R`). -/
def freeKernel (R : ℝ) (x : ℝ) (z : ℂ) : ℝ := neumannH (x : ℂ) z - KernelId.fcPot R 0 z

lemma measurable_freeKernel {R : ℝ} (hR : 0 < R) : Measurable (Function.uncurry (freeKernel R)) :=
  (measurable_neumannH.comp ((Complex.measurable_ofReal.comp measurable_fst).prodMk
    measurable_snd)).sub ((KernelId.continuous_fcPot hR 0).measurable.comp measurable_snd)

lemma abs_log_le_of_le {d D : ℝ} (hd : 0 ≤ d) (hdD : d ≤ D) (hD : 1 ≤ D) :
    |Real.log d| ≤ Real.log D + max 0 (-Real.log d) := by
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have h1 : Real.log d ≤ Real.log D := by
    rcases hd.eq_or_lt with h | h
    · rw [← h, Real.log_zero]; exact hlD
    · exact Real.log_le_log h hdD
  rw [abs_le]
  constructor
  · linarith [le_max_right 0 (-Real.log d)]
  · linarith [le_max_left 0 (-Real.log d)]

/-- `y ↦ log ‖y − x‖` is integrable against an admissible measure. -/
lemma integrable_log_norm_sub {ν : Measure ℂ} (hν : IsAdmissibleH ν) (x : ℂ) :
    Integrable (fun y => Real.log ‖y - x‖) ν := by
  obtain ⟨hνf, ⟨K, hK, -, hKc⟩, C, hC, hbd⟩ := hν
  have := hνf
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  set D := max 1 (ρ + ‖x‖) with hD
  have hmeas : Measurable fun y : ℂ => Real.log ‖y - x‖ :=
    Real.measurable_log.comp (measurable_id.sub_const x).norm
  have hneg : Integrable (fun y => (ENNReal.ofReal (-Real.log ‖y - x‖)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp hmeas.neg).aemeasurable ((hbd x).trans_lt hC).ne
  refine ((integrable_const (Real.log D)).add hneg).mono' hmeas.aestronglyMeasurable ?_
  have hKae : ∀ᵐ y ∂ν, y ∈ K := ae_iff.2 hKc
  filter_upwards [hKae] with y hy
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, ENNReal.toReal_ofReal', max_comm]
  refine abs_log_le_of_le (norm_nonneg _) ?_ (le_max_left _ _)
  calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
    _ ≤ ρ + ‖x‖ := by linarith [hρ y hy]
    _ ≤ D := le_max_right _ _

lemma integrable_continuous_adm {ν : Measure ℂ} (hν : IsAdmissibleH ν) {f : ℂ → ℝ}
    (hf : Continuous f) : Integrable f ν := by
  obtain ⟨hνf, ⟨K, hK, -, hKc⟩, -⟩ := hν
  have := hνf
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hKae : ∀ᵐ y ∂ν, y ∈ K := ae_iff.2 hKc
  exact Integrable.of_bound hf.aestronglyMeasurable C (hKae.mono fun y hy => hC y hy)

lemma neumannH_ofReal_left (x : ℝ) (z : ℂ) :
    neumannH (x : ℂ) z = -2 * Real.log ‖z - x‖ := by
  unfold neumannH
  have h1 : ‖(x : ℂ) - (starRingEnd ℂ) z‖ = ‖z - x‖ := by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj, Complex.conj_ofReal, norm_sub_rev]
  rw [h1, norm_sub_rev]; ring

lemma fcPot_ofReal (r x : ℝ) (y : ℂ) :
    KernelId.fcPot r x y = -2 * Real.log (max r ‖y - x‖) := by
  unfold KernelId.fcPot
  have h1 : ‖(x : ℂ) - (starRingEnd ℂ) y‖ = ‖y - x‖ := by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj, Complex.conj_ofReal, norm_sub_rev]
  rw [h1, norm_sub_rev]; ring

lemma abs_log_max_le {r d : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) :
    |Real.log (max r d)| ≤ |Real.log d| := by
  rcases le_total r d with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, abs_of_nonpos (Real.log_nonpos hr.le hr1),
      abs_of_nonpos (Real.log_nonpos hd.le (h.trans hr1))]
    exact neg_le_neg (Real.log_le_log hd h)

/-- The potential of an admissible measure against shrinking folded circles at a real point. -/
lemma tendsto_integral_fcPot {ν : Measure ℂ} (hν : IsAdmissibleH ν) (x : ℝ) :
    Tendsto (fun k => ∫ y, KernelId.fcPot (radius k) x y ∂ν) atTop
      (𝓝 (∫ y, neumannH (x : ℂ) y ∂ν)) := by
  have hint := (integrable_log_norm_sub hν (x : ℂ)).abs.const_mul 2
  refine tendsto_integral_of_dominated_convergence (fun y => 2 * |Real.log ‖y - x‖|)
    (fun k => (KernelId.continuous_fcPot (radius_pos k) _).aestronglyMeasurable) hint
    (fun k => ?_) ?_
  · have hna : ∀ᵐ y ∂ν, y ≠ (x : ℂ) := by
      rw [ae_iff]; simpa using noAtoms_of_isAdmissibleH hν (x : ℂ)
    filter_upwards [hna] with y hy
    have hd : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
    rw [fcPot_ofReal, Real.norm_eq_abs, abs_mul, abs_neg, abs_two]
    exact mul_le_mul_of_nonneg_left (abs_log_max_le (radius_pos k) (radius_le_one k) hd)
      zero_le_two
  · have hna : ∀ᵐ y ∂ν, y ≠ (x : ℂ) := by
      rw [ae_iff]; simpa using noAtoms_of_isAdmissibleH hν (x : ℂ)
    filter_upwards [hna] with y hy
    have hd : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
    have hev : ∀ᶠ k in atTop, KernelId.fcPot (radius k) x y = neumannH (x : ℂ) y := by
      have hr : Tendsto radius atTop (𝓝 0) := RegClosure.tendsto_radius_nhdsGT.mono_right
        nhdsWithin_le_nhds
      filter_upwards [hr.eventually (gt_mem_nhds hd)] with k hk
      rw [fcPot_ofReal, neumannH_ofReal_left, max_eq_right hk.le]
    exact tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm)

/-- **`hcov` for the free field.** -/
theorem tendsto_covariance_zG (hX : IsFreeGFFModConstH X P) {R : ℝ} {ν : Measure ℂ}
    (hν : IsAdmissibleH ν) {x : ℝ} (hx : |x| + 1 ≤ R) :
    Tendsto (fun k => cov[fun ω => zG X R ω ν, fun ω => zG X R ω (fcK x k); P]) atTop
      (𝓝 (∫ z, freeKernel R x z ∂ν)) := by
  have hR : 0 < R := by linarith [abs_nonneg x]
  have e : ∀ k, cov[fun ω => zG X R ω ν, fun ω => zG X R ω (fcK x k); P] =
      ∫ y, KernelId.fcPot (radius k) x y ∂ν - ∫ y, KernelId.fcPot R 0 y ∂ν := fun k =>
    covariance_zG_fc hX hν (radius_pos k) (by linarith [radius_le_one k])
  simp_rw [e]
  have hlim : ∫ z, freeKernel R x z ∂ν =
      ∫ y, neumannH (x : ℂ) y ∂ν - ∫ y, KernelId.fcPot R 0 y ∂ν := by
    unfold freeKernel
    refine integral_sub ?_ (integrable_continuous_adm hν (KernelId.continuous_fcPot hR 0))
    have := (integrable_log_norm_sub hν (x : ℂ)).const_mul (-2)
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [neumannH_ofReal_left]
  rw [hlim]
  exact (tendsto_integral_fcPot hν x).sub_const _

/-! ### Part 3: the log-singular decomposition of the shift -/

/-- **Decomposition of the Palm shift.** `(γ/2) c(x,z) = γ (−log ‖z − x‖) + h(z)` with the
continuous `h = −(γ/2) fcPot R 0` (the potential of the normalization circle). -/
theorem half_freeKernel_eq (γ R x : ℝ) (z : ℂ) :
    γ / 2 * freeKernel R x z =
      γ * (-Real.log ‖z - (x : ℂ)‖) + (-(γ / 2) * KernelId.fcPot R 0 z) := by
  unfold freeKernel; rw [neumannH_ofReal_left]; ring

theorem continuous_half_freeKernel_rem (γ : ℝ) {R : ℝ} (hR : 0 < R) :
    Continuous fun z => -(γ / 2) * KernelId.fcPot R 0 z :=
  continuous_const.mul (KernelId.continuous_fcPot hR 0)

/-- The decomposition at the level of pairings with admissible measures. -/
theorem ofFun_half_freeKernel_apply (γ : ℝ) {R : ℝ} (hR : 0 < R) (x : ℝ) {ν : Measure ℂ}
    (hν : IsAdmissibleH ν) :
    ofFun (fun z => γ / 2 * freeKernel R x z) ν =
      ofFun (fun z => γ * (-Real.log ‖z - (x : ℂ)‖)) ν +
        ofFun (fun z => -(γ / 2) * KernelId.fcPot R 0 z) ν := by
  simp only [ofFun, half_freeKernel_eq]
  exact integral_add (((integrable_log_norm_sub hν (x : ℂ)).neg).const_mul γ)
    (integrable_continuous_adm hν (continuous_half_freeKernel_rem γ hR))

end FreeGauss

/-! ## 4. Discharging the remaining hypotheses for `Y = ofFun m + zG X R` -/

section FreeHyp

variable {X : Ω → FieldSample}

open BdryExist GoodSample

/-- `avgReg` only reads folded circles centred in `Hbar`. -/
lemma avgReg_congr_Hbar {y y' : FieldSample} (k : ℕ)
    (h : ∀ w ∈ Hbar, y (foldedCircle w (radius k)) = y' (foldedCircle w (radius k)))
    {z : ℂ} (hz : z ∈ Hbar) : avgReg y k z = avgReg y' k z := by
  unfold avgReg
  congr 1; funext n
  exact h _ (CircleCont.dyadicRoundC_mem_Hbar hz n)

lemma bdryApprox_congr_Hbar {y y' : FieldSample}
    (h : ∀ w ∈ Hbar, ∀ r > 0, y (foldedCircle w r) = y' (foldedCircle w r)) :
    bdryApprox γ y = bdryApprox γ y' := by
  funext k
  unfold bdryApprox
  congr 1; funext t
  rw [avgReg_congr_Hbar k (fun w hw => h w hw _ (radius_pos k)) (GaussTK.ofReal_mem_Hbar t)]

lemma qBoundaryMeasure_congr_Hbar {y y' : FieldSample}
    (h : ∀ w ∈ Hbar, ∀ r > 0, y (foldedCircle w r) = y' (foldedCircle w r)) :
    qBoundaryMeasure γ y = qBoundaryMeasure γ y' := by
  unfold qBoundaryMeasure
  rw [bdryApprox_congr_Hbar h]

lemma zG_add_fc (R : ℝ) (m : ℂ → ℝ) (ω : Ω) :
    ∀ w ∈ Hbar, ∀ r > 0, (ofFun m + zG X R ω) (foldedCircle w r) =
      (zField X R ω + ofFun m) (foldedCircle w r) := fun w hw r hr => by
  simp only [Pi.add_apply]; rw [zG_fc hw hr, add_comm]

lemma zG_add_fc' (R : ℝ) (m : ℂ → ℝ) (ω : Ω) :
    ∀ w ∈ Hbar, ∀ r > 0, (ofFun m + zG X R ω) (foldedCircle w r) =
      (ofFun m + zField X R ω) (foldedCircle w r) := fun w hw r hr => by
  simp only [Pi.add_apply]; rw [zG_fc hw hr]

lemma bdryApprox_zG (R : ℝ) (m : ℂ → ℝ) (ω : Ω) :
    bdryApprox γ (ofFun m + zG X R ω) = bdryApprox γ (zField X R ω + ofFun m) :=
  bdryApprox_congr_Hbar (zG_add_fc R m ω)

lemma qBoundaryMeasure_zG (R : ℝ) (m : ℂ → ℝ) (ω : Ω) :
    qBoundaryMeasure γ (ofFun m + zG X R ω) = qBoundaryMeasure γ (zField X R ω + ofFun m) :=
  qBoundaryMeasure_congr_Hbar (zG_add_fc R m ω)

lemma ae_isRegularSample_zField [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (R : ℝ) : ∀ᵐ ω ∂P, IsRegularSample (zField X R ω) := by
  filter_upwards [RegSample.ae_isRegularSample hX] with ω hω
  have : zField X R ω = X ω + ofFun (fun _ => -X ω (foldedCircle 0 R)) :=
    addConst_eq_add_ofFun _ _
  rw [this]; exact gs_add_ofFun_sample hω continuousOn_const

/-- **`hreg` for the free field.** -/
theorem ae_avgReg_zG [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (R : ℝ)
    (hm : ContinuousOn m Hbar) (k : ℕ) (x : ℝ) :
    ∀ᵐ ω ∂P, avgReg (ofFun m + zG X R ω) k (x : ℂ) = (ofFun m + zG X R ω) (fcK x k) := by
  have hx := GaussTK.ofReal_mem_Hbar x
  filter_upwards [ae_isRegularSample_zField hX R, avgReg_zField_ae_eq hX R k hx] with ω hreg h2
  obtain ⟨F, hF⟩ := hreg
  have e1 := (gs_add_ofFun hF hm).avgReg_eq k hx
  have e2 := hF.avgReg_eq k hx
  rw [avgReg_congr_Hbar k (fun w hw => zG_add_fc R m ω w hw _ (radius_pos k)) hx, e1]
  simp only [Pi.add_apply]
  rw [← e2, h2, zG_fc hx (radius_pos k), ← GaussTK.addConst_fc_eq_fcPairVal]
  simp only [ofFun, fcK, zField]
  ring

/-! ### Pathwise: adding a continuous function to a regular sample -/

/-- The weight `e^{γ m/2}` and its level-`k` smoothing. -/
def eW (γ : ℝ) (m : ℂ → ℝ) (t : ℝ) : ℝ := Real.exp (γ / 2 * m t)

def eWk (γ : ℝ) (m : ℂ → ℝ) (k : ℕ) (t : ℝ) : ℝ := Real.exp (γ / 2 * smoothFun m t (radius k))

lemma continuous_eW (γ : ℝ) (hm : ContinuousOn m Hbar) : Continuous (eW γ m) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_ofReal_comp hm))

lemma continuous_eWk (γ : ℝ) (hm : ContinuousOn m Hbar) (k : ℕ) : Continuous (eWk γ m k) :=
  Real.continuous_exp.comp (continuous_const.mul
    ((continuous_smoothFun hm _).comp Complex.continuous_ofReal))

lemma bdryR_radius' {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (k : ℕ) :
    bdryR γ x (radius k) = bdryApprox γ x k := by
  have := bdryR_radius γ hF k; rwa [one_mul] at this

lemma isFiniteMeasureOnCompacts_bdryApprox {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (k : ℕ) : IsFiniteMeasureOnCompacts (bdryApprox γ x k) :=
  ⟨fun K hK => by rw [← bdryR_radius' hF k]; exact bdryR_lt_top γ hF (radius_pos k) hK⟩

lemma integral_bdryApprox_add_ofFun {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (hm : ContinuousOn m Hbar) (k : ℕ) (f : ℝ → ℝ) :
    ∫ t, f t ∂bdryApprox γ (x + ofFun m) k = ∫ t, eWk γ m k t * f t ∂bdryApprox γ x k := by
  have := integral_bdryR_add_ofFun γ hF hm (radius_pos k) f
  rw [bdryR_radius' hF k, bdryR_radius' (gs_add_ofFun hF hm) k] at this
  exact this

lemma eventually_smooth_close (hm : ContinuousOn m Hbar) (c : ℝ) {K : Set ℝ} (hK : IsCompact K)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ t ∈ K, |c * smoothFun m t (radius k) - c * m t| < δ := by
  have hc := smooth_unif hm (hK.image Complex.continuous_ofReal)
    (fun _ ⟨t, _, ht⟩ => ht ▸ show (0 : ℝ) ≤ (t : ℂ).im by simp) (δ / (|c| + 1)) (by positivity)
  filter_upwards [RegClosure.tendsto_radius_nhdsGT.eventually hc] with k hk t ht
  have h2 := hk _ ⟨t, ht, rfl⟩
  rw [← mul_sub, abs_mul]
  calc |c| * |smoothFun m t (radius k) - m t| ≤ |c| * (δ / (|c| + 1)) :=
        mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

/-- Rule (5.1) along `2^{-k}` for a regular sample. -/
lemma isVagueLimitR_add_ofFun {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (hm : ContinuousOn m Hbar) {ν : Measure ℝ} (hν : IsVagueLimitR (bdryApprox γ x) ν) :
    IsVagueLimitR (bdryApprox γ (x + ofFun m))
      (ν.withDensity fun t => ENNReal.ofReal (eW γ m t)) := by
  have hφr := continuous_ofReal_comp hm
  have hdc := continuous_eW γ hm
  have := hν.1
  refine ⟨?_, fun f hf hfc => ?_⟩
  · have : IsFiniteMeasureOnCompacts (ν.withDensity fun t => ENNReal.ofReal (eW γ m t)) :=
      ⟨fun K hK => withDensity_lt_top hK hK.measure_lt_top hdc.continuousOn⟩
    infer_instance
  rw [integral_withDensity_ofReal hdc.measurable fun _ => (Real.exp_pos _).le]
  have key := tendsto_integral_exp_mul (X := ℝ) (L := atTop) (U := univ) isOpen_univ
    (νs := fun k => bdryApprox γ x k) (ν := ν)
    (Eventually.of_forall fun k K hK _ => by
      rw [← bdryR_radius' hF k]; exact bdryR_lt_top γ hF (radius_pos k) hK)
    (fun g hg hgc _ => hν.2 g hg hgc)
    (v := fun k t => γ / 2 * smoothFun m t (radius k)) (v0 := fun t => γ / 2 * m t)
    (continuous_const.mul hφr).continuousOn
    (Eventually.of_forall fun k => (continuous_const.mul
      ((continuous_smoothFun hm _).comp Complex.continuous_ofReal)).continuousOn)
    (fun K hK _ ε hε => eventually_smooth_close hm (γ / 2) hK ε hε)
    hf hfc (subset_univ _)
  exact key.congr fun k => (integral_bdryApprox_add_ofFun hF hm k f).symm

/-- A.s. `ν_{Z + m} = e^{γ m/2} ν_Z` for the normalized free field. -/
lemma ae_qBoundaryMeasure_add_ofFun [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) (hm : ContinuousOn m Hbar) :
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (zField X R ω + ofFun m) =
      (qBoundaryMeasure γ (zField X R ω)).withDensity fun t => ENNReal.ofReal (eW γ m t) := by
  filter_upwards [ae_isRegularSample_zField hX R,
    ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R] with ω hreg hv
  obtain ⟨F, hF⟩ := hreg
  exact qBoundaryMeasure_eq (isVagueLimitR_add_ofFun hF hm hv)

/-- **`hfin` for the free field.** -/
theorem lintegral_qBoundaryMeasure_zG_lt_top [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {R : ℝ}
    (hR : (N : ℝ) + 2 ≤ R) {a b : ℝ} (hab : Icc a b ⊆ Icc (-(N : ℝ)) N)
    (hm : ContinuousOn m Hbar) :
    ∫⁻ ω, qBoundaryMeasure γ (ofFun m + zG X R ω) (Icc a b) ∂P < ∞ := by
  have hSR : ∀ t ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), |t| + 1 ≤ R := fun t ht =>
    (testSet_bound N t ht).trans hR
  obtain ⟨hGi, -⟩ := tendsto_integral_bdryApprox hX hγ hγ2 measurableSet_Icc
    (volume_testSet_lt_top N) hSR (BdryVague.continuous_bump N) (BdryVague.hasCompactSupport_bump N)
    (fun t ht => bump_eq_zero_of_notMem ht)
  obtain ⟨E, hE⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (continuous_eW γ hm).continuousOn
  have hbd : ∀ᵐ ω ∂P, qBoundaryMeasure γ (ofFun m + zG X R ω) (Icc a b) ≤
      ENNReal.ofReal E * ENNReal.ofReal
        (∫ t, BdryVague.bump N t ∂qBoundaryMeasure γ (zField X R ω)) := by
    filter_upwards [ae_qBoundaryMeasure_add_ofFun hX hγ hγ2 R hm,
      ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R] with ω hω hv
    have := hv.1
    rw [qBoundaryMeasure_zG, hω, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ t in Icc a b, ENNReal.ofReal (eW γ m t) ∂qBoundaryMeasure γ (zField X R ω)
        ≤ ∫⁻ _ in Icc a b, ENNReal.ofReal E ∂qBoundaryMeasure γ (zField X R ω) :=
          setLIntegral_mono measurable_const fun t ht => ENNReal.ofReal_le_ofReal
            ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hE t ht))
      _ = ENNReal.ofReal E * qBoundaryMeasure γ (zField X R ω) (Icc a b) :=
          setLIntegral_const _ _
      _ ≤ _ := by
          gcongr
          rw [ofReal_integral_eq_lintegral_ofReal ((BdryVague.continuous_bump N).integrable_of_hasCompactSupport
            (BdryVague.hasCompactSupport_bump N)) (ae_of_all _ (BdryVague.bump_nonneg N)),
            ← lintegral_indicator_one measurableSet_Icc]
          refine lintegral_mono fun t => ?_
          by_cases ht : t ∈ Icc a b
          · rw [indicator_of_mem ht, Pi.one_apply, BdryVague.bump_eq_one (abs_le.2 (hab ht)),
              ENNReal.ofReal_one]
          · rw [indicator_of_notMem ht]; exact bot_le
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal E * ENNReal.ofReal
        (∫ t, BdryVague.bump N t ∂qBoundaryMeasure γ (zField X R ω)) ∂P := lintegral_mono_ae hbd
    _ = ENNReal.ofReal E * ∫⁻ ω, ENNReal.ofReal
        (∫ t, BdryVague.bump N t ∂qBoundaryMeasure γ (zField X R ω)) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGi.lintegral_lt_top

lemma tendsto_zero_of_eventually_le {a G : ℕ → ℝ} {L C : ℝ} (ha : ∀ k, 0 ≤ a k) (hC : 0 ≤ C)
    (hG : Tendsto G atTop (𝓝 L))
    (h : ∀ η > 0, ∀ᶠ k in atTop, a k ≤ η * C * G k) : Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set D := C * (|L| + 1) with hD
  have hD0 : 0 ≤ D := mul_nonneg hC (by positivity)
  have hη : 0 < ε / (D + 1) := by positivity
  obtain ⟨N1, hN1⟩ := (h _ hη).exists_forall_of_atTop
  obtain ⟨N2, hN2⟩ := (hG.eventually (gt_mem_nhds
    (show L < |L| + 1 by linarith [le_abs_self L]))).exists_forall_of_atTop
  refine ⟨max N1 N2, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha n)]
  have h1 := hN1 n (le_of_max_le_left hn)
  have h2 := hN2 n (le_of_max_le_right hn)
  calc a n ≤ ε / (D + 1) * C * G n := h1
    _ ≤ ε / (D + 1) * C * (|L| + 1) := by
        gcongr
    _ = ε * D / (D + 1) := by rw [hD]; ring
    _ < ε := by rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- **`L¹` convergence (`C_c` form) for the free field.** -/
theorem bdryL1ConvCc_zG [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ)
    (hγ2 : γ < 2) {N : ℕ} {R : ℝ} (hR : (N : ℝ) + 2 ≤ R) {a b : ℝ}
    (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) (hm : ContinuousOn m Hbar) :
    BdryL1ConvCc γ m (zG X R) P (fun ω => qBoundaryMeasure γ (ofFun m + zG X R ω)) a b := by
  intro f hf hfc hfab
  have hSR : ∀ t ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), |t| + 1 ≤ R := fun t ht =>
    (testSet_bound N t ht).trans hR
  have hfS : ∀ t ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), f t = 0 := fun t ht => hfab t fun h =>
    ht ⟨by linarith [(hab h).1], by linarith [(hab h).2]⟩
  have hec := continuous_eW γ hm
  have hekc := continuous_eWk γ hm
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfc
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
  -- the `B` part: the rate lemma for `e f`
  have hef_c : Continuous (fun t => eW γ m t * f t) := hec.mul hf
  have hef_cs : HasCompactSupport (fun t => eW γ m t * f t) := hfc.mul_left
  obtain ⟨CB, -, hCB⟩ := integral_abs_bdryApprox_sub_qBoundaryMeasure_le hX hγ hγ2
    measurableSet_Icc (volume_testSet_lt_top N) hSR hef_c hef_cs
    (fun t ht => by rw [hfS t ht, mul_zero])
  have hB0 : Tendsto (fun k => ∫ ω, |∫ t, eW γ m t * f t ∂bdryApprox γ (zField X R ω) k -
      ∫ t, eW γ m t * f t ∂qBoundaryMeasure γ (zField X R ω)| ∂P) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k : ℕ => CB * Real.exp (-bdryRate γ * (k * Real.log 2))) atTop
        (𝓝 0) := by
      have hq1 : Real.exp (-bdryRate γ * Real.log 2) < 1 := by
        rw [Real.exp_lt_one_iff]
        have := bdryRate_pos hγ hγ2
        have := Real.log_pos one_lt_two
        nlinarith
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hq1).const_mul CB
      rw [mul_zero] at this
      refine this.congr fun k => ?_
      rw [← Real.exp_nat_mul]; congr 2; ring
    exact squeeze_zero (fun k => integral_nonneg fun ω => abs_nonneg _) (fun k => (hCB k).2) hlim
  -- the `A` part
  have hbump1 : ∀ t, |BdryVague.bump N t| ≤ 1 := fun t => by
    rw [abs_of_nonneg (BdryVague.bump_nonneg N t)]
    exact max_le zero_le_one (min_le_left _ _)
  have hGint : ∀ k, Integrable (fun ω => ∫ t, BdryVague.bump N t ∂bdryApprox γ (zField X R ω) k)
      P := fun k => integrable_integral_bdryApprox hX measurableSet_Icc (volume_testSet_lt_top N)
    hSR γ (BdryVague.continuous_bump N).measurable hbump1 (fun t ht => bump_eq_zero_of_notMem ht) k
  obtain ⟨-, hGt⟩ := tendsto_integral_bdryApprox hX hγ hγ2 measurableSet_Icc
    (volume_testSet_lt_top N) hSR (BdryVague.continuous_bump N) (BdryVague.hasCompactSupport_bump N)
    (fun t ht => bump_eq_zero_of_notMem ht)
  have hAint : ∀ k, Integrable (fun ω => ∫ t, (eWk γ m k t - eW γ m t) * f t
      ∂bdryApprox γ (zField X R ω) k) P := fun k => by
    have hc : Continuous fun t => (eWk γ m k t - eW γ m t) * f t := ((hekc k).sub hec).mul hf
    obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hfc.mul_left
    exact integrable_integral_bdryApprox hX measurableSet_Icc (volume_testSet_lt_top N) hSR γ
      hc.measurable (M := M) (fun t => by simpa [Real.norm_eq_abs] using hM t)
      (fun t ht => by rw [hfS t ht, mul_zero]) k
  -- uniform closeness of the weights on `[a,b]`
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (continuous_const.mul (continuous_ofReal_comp hm) : Continuous fun t : ℝ => γ / 2 * m t).continuousOn
  have hclose : ∀ η > 0, ∀ᶠ k in atTop, ∀ t ∈ Icc a b, |eWk γ m k t - eW γ m t| ≤ η := by
    intro η hη
    have hδ : 0 < min 1 (η / Real.exp (M0 + 1)) := lt_min one_pos (by positivity)
    filter_upwards [eventually_smooth_close hm (γ / 2) isCompact_Icc _ hδ] with k hk t ht
    have h1 := hk t ht
    have hv : γ / 2 * m t ≤ M0 :=
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hM0 t ht)
    have hu : γ / 2 * smoothFun m t (radius k) ≤ M0 + 1 := by
      have := (abs_lt.1 h1).2
      linarith [min_le_left 1 (η / Real.exp (M0 + 1))]
    unfold eWk eW
    calc |Real.exp (γ / 2 * smoothFun m t (radius k)) - Real.exp (γ / 2 * m t)|
        ≤ Real.exp (M0 + 1) * |γ / 2 * smoothFun m t (radius k) - γ / 2 * m t| :=
          RegSample.abs_exp_sub_exp_le hu (by linarith)
      _ ≤ Real.exp (M0 + 1) * (η / Real.exp (M0 + 1)) :=
          mul_le_mul_of_nonneg_left (h1.le.trans (min_le_right _ _)) (Real.exp_pos _).le
      _ = η := by field_simp
  have hA0 : Tendsto (fun k => ∫ ω, |∫ t, (eWk γ m k t - eW γ m t) * f t
      ∂bdryApprox γ (zField X R ω) k| ∂P) atTop (𝓝 0) := by
    refine tendsto_zero_of_eventually_le (fun k => integral_nonneg fun ω => abs_nonneg _) hCf0 hGt
      fun η hη => ?_
    filter_upwards [hclose η hη] with k hk
    have hpt : ∀ t, ‖(eWk γ m k t - eW γ m t) * f t‖ ≤ η * Cf * BdryVague.bump N t := by
      intro t
      by_cases ht : t ∈ Icc a b
      · rw [BdryVague.bump_eq_one (abs_le.2 (hab ht)), mul_one, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hk t ht) (hCf t) (norm_nonneg _) hη.le
      · rw [hfab t ht, mul_zero, norm_zero]
        exact mul_nonneg (mul_nonneg hη.le hCf0) (BdryVague.bump_nonneg N t)
    have hbd : ∀ᵐ ω ∂P, |∫ t, (eWk γ m k t - eW γ m t) * f t ∂bdryApprox γ (zField X R ω) k| ≤
        η * Cf * ∫ t, BdryVague.bump N t ∂bdryApprox γ (zField X R ω) k := by
      filter_upwards [ae_isRegularSample_zField hX R] with ω hreg
      obtain ⟨F, hF⟩ := hreg
      have := isFiniteMeasureOnCompacts_bdryApprox (γ := γ) hF k
      rw [← integral_const_mul, ← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le (((BdryVague.continuous_bump N).integrable_of_hasCompactSupport
        (BdryVague.hasCompactSupport_bump N)).const_mul _) (ae_of_all _ hpt)
    calc ∫ ω, |∫ t, (eWk γ m k t - eW γ m t) * f t ∂bdryApprox γ (zField X R ω) k| ∂P
        ≤ ∫ ω, η * Cf * ∫ t, BdryVague.bump N t ∂bdryApprox γ (zField X R ω) k ∂P :=
          integral_mono_ae (hAint k).abs ((hGint k).const_mul _) hbd
      _ = η * Cf * ∫ ω, ∫ t, BdryVague.bump N t ∂bdryApprox γ (zField X R ω) k ∂P :=
          integral_const_mul _ _
  -- pathwise decomposition
  have hdec : ∀ k, ∀ᵐ ω ∂P, ∫ t, f t ∂bdryApprox γ (ofFun m + zG X R ω) k -
      ∫ t, f t ∂qBoundaryMeasure γ (ofFun m + zG X R ω) =
      (∫ t, (eWk γ m k t - eW γ m t) * f t ∂bdryApprox γ (zField X R ω) k) +
      (∫ t, eW γ m t * f t ∂bdryApprox γ (zField X R ω) k -
        ∫ t, eW γ m t * f t ∂qBoundaryMeasure γ (zField X R ω)) := by
    intro k
    filter_upwards [ae_isRegularSample_zField hX R, ae_qBoundaryMeasure_add_ofFun hX hγ hγ2 R hm]
      with ω hreg hq
    obtain ⟨F, hF⟩ := hreg
    have := isFiniteMeasureOnCompacts_bdryApprox (γ := γ) hF k
    rw [bdryApprox_zG, qBoundaryMeasure_zG, hq, integral_bdryApprox_add_ofFun hF hm k f,
      integral_withDensity_ofReal hec.measurable (fun _ => (Real.exp_pos _).le)]
    have hi1 : Integrable (fun t => eWk γ m k t * f t) (bdryApprox γ (zField X R ω) k) :=
      ((hekc k).mul hf).integrable_of_hasCompactSupport hfc.mul_left
    have hi2 : Integrable (fun t => eW γ m t * f t) (bdryApprox γ (zField X R ω) k) :=
      hef_c.integrable_of_hasCompactSupport hef_cs
    have e3 : ∫ t, (eWk γ m k t - eW γ m t) * f t ∂bdryApprox γ (zField X R ω) k =
        ∫ t, eWk γ m k t * f t ∂bdryApprox γ (zField X R ω) k -
          ∫ t, eW γ m t * f t ∂bdryApprox γ (zField X R ω) k := by
      simp_rw [sub_mul]; exact integral_sub hi1 hi2
    rw [e3]; ring
  refine squeeze_zero (fun k => integral_nonneg fun ω => abs_nonneg _) (fun k => ?_)
    (by simpa using hA0.add hB0)
  rw [← integral_add (hAint k).abs (hCB k).1.abs]
  refine integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
    ((hAint k).abs.add (hCB k).1.abs) ?_
  filter_upwards [hdec k] with ω hω
  rw [hω]; exact abs_add_le _ _

/-- **`hν` for the free field**: `ω ↦ ν_{ofFun m + zField X R ω}` is a.e. measurable. -/
theorem aemeasurable_qBoundaryMeasure_free [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) (hm : ContinuousOn m Hbar) :
    AEMeasurable (fun ω => qBoundaryMeasure γ (ofFun m + zField X R ω)) P := by
  have hae : ∀ᵐ ω ∂P, IsVagueLimitR (bdryApprox γ (zField X R ω + ofFun m))
      (qBoundaryMeasure γ (zField X R ω + ofFun m)) := by
    filter_upwards [ae_isRegularSample_zField hX R,
      ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R] with ω hreg hv
    obtain ⟨F, hF⟩ := hreg
    have hv' := isVagueLimitR_add_ofFun hF hm hv
    rwa [qBoundaryMeasure_eq hv']
  have h := LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae
    (X := fun ω => zField X R ω + ofFun m)
    (fun μ => ((measurable_pi_apply μ).comp (measurable_zField hX R)).add_const _) hae
  refine h.congr (ae_of_all _ fun ω => ?_)
  show qBoundaryMeasure γ (zField X R ω + ofFun m) = qBoundaryMeasure γ (ofFun m + zField X R ω)
  rw [add_comm]

end FreeHyp

/-! ## 5. The free-field Palm formula -/

/-- **Blueprint D1 for the free field (weighted form).** Let `X` be a free GFF on `ℍ` modulo
constants, `Y = ofFun m + zField X R` its normalization at `fc(0,R)` plus a continuous `m`,
`ν_Y = qBoundaryMeasure γ Y`, `0 < γ < 2`, and `[a,b] ⊆ [-N,N]` with `N + 2 ≤ R`. For a
continuous nonnegative compactly supported weight `w` vanishing off `[a,b]`, admissible measures
`μ_j`, and bounded measurable `φ`,
`E ∫ w(x) φ((Y μ_j)_j, x) ν_Y(dx) =
  ∫ w(x) exp(γ m(x)/2 + γ² log R / 4) E φ(((Y + ofFun((γ/2) c(x,·))) μ_j)_j, x) dx`
with `c = freeKernel R` (`c(x,z) = G_N(x,z) − ∫ G_N(z,·) d fc(0,R)`, `c̃ = 2 log R`). No
hypothesis beyond the setting remains. -/
theorem palm_formula_free {X : Ω → FieldSample} [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {R : ℝ}
    (hR : (N : ℝ) + 2 ≤ R) {a b : ℝ} (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) (hm : Continuous m)
    (hμ : ∀ j, IsAdmissibleH (μ j))
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hwab : ∀ x ∉ Icc a b, w x = 0)
    {φ : (ℕ → ℝ) → ℝ → ℝ} (hφ : Measurable (Function.uncurry φ)) {Cφ : ℝ}
    (hφb : ∀ y x, |φ y x| ≤ Cφ) :
    ∫ ω, ∫ x, w x * φ (fun j => (ofFun m + BdryExist.zField X R ω) (μ j)) x
        ∂(qBoundaryMeasure γ (ofFun m + BdryExist.zField X R ω)) ∂P =
      ∫ x, w x * Real.exp (γ * m x / 2 + γ ^ 2 * (2 * Real.log R) / 8) *
        ∫ ω, φ (fun j => (ofFun m + BdryExist.zField X R ω +
          ofFun (fun z => γ / 2 * freeKernel R x z)) (μ j)) x ∂P := by
  have hR0 : 0 < R := by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  have : ∀ j, IsFiniteMeasure (μ j) := fun j => (hμ j).1
  have hxR : ∀ x ∈ Icc a b, |x| + 1 ≤ R := fun x hx => by
    have := abs_le.2 (hab hx); linarith
  have hqb : ∀ ω, qBoundaryMeasure γ (ofFun m + zG X R ω) =
      qBoundaryMeasure γ (ofFun m + BdryExist.zField X R ω) := fun ω =>
    qBoundaryMeasure_congr_Hbar (zG_add_fc' R m ω)
  have hν' : AEMeasurable (fun ω => qBoundaryMeasure γ (ofFun m + zG X R ω)) P := by
    rw [show (fun ω => qBoundaryMeasure γ (ofFun m + zG X R ω)) = fun ω =>
      qBoundaryMeasure γ (ofFun m + BdryExist.zField X R ω) from funext hqb]
    exact aemeasurable_qBoundaryMeasure_free hX hγ hγ2 R hm.continuousOn
  have hvar : ∀ k, ∀ x ∈ Icc a b,
      Var[fun ω => zG X R ω (fcK x k); P] + 2 * Real.log (radius k) = 2 * Real.log R :=
    fun k x hx => variance_zG_fc hX (radius_pos k) (by linarith [hxR x hx, BdryExist.radius_le_one k])
  have H := palm_formula_weight (Z := zG X R) (μ := μ) (γ := γ)
    (ν := fun ω => qBoundaryMeasure γ (ofFun m + zG X R ω)) (isCenteredGaussianField_zG hX hR0) hm
    (Cv := 2 * Real.log R) (ctil := fun _ => 2 * Real.log R) measurable_const
    (measurable_freeKernel hR0)
    (fun k x _ => ae_avgReg_zG hX R hm.continuousOn k x)
    (fun k x hx => (hvar k x hx).le)
    (fun x hx => tendsto_const_nhds.congr fun k => (hvar k x hx).symm)
    (fun x hx j => tendsto_covariance_zG hX (hμ j) (hxR x hx))
    hν' (lintegral_qBoundaryMeasure_zG_lt_top hX hγ hγ2 hR hab hm.continuousOn)
    (bdryL1ConvCc_zG hX hγ hγ2 hR hab hm.continuousOn) hw hwc hw0 hwab hφ hφb
  have hc1 : ∀ ω, (fun j => (ofFun m + zG X R ω) (μ j)) =
      fun j => (ofFun m + BdryExist.zField X R ω) (μ j) := fun ω => by
    funext j; simp only [Pi.add_apply]; rw [zG_of_adm (hμ j)]
  have hc2 : ∀ ω x, (fun j => (ofFun m + zG X R ω + ofFun (fun z => γ / 2 * freeKernel R x z))
      (μ j)) = fun j => (ofFun m + BdryExist.zField X R ω +
        ofFun (fun z => γ / 2 * freeKernel R x z)) (μ j) := fun ω x => by
    funext j; simp only [Pi.add_apply]; rw [zG_of_adm (hμ j)]
  simp only [hc1, hc2, hqb] at H
  exact H

end PalmFree
end QuantumZipper
