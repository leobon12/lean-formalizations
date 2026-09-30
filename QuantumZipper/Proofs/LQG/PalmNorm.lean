import QuantumZipper.Proofs.LQG.PalmFree
import QuantumZipper.Proofs.LQG.PalmArea

/-!
# E1 sub-node PALM-NORM: the boundary Palm formula with a general admissible normalizer

Blueprint `E_BRANCH_BLUEPRINT.md` §4 E1, step (2). For `X` free, `h` continuous and `ϖ` an
admissible probability measure, `N_ϖ y := addConst y (−(y ϖ))` (E_BRANCH §2):
`E ∫ w(x) φ(N_ϖ(ofFun h + X), x) ν(dx)
  = ∫ w(x) ρ_ϖ(x) E φ(N_ϖ(ofFun (h + (γ/2)(neumannH x · − k_ϖ)) + X), x) dx`
with `ν = qBoundaryMeasure γ (N_ϖ(ofFun h + X))`, `k_ϖ u = ∫ neumannH u v dϖ(v)`,
`kk_ϖ = ∫∫ neumannH dϖ dϖ` and
`ρ_ϖ(x) = exp(γ h(x)/2 − (γ/2) ∫ h dϖ − (γ²/4) k_ϖ(x) + (γ²/8) kk_ϖ)`,
for nonnegative measurable (possibly unbounded) `φ`, in `lintegral` form (`palm_formula_norm`).

Sources. The Palm (rooted-measure) formula for Gaussian multiplicative chaos is due to
B. Duplantier, S. Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
arXiv:0808.1560, §3 (quantum typical points / rooted measure); the change of normalizer by a
Cameron–Martin tilt is the route of `blueprint/E_BRANCH_BLUEPRINT.md` §4 E1 (project design; the
Cameron–Martin formula itself is `CameronMartin.map_tiltMeasure_path`, blueprint A9).

Route (blueprint): `palm_lintegral_coords` is `palm_formula_weight_coords` for nonnegative
unbounded `G` (the two Palm measures agree); the free-field instance `palm_lintegral_free` uses the
normalizer `fc(0,R)`; then the factor `e^{−γ Y(ϖ)/2}` relating `ν_{N_ϖ Y}` to `ν_Y` is inserted into
`φ` and removed on the right side by Cameron–Martin (`lintegral_mul_tiltDensity`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

set_option linter.unusedSectionVars false

namespace QuantumZipper
namespace PalmNorm

open Palm PalmFree

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Z : Ω → FieldSample} {m : ℂ → ℝ} {μ : ℕ → Measure ℂ} {γ : ℝ} {a b : ℝ}
  {ν : Ω → Measure ℝ}

/-! ## 1. The Palm formula for nonnegative unbounded test functions -/

/-- **Palm identity, `lintegral` form**: `palm_formula_weight_coords` for every measurable
`G ≥ 0` (the two Palm measures on `(ℕ → ℝ) × ℝ` coincide). -/
theorem palm_lintegral_coords (hZ : IsCenteredGaussianField P Z)
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
    {G : (ℕ → ℝ) × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (w x) * G (coords m Z μ ω, x) ∂(ν ω) ∂P =
      ∫⁻ x, ENNReal.ofReal (w x * rhoLim γ m ctil x) *
        ∫⁻ ω, G (coords m Z μ ω + shiftLim γ c μ x, x) ∂P := by
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
  -- lintegral against the two measures
  have hWG : Measurable ((fun p : (ℕ → ℝ) × ℝ => (wN p.2 : ℝ≥0∞)) * G) := hwNm'.mul hG
  have hLlin : ∫⁻ p, G p ∂ML =
      ∫⁻ ω, ∫⁻ x in Icc a b, ENNReal.ofReal (w x) * G (coords m Z μ ω, x) ∂(ν ω) ∂P := by
    rw [hML, lintegral_withDensity_eq_lintegral_mul _ hwNm' hG, hML0,
      lintegral_map hWG hmapL, Measure.lintegral_compProd (f := fun q : Ω × ℝ =>
        ((fun p : (ℕ → ℝ) × ℝ => (wN p.2 : ℝ≥0∞)) * G) (coords m Z μ q.1, q.2))
        (hWG.comp hmapL)]
    refine lintegral_congr_ae ((nuMod_ae_eq hν hI hfin).mono fun ω hω => ?_)
    simp only [hκ, kerI_apply, hω, Pi.mul_apply]
    rfl
  have hRlin : ∫⁻ p, G p ∂MR = ∫⁻ x in Icc a b, ENNReal.ofReal (rhoLim γ m ctil x) *
      (ENNReal.ofReal (w x) * ∫⁻ ω, G (coords m Z μ ω + shiftLim γ c μ x, x) ∂P) := by
    have hin : Measurable fun x => ∫⁻ ω,
        (wN x : ℝ≥0∞) * G (coords m Z μ ω + shiftLim γ c μ x, x) ∂P :=
      Measurable.lintegral_prod_right' (f := fun p : ℝ × Ω =>
        (wN p.1 : ℝ≥0∞) * G (coords m Z μ p.2 + shiftLim γ c μ p.1, p.1)) (hWG.comp hmapR)
    rw [hMR, lintegral_withDensity_eq_lintegral_mul _ hwNm' hG, hMR0,
      lintegral_map hWG hmapR, lintegral_prod (f := fun q : ℝ × Ω =>
        ((fun p : (ℕ → ℝ) × ℝ => (wN p.2 : ℝ≥0∞)) * G) (coords m Z μ q.2 + shiftLim γ c μ q.1, q.1))
        (hWG.comp hmapR).aemeasurable, hD]
    simp only [Pi.mul_apply]
    rw [lintegral_withDensity_eq_lintegral_mul _ hρNm.coe_nnreal_ennreal hin]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [lintegral_const_mul _ (f := fun ω => G (coords m Z μ ω + shiftLim γ c μ x, x))
      (hG.comp (((measurable_coords hZ).add_const _).prodMk measurable_const))]
    rfl
  have hsuppL : ∀ ω, (fun x => ENNReal.ofReal (w x) * G (coords m Z μ ω, x)).support ⊆ Icc a b :=
    fun ω x hx => by
      by_contra h
      exact hx (by simp only [hwab x h, ENNReal.ofReal_zero, zero_mul])
  have hsuppR : (fun x => ENNReal.ofReal (w x * rhoLim γ m ctil x) *
      ∫⁻ ω, G (coords m Z μ ω + shiftLim γ c μ x, x) ∂P).support ⊆ Icc a b := fun x hx => by
    by_contra h
    exact hx (by simp only [hwab x h, zero_mul, ENNReal.ofReal_zero])
  have h1 := hLlin
  rw [hM, hRlin] at h1
  have eL : ∀ ω, ∫⁻ x, ENNReal.ofReal (w x) * G (coords m Z μ ω, x) ∂(ν ω) =
      ∫⁻ x in Icc a b, ENNReal.ofReal (w x) * G (coords m Z μ ω, x) ∂(ν ω) := fun ω =>
    (setLIntegral_eq_of_support_subset (hsuppL ω)).symm
  rw [lintegral_congr eL, ← setLIntegral_eq_of_support_subset hsuppR, ← h1]
  refine setLIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [ENNReal.ofReal_mul (hw0 x)]
  ring

/-- **Free-field Palm identity, `lintegral` form** (normalizer `fc(0,R)`). -/
theorem palm_lintegral_free {X : Ω → FieldSample} [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {R : ℝ}
    (hR : (N : ℝ) + 2 ≤ R) (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) (hm : Continuous m)
    (hμ : ∀ j, IsAdmissibleH (μ j))
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hwab : ∀ x ∉ Icc a b, w x = 0)
    {G : (ℕ → ℝ) × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (w x) *
        G (fun j => (ofFun m + BdryExist.zField X R ω) (μ j), x)
        ∂(qBoundaryMeasure γ (ofFun m + BdryExist.zField X R ω)) ∂P =
      ∫⁻ x, ENNReal.ofReal (w x * Real.exp (γ * m x / 2 + γ ^ 2 * (2 * Real.log R) / 8)) *
        ∫⁻ ω, G (fun j => (ofFun m + BdryExist.zField X R ω +
          ofFun (fun z => γ / 2 * freeKernel R x z)) (μ j), x) ∂P := by
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
    fun k x hx => variance_zG_fc hX (radius_pos k)
      (by linarith [hxR x hx, BdryExist.radius_le_one k])
  have H := palm_lintegral_coords (Z := zG X R) (μ := μ) (γ := γ)
    (ν := fun ω => qBoundaryMeasure γ (ofFun m + zG X R ω)) (isCenteredGaussianField_zG hX hR0) hm
    (Cv := 2 * Real.log R) (ctil := fun _ => 2 * Real.log R) measurable_const
    (measurable_freeKernel hR0)
    (fun k x _ => ae_avgReg_zG hX R hm.continuousOn k x)
    (fun k x hx => (hvar k x hx).le)
    (fun x hx => tendsto_const_nhds.congr fun k => (hvar k x hx).symm)
    (fun x hx j => tendsto_covariance_zG hX (hμ j) (hxR x hx))
    hν' (lintegral_qBoundaryMeasure_zG_lt_top hX hγ hγ2 hR hab hm.continuousOn)
    (bdryL1ConvCc_zG hX hγ hγ2 hR hab hm.continuousOn) hw hwc hw0 hwab hG
  simp only [coords_add_shiftLim'] at H
  have hc1 : ∀ ω, coords m (zG X R) μ ω =
      fun j => (ofFun m + BdryExist.zField X R ω) (μ j) := fun ω => by
    funext j; simp only [coords, Pi.add_apply]; rw [zG_of_adm (hμ j)]
  have hc2 : ∀ ω x, (fun j => (ofFun m + zG X R ω + ofFun (fun z => γ / 2 * freeKernel R x z))
      (μ j)) = fun j => (ofFun m + BdryExist.zField X R ω +
        ofFun (fun z => γ / 2 * freeKernel R x z)) (μ j) := fun ω x => by
    funext j; simp only [Pi.add_apply]; rw [zG_of_adm (hμ j)]
  simp only [hc1, hc2, hqb, rhoLim] at H
  exact H

/-! ## 2. Cameron–Martin in `lintegral` form -/

theorem lintegral_mul_tiltDensity {I : Type*} {X : I → Ω → ℝ} (hX : IsGaussianProcess X P)
    (hmeas : ∀ i, Measurable (X i)) (hcent : ∀ i, P[X i] = 0) (σ : I →₀ ℝ)
    (Φ : (I → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (fun j => X j ω) * ENNReal.ofReal (CameronMartin.tiltDensity X P σ ω) ∂P =
      ∫⁻ ω, Φ (fun j => X j ω + CameronMartin.covShift X P σ j) ∂P := by
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  have hp' : Measurable fun ω j ↦ X j ω + CameronMartin.covShift X P σ j :=
    measurable_pi_iff.mpr fun j ↦ (hmeas j).add_const _
  rw [← lintegral_map hΦ hp', ← CameronMartin.map_tiltMeasure_path hX hmeas hcent σ,
    lintegral_map hΦ hp, CameronMartin.tiltMeasure,
    lintegral_withDensity_eq_lintegral_mul _
      (CameronMartin.measurable_tiltDensity hX hmeas σ).real_toNNReal.coe_nnreal_ennreal
      (g := fun a => Φ fun j => X j a) (hΦ.comp hp)]
  refine lintegral_congr fun ω => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm]; rfl

/-! ## 3. The general normalizer -/

/-- `N_ϖ y := addConst y (−(y ϖ))` (E_BRANCH §2). -/
def normAt (ϖ : Measure ℂ) (y : FieldSample) : FieldSample := addConst y (-(y ϖ))

/-- The potential `k_ϖ u = ∫ neumannH u v dϖ(v)`. -/
def kPot (ϖ : Measure ℂ) (u : ℂ) : ℝ := ∫ v, neumannH u v ∂ϖ

/-- `kk_ϖ = ∫∫ neumannH dϖ dϖ`. -/
def kkPot (ϖ : Measure ℂ) : ℝ := kernelCov neumannH ϖ ϖ

/-- The Palm density `ρ_ϖ(x) = exp(γ h(x)/2 − (γ/2)∫h dϖ − (γ²/4) k_ϖ(x) + (γ²/8) kk_ϖ)`. -/
def rhoNorm (γ : ℝ) (h : ℂ → ℝ) (ϖ : Measure ℂ) (x : ℝ) : ℝ :=
  Real.exp (γ * h x / 2 - γ / 2 * ∫ u, h u ∂ϖ - γ ^ 2 / 4 * kPot ϖ x + γ ^ 2 / 8 * kkPot ϖ)

/-- The shifted mean `h + (γ/2)(neumannH x · − k_ϖ)`. -/
def shiftFun (γ : ℝ) (h : ℂ → ℝ) (ϖ : Measure ℂ) (x : ℝ) (u : ℂ) : ℝ :=
  h u + γ / 2 * (neumannH (x : ℂ) u - kPot ϖ u)

/-- The coordinate family `ϖ, μ 0, μ 1, …`. -/
def muCons (ϖ : Measure ℂ) (μ : ℕ → Measure ℂ) : ℕ → Measure ℂ
  | 0 => ϖ
  | n + 1 => μ n

section Norm

variable {X : Ω → FieldSample} {h : ℂ → ℝ} {ϖ : Measure ℂ}

open BdryExist

lemma normAt_zField (hϖ1 : ϖ univ = 1) (R : ℝ) (g : ℂ → ℝ) (ω : Ω) :
    normAt ϖ (ofFun g + X ω) = normAt ϖ (ofFun g + zField X R ω) := by
  funext ν
  simp only [normAt, addConst, zField, Pi.add_apply, hϖ1, ENNReal.toReal_one]
  ring

lemma kernelCov_symm_adm {μ₁ μ₂ : Measure ℂ} (h₁ : IsAdmissibleH μ₁) (h₂ : IsAdmissibleH μ₂) :
    kernelCov neumannH μ₁ μ₂ = kernelCov neumannH μ₂ μ₁ := by
  have := h₁.1; have := h₂.1
  unfold kernelCov
  rw [integral_integral_swap (integrable_neumannH_prod h₁ h₂)]
  simp_rw [neumannH_symm]

lemma integrable_kPot {ν : Measure ℂ} (hν : IsAdmissibleH ν) (hϖ : IsAdmissibleH ϖ) :
    Integrable (kPot ϖ) ν := by
  have := hν.1; have := hϖ.1
  exact (integrable_neumannH_prod hν hϖ).integral_prod_left

/-- A.s. `ν_{N_ϖ Y} = e^{−γ Y(ϖ)/2} ν_Y` for `Y = ofFun h + zField X R`. -/
lemma ae_qBoundaryMeasure_normAt [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) (hh : Continuous h) :
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (normAt ϖ (ofFun h + zField X R ω)) =
      ENNReal.ofReal (Real.exp (γ / 2 * -((ofFun h + zField X R ω) ϖ))) •
        qBoundaryMeasure γ (ofFun h + zField X R ω) := by
  filter_upwards [ae_isRegularSample_zField hX R,
    ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R] with ω hreg hv
  obtain ⟨F, hF⟩ := hreg
  set c := -((ofFun h + zField X R ω) ϖ) with hc
  have hF1 := GoodSample.gs_add_ofFun hF hh.continuousOn
  have hv1 := isVagueLimitR_add_ofFun hF hh.continuousOn hv
  have hv2 := isVagueLimitR_add_ofFun hF1 (m := fun _ => c) continuousOn_const hv1
  have e1 : normAt ϖ (ofFun h + zField X R ω) = zField X R ω + ofFun h + ofFun (fun _ => c) := by
    unfold normAt; rw [GoodSample.addConst_eq_add_ofFun]; congr 1; exact add_comm _ _
  rw [e1, qBoundaryMeasure_eq hv2, show ofFun h + zField X R ω = zField X R ω + ofFun h from
    add_comm _ _, qBoundaryMeasure_eq hv1]
  simp only [PalmFree.eW]
  exact withDensity_const _

lemma covariance_zG_varpi (hX : IsFreeGFFModConstH X P) {R : ℝ} (hR : 0 < R)
    (hϖ : IsAdmissibleH ϖ) (hϖ1 : ϖ univ = 1) {ν : Measure ℂ} (hν : IsAdmissibleH ν) :
    cov[fun ω => zG X R ω ν, fun ω => zG X R ω ϖ; P] =
      ∫ u, kPot ϖ u ∂ν - ∫ u, KernelId.fcPot R 0 u ∂ν -
        (ν univ).toReal * (kernelCov neumannH (foldedCircle 0 R) ϖ -
          kernelCov neumannH (foldedCircle 0 R) (foldedCircle 0 R)) := by
  rw [covariance_zG hX hR hν hϖ]
  have hm1 : massN ϖ = 1 := by simp [massN, hϖ1]
  simp only [kernelCov2, hm1, one_smul, kernelCov_smul_left]
  rw [kernelCov_fc_right' _ _ hR]
  simp only [massN, ENNReal.coe_toNNReal_eq_toReal]
  unfold kPot kernelCov
  ring

end Norm

/-- **PALM-NORM (E1, step (2)).** For `X` free, `h` continuous, `ϖ` an admissible probability
measure, `N_ϖ(y) = addConst y (−(y ϖ))`, `ν = qBoundaryMeasure γ (N_ϖ(ofFun h + X))`, a window
`[a,b] ⊆ [−N,N]`, a continuous nonnegative weight `w` vanishing off `[a,b]`, admissible `μ_j` and
any measurable `φ ≥ 0`:
`E ∫ w(x) φ((N_ϖ(ofFun h + X) μ_j)_j, x) ν(dx) =
  ∫ w(x) ρ_ϖ(x) E φ((N_ϖ(ofFun (h + (γ/2)(neumannH x · − k_ϖ)) + X) μ_j)_j, x) dx`. -/
theorem palm_formula_norm {X : Ω → FieldSample} {h : ℂ → ℝ} {ϖ : Measure ℂ}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2)
    {N : ℕ} (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) (hh : Continuous h) (hϖ : IsAdmissibleH ϖ)
    (hϖ1 : ϖ univ = 1) (hμ : ∀ j, IsAdmissibleH (μ j))
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hwab : ∀ x ∉ Icc a b, w x = 0)
    {φ : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hφ : Measurable (Function.uncurry φ)) :
    ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (w x) * φ (fun j => normAt ϖ (ofFun h + X ω) (μ j)) x
        ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h + X ω))) ∂P =
      ∫⁻ x, ENNReal.ofReal (w x * rhoNorm γ h ϖ x) *
        ∫⁻ ω, φ (fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j)) x ∂P := by
  set R : ℝ := (N : ℝ) + 2 with hRdef
  have hR0 : 0 < R := by positivity
  have hFa : IsAdmissibleH (foldedCircle 0 R) :=
    isAdmissibleH_foldedCircle (by simp [Hbar]) hR0
  have hμ' : ∀ j, IsAdmissibleH (muCons ϖ μ j) := fun j => by
    cases j with
    | zero => exact hϖ
    | succ n => exact hμ n
  set mass : ℕ → ℝ := fun j => (μ j univ).toReal with hmass
  set G : (ℕ → ℝ) × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (γ / 2 * -(p.1 0))) *
    φ (fun j => p.1 (j + 1) + -(p.1 0) * mass j) p.2 with hGdef
  have hG : Measurable G := by
    have h1 : Measurable fun p : (ℕ → ℝ) × ℝ => ENNReal.ofReal (Real.exp (γ / 2 * -(p.1 0))) := by
      fun_prop
    have hmap : Measurable fun p : (ℕ → ℝ) × ℝ =>
        ((fun j => p.1 (j + 1) + -(p.1 0) * mass j), p.2) := by
      refine Measurable.prodMk (measurable_pi_iff.2 fun j => ?_) measurable_snd
      fun_prop
    exact h1.mul (hφ.comp hmap)
  have H := palm_lintegral_free (m := h) (μ := muCons ϖ μ) (γ := γ) hX hγ hγ2 (le_refl R) hab hh
    hμ' hw hwc hw0 hwab hG
  -- the left side
  have hL : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (w x) * φ (fun j => normAt ϖ (ofFun h + X ω) (μ j)) x
      ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h + X ω))) ∂P =
      ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (w x) *
        G (fun j => (ofFun h + BdryExist.zField X R ω) (muCons ϖ μ j), x)
        ∂(qBoundaryMeasure γ (ofFun h + BdryExist.zField X R ω)) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_qBoundaryMeasure_normAt (ϖ := ϖ) hX hγ hγ2 R hh] with ω hω
    rw [normAt_zField hϖ1 R, hω, lintegral_smul_measure, smul_eq_mul,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    simp only [hGdef, muCons, normAt, addConst, hmass]
    ring
  -- the right side, pointwise in `x`
  have hRx : ∀ x, ENNReal.ofReal (w x * Real.exp (γ * h x / 2 + γ ^ 2 * (2 * Real.log R) / 8)) *
      ∫⁻ ω, G (fun j => (ofFun h + BdryExist.zField X R ω +
        ofFun (fun z => γ / 2 * freeKernel R x z)) (muCons ϖ μ j), x) ∂P =
      ENNReal.ofReal (w x * rhoNorm γ h ϖ x) *
        ∫⁻ ω, φ (fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j)) x ∂P := by
    intro x
    have hZ := isCenteredGaussianField_zG hX hR0 (P := P)
    set g : ℂ → ℝ := fun z => γ / 2 * freeKernel R x z with hg
    set β : ℕ → ℝ := fun j => ofFun h (muCons ϖ μ j) + ofFun g (muCons ϖ μ j) with hβdef
    set σ : Measure ℂ →₀ ℝ := Finsupp.single ϖ (-(γ / 2)) with hσ
    set V : ℝ := cov[fun ω => zG X R ω ϖ, fun ω => zG X R ω ϖ; P] with hVdef
    set Ψ : (Measure ℂ → ℝ) → ℝ≥0∞ := fun y =>
      φ (fun j => β (j + 1) + y (μ j) + -(β 0 + y ϖ) * mass j) x with hΨ
    have hΨm : Measurable Ψ := by
      have hmap : Measurable fun y : Measure ℂ → ℝ =>
          ((fun j => β (j + 1) + y (μ j) + -(β 0 + y ϖ) * mass j), x) := by
        refine Measurable.prodMk (measurable_pi_iff.2 fun j => ?_) measurable_const
        exact (measurable_const.add (measurable_pi_apply (μ j))).add
          ((measurable_const.add (measurable_pi_apply ϖ)).neg.mul_const _)
      exact hφ.comp hmap
    have hco : ∀ ω j, (ofFun h + BdryExist.zField X R ω + ofFun g) (muCons ϖ μ j) =
        β j + zG X R ω (muCons ϖ μ j) := fun ω j => by
      simp only [Pi.add_apply, hβdef]; rw [zG_of_adm (hμ' j)]; ring
    -- step 1: the integrand
    have hstep1 : ∀ ω, G (fun j => (ofFun h + BdryExist.zField X R ω + ofFun g) (muCons ϖ μ j), x)
        = ENNReal.ofReal (Real.exp (γ / 2 * -(β 0) + γ ^ 2 * V / 8)) *
          (Ψ (fun ν => zG X R ω ν) *
            ENNReal.ofReal (CameronMartin.tiltDensity (fun ν ω => zG X R ω ν) P σ ω)) := by
      intro ω
      simp only [hGdef, hco]
      simp only [hΨ, muCons]
      have e : Real.exp (γ / 2 * -(β 0 + zG X R ω ϖ)) =
          Real.exp (γ / 2 * -(β 0) + γ ^ 2 * V / 8) *
            CameronMartin.tiltDensity (fun ν ω => zG X R ω ν) P σ ω := by
        rw [CameronMartin.tiltDensity, hσ, comb_single, covNorm_single, ← Real.exp_add]
        congr 1
        simp only [CameronMartin.covK, hVdef]
        ring
      rw [e, ENNReal.ofReal_mul (Real.exp_pos _).le]
      ring
    -- step 2: Cameron–Martin
    have hstep2 : ∫⁻ ω, G (fun j => (ofFun h + BdryExist.zField X R ω + ofFun g)
        (muCons ϖ μ j), x) ∂P =
        ENNReal.ofReal (Real.exp (γ / 2 * -(β 0) + γ ^ 2 * V / 8)) *
          ∫⁻ ω, Ψ (fun ν => zG X R ω ν +
            CameronMartin.covShift (fun ν ω => zG X R ω ν) P σ ν) ∂P := by
      simp_rw [hstep1]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_mul_tiltDensity hZ.gauss hZ.meas hZ.cent σ Ψ hΨm]
    -- step 3: identification of the shifted field
    set C : ℝ := γ / 2 * (kernelCov neumannH (foldedCircle 0 R) ϖ -
      kernelCov neumannH (foldedCircle 0 R) (foldedCircle 0 R)) with hC
    have hofg : ∀ {ν : Measure ℂ}, IsAdmissibleH ν → ofFun g ν =
        γ / 2 * (∫ z, neumannH (x : ℂ) z ∂ν - ∫ z, KernelId.fcPot R 0 z ∂ν) := fun hν => by
      simp only [ofFun, hg, freeKernel]
      rw [integral_const_mul, integral_sub (PalmArea.integrable_neumannH_left hν _)
        (integrable_continuous_adm hν (KernelId.continuous_fcPot hR0 0))]
    have hoff : ∀ {ν : Measure ℂ}, IsAdmissibleH ν → ofFun (shiftFun γ h ϖ x) ν =
        ∫ z, h z ∂ν + γ / 2 * (∫ z, neumannH (x : ℂ) z ∂ν - ∫ z, kPot ϖ z ∂ν) := fun hν => by
      simp only [ofFun, shiftFun]
      rw [integral_add (f := fun z => h z)
        (g := fun z => γ / 2 * (neumannH (x : ℂ) z - kPot ϖ z)) (integrable_continuous_adm hν hh)
        (((PalmArea.integrable_neumannH_left hν _).sub (integrable_kPot hν hϖ)).const_mul _),
        integral_const_mul, integral_sub (f := fun z => neumannH (x : ℂ) z) (g := kPot ϖ)
          (PalmArea.integrable_neumannH_left hν _) (integrable_kPot hν hϖ)]
    have hβν : ∀ {ν : Measure ℂ}, IsAdmissibleH ν →
        ofFun h ν + ofFun g ν + -(γ / 2) * cov[fun ω => zG X R ω ν, fun ω => zG X R ω ϖ; P] =
          ofFun (shiftFun γ h ϖ x) ν + (ν univ).toReal * C := fun hν => by
      rw [hofg hν, hoff hν, covariance_zG_varpi hX hR0 hϖ hϖ1 hν, hC]
      simp only [ofFun]
      ring
    have hzG : ∀ ω {ν : Measure ℂ}, IsAdmissibleH ν →
        zG X R ω ν = X ω ν + -X ω (foldedCircle 0 R) * (ν univ).toReal := fun ω ν hν => by
      rw [zG_of_adm hν]; rfl
    have hstep3 : ∀ ω, Ψ (fun ν => zG X R ω ν +
        CameronMartin.covShift (fun ν ω => zG X R ω ν) P σ ν) =
        φ (fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j)) x := by
      intro ω
      simp only [hΨ]
      congr 1
      funext j
      have e1 := hβν (hμ j)
      have e2 := hβν hϖ
      have e3 := hzG ω (hμ j)
      have e4 := hzG ω hϖ
      rw [hϖ1, ENNReal.toReal_one] at e2 e4
      simp only [hσ, covShift_single, CameronMartin.covK, hβdef, muCons, normAt, addConst,
        Pi.add_apply, hmass]
      linear_combination e1 + e3 - (μ j univ).toReal * (e2 + e4)
    -- step 4: the constants
    have hKFF : kernelCov neumannH (foldedCircle 0 R) (foldedCircle 0 R) = -2 * Real.log R :=
      kernelCov_fc_bigCircle_left hR0 (by simp)
    have hKFϖ : kernelCov neumannH (foldedCircle 0 R) ϖ = ∫ z, KernelId.fcPot R 0 z ∂ϖ := by
      rw [kernelCov_symm_adm hFa hϖ, kernelCov_fc_right' _ _ hR0]
    have hV : V = kkPot ϖ - 2 * ∫ z, KernelId.fcPot R 0 z ∂ϖ - 2 * Real.log R := by
      rw [hVdef, covariance_zG_varpi hX hR0 hϖ hϖ1 hϖ, hKFF, hKFϖ, hϖ1, ENNReal.toReal_one]
      simp only [kkPot, kernelCov, kPot]
      ring
    have hβ0 : β 0 = ∫ z, h z ∂ϖ + γ / 2 * (kPot ϖ x - ∫ z, KernelId.fcPot R 0 z ∂ϖ) := by
      simp only [hβdef, muCons]
      rw [hofg hϖ]
      rfl
    rw [show (fun ω => G (fun j => (ofFun h + BdryExist.zField X R ω +
        ofFun (fun z => γ / 2 * freeKernel R x z)) (muCons ϖ μ j), x)) =
        fun ω => G (fun j => (ofFun h + BdryExist.zField X R ω + ofFun g) (muCons ϖ μ j), x)
        from rfl, hstep2]
    simp_rw [hstep3]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (hw0 x) (Real.exp_pos _).le)]
    congr 2
    rw [mul_assoc, ← Real.exp_add, rhoNorm]
    congr 2
    linear_combination (-(γ / 2)) * hβ0 + γ ^ 2 / 8 * hV
  rw [hL, H]
  exact lintegral_congr hRx

end PalmNorm
end QuantumZipper
