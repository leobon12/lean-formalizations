import QuantumZipper.Proofs.LQG.FractionalMoments
import QuantumZipper.Proofs.LQG.AreaExistenceAS
import QuantumZipper.Proofs.LQG.GoodSample
import QuantumZipper.Proofs.LQG.RegularSample

/-!
# M4-A3: fractional moments of the area measure near `ℝ` and finiteness of `μ(B(0,a) ∩ ℍ)`

Blueprint `M4_BLUEPRINT.md`, nodes M4-P3 (area version at boundary points) and M4-A3.

Fix `t ∈ ℝ`, `δ > 0` with `|t| + δ ≤ R`. As in `FractionalMoments` (boundary case) we split the
normalized field `Z = aZ X R` inside `B(t, δ)` as `Z_ρ(z) = Ω + Y_ρ(z)`, with
`Ω = Z(fc(t,δ))` and `Y` the (complex-centred) inner field, independent of `Ω`. For a set
`K ⊆ ℍ` with `Im z ≥ d` and `‖z − t‖ + 2^{-k} < δ` on `K`:

* `areaApprox_eq_omega_mul`: `μ_{2^{-k}}(K) = e^{γΩ} δ^{γ²/2} W_k(K)` a.s., with `W_k` a function
  of the inner field and `E W_k ≤ (δ/2d)^{γ²/2} |K|` (`lintegral_innerMassC_le`);
* (1) `lintegral_areaApprox_rpow_le`:
  `E μ_{2^{-k}}(K)^p ≤ δ^{pγ²/2} e^{(2 log R − 2 log δ)(pγ)²/2} ((δ/2d)^{γ²/2} |K|)^p`, and
  `lintegral_qAreaMeasure_rpow_le` the same for the limit `μ = qAreaMeasure` on open `U ⊆ K`
  (Fatou);
* (2) `ae_qAreaMeasure_ball_lt_top`: a.s. `μ_X(B(0,a) ∩ ℍ) < ∞` for every `a`;
* (3) `ae_qAreaMeasure_add_ofFun_ball_lt_top`: the same for `X + ofFun φ`, `φ` continuous on
  `Hbar`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace FinArea

open GaussTK TwoRadius KernelId

/-! ### Kernel identities for an interior circle inside a real-centred semicircle -/

theorem norm_ofReal_sub_conj (t : ℝ) (w : ℂ) : ‖(t : ℂ) - conj w‖ = ‖(t : ℂ) - w‖ := by
  rw [← Complex.norm_conj, map_sub, Complex.conj_conj, conj_ofReal']

theorem kernelCov_fc_inside_real {z : ℂ} {t r δ : ℝ} (hr : 0 < r) (h : ‖z - t‖ + r ≤ δ) :
    kernelCov neumannH (foldedCircle z r) (foldedCircle (t : ℂ) δ) = -2 * log δ := by
  have hδ : 0 < δ := by linarith [norm_nonneg (z - t)]
  refine kernelCov_fc_master_in z t r hδ ?_
  filter_upwards [ae_norm_sub_center z hr] with x hx
  have h1 : ‖x - t‖ ≤ δ := by
    calc ‖x - t‖ = ‖(x - z) + (z - t)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - z‖ + ‖z - t‖ := norm_add_le _ _
      _ ≤ δ := by rw [hx]; linarith
  exact ⟨h1, by rw [conj_ofReal']; exact h1⟩

theorem kernelCov_real_fc_inside {z : ℂ} {t r δ : ℝ} (hr : 0 < r) (h : ‖z - t‖ + r ≤ δ) :
    kernelCov neumannH (foldedCircle (t : ℂ) δ) (foldedCircle z r) = -2 * log δ := by
  have hδ : 0 < δ := by linarith [norm_nonneg (z - t)]
  have hzt : ‖(t : ℂ) - z‖ = ‖z - t‖ := norm_sub_rev _ _
  rw [kernelCov_fc_master_out (t : ℂ) z hδ hr ?_]
  · have h1 : ‖(t : ℂ) - z‖ ≤ δ := by rw [hzt]; linarith
    have h2 : ‖(t : ℂ) - conj z‖ ≤ δ := by rw [norm_ofReal_sub_conj]; exact h1
    rw [max_eq_left h1, max_eq_left h2]; ring
  · filter_upwards [ae_norm_sub_center (t : ℂ) hδ] with x hx
    have e1 := norm_sub_norm_le (x - t) (z - t)
    rw [sub_sub_sub_cancel_right] at e1
    have e2 := norm_sub_norm_le (x - t) (conj z - t)
    rw [sub_sub_sub_cancel_right] at e2
    have e3 : ‖conj z - (t : ℂ)‖ = ‖z - t‖ := by
      rw [norm_sub_rev, norm_ofReal_sub_conj, hzt]
    constructor <;> linarith

/-! ### The complex inner field -/

/-- Index set of the complex inner field: `(w, r)` with `Im w ≥ 0`, `r > 0`, `‖w‖ + r ≤ 1`. -/
abbrev InnerQC := {q : ℂ × ℝ // 0 ≤ q.1.im ∧ 0 < q.2 ∧ ‖q.1‖ + q.2 ≤ 1}

/-- The pair index `(t + δw, δr; t, δ)`. -/
def innerIdxC (t δ : ℝ) (w : ℂ) (r : ℝ) : FcIdx := ((t : ℂ) + (δ : ℂ) * w, δ * r, (t : ℂ), δ)

theorem good_innerIdxC {t δ : ℝ} (hδ : 0 < δ) (q : InnerQC) :
    FcIdx.Good (innerIdxC t δ q.1.1 q.1.2) := by
  refine ⟨?_, mul_pos hδ q.2.2.1, ofReal_mem_Hbar t, hδ⟩
  show 0 ≤ ((t : ℂ) + (δ : ℂ) * q.1.1).im
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
    zero_mul, add_zero]
  exact mul_nonneg hδ.le q.2.1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The complex inner process. -/
def innerProcC (X : Ω → FieldSample) (t δ : ℝ) (ω : Ω) : InnerQC → ℝ :=
  fun q => fcPairVal X (innerIdxC t δ q.1.1 q.1.2) ω

/-- The folded circle attached to `q` at `(t, δ)`. -/
def innerMeasC (t δ : ℝ) (q : InnerQC) : Measure ℂ :=
  foldedCircle ((t : ℂ) + (δ : ℂ) * q.1.1) (δ * q.1.2)

open Classical in
/-- Rebuild a field sample from complex inner coordinates. -/
def innerRebuildC (t δ : ℝ) (y : InnerQC → ℝ) : FieldSample := fun μ =>
  if h : ∃ q : InnerQC, innerMeasC t δ q = μ then y h.choose else 0

/-- The complex inner field sample, a function of the inner process only. -/
def innerSampleC (X : Ω → FieldSample) (t δ : ℝ) (ω : Ω) : FieldSample :=
  innerRebuildC t δ (innerProcC X t δ ω)

theorem measurable_innerRebuildC (t δ : ℝ) : Measurable (innerRebuildC t δ) := by
  refine measurable_pi_iff.mpr fun μ => ?_
  by_cases h : ∃ q : InnerQC, innerMeasC t δ q = μ
  · have e : (fun y : InnerQC → ℝ => innerRebuildC t δ y μ) = fun y => y h.choose := by
      funext y; simp only [innerRebuildC, dif_pos h]
    rw [e]; exact measurable_pi_apply _
  · have e : (fun y : InnerQC → ℝ => innerRebuildC t δ y μ) = fun _ => 0 := by
      funext y; simp only [innerRebuildC, dif_neg h]
    rw [e]; exact measurable_const

theorem measurable_innerSampleC (hX : IsFreeGFFModConstH X P) (t δ : ℝ) :
    Measurable (innerSampleC X t δ) :=
  (measurable_innerRebuildC t δ).comp (measurable_pi_iff.mpr fun q => measurable_fcPairVal hX _)

theorem innerSampleC_apply (t δ : ℝ) (ω : Ω) (q : InnerQC) :
    innerSampleC X t δ ω (innerMeasC t δ q) =
      X ω (innerMeasC t δ q) - X ω (foldedCircle (t : ℂ) δ) := by
  have h : ∃ q' : InnerQC, innerMeasC t δ q' = innerMeasC t δ q := ⟨q, rfl⟩
  have e : innerSampleC X t δ ω (innerMeasC t δ q) =
      fcPairVal X (innerIdxC t δ h.choose.1.1 h.choose.1.2) ω := by
    simp only [innerSampleC, innerRebuildC, dif_pos h, innerProcC]
  rw [e]
  show X ω (innerMeasC t δ h.choose) - X ω (foldedCircle (t : ℂ) δ) = _
  rw [h.choose_spec]

/-- Pathwise identification of the inner field's regularized averages. -/
theorem avgReg_innerSampleC_eq {t δ : ℝ} {z : ℂ} {k : ℕ} (hδ : 0 < δ) (hz : z ∈ Hbar)
    (hs : ‖z - t‖ + radius k < δ) {ω : Ω}
    (hlim : Tendsto (fun j => X ω (foldedCircle (dyadicRoundC j z) (radius k))) atTop
      (𝓝 (avgReg (X ω) k z))) :
    avgReg (innerSampleC X t δ ω) k z = avgReg (X ω) k z - X ω (foldedCircle (t : ℂ) δ) := by
  have hr := radius_pos k
  have hε : 0 < (δ - ‖z - t‖ - radius k) / 2 := by linarith
  have hev : ∀ᶠ j : ℕ in atTop, (1 / 2 : ℝ) ^ j < (δ - ‖z - t‖ - radius k) / 2 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).eventually
      (gt_mem_nhds hε)
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have heq : ∀ᶠ j : ℕ in atTop,
      X ω (foldedCircle (dyadicRoundC j z) (radius k)) - X ω (foldedCircle (t : ℂ) δ) =
        innerSampleC X t δ ω (foldedCircle (dyadicRoundC j z) (radius k)) := by
    filter_upwards [hev] with j hj
    set d := dyadicRoundC j z with hd
    have hdz : ‖d - z‖ ≤ 2 * (1 / 2 ^ j) := CircleCont.norm_dyadicRoundC_sub_le j z
    have hdH : d ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hz j
    rw [one_div_pow] at hj
    have hdt : ‖d - t‖ ≤ ‖d - z‖ + ‖z - t‖ := by
      calc ‖d - t‖ = ‖(d - z) + (z - t)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have him : ((d - t) / (δ : ℂ)).im = d.im / δ := by
      rw [Complex.div_ofReal_im]; simp
    have hnorm : ‖(d - t) / (δ : ℂ)‖ = ‖d - t‖ / δ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    have hq : 0 ≤ ((d - t) / (δ : ℂ)).im ∧ 0 < radius k / δ ∧
        ‖(d - t) / (δ : ℂ)‖ + radius k / δ ≤ 1 := by
      refine ⟨by rw [him]; exact div_nonneg hdH hδ.le, div_pos hr hδ, ?_⟩
      rw [hnorm, ← add_div, div_le_one hδ]
      linarith
    let q : InnerQC := ⟨((d - t) / (δ : ℂ), radius k / δ), hq⟩
    have hm : innerMeasC t δ q = foldedCircle d (radius k) := by
      simp only [innerMeasC, q]
      congr 1
      · have e : (δ : ℂ) * ((d - t) / δ) = d - t := by field_simp
        rw [e]; ring
      · field_simp
    rw [← hm, innerSampleC_apply]
  exact ((hlim.sub_const _).congr' heq).limUnder_eq

/-- Almost surely, on `Hbar ∩ B(t, δ − 2^{-k})`, `Z_{2^{-k}} = Ω + Y_{2^{-k}}`. -/
theorem ae_avgReg_aZ_eq_innerC (hX : IsFreeGFFModConstH X P) (R : ℝ) {t δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) :
    ∀ᵐ ω ∂P, ∀ z ∈ Hbar, ‖z - t‖ + radius k < δ →
      avgReg (AreaExist.aZ X R ω) k z =
        FracMom.omegaAvg X R t δ ω + avgReg (innerSampleC X t δ ω) k z := by
  filter_upwards [(AreaExist.ae_avgReg_spec hX k).1, AreaExist.ae_avgReg_aZ hX R k]
    with ω h1 h2 z hz hs
  rw [h2 z hz, avgReg_innerSampleC_eq hδ hz hs (h1 z hz), FracMom.omegaAvg, fcPairVal]
  ring

theorem avgReg_innerSampleC_ae_eq (hX : IsFreeGFFModConstH X P) {t δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    {z : ℂ} (hz : z ∈ Hbar) (hs : ‖z - t‖ + radius k < δ) :
    (fun ω => avgReg (innerSampleC X t δ ω) k z) =ᵐ[P]
      fcPairVal X (z, radius k, (t : ℂ), δ) := by
  filter_upwards [(AreaExist.ae_avgReg_spec hX k).1, (AreaExist.ae_avgReg_spec hX k).2 z hz]
    with ω h1 h2
  rw [avgReg_innerSampleC_eq hδ hz hs (h1 z hz), h2, fcPairVal]

/-! ### Covariances and laws -/

theorem fcPairCov_innerUC_self {z : ℂ} {t r δ : ℝ} (hr : 0 < r) (hrz : r ≤ z.im)
    (h : ‖z - t‖ + r ≤ δ) :
    fcPairCov (z, r, (t : ℂ), δ) (z, r, (t : ℂ), δ) =
      2 * log δ - log r - log ‖z - conj z‖ := by
  have hδ : 0 < δ := by linarith [norm_nonneg (z - t)]
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_sameCenter hr hr hrz hrz, kernelCov_fc_inside_real hr h,
    kernelCov_real_fc_inside hr h, kernelCov_fc_real_sameCenter hδ hδ, max_self, max_self]
  ring

theorem fcPairCov_innerC_Z {t δ R : ℝ} (hδ : 0 < δ) (q : InnerQC) (hR : |t| + δ ≤ R) :
    fcPairCov (innerIdxC t δ q.1.1 q.1.2) ((t : ℂ), δ, 0, R) = 0 := by
  set w := q.1.1 with hwdef
  set r := q.1.2 with hrdef
  have hr : 0 < r := q.2.2.1
  have hwr : ‖w‖ + r ≤ 1 := q.2.2.2
  have hρ : 0 < δ * r := mul_pos hδ hr
  have hnw : ‖(δ : ℂ) * w‖ = δ * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hin : ‖((t : ℂ) + (δ : ℂ) * w) - t‖ + δ * r ≤ δ := by
    rw [add_sub_cancel_left, hnw]; nlinarith
  have hin' : ‖(t : ℂ) + (δ : ℂ) * w‖ + δ * r ≤ R := by
    have := norm_add_le (t : ℂ) ((δ : ℂ) * w)
    rw [hnw, norm_ofReal'] at this
    nlinarith
  simp only [fcPairCov, kernelCov2, innerIdxC]
  rw [kernelCov_fc_inside_real hρ hin, kernelCov_fc_bigCircle_right hρ hin',
    kernelCov_fc_real_sameCenter hδ hδ, max_self,
    kernelCov_fc_bigCircle_right hδ (by rw [norm_ofReal']; linarith)]
  ring

/-- Variance of `Y_{2^{-k}}(z)`. -/
def vC (δ : ℝ) (k : ℕ) (z : ℂ) : ℝ≥0 :=
  (2 * log δ - log (radius k) - log ‖z - conj z‖).toNNReal

theorem hasLaw_innerUC (hX : IsFreeGFFModConstH X P) {t δ : ℝ} (hδ : 0 < δ) (k : ℕ) {z : ℂ}
    (hrz : radius k ≤ z.im) (hs : ‖z - t‖ + radius k < δ) :
    HasLaw (fun ω => avgReg (innerSampleC X t δ ω) k z) (gaussianReal 0 (vC δ k z)) P := by
  have hr := radius_pos k
  have hz : z ∈ Hbar := show 0 ≤ z.im by linarith
  have := (AreaExist.hasLaw_fcPairVal' hX (show FcIdx.Good (z, radius k, (t : ℂ), δ) from
    ⟨hz, hr, ofReal_mem_Hbar t, hδ⟩)).congr (avgReg_innerSampleC_ae_eq hX hδ k hz hs)
  rwa [fcPairCov_innerUC_self hr hrz hs.le] at this

theorem indepFun_omega_innerSampleC (hX : IsFreeGFFModConstH X P) {R t δ : ℝ} (hδ : 0 < δ)
    (hR : |t| + δ ≤ R) : IndepFun (FracMom.omegaAvg X R t δ) (innerSampleC X t δ) P := by
  have hR0 : 0 < R := by linarith [abs_nonneg t]
  have hI := indepFun_fcPair hX (P := P)
    (fun q : InnerQC => (⟨innerIdxC t δ q.1.1 q.1.2, good_innerIdxC hδ q⟩ :
      {p : FcIdx // p.Good}))
    (fun _ : Unit => (⟨((t : ℂ), δ, 0, R), good_Z (ofReal_mem_Hbar t) hδ hR0⟩ :
      {p : FcIdx // p.Good}))
    (fun q _ => fcPairCov_innerC_Z hδ q hR)
  exact hI.symm.comp (measurable_pi_apply ()) (measurable_innerRebuildC t δ)

/-! ### Masses and the decomposition -/

/-- Rescaled area density `(2^{-k}/δ)^{γ²/2} e^{γ avgReg x k z}`. -/
def wDensC (γ δ : ℝ) (k : ℕ) (x : FieldSample) (z : ℂ) : ℝ :=
  (radius k / δ) ^ (γ ^ 2 / 2) * exp (γ * avgReg x k z)

/-- Rescaled area mass `W_k(K)`. -/
def massFunC (γ : ℝ) (K : Set ℂ) (δ : ℝ) (k : ℕ) (x : FieldSample) : ℝ≥0∞ :=
  ∫⁻ z in K, ENNReal.ofReal (wDensC γ δ k x z)

theorem measurable_wDensC₂ (γ δ : ℝ) (k : ℕ) :
    Measurable (fun p : FieldSample × ℂ => wDensC γ δ k p.1 p.2) :=
  measurable_const.mul (((measurable_avgReg k).const_mul _).exp)

theorem measurable_massFunC (γ : ℝ) (K : Set ℂ) (δ : ℝ) (k : ℕ) :
    Measurable (massFunC γ K δ k) :=
  (ENNReal.measurable_ofReal.comp (measurable_wDensC₂ γ δ k)).lintegral_prod_right'

theorem wDensC_nonneg (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (x : FieldSample) (z : ℂ) :
    0 ≤ wDensC γ δ k x z :=
  mul_nonneg (rpow_nonneg (div_nonneg (radius_pos k).le hδ.le) _) (exp_pos _).le

/-- Deterministic decomposition of `μ_{2^{-k}}(K)`. -/
theorem areaApprox_eq_of (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (x y : FieldSample) (c : ℝ)
    {K : Set ℂ} (hK : MeasurableSet K) (hKH : K ⊆ H)
    (hxy : ∀ z ∈ K, avgReg x k z = c + avgReg y k z) :
    areaApprox γ x k K =
      ENNReal.ofReal (exp (γ * c) * δ ^ (γ ^ 2 / 2)) * massFunC γ K δ k y := by
  have hU : Measurable (fun z : ℂ => avgReg y k z) :=
    (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (fun z : ℂ => ENNReal.ofReal (wDensC γ δ k y z)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hU.const_mul _).exp)
  rw [areaApprox, withDensity_apply _ hK, Measure.restrict_restrict hK,
    Set.inter_eq_left.2 hKH, massFunC, ← lintegral_const_mul _ hm]
  refine setLIntegral_congr_fun hK fun z hz => ?_
  have hδa : 0 < δ ^ (γ ^ 2 / 2) := rpow_pos_of_pos hδ _
  have e : radius k ^ (γ ^ 2 / 2) * exp (γ * avgReg x k z) =
      (exp (γ * c) * δ ^ (γ ^ 2 / 2)) * wDensC γ δ k y z := by
    rw [hxy z hz, wDensC, div_rpow (radius_pos k).le hδ.le, mul_add, exp_add]
    field_simp
  show ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * exp (γ * avgReg x k z)) = _
  rw [e, ENNReal.ofReal_mul (mul_pos (exp_pos _) hδa).le]

/-- Admissible region at level `k`: `Im z ≥ d ≥ 2^{-k}` and `‖z − t‖ + 2^{-k} < δ`. -/
def Adm (t δ d : ℝ) (k : ℕ) (K : Set ℂ) : Prop :=
  radius k ≤ d ∧ ∀ z ∈ K, d ≤ z.im ∧ ‖z - t‖ + radius k < δ

theorem Adm.subset_H {t δ d : ℝ} {k : ℕ} {K : Set ℂ} (h : Adm t δ d k K) : K ⊆ H :=
  fun z hz => show 0 < z.im from lt_of_lt_of_le (radius_pos k) (h.1.trans (h.2 z hz).1)

/-- **Decomposition** `μ_{2^{-k}}(K) = e^{γΩ} δ^{γ²/2} W_k(K)`, a.s. simultaneously for all
admissible `k`. -/
theorem ae_areaApprox_eq_omega_mul (hX : IsFreeGFFModConstH X P) (γ R : ℝ) {t δ d : ℝ}
    (hδ : 0 < δ) {K : Set ℂ} (hK : MeasurableSet K) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Adm t δ d k K →
      areaApprox γ (AreaExist.aZ X R ω) k K =
        ENNReal.ofReal (exp (γ * FracMom.omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 2)) *
          massFunC γ K δ k (innerSampleC X t δ ω) := by
  have h : ∀ k, ∀ᵐ ω ∂P, ∀ z ∈ Hbar, ‖z - t‖ + radius k < δ →
      avgReg (AreaExist.aZ X R ω) k z =
        FracMom.omegaAvg X R t δ ω + avgReg (innerSampleC X t δ ω) k z :=
    fun k => ae_avgReg_aZ_eq_innerC hX R hδ k
  rw [← ae_all_iff] at h
  filter_upwards [h] with ω hω k hk
  exact areaApprox_eq_of γ hδ k _ _ _ hK hk.subset_H fun z hz =>
    hω k z (show (0 : ℝ) ≤ z.im from le_of_lt (hk.subset_H hz)) (hk.2 z hz).2

/-- One-point first moment: `E wDensC ≤ (δ/2d)^{γ²/2}`. -/
theorem integral_wDensC_le (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (γ : ℝ)
    {t δ d : ℝ} (hδ : 0 < δ) (hd : 0 < d) {k : ℕ} {z : ℂ} (hdz : d ≤ z.im)
    (hkd : radius k ≤ d) (hs : ‖z - t‖ + radius k < δ) :
    Integrable (fun ω => wDensC γ δ k (innerSampleC X t δ ω) z) P ∧
      ∫ ω, wDensC γ δ k (innerSampleC X t δ ω) z ∂P ≤ exp (γ ^ 2 / 2 * log (δ / (2 * d))) := by
  have hr := radius_pos k
  have hrz : radius k ≤ z.im := hkd.trans hdz
  have hL := hasLaw_innerUC hX (P := P) hδ k hrz hs
  have hi : Integrable (fun ω => exp (0 + γ * avgReg (innerSampleC X t δ ω) k z)) P :=
    hL.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ γ 0)
  simp only [zero_add] at hi
  refine ⟨hi.const_mul _, ?_⟩
  have h2 := integral_exp_mul_add_gaussianReal (vC δ k z) γ 0
  simp only [zero_add] at h2
  have h3 : ∫ ω, exp (γ * avgReg (innerSampleC X t δ ω) k z) ∂P = exp (vC δ k z * γ ^ 2 / 2) := by
    rw [← h2]; exact hL.integral_comp (f := fun x => exp (γ * x)) (by fun_prop)
  simp only [wDensC]
  rw [integral_const_mul, h3]
  -- the variance
  set N := ‖z - conj z‖ with hN
  have hN2 : 2 * z.im ≤ N := AreaExist.two_im_le_norm_sub_conj z
  have hNpos : 0 < N := by linarith
  have hNle : N ≤ 2 * ‖z - t‖ := by
    calc N = ‖(z - t) + ((t : ℂ) - conj z)‖ := by rw [hN, sub_add_sub_cancel]
      _ ≤ ‖z - t‖ + ‖(t : ℂ) - conj z‖ := norm_add_le _ _
      _ = 2 * ‖z - t‖ := by rw [norm_ofReal_sub_conj, norm_sub_rev]; ring
  have hv0 : 0 ≤ 2 * log δ - log (radius k) - log N := by
    have hprod : radius k * N ≤ δ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hNle hr.le, mul_pos hr hr, norm_nonneg (z - t),
        sq_nonneg (δ - radius k), mul_le_mul_of_nonneg_left hs.le hr.le]
    have := log_le_log (mul_pos hr hNpos) hprod
    rw [log_mul hr.ne' hNpos.ne', log_pow] at this
    push_cast at this
    linarith
  rw [vC, ← hN, Real.coe_toNNReal _ hv0, rpow_def_of_pos (div_pos hr hδ), ← exp_add,
    log_div hr.ne' hδ.ne']
  apply exp_le_exp.2
  have hl : log (2 * d) ≤ log N := log_le_log (by positivity) (by linarith)
  rw [log_div hδ.ne' (by positivity)]
  have hg : 0 ≤ γ ^ 2 / 2 := by positivity
  nlinarith

/-- `E W_k(K) ≤ (δ/2d)^{γ²/2} |K|`. -/
theorem lintegral_innerMassC_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (γ : ℝ) {t δ d : ℝ} (hδ : 0 < δ) (hd : 0 < d) {K : Set ℂ} (hK : MeasurableSet K) {k : ℕ}
    (hadm : Adm t δ d k K) :
    ∫⁻ ω, massFunC γ K δ k (innerSampleC X t δ ω) ∂P ≤
      ENNReal.ofReal (exp (γ ^ 2 / 2 * log (δ / (2 * d)))) * volume K := by
  have hU : Measurable (fun q : Ω × ℂ => avgReg (innerSampleC X t δ q.1) k q.2) :=
    (measurable_avgReg k).comp (((measurable_innerSampleC hX t δ).comp measurable_fst).prodMk
      measurable_snd)
  have hmeas : Measurable (fun q : Ω × ℂ =>
      ENNReal.ofReal (wDensC γ δ k (innerSampleC X t δ q.1) q.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hU.const_mul _).exp)
  simp only [massFunC]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ z in K, ∫⁻ ω, ENNReal.ofReal (wDensC γ δ k (innerSampleC X t δ ω) z) ∂P
      ≤ ∫⁻ z in K, ENNReal.ofReal (exp (γ ^ 2 / 2 * log (δ / (2 * d)))) :=
        setLIntegral_mono measurable_const fun z hz => by
          obtain ⟨hi, hle⟩ := integral_wDensC_le hX (P := P) γ hδ hd (hadm.2 z hz).1 hadm.1
            (hadm.2 z hz).2
          rw [← ofReal_integral_eq_lintegral_ofReal hi
            (ae_of_all _ fun ω => wDensC_nonneg γ hδ k _ z)]
          exact ENNReal.ofReal_le_ofReal hle
    _ = _ := setLIntegral_const _ _

/-- `E[(e^{γΩ} δ^{γ²/2})^p] = δ^{pγ²/2} e^{Var Ω (pγ)²/2}`. -/
theorem lintegral_omega_factorC_rpow (hX : IsFreeGFFModConstH X P) (γ : ℝ) {R t δ p : ℝ}
    (hδ : 0 < δ) (hR : |t| + δ ≤ R) (hp0 : 0 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (exp (γ * FracMom.omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 2)) ^ p ∂P =
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 2)) *
        exp ((2 * log R - 2 * log δ).toNNReal * (p * γ) ^ 2 / 2)) := by
  have hL := FracMom.hasLaw_omegaAvg hX (P := P) hδ hR
  set v := (2 * log R - 2 * log δ).toNNReal
  have hpt : ∀ ω, ENNReal.ofReal (exp (γ * FracMom.omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 2)) ^ p =
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 2)) * exp (p * γ * FracMom.omegaAvg X R t δ ω)) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0, mul_rpow (exp_pos _).le
      (rpow_pos_of_pos hδ _).le, ← exp_mul, ← rpow_mul hδ.le, mul_comm]
    congr 3 <;> ring
  simp_rw [hpt]
  have hi : Integrable (fun ω => exp (0 + p * γ * FracMom.omegaAvg X R t δ ω)) P :=
    hL.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (p * γ) 0)
  simp only [zero_add] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _)
    (ae_of_all _ fun ω => by simp only [Pi.zero_apply]; positivity), integral_const_mul]
  have h2 := integral_exp_mul_add_gaussianReal v (p * γ) 0
  simp only [zero_add] at h2
  rw [← h2]
  congr 2
  exact hL.integral_comp (f := fun x => exp (p * γ * x)) (by fun_prop)

/-- **(1) Fractional moment of `μ_{2^{-k}}(K)` near the boundary point `t`.** -/
theorem lintegral_areaApprox_rpow_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (γ : ℝ) {R t δ d p : ℝ} (hδ : 0 < δ) (hd : 0 < d) (hR : |t| + δ ≤ R) (hp0 : 0 < p)
    (hp1 : p ≤ 1) {K : Set ℂ} (hK : MeasurableSet K) {k : ℕ} (hadm : Adm t δ d k K) :
    ∫⁻ ω, areaApprox γ (AreaExist.aZ X R ω) k K ^ p ∂P ≤
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 2)) *
        exp ((2 * log R - 2 * log δ).toNNReal * (p * γ) ^ 2 / 2)) *
      (ENNReal.ofReal (exp (γ ^ 2 / 2 * log (δ / (2 * d)))) * volume K) ^ p := by
  set A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (exp (γ * FracMom.omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 2)) ^ p with hA
  set W : Ω → ℝ≥0∞ := fun ω => massFunC γ K δ k (innerSampleC X t δ ω) ^ p with hW
  have hφ : Measurable (fun x : ℝ => ENNReal.ofReal (exp (γ * x) * δ ^ (γ ^ 2 / 2)) ^ p) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).pow_const p
  have hψ : Measurable (fun x : FieldSample => massFunC γ K δ k x ^ p) :=
    (measurable_massFunC γ K δ k).pow_const p
  have hind : IndepFun A W P := (indepFun_omega_innerSampleC hX hδ hR).comp hφ hψ
  have hAm : Measurable A := hφ.comp (FracMom.measurable_omegaAvg hX R t δ)
  have hWm : Measurable W := hψ.comp (measurable_innerSampleC hX t δ)
  have hJ : ∫⁻ ω, massFunC γ K δ k (innerSampleC X t δ ω) ^ p ∂P ≤
      (∫⁻ ω, massFunC γ K δ k (innerSampleC X t δ ω) ∂P) ^ p :=
    FracMom.lintegral_rpow_le_rpow_lintegral
      ((measurable_massFunC γ K δ k).comp (measurable_innerSampleC hX t δ)).aemeasurable hp0 hp1
  calc ∫⁻ ω, areaApprox γ (AreaExist.aZ X R ω) k K ^ p ∂P
      = ∫⁻ ω, (A * W) ω ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_areaApprox_eq_omega_mul hX γ R (P := P) (t := t) (d := d) hδ hK]
          with ω hω
        rw [hω k hadm, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rfl
    _ = (∫⁻ ω, A ω ∂P) * ∫⁻ ω, W ω ∂P :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hAm hWm hind
    _ ≤ (∫⁻ ω, A ω ∂P) *
          (∫⁻ ω, massFunC γ K δ k (innerSampleC X t δ ω) ∂P) ^ p := by gcongr
    _ ≤ (∫⁻ ω, A ω ∂P) *
          (ENNReal.ofReal (exp (γ ^ 2 / 2 * log (δ / (2 * d)))) * volume K) ^ p := by
        gcongr
        exact lintegral_innerMassC_le hX γ hδ hd hK hadm
    _ = _ := by rw [hA, lintegral_omega_factorC_rpow hX γ hδ hR hp0.le]

/-! ### Fatou: the limit measure on open sets -/

/-- Test functions `min 1 (n · dist(z, Uᶜ))`, increasing to `1_U`. -/
def ramp (U : Set ℂ) (n : ℕ) (z : ℂ) : ℝ := min 1 (n * Metric.infDist z Uᶜ)

theorem continuous_ramp (U : Set ℂ) (n : ℕ) : Continuous (ramp U n) :=
  continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))

theorem ramp_nonneg (U : Set ℂ) (n : ℕ) (z : ℂ) : 0 ≤ ramp U n z :=
  le_min zero_le_one (mul_nonneg n.cast_nonneg Metric.infDist_nonneg)

theorem ramp_le_one (U : Set ℂ) (n : ℕ) (z : ℂ) : ramp U n z ≤ 1 := min_le_left _ _

theorem ramp_eq_zero {U : Set ℂ} (n : ℕ) {z : ℂ} (hz : z ∉ U) : ramp U n z = 0 := by
  unfold ramp
  rw [Metric.infDist_zero_of_mem (Set.mem_compl hz), mul_zero, min_eq_right zero_le_one]

theorem ramp_mono (U : Set ℂ) (z : ℂ) : Monotone fun n : ℕ => ramp U n z := fun n n' h =>
  min_le_min le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast h) Metric.infDist_nonneg)

theorem exists_ramp_eq_one {U : Set ℂ} (hU : IsOpen U) (hne : Uᶜ.Nonempty) {z : ℂ}
    (hz : z ∈ U) : ∃ n : ℕ, ramp U n z = 1 := by
  have hpos : 0 < Metric.infDist z Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 (Set.notMem_compl_iff.2 hz)
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / Metric.infDist z Uᶜ)
  refine ⟨n, min_eq_left ?_⟩
  rw [div_le_iff₀ hpos] at hn
  linarith

/-- **Portmanteau (liminf form).** For a vague limit on `ℍ`, `U` open and `U ⊆ K ⊆ ℍ` with
`K` compact: `μ(U)^p ≤ liminf_k μ_k(K)^p`. -/
theorem rpow_le_liminf_of_isVagueLimitOn {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (h : IsVagueLimitOn H μs μ) {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKH : K ⊆ H) {p : ℝ} (hp : 0 < p) :
    μ U ^ p ≤ liminf (fun k => μs k K ^ p) atTop := by
  have hne : Uᶜ.Nonempty := ⟨0, fun h0 => by
    have := hKH (hUK h0)
    simp [H] at this⟩
  have hts : ∀ n, tsupport (ramp U n) ⊆ K := fun n =>
    closure_minimal (fun z hz => hUK (by by_contra hc; exact hz (ramp_eq_zero n hc)))
      hK.isClosed
  have hcs : ∀ n, HasCompactSupport (ramp U n) := fun n =>
    HasCompactSupport.intro hK fun z hz => ramp_eq_zero n fun h => hz (hUK h)
  set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ z, ENNReal.ofReal (ramp U n z) ∂μ with ha
  have hamono : Monotone a := fun n n' h =>
    lintegral_mono fun z => ENNReal.ofReal_le_ofReal (ramp_mono U z h)
  have hsup : ⨆ n, a n = μ U := by
    show ⨆ n, ∫⁻ z, ENNReal.ofReal (ramp U n z) ∂μ = μ U
    rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (ramp U n z))
      (fun n => ENNReal.measurable_ofReal.comp (continuous_ramp U n).measurable)
      (fun n n' h z => ENNReal.ofReal_le_ofReal (ramp_mono U z h)),
      ← lintegral_indicator_one hU.measurableSet]
    congr 1
    funext z
    by_cases hz : z ∈ U
    · rw [Set.indicator_of_mem hz, Pi.one_apply]
      obtain ⟨n, hn⟩ := exists_ramp_eq_one hU hne hz
      refine le_antisymm (iSup_le fun m => ENNReal.ofReal_le_one.2 (ramp_le_one U m z)) ?_
      exact (le_iSup (fun m => ENNReal.ofReal (ramp U m z)) n).trans' (by simp [hn])
    · rw [Set.indicator_of_notMem hz]
      have h0 : ∀ m, ramp U m z = 0 := fun m => ramp_eq_zero m hz
      simp [h0]
  have hbound : ∀ n, a n ^ p ≤ liminf (fun k => μs k K ^ p) atTop := by
    intro n
    have hint : Integrable (ramp U n) μ :=
      GoodSample.integrable_of_tsupport (U := H) h.2.1 (continuous_ramp U n) (hcs n)
        ((hts n).trans hKH)
    have han : a n = ENNReal.ofReal (∫ z, ramp U n z ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (ramp_nonneg U n))).symm
    have ht : Tendsto (fun k => ENNReal.ofReal (∫ z, ramp U n z ∂μs k) ^ p) atTop
        (𝓝 (ENNReal.ofReal (∫ z, ramp U n z ∂μ) ^ p)) :=
      ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
        (ENNReal.tendsto_ofReal (h.2.2 _ (continuous_ramp U n) (hcs n) ((hts n).trans hKH)))
    rw [han, ← ht.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
    show ENNReal.ofReal (∫ z, ramp U n z ∂μs k) ^ p ≤ μs k K ^ p
    refine ENNReal.rpow_le_rpow ?_ hp.le
    by_cases hi : Integrable (ramp U n) (μs k)
    · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (ramp_nonneg U n))]
      calc ∫⁻ z, ENNReal.ofReal (ramp U n z) ∂μs k ≤ ∫⁻ z, K.indicator 1 z ∂μs k :=
            lintegral_mono fun z => by
              by_cases hz : z ∈ K
              · rw [Set.indicator_of_mem hz, Pi.one_apply]
                exact ENNReal.ofReal_le_one.2 (ramp_le_one U n z)
              · rw [ramp_eq_zero n fun h => hz (hUK h), ENNReal.ofReal_zero]; exact bot_le
        _ = μs k K := lintegral_indicator_one hK.isClosed.measurableSet
    · rw [integral_undef hi, ENNReal.ofReal_zero]; exact bot_le
  have hT : Tendsto (fun n => a n ^ p) atTop (𝓝 (μ U ^ p)) := by
    rw [← hsup]
    exact ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp (tendsto_atTop_iSup hamono)
  exact le_of_tendsto' hT hbound

theorem measurable_areaApprox_aZ_apply (hX : IsFreeGFFModConstH X P) (γ R : ℝ) (k : ℕ)
    {K : Set ℂ} (hK : MeasurableSet K) :
    Measurable (fun ω => areaApprox γ (AreaExist.aZ X R ω) k K) :=
  (Measure.measurable_coe hK).comp ((measurable_areaApprox γ k).comp (AreaExist.measurable_aZ hX R))

theorem exists_radius_le {d : ℝ} (hd : 0 < d) : ∃ k₀ : ℕ, radius k₀ ≤ d := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hd (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact ⟨n, hn.le⟩

/-- The common bound of (1). -/
def fracBoundC (γ R δ d p : ℝ) (K : Set ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 2)) *
    exp ((2 * log R - 2 * log δ).toNNReal * (p * γ) ^ 2 / 2)) *
  (ENNReal.ofReal (exp (γ ^ 2 / 2 * log (δ / (2 * d)))) * volume K) ^ p

/-- Fatou: `E liminf_k μ_{2^{-k}}(K)^p ≤` the bound of (1). -/
theorem lintegral_liminf_areaApprox_rpow_le [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (γ : ℝ) {R t δ d p : ℝ} (hδ : 0 < δ) (hd : 0 < d)
    (hR : |t| + δ ≤ R) (hp0 : 0 < p) (hp1 : p ≤ 1) {K : Set ℂ} (hK : MeasurableSet K)
    (hKz : ∀ z ∈ K, d ≤ z.im ∧ ‖z - t‖ + 2 * d ≤ δ) :
    ∫⁻ ω, liminf (fun k => areaApprox γ (AreaExist.aZ X R ω) k K ^ p) atTop ∂P ≤
      fracBoundC γ R δ d p K := by
  obtain ⟨k₀, hk₀⟩ := exists_radius_le hd
  have hadm : ∀ k, k₀ ≤ k → Adm t δ d k K := fun k hk =>
    ⟨(AreaExist.aradius_anti hk).trans hk₀, fun z hz => ⟨(hKz z hz).1, by
      have := (AreaExist.aradius_anti hk).trans hk₀
      linarith [(hKz z hz).2]⟩⟩
  refine (lintegral_liminf_le fun k =>
    (measurable_areaApprox_aZ_apply hX γ R k hK).pow_const p).trans ?_
  exact liminf_le_of_frequently_le' (Eventually.frequently (eventually_atTop.2
    ⟨k₀, fun k hk => lintegral_areaApprox_rpow_le hX γ hδ hd hR hp0 hp1 hK (hadm k hk)⟩))

/-- The limit measures of `Z = aZ X R` and of `X` differ by the constant `e^{-γ X(fc(0,R))}`. -/
theorem ae_qAreaMeasure_aZ_eq_smul [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (AreaExist.aZ X R ω) =
      ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 R)))) • qAreaMeasure γ (X ω) := by
  filter_upwards [AreaExist.ae_isVagueLimitOn_qAreaMeasure hX (P := P) hγ hγ2,
    AreaExist.ae_areaApprox_aZ_eq (P := P) hX γ R] with ω ⟨h0, hK, ht⟩ hsc
  set c := ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 R)))) with hc
  refine qAreaMeasure_eq ⟨by rw [Measure.smul_apply, h0, smul_zero], fun K hKc hKH => ?_,
    fun f hf hfc hfH => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hK K hKc hKH)
  · simp_rw [hsc, integral_smul_measure]
    exact (ht f hf hfc hfH).const_smul _

/-! ### (2) Finite area up to `ℝ` -/

/-- Open box of scale `r = 2^{-n}` above `t = j r`: `|Re z − t| < r`, `r/2 < Im z < 3r`. -/
def boxU (n : ℕ) (j : ℤ) : Set ℂ :=
  {z | |z.re - j * radius n| < radius n ∧ radius n / 2 < z.im ∧ z.im < 3 * radius n}

/-- The closed box. -/
def boxK (n : ℕ) (j : ℤ) : Set ℂ :=
  {z | |z.re - j * radius n| ≤ radius n ∧ radius n / 2 ≤ z.im ∧ z.im ≤ 3 * radius n}

theorem isOpen_boxU (n : ℕ) (j : ℤ) : IsOpen (boxU n j) :=
  (isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
    continuous_const).inter ((isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const))

theorem isClosed_boxK (n : ℕ) (j : ℤ) : IsClosed (boxK n j) :=
  (isClosed_le (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
    continuous_const).inter ((isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const))

theorem boxU_subset_boxK (n : ℕ) (j : ℤ) : boxU n j ⊆ boxK n j :=
  fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

theorem norm_sub_le_of_mem_boxK {n : ℕ} {j : ℤ} {z : ℂ} (hz : z ∈ boxK n j) :
    ‖z - ((j * radius n : ℝ) : ℂ)‖ ≤ 4 * radius n := by
  have h := Complex.norm_le_abs_re_add_abs_im (z - ((j * radius n : ℝ) : ℂ))
  have him : 0 ≤ z.im := le_trans (by linarith [radius_pos n]) hz.2.1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
    abs_of_nonneg him] at h
  linarith [hz.1, hz.2.2]

theorem boxK_subset_ball (n : ℕ) (j : ℤ) :
    boxK n j ⊆ Metric.closedBall ((j * radius n : ℝ) : ℂ) (4 * radius n) := fun z hz => by
  rw [Metric.mem_closedBall, dist_eq_norm]; exact norm_sub_le_of_mem_boxK hz

theorem isCompact_boxK (n : ℕ) (j : ℤ) : IsCompact (boxK n j) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_boxK n j) (boxK_subset_ball n j)

theorem boxK_spec (n : ℕ) (j : ℤ) : ∀ z ∈ boxK n j, radius n / 2 ≤ z.im ∧
    ‖z - ((j * radius n : ℝ) : ℂ)‖ + 2 * (radius n / 2) ≤ 5 * radius n := fun z hz =>
  ⟨hz.2.1, by linarith [norm_sub_le_of_mem_boxK hz]⟩

theorem boxK_subset_H (n : ℕ) (j : ℤ) : boxK n j ⊆ H := fun z hz =>
  show 0 < z.im from lt_of_lt_of_le (by linarith [radius_pos n]) hz.2.1

theorem volume_boxK_le (n : ℕ) (j : ℤ) :
    volume (boxK n j) ≤ ENNReal.ofReal (16 * π * radius n ^ 2) := by
  calc volume (boxK n j) ≤ volume (Metric.closedBall ((j * radius n : ℝ) : ℂ) (4 * radius n)) :=
        measure_mono (boxK_subset_ball n j)
    _ = _ := by
        rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow (by linarith [radius_pos n]),
          ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- The exponent `e(p) = p(2 + γ²/2) − p²γ²`. -/
def eA (γ p : ℝ) : ℝ := p * (γ ^ 2 / 2) - p ^ 2 * γ ^ 2 + 2 * p

/-- The constant of the box bound. -/
def cA (γ R p : ℝ) : ℝ :=
  p * (γ ^ 2 / 2) * log 5 + (2 * log R - 2 * log 5) * (p * γ) ^ 2 / 2 +
    p * (γ ^ 2 / 2 * log 5 + log (16 * π))

/-- **Box bound**: the bound of (1) for `boxK n j` (`δ = 5·2^{-n}`, `d = 2^{-n-1}`) is at most
`e^{cA} 2^{-n e(p)}`. -/
theorem fracBoundC_boxK_le {γ R p : ℝ} (hp0 : 0 < p) {n : ℕ} (j : ℤ)
    (hR : 5 * radius n ≤ R) :
    fracBoundC γ R (5 * radius n) (radius n / 2) p (boxK n j) ≤
      ENNReal.ofReal (exp (cA γ R p) * exp (-(n : ℝ) * log 2 * eA γ p)) := by
  have hr := radius_pos n
  have h5r : 0 < 5 * radius n := by positivity
  have hR0 : 0 < R := h5r.trans_le hR
  have hL : log (radius n) = -(n : ℝ) * log 2 := by
    have := BdryExist.log_one_div_radius n
    rw [one_div, log_inv] at this
    linarith
  have hq : 5 * radius n / (2 * (radius n / 2)) = 5 := by field_simp
  have hv : ((2 * log R - 2 * log (5 * radius n)).toNNReal : ℝ) =
      2 * log R - 2 * log (5 * radius n) :=
    Real.coe_toNNReal _ (by linarith [log_le_log h5r hR])
  unfold fracBoundC
  rw [hq, hv]
  set E := exp (γ ^ 2 / 2 * log 5) with hE
  have hE0 : 0 < E := exp_pos _
  calc ENNReal.ofReal ((5 * radius n) ^ (p * (γ ^ 2 / 2)) *
          exp ((2 * log R - 2 * log (5 * radius n)) * (p * γ) ^ 2 / 2)) *
        (ENNReal.ofReal E * volume (boxK n j)) ^ p
      ≤ ENNReal.ofReal ((5 * radius n) ^ (p * (γ ^ 2 / 2)) *
          exp ((2 * log R - 2 * log (5 * radius n)) * (p * γ) ^ 2 / 2)) *
        (ENNReal.ofReal E * ENNReal.ofReal (16 * π * radius n ^ 2)) ^ p := by
        gcongr; exact volume_boxK_le n j
    _ = ENNReal.ofReal ((5 * radius n) ^ (p * (γ ^ 2 / 2)) *
          exp ((2 * log R - 2 * log (5 * radius n)) * (p * γ) ^ 2 / 2) *
          (E * (16 * π * radius n ^ 2)) ^ p) := by
        rw [← ENNReal.ofReal_mul hE0.le, ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
          ← ENNReal.ofReal_mul (by positivity)]
    _ = _ := by
        congr 1
        have h1 : log (5 * radius n) = log 5 + log (radius n) := log_mul (by norm_num) hr.ne'
        have h2 : log (E * (16 * π * radius n ^ 2)) =
            γ ^ 2 / 2 * log 5 + log (16 * π) + 2 * log (radius n) := by
          rw [log_mul hE0.ne' (by positivity), hE, log_exp, log_mul (by positivity) (by positivity),
            log_pow]
          push_cast; ring
        rw [rpow_def_of_pos h5r, rpow_def_of_pos (by positivity), h1, h2, ← exp_add, ← exp_add,
          ← exp_add, cA, eA, hL]
        congr 1; ring

/-- Subadditivity of `x ↦ x^p` over finite sums in `ℝ≥0∞`. -/
theorem rpow_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) : (∑ i ∈ s, f i) ^ p ≤ ∑ i ∈ s, f i ^ p := by
  classical
  refine Finset.induction_on s (by simp [ENNReal.zero_rpow_of_pos hp0]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1).trans (add_le_add le_rfl ih)

/-- Indices of the boxes at level `n` meeting `B(0,a)`. -/
def boxIdx (a n : ℕ) : Finset ℤ :=
  Finset.Icc (-(⌈(a : ℝ) / radius n⌉ + 1)) (⌈(a : ℝ) / radius n⌉ + 1)

theorem ceil_nonneg_aux (a n : ℕ) : 0 ≤ ⌈(a : ℝ) / radius n⌉ :=
  Int.ceil_nonneg (div_nonneg a.cast_nonneg (radius_pos n).le)

theorem abs_le_of_mem_boxIdx {a n : ℕ} {j : ℤ} (hj : j ∈ boxIdx a n) :
    |(j : ℝ)| ≤ (a : ℝ) / radius n + 2 := by
  rw [boxIdx, Finset.mem_Icc] at hj
  have hc := Int.ceil_lt_add_one ((a : ℝ) / radius n)
  have h1 : (j : ℝ) ≤ (⌈(a : ℝ) / radius n⌉ : ℝ) + 1 := by exact_mod_cast hj.2
  have h2 : -((⌈(a : ℝ) / radius n⌉ : ℝ) + 1) ≤ j := by exact_mod_cast hj.1
  rw [abs_le]; constructor <;> linarith

theorem card_boxIdx_le (a n : ℕ) :
    ((boxIdx a n).card : ℝ) ≤ (2 * a + 5) * (1 / radius n) := by
  have hr := radius_pos n
  have hr1 : radius n ≤ 1 := BdryExist.radius_le_one n
  have hc0 := ceil_nonneg_aux a n
  have hcard : ((boxIdx a n).card : ℤ) = 2 * ⌈(a : ℝ) / radius n⌉ + 3 := by
    rw [boxIdx, Int.card_Icc_of_le (a := -(⌈(a : ℝ) / radius n⌉ + 1))
      (b := ⌈(a : ℝ) / radius n⌉ + 1) (by linarith)]
    ring
  have hcardR : ((boxIdx a n).card : ℝ) = 2 * (⌈(a : ℝ) / radius n⌉ : ℝ) + 3 := by
    exact_mod_cast hcard
  have hc := Int.ceil_lt_add_one ((a : ℝ) / radius n)
  have hinv : 1 ≤ 1 / radius n := by rw [le_div_iff₀ hr]; linarith
  rw [hcardR]
  have : (a : ℝ) / radius n = a * (1 / radius n) := by ring
  nlinarith [a.cast_nonneg (α := ℝ)]

theorem boxIdx_R {a n : ℕ} {j : ℤ} (hj : j ∈ boxIdx a n) :
    |(j * radius n : ℝ)| + 5 * radius n ≤ (a : ℝ) + 7 := by
  have hr := radius_pos n
  have hr1 : radius n ≤ 1 := BdryExist.radius_le_one n
  have h := abs_le_of_mem_boxIdx hj
  rw [abs_mul, abs_of_pos hr]
  have : |(j : ℝ)| * radius n ≤ ((a : ℝ) / radius n + 2) * radius n :=
    mul_le_mul_of_nonneg_right h hr.le
  rw [add_mul, div_mul_cancel₀ _ hr.ne'] at this
  linarith

/-- Covering of `B(0,a) ∩ ℍ` by a compact of `ℍ` and the boxes. -/
theorem ball_inter_H_subset (a : ℕ) :
    Metric.ball (0 : ℂ) a ∩ H ⊆ VagueH.Kset a ∪ ⋃ n, ⋃ j ∈ boxIdx a n, boxU n j := by
  classical
  rintro z ⟨hzb, hzH⟩
  have hza : ‖z‖ < a := by simpa using hzb
  have hzH' : 0 < z.im := hzH
  by_cases him : 1 ≤ z.im
  · left
    refine ⟨hza.le, le_trans ?_ him⟩
    rw [div_le_one (by positivity)]; linarith [a.cast_nonneg (α := ℝ)]
  right
  have him : z.im < 1 := not_le.1 him
  have hex : ∃ n, radius n < z.im := exists_pow_lt_of_lt_one hzH' (by norm_num : (2 : ℝ)⁻¹ < 1)
  set n := Nat.find hex with hn
  have hspec : radius n < z.im := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp [radius] at hspec
    linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hn0
  have hmin : ¬ radius m < z.im := Nat.find_min hex (by omega)
  have hup : z.im ≤ 2 * radius n := by
    have hmin' : z.im ≤ radius m := not_lt.1 hmin
    rw [hm, BdryExist.radius_succ]; linarith
  have hr := radius_pos n
  set j := ⌊z.re / radius n⌋ with hj
  have hj1 : (j : ℝ) ≤ z.re / radius n := Int.floor_le _
  have hj2 : z.re / radius n < j + 1 := Int.lt_floor_add_one _
  have hre : |z.re| < a := lt_of_le_of_lt (Complex.abs_re_le_norm z) hza
  have hj1' : (j : ℝ) * radius n ≤ z.re := by rwa [le_div_iff₀ hr] at hj1
  have hj2' : z.re < (j + 1) * radius n := by rwa [div_lt_iff₀ hr] at hj2
  have hbox : z ∈ boxU n j := by
    refine ⟨?_, by linarith, by linarith⟩
    rw [abs_lt]; constructor <;> nlinarith
  have hjS : j ∈ boxIdx a n := by
    rw [boxIdx, Finset.mem_Icc]
    have hc := Int.le_ceil ((a : ℝ) / radius n)
    have hre' := abs_lt.1 hre
    have ha1 : z.re / radius n < (a : ℝ) / radius n := div_lt_div_of_pos_right hre'.2 hr
    have ha2 : -((a : ℝ) / radius n) < z.re / radius n := by
      rw [← neg_div]; exact div_lt_div_of_pos_right hre'.1 hr
    constructor
    · have : (-(⌈(a : ℝ) / radius n⌉ + 1) : ℝ) < j := by push_cast; linarith
      exact_mod_cast this.le
    · have : (j : ℝ) ≤ (⌈(a : ℝ) / radius n⌉ + 1 : ℝ) := by linarith
      exact_mod_cast this
  exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion₂.2 ⟨j, hjS, hbox⟩⟩

/-- **(2) for the normalized field.** A.s. `μ_Z(B(0,a) ∩ ℍ) < ∞`, `Z = aZ X (a + 7)`. -/
theorem ae_qAreaMeasure_aZ_ball_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (a : ℕ) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (AreaExist.aZ X ((a : ℝ) + 7) ω) (Metric.ball 0 a ∩ H) < ⊤ := by
  set R : ℝ := (a : ℝ) + 7 with hRdef
  set η : ℝ := (4 - γ ^ 2) / 16 with hη
  set p : ℝ := 1 / 2 + η with hp
  have hγ4 : γ ^ 2 < 4 := by nlinarith
  have hη0 : 0 < η := by rw [hη]; linarith
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : p ≤ 1 := by rw [hp, hη]; nlinarith
  have he : 0 < eA γ p - 1 := by
    have : eA γ p - 1 = η * (4 - γ ^ 2) * (1 / 2 - γ ^ 2 / 16) := by rw [eA, hp, hη]; ring
    rw [this]
    have h1 : 0 < 4 - γ ^ 2 := by linarith
    have h2 : 0 < 1 / 2 - γ ^ 2 / 16 := by linarith
    exact mul_pos (mul_pos hη0 h1) h2
  set G : ℕ → ℤ → Ω → ℝ≥0∞ := fun n j ω =>
    liminf (fun k => areaApprox γ (AreaExist.aZ X R ω) k (boxK n j) ^ p) atTop with hG
  have hGm : ∀ n j, Measurable (G n j) := fun n j =>
    Measurable.liminf fun k =>
      (measurable_areaApprox_aZ_apply hX γ R k (isClosed_boxK n j).measurableSet).pow_const p
  set f : ℕ → ℝ := fun n =>
    (2 * a + 5) * exp (cA γ R p) * exp (-(log 2 * (eA γ p - 1))) ^ n with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by rw [hf]; positivity
  have hfs : Summable f := by
    refine (summable_geometric_of_lt_one (exp_pos _).le ?_).mul_left _
    rw [Real.exp_lt_one_iff]
    have := log_pos one_lt_two
    nlinarith
  have hGn : ∀ n, ∑ j ∈ boxIdx a n, ∫⁻ ω, G n j ω ∂P ≤ ENNReal.ofReal (f n) := by
    intro n
    have hr := radius_pos n
    have hb : ∀ j ∈ boxIdx a n, ∫⁻ ω, G n j ω ∂P ≤
        ENNReal.ofReal (exp (cA γ R p) * exp (-(n : ℝ) * log 2 * eA γ p)) := by
      intro j hj
      have hRj := boxIdx_R hj
      have hj0 := abs_nonneg ((j : ℝ) * radius n)
      have h5R : 5 * radius n ≤ R := by rw [hRdef]; linarith
      exact (lintegral_liminf_areaApprox_rpow_le hX γ (t := j * radius n) (by positivity)
        (by positivity) hRj hp0 hp1 (isClosed_boxK n j).measurableSet
        (boxK_spec n j)).trans (fracBoundC_boxK_le hp0 j h5R)
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hinv : 1 / radius n = exp ((n : ℝ) * log 2) := by
      rw [← BdryExist.log_one_div_radius n, exp_log (by positivity)]
    calc ((boxIdx a n).card : ℝ) * (exp (cA γ R p) * exp (-(n : ℝ) * log 2 * eA γ p))
        ≤ (2 * a + 5) * (1 / radius n) * (exp (cA γ R p) * exp (-(n : ℝ) * log 2 * eA γ p)) :=
          mul_le_mul_of_nonneg_right (card_boxIdx_le a n) (by positivity)
      _ = f n := by
          simp only [hf]
          rw [hinv, ← exp_nat_mul, (show (2 * (a : ℝ) + 5) * exp ((n : ℝ) * log 2) *
              (exp (cA γ R p) * exp (-(n : ℝ) * log 2 * eA γ p)) = (2 * a + 5) * exp (cA γ R p) *
              (exp ((n : ℝ) * log 2) * exp (-(n : ℝ) * log 2 * eA γ p)) by ring), ← exp_add]
          congr 2; ring
  have hsum : ∫⁻ ω, ∑' n, ∑ j ∈ boxIdx a n, G n j ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => (Finset.measurable_sum _ fun j _ => hGm n j).aemeasurable]
    have hle : ∑' n, ∫⁻ ω, ∑ j ∈ boxIdx a n, G n j ω ∂P ≤ ∑' n, ENNReal.ofReal (f n) :=
      ENNReal.tsum_le_tsum fun n => by
        rw [lintegral_finset_sum _ fun j _ => hGm n j]; exact hGn n
    refine ne_top_of_le_ne_top ?_ hle
    rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfs]; exact ENNReal.ofReal_ne_top
  have hfin := ae_lt_top (Measurable.ennreal_tsum fun n =>
    Finset.measurable_sum _ fun j _ => hGm n j) hsum
  filter_upwards [hfin, AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX (P := P) hγ hγ2 R]
    with ω hω hv
  set μ := qAreaMeasure γ (AreaExist.aZ X R ω) with hμ
  have hle : ∀ n j, μ (boxU n j) ^ p ≤ G n j ω := fun n j =>
    rpow_le_liminf_of_isVagueLimitOn hv (isOpen_boxU n j) (isCompact_boxK n j)
      (boxU_subset_boxK n j) (boxK_subset_H n j) hp0
  have hS : (∑' n, ∑ j ∈ boxIdx a n, μ (boxU n j)) < ⊤ := by
    have h : (∑' n, ∑ j ∈ boxIdx a n, μ (boxU n j)) ^ p < ⊤ :=
      calc (∑' n, ∑ j ∈ boxIdx a n, μ (boxU n j)) ^ p
          ≤ ∑' n, (∑ j ∈ boxIdx a n, μ (boxU n j)) ^ p :=
            FracMom.rpow_tsum_le_tsum_rpow _ hp0 hp1
        _ ≤ ∑' n, ∑ j ∈ boxIdx a n, μ (boxU n j) ^ p :=
            ENNReal.tsum_le_tsum fun n => rpow_finset_sum_le _ _ hp0 hp1
        _ ≤ ∑' n, ∑ j ∈ boxIdx a n, G n j ω :=
            ENNReal.tsum_le_tsum fun n => Finset.sum_le_sum fun j _ => hle n j
        _ < ⊤ := hω
    exact (ENNReal.rpow_lt_top_iff_of_pos hp0).1 h
  calc μ (Metric.ball 0 a ∩ H)
      ≤ μ (VagueH.Kset a ∪ ⋃ n, ⋃ j ∈ boxIdx a n, boxU n j) :=
        measure_mono (ball_inter_H_subset a)
    _ ≤ μ (VagueH.Kset a) + ∑' n, ∑ j ∈ boxIdx a n, μ (boxU n j) :=
        (measure_union_le _ _).trans (add_le_add le_rfl ((measure_iUnion_le _).trans
          (ENNReal.tsum_le_tsum fun n => measure_biUnion_finset_le _ _)))
    _ < ⊤ := ENNReal.add_lt_top.2
        ⟨hv.2.1 _ (VagueH.isCompact_Kset a) (VagueH.Kset_subset_H a), hS⟩

/-- **(2) M4-A3 for the free field.** Almost surely `μ_X(B(0,a) ∩ ℍ) < ∞` for every `a`,
`μ_X = qAreaMeasure γ X`. -/
theorem ae_qAreaMeasure_ball_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, qAreaMeasure γ (X ω) (Metric.ball 0 a ∩ H) < ⊤ := by
  have h1 := ae_all_iff.2 fun a : ℕ => ae_qAreaMeasure_aZ_ball_lt_top hX (P := P) hγ hγ2 a
  have h2 := ae_all_iff.2 fun a : ℕ => ae_qAreaMeasure_aZ_eq_smul hX (P := P) hγ hγ2 ((a : ℝ) + 7)
  filter_upwards [h1, h2] with ω h1 h2 a
  obtain ⟨N, hN⟩ := exists_nat_ge a
  have hsub : Metric.ball (0 : ℂ) a ∩ H ⊆ Metric.ball 0 N ∩ H :=
    Set.inter_subset_inter_left _ (Metric.ball_subset_ball hN)
  refine (measure_mono hsub).trans_lt ?_
  have h := h1 N
  rw [h2 N, Measure.smul_apply, smul_eq_mul] at h
  have hc : ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 ((N : ℝ) + 7))))) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact exp_pos _
  exact ENNReal.lt_top_of_mul_ne_top_right h.ne hc

/-! ### (3) Adding a continuous function -/

section OfFun

open GoodSample RegClosure CircleFubini

theorem tendsto_radius_nhdsGT : Tendsto (fun k : ℕ => radius k) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
    Eventually.of_forall radius_pos⟩

/-- **Rule (5.1) along `2^{-k}`**: for a regular sample `x` with a vague area limit `μ` and `φ`
continuous on `Hbar`, `x + ofFun φ` has the vague area limit `e^{γφ} μ`. -/
theorem isVagueLimitOn_add_ofFun {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x)
    {μ : Measure ℂ} (hμ : IsVagueLimitOn H (areaApprox γ x) μ) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) :
    IsVagueLimitOn H (areaApprox γ (x + ofFun φ))
      (μ.withDensity fun z => ENNReal.ofReal (exp (γ * φ z))) := by
  obtain ⟨F, hF⟩ := hx
  obtain ⟨F', hF'⟩ := gs_add_ofFun_sample ⟨F, hF⟩ hφ
  have hφf : Continuous fun z => φ (foldH z) := continuous_comp_foldH hφ
  have hdc : Continuous fun z => exp (γ * φ (foldH z)) :=
    continuous_exp.comp (continuous_const.mul hφf)
  have hae : ∀ᵐ z ∂μ, z ∈ H := ae_Hbar_of_null hμ.1
  have heq : (μ.withDensity fun z => ENNReal.ofReal (exp (γ * φ z))) =
      μ.withDensity fun z => ENNReal.ofReal (exp (γ * φ (foldH z))) :=
    withDensity_congr_ae (hae.mono fun z hz => by
      simp only [foldH_of_mem' (show (0 : ℝ) ≤ z.im from le_of_lt hz)])
  rw [heq]
  refine ⟨withDensity_absolutelyContinuous _ _ hμ.1,
    fun K hK hKH => withDensity_lt_top hK (hμ.2.1 K hK hKH) hdc.continuousOn,
    fun f hf hfc hfU => ?_⟩
  rw [integral_withDensity_ofReal hdc.measurable fun _ => (exp_pos _).le]
  have key := tendsto_integral_exp_mul (X := ℂ) (L := atTop) (U := H) isOpen_H
    (νs := fun k => areaR γ x (radius k)) (ν := μ)
    (Eventually.of_forall fun k K hK _ => areaR_lt_top γ hF (radius_pos k) hK)
    (fun g hg hgc hgU => (hμ.2.2 g hg hgc hgU).congr fun k => by
      rw [← areaR_radius γ hF k, one_mul])
    (v := fun k z => γ * smoothFun φ z (radius k)) (v0 := fun z => γ * φ (foldH z))
    (continuous_const.mul hφf).continuousOn
    (Eventually.of_forall fun k => (continuous_const.mul (continuous_smoothFun hφ _)).continuousOn)
    (fun K hK hKH ε hε => by
      have hs := tendsto_radius_nhdsGT.eventually (smooth_unif hφ hK
        (fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt (hKH hz)) (ε / (|γ| + 1)) (by positivity))
      filter_upwards [hs] with k hk z hz
      rw [foldH_of_mem' (show (0 : ℝ) ≤ z.im from le_of_lt (hKH hz)), ← mul_sub, abs_mul]
      calc |γ| * |smoothFun φ z (radius k) - φ z| ≤ |γ| * (ε / (|γ| + 1)) :=
            mul_le_mul_of_nonneg_left (hk z hz).le (abs_nonneg _)
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith [abs_nonneg γ])
    hf hfc hfU
  refine key.congr fun k => ?_
  rw [← areaR_radius γ hF' k, one_mul, integral_areaR_add_ofFun γ hF hφ (radius_pos k) f]

/-- A.s. `qAreaMeasure γ (X + ofFun φ) = e^{γφ} qAreaMeasure γ X`. -/
theorem ae_qAreaMeasure_add_ofFun [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (X ω + ofFun φ) =
      (qAreaMeasure γ (X ω)).withDensity fun z => ENNReal.ofReal (exp (γ * φ z)) := by
  filter_upwards [RegSample.ae_isRegularSample hX, AreaExist.ae_isVagueLimitOn_qAreaMeasure hX (P := P) hγ hγ2]
    with ω hr hv
  exact qAreaMeasure_eq (isVagueLimitOn_add_ofFun hr hv hφ)

end OfFun

end FinArea
end QuantumZipper
