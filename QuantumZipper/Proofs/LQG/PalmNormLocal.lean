import QuantumZipper.Proofs.LQG.PalmNorm
import QuantumZipper.Proofs.LQG.LocalRule

/-!
# PALM-NORM, local version: `h` only continuous near the window

Blueprint `E_BRANCH_BLUEPRINT.md` §4 E1, step (2), last sentence: "`h0rev` is continuous near
`F J`; replace it by a continuous function off a neighbourhood and absorb the difference in `φ`."

* Locality of the boundary measure (`qBoundaryMeasure_restrict_eq_of_avgReg`,
  `qBoundaryMeasure_restrict_Ioo_eq`, `eventually_avgReg_normAt_eq`): the dyadic approximations
  `bdryApprox γ x k` only read the raw values of `x` on folded circles of radius `2^{-k}`, so two
  samples whose regularized averages agree near `[a,b]` for all large `k` have vague limits that
  agree on `(a,b)` (uniqueness of local vague limits, `LocalRule.isVagueLimitOnR_unique`).
* `palm_formula_norm_local`: `palm_formula_norm` for `h` that agrees with a continuous `h'` on an
  open neighbourhood `W` of `[a,b]` (and is `ϖ`, `μ_j`-integrable), provided the vague limit
  defining `ν = qBoundaryMeasure γ (N_ϖ(ofFun h + X))` exists a.s. Proof: apply
  `palm_formula_norm` to `h'` and to `φ'(v, x) = e^{−γ d/2} φ(v + s, x)`, where
  `d = ∫(h − h') dϖ` and `s_j = ∫(h − h') dμ_j − d μ_j(ℂ)` is the deterministic coordinate shift;
  on `(a,b)`, `ν_h = e^{−γ d/2} ν_{h'}` by locality, and `ρ_{h'} e^{−γ d/2} = ρ_h` on `W`.

Sources. This is the elementary locality of the Duplantier–Sheffield boundary measure
(B. Duplantier, S. Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
arXiv:0808.1560, §3 and (1.2): `ν` is the limit of `ε^{γ²/4} e^{γ h_ε/2} dx`, where `h_ε(x)` only
depends on `h` in `B_ε(x)`); the reduction is the project route of E_BRANCH §4 E1. No published
Lean/proof text exists for this bookkeeping step; the argument is our own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace QuantumZipper
namespace PalmNorm

open Palm PalmFree BdryExist

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ a b : ℝ}

/-! ## 1. Locality of vague limits on `ℝ` -/

lemma isVagueLimitOnR_restrict_of_R {νs : ℕ → Measure ℝ} {ν : Measure ℝ}
    (h : IsVagueLimitR νs ν) {U : Set ℝ} (hU : IsOpen U) :
    IsVagueLimitOnR U νs (ν.restrict U) := by
  have := h.1
  refine ⟨?_, fun K hK _ => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.restrict_apply hU.measurableSet.compl]; simp
  · exact (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => image_eq_zero_of_notMem_tsupport (fun h' => ht (hfU h')))]
    exact h.2 f hf hfc

lemma integral_eq_of_restrict_eq' {μ μ' : Measure ℝ} {U : Set ℝ}
    (h : μ.restrict U = μ'.restrict U) {f : ℝ → ℝ} (hfU : ∀ t, t ∉ U → f t = 0) :
    ∫ t, f t ∂μ = ∫ t, f t ∂μ' := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) hfU, h,
    setIntegral_eq_integral_of_forall_compl_eq_zero hfU]

lemma bdryApprox_restrict_eq {x y : FieldSample} {k : ℕ} {U : Set ℝ} (hU : MeasurableSet U)
    (h : ∀ t ∈ U, avgReg x k (t : ℂ) = avgReg y k (t : ℂ)) :
    (bdryApprox γ x k).restrict U = (bdryApprox γ y k).restrict U := by
  unfold bdryApprox
  rw [restrict_withDensity hU, restrict_withDensity hU]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hU] with t ht
  rw [h t ht]

/-- **Locality of `qBoundaryMeasure`.** If the regularized averages of `x` and `y` agree on the
open set `U` for all large `k`, and both vague limits exist, the boundary measures agree on `U`. -/
theorem qBoundaryMeasure_restrict_eq_of_avgReg {x y : FieldSample} {U : Set ℝ} (hU : IsOpen U)
    (hx : ∃ ν, IsVagueLimitR (bdryApprox γ x) ν) (hy : ∃ ν, IsVagueLimitR (bdryApprox γ y) ν)
    (h : ∀ᶠ k in atTop, ∀ t ∈ U, avgReg x k (t : ℂ) = avgReg y k (t : ℂ)) :
    (qBoundaryMeasure γ x).restrict U = (qBoundaryMeasure γ y).restrict U := by
  obtain ⟨ν, hν⟩ := hx
  obtain ⟨ν', hν'⟩ := hy
  rw [qBoundaryMeasure_eq hν, qBoundaryMeasure_eq hν']
  have h1 := isVagueLimitOnR_restrict_of_R hν hU
  have h2 := isVagueLimitOnR_restrict_of_R hν' hU
  refine LocalRule.isVagueLimitOnR_unique hU h1 ⟨h2.1, h2.2.1, fun f hf hfc hfU => ?_⟩
  refine (h2.2.2 f hf hfc hfU).congr' ?_
  filter_upwards [h] with k hk
  exact (integral_eq_of_restrict_eq' (bdryApprox_restrict_eq hU.measurableSet hk)
    (fun t ht => image_eq_zero_of_notMem_tsupport fun h' => ht (hfU h'))).symm

/-- If `h = h'` on an open `W ⊇ [a,b]`, then for small dyadic radii the integrals of `h` and `h'`
over folded circles centred near `[a,b]` agree. -/
lemma exists_eventually_ofFun_fc_eq {h h' : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hab : ∀ t ∈ Icc a b, (t : ℂ) ∈ W) (hEq : EqOn h h' W) :
    ∃ ρ > 0, ∀ᶠ k in atTop, ∀ t ∈ Icc a b, ∀ c ∈ Hbar, dist c (t : ℂ) < ρ →
      ofFun h (foldedCircle c (radius k)) = ofFun h' (foldedCircle c (radius k)) := by
  set K : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc a b with hKdef
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW
    (by rintro _ ⟨t, ht, rfl⟩; exact hab t ht)
  refine ⟨δ / 2, by positivity, ?_⟩
  have hr : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hr.eventually (gt_mem_nhds (half_pos hδ))] with k hk t ht c hc hct
  refine LocalRule.ofFun_fc_congr hc (radius_pos k) fun u hu => hEq (hδW ?_)
  refine Metric.mem_cthickening_of_dist_le u (t : ℂ) δ K ⟨t, ht, rfl⟩ ?_
  have hu' := Metric.mem_closedBall.1 hu
  calc dist u (t : ℂ) ≤ dist u c + dist c (t : ℂ) := dist_triangle _ _ _
    _ ≤ δ := by linarith

/-- Normalized form: near `[a,b]`, `N_ϖ(ofFun h + Y)` is `N_ϖ(ofFun h' + Y)` shifted by the
constant `−∫(h − h') dϖ`. -/
theorem eventually_avgReg_normAt_eq {h h' : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hab : ∀ t ∈ Icc a b, (t : ℂ) ∈ W) (hEq : EqOn h h' W) (ϖ : Measure ℂ) (Y : FieldSample) :
    ∀ᶠ k in atTop, ∀ t ∈ Ioo a b, avgReg (normAt ϖ (ofFun h + Y)) k (t : ℂ) =
      avgReg (addConst (normAt ϖ (ofFun h' + Y)) (-(ofFun h ϖ - ofFun h' ϖ))) k (t : ℂ) := by
  obtain ⟨ρ, hρ, hev⟩ := exists_eventually_ofFun_fc_eq hW hab hEq
  filter_upwards [hev] with k hk t ht
  refine LocalRule.avgReg_congr_local k hρ (fun c hc hct => ?_) (GaussTK.ofReal_mem_Hbar t)
  simp only [normAt, addConst, Pi.add_apply]
  rw [hk t (Ioo_subset_Icc_self ht) c hc hct]
  ring

/-! ## 2. Algebra of the shift -/

lemma normAt_ofFun_sub (ϖ : Measure ℂ) (f f' : ℂ → ℝ) (Y : FieldSample) (ν : Measure ℂ) :
    normAt ϖ (ofFun f + Y) ν = normAt ϖ (ofFun f' + Y) ν +
      ((ofFun f ν - ofFun f' ν) - (ofFun f ϖ - ofFun f' ϖ) * (ν univ).toReal) := by
  simp only [normAt, addConst, Pi.add_apply]
  ring

lemma integrable_of_continuous_adm {f : ℂ → ℝ} (hf : Continuous f) {ν : Measure ℂ}
    (hν : IsAdmissibleH ν) : Integrable f ν := by
  obtain ⟨hfin, ⟨K, hK, -, hK0⟩, -⟩ := hν
  have hr : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hK0)
  have := hf.continuousOn.integrableOn_compact (μ := ν) hK
  rwa [IntegrableOn, hr] at this

lemma ofFun_shiftFun_sub {h h' : ℂ → ℝ} {ϖ ν : Measure ℂ} (hν : IsAdmissibleH ν)
    (hϖ : IsAdmissibleH ϖ) (hhν : Integrable h ν) (hh'ν : Integrable h' ν) (x : ℝ) :
    ofFun (shiftFun γ h ϖ x) ν - ofFun (shiftFun γ h' ϖ x) ν = ofFun h ν - ofFun h' ν := by
  have hg : Integrable (fun u => γ / 2 * (neumannH (x : ℂ) u - kPot ϖ u)) ν :=
    ((PalmArea.integrable_neumannH_left hν _).sub (integrable_kPot hν hϖ)).const_mul _
  simp only [ofFun, shiftFun]
  rw [integral_add hhν hg, integral_add hh'ν hg]
  ring

lemma rhoNorm_mul_exp {h h' : ℂ → ℝ} (ϖ : Measure ℂ) {x : ℝ} (hx : h x = h' x) :
    rhoNorm γ h' ϖ x * Real.exp (γ / 2 * -(ofFun h ϖ - ofFun h' ϖ)) = rhoNorm γ h ϖ x := by
  unfold rhoNorm
  rw [← Real.exp_add, hx]
  congr 1
  simp only [ofFun]
  ring

/-- A.s. regular base: `N_ϖ(ofFun g + x)` shifted by any constant has a vague limit, and the
constant rescales it. -/
lemma normAt_addConst_vague {x : FieldSample} (hreg : IsRegularSample x) {ν : Measure ℝ}
    (hv : IsVagueLimitR (bdryApprox γ x) ν) {g : ℂ → ℝ} (hg : Continuous g) (ϖ : Measure ℂ)
    (c : ℝ) :
    (∃ ν', IsVagueLimitR (bdryApprox γ (addConst (normAt ϖ (ofFun g + x)) c)) ν') ∧
    qBoundaryMeasure γ (addConst (normAt ϖ (ofFun g + x)) c) =
      ENNReal.ofReal (Real.exp (γ / 2 * c)) • qBoundaryMeasure γ (normAt ϖ (ofFun g + x)) := by
  obtain ⟨F, hF⟩ := hreg
  set c0 := -((ofFun g + x) ϖ) with hc0
  have hF1 := GoodSample.gs_add_ofFun hF hg.continuousOn
  have hF2 := GoodSample.gs_add_ofFun hF1 (φ := fun _ => c0) continuousOn_const
  have hv1 := isVagueLimitR_add_ofFun hF hg.continuousOn hv
  have hv2 := isVagueLimitR_add_ofFun hF1 (m := fun _ => c0) continuousOn_const hv1
  have hv3 := isVagueLimitR_add_ofFun hF2 (m := fun _ => c) continuousOn_const hv2
  have e1 : normAt ϖ (ofFun g + x) = x + ofFun g + ofFun (fun _ => c0) := by
    unfold normAt; rw [GoodSample.addConst_eq_add_ofFun]; congr 1; exact add_comm _ _
  rw [e1, GoodSample.addConst_eq_add_ofFun]
  refine ⟨⟨_, hv3⟩, ?_⟩
  rw [qBoundaryMeasure_eq hv3, qBoundaryMeasure_eq hv2]
  simp only [PalmFree.eW]
  exact withDensity_const _

lemma weight_eq_zero_off_Ioo {w : ℝ → ℝ} (hw : Continuous w)
    (hwab : ∀ x ∉ Icc a b, w x = 0) : ∀ x ∉ Ioo a b, w x = 0 := by
  have hwa : w a = 0 := by
    have h1 : Tendsto w (𝓝[<] a) (𝓝 (w a)) := hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto w (𝓝[<] a) (𝓝 0) := tendsto_const_nhds.congr'
      (eventually_nhdsWithin_of_forall fun x hx =>
        (hwab x fun hx' => not_le.2 (show x < a from hx) hx'.1).symm)
    exact tendsto_nhds_unique h1 h2
  have hwb : w b = 0 := by
    have h1 : Tendsto w (𝓝[>] b) (𝓝 (w b)) := hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto w (𝓝[>] b) (𝓝 0) := tendsto_const_nhds.congr'
      (eventually_nhdsWithin_of_forall fun x hx =>
        (hwab x fun hx' => not_le.2 (show b < x from hx) hx'.2).symm)
    exact tendsto_nhds_unique h1 h2
  intro x hx
  by_cases hxI : x ∈ Icc a b
  · rcases hxI.1.eq_or_lt with hax | hax
    · rw [← hax]; exact hwa
    · rcases hxI.2.eq_or_lt with hxb | hxb
      · rw [hxb]; exact hwb
      · exact absurd ⟨hax, hxb⟩ hx
  · exact hwab x hxI

/-! ## 3. The Palm formula with `h` continuous only near the window -/

/-- **PALM-NORM, local version (E1, step (2)).** As `palm_formula_norm`, but `h` need only agree
with a continuous `h'` on an open neighbourhood `W` of `[a,b]` (and be `ϖ`- and
`μ_j`-integrable), provided the vague limit defining `qBoundaryMeasure γ (N_ϖ(ofFun h + X))`
exists a.s. -/
theorem palm_formula_norm_local {X : Ω → FieldSample} {h h' : ℂ → ℝ} {ϖ : Measure ℂ}
    {μ : ℕ → Measure ℂ}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2)
    {N : ℕ} (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) (hh' : Continuous h')
    {W : Set ℂ} (hW : IsOpen W) (habW : ∀ t ∈ Icc a b, (t : ℂ) ∈ W) (hEq : EqOn h h' W)
    (hϖ : IsAdmissibleH ϖ) (hϖ1 : ϖ univ = 1) (hμ : ∀ j, IsAdmissibleH (μ j))
    (hhϖ : Integrable h ϖ) (hhμ : ∀ j, Integrable h (μ j))
    (hex : ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitR (bdryApprox γ (normAt ϖ (ofFun h + X ω))) ν)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hwab : ∀ x ∉ Icc a b, w x = 0)
    {φ : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hφ : Measurable (Function.uncurry φ)) :
    ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (w x) * φ (fun j => normAt ϖ (ofFun h + X ω) (μ j)) x
        ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h + X ω))) ∂P =
      ∫⁻ x, ENNReal.ofReal (w x * rhoNorm γ h ϖ x) *
        ∫⁻ ω, φ (fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j)) x ∂P := by
  set d : ℝ := ofFun h ϖ - ofFun h' ϖ with hd
  set s : ℕ → ℝ := fun j => (ofFun h (μ j) - ofFun h' (μ j)) - d * (μ j univ).toReal with hs
  set C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ / 2 * -d)) with hC
  set φ' : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun v x => C * φ (fun j => v j + s j) x with hφ'
  have hφ'm : Measurable (Function.uncurry φ') := by
    have hmap : Measurable fun p : (ℕ → ℝ) × ℝ => ((fun j => p.1 j + s j), p.2) :=
      (measurable_pi_iff.2 fun j =>
        ((measurable_pi_apply j).comp measurable_fst).add measurable_const).prodMk measurable_snd
    exact measurable_const.mul (hφ.comp hmap)
  have H := palm_formula_norm (P := P) (μ := μ) (γ := γ) hX hγ hγ2 hab hh' hϖ hϖ1 hμ hw hwc hw0
    hwab hφ'm
  have hwU := weight_eq_zero_off_Ioo hw hwab
  have hcoL : ∀ Y : FieldSample, (fun j => normAt ϖ (ofFun h + Y) (μ j)) =
      fun j => normAt ϖ (ofFun h' + Y) (μ j) + s j := fun Y => by
    funext j; rw [normAt_ofFun_sub ϖ h h' Y (μ j)]
  -- the left side
  have hL : ∀ᵐ ω ∂P,
      ∫⁻ x, ENNReal.ofReal (w x) * φ (fun j => normAt ϖ (ofFun h + X ω) (μ j)) x
        ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h + X ω))) =
      ∫⁻ x, ENNReal.ofReal (w x) * φ' (fun j => normAt ϖ (ofFun h' + X ω) (μ j)) x
        ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h' + X ω))) := by
    filter_upwards [hex, ae_isRegularSample_zField hX 1,
      ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 1] with ω hexω hreg hv
    rw [hcoL (X ω), normAt_zField hϖ1 1 h ω, normAt_zField hϖ1 1 h' ω]
    rw [normAt_zField hϖ1 1 h ω] at hexω
    obtain ⟨hey, hq⟩ := normAt_addConst_vague hreg hv hh' ϖ (-d)
    have hloc := qBoundaryMeasure_restrict_eq_of_avgReg isOpen_Ioo hexω hey
      (eventually_avgReg_normAt_eq hW habW hEq ϖ (zField X 1 ω))
    rw [hq, Measure.restrict_smul] at hloc
    set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (w x) *
      φ (fun j => normAt ϖ (ofFun h' + zField X 1 ω) (μ j) + s j) x with hF
    have hsupp : Function.support F ⊆ Ioo a b := by
      intro x hx
      by_contra hxU
      exact hx (by simp only [hF, hwU x hxU, ENNReal.ofReal_zero, zero_mul])
    calc ∫⁻ x, F x ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h + zField X 1 ω)))
        = ∫⁻ x in Ioo a b, F x ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h + zField X 1 ω))) :=
          (setLIntegral_eq_of_support_subset hsupp).symm
      _ = C * ∫⁻ x in Ioo a b, F x
            ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h' + zField X 1 ω))) := by
          rw [hloc, lintegral_smul_measure, smul_eq_mul]
      _ = C * ∫⁻ x, F x ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h' + zField X 1 ω))) := by
          rw [setLIntegral_eq_of_support_subset hsupp]
      _ = _ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          simp only [hF, hφ']
          ring
  -- the right side, pointwise in `x`
  have hR : ∀ x, ENNReal.ofReal (w x * rhoNorm γ h' ϖ x) *
      ∫⁻ ω, φ' (fun j => normAt ϖ (ofFun (shiftFun γ h' ϖ x) + X ω) (μ j)) x ∂P =
      ENNReal.ofReal (w x * rhoNorm γ h ϖ x) *
        ∫⁻ ω, φ (fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j)) x ∂P := by
    intro x
    by_cases hx0 : w x = 0
    · simp [hx0]
    have hxI : x ∈ Icc a b := by by_contra hxI; exact hx0 (hwab x hxI)
    have hxe : h x = h' x := hEq (habW x hxI)
    have hco : ∀ ω, (fun j => normAt ϖ (ofFun (shiftFun γ h' ϖ x) + X ω) (μ j) + s j) =
        fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j) := fun ω => by
      funext j
      rw [normAt_ofFun_sub ϖ (shiftFun γ h ϖ x) (shiftFun γ h' ϖ x) (X ω) (μ j),
        ofFun_shiftFun_sub (hμ j) hϖ (hhμ j) (integrable_of_continuous_adm hh' (hμ j)) x,
        ofFun_shiftFun_sub hϖ hϖ hhϖ (integrable_of_continuous_adm hh' hϖ) x]
    have hint : ∫⁻ ω, φ' (fun j => normAt ϖ (ofFun (shiftFun γ h' ϖ x) + X ω) (μ j)) x ∂P =
        C * ∫⁻ ω, φ (fun j => normAt ϖ (ofFun (shiftFun γ h ϖ x) + X ω) (μ j)) x ∂P := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ω => ?_
      simp only [hφ']
      rw [hco ω]
    have hnn : 0 ≤ w x * rhoNorm γ h' ϖ x := mul_nonneg (hw0 x) (by unfold rhoNorm; positivity)
    rw [hint, ← mul_assoc, hC, ← ENNReal.ofReal_mul hnn, mul_assoc, hd,
      rhoNorm_mul_exp ϖ hxe]
  rw [lintegral_congr_ae hL, H]
  exact lintegral_congr hR

end PalmNorm
end QuantumZipper
