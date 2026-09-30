import QuantumZipper.Proofs.LQG.RegularSample
import QuantumZipper.Proofs.LQG.GoodSample
import QuantumZipper.Proofs.LQG.BoundaryExistenceAS

/-!
# M4-B4, part 1: circle values at arbitrary radii and the two-radius lemma at an offset

Blueprint `M4_BLUEPRINT.md`, node M4-B4 (inputs).

* `measurable_evalReg_fc_real`: `(x, t) ↦ evalReg x (fc(t, r))` is jointly measurable.
* `ae_evalReg_fc_eq`: for the free field and a fixed circle, `evalReg (X ω) (fc(w,r))` agrees
  almost surely with the raw coordinate `X ω (fc(w,r))` (at **every** radius `r > 0`).
* `zV X R r t ω = evalReg (Z ω) (fc(t,r))` for the normalized field `Z = zField X R`, its law,
  and the joint integrability of `g(t) · bdryDens γ (Z ω) r t`.
* `integral_abs_bA_sub_lim_le`: for `c ∈ [1,2]`,
  `E|∫ g dν_{c 2^{-k}}(Z) − ∫ g dν(Z)| ≤ C e^{-β k log 2}`, with `C` uniform in `c` and `k`
  (two-radius lemma with the constant profiles `c 2^{-k}`, `2^{-k}`, plus M4-B3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace AllOffsets

open BdryExist GaussTK TwoRadius

/-! ## A1. Joint measurability of circle values at a fixed radius -/

theorem measurable_evalReg_fc_real (r : ℝ) :
    Measurable (fun p : FieldSample × ℝ => evalReg p.1 (foldedCircle (p.2 : ℂ) r)) := by
  have key : ∀ k : ℕ, StronglyMeasurable (fun p : FieldSample × ℝ =>
      ∫ w, avgReg p.1 k w ∂foldedCircle (p.2 : ℂ) r) := by
    intro k
    have hc : Measurable (fun s : ℝ × ℝ => circleMap (s.1 : ℂ) r s.2) := by
      have : Continuous (fun s : ℝ × ℝ => circleMap (s.1 : ℂ) r s.2) := by
        simp only [circleMap]; fun_prop
      exact this.measurable
    have hjm : Measurable (fun q : (FieldSample × ℝ) × ℝ =>
        avgReg q.1.1 k (foldH (circleMap (q.1.2 : ℂ) r q.2))) :=
      (measurable_avgReg k).comp (measurable_fst.fst.prodMk
        (measurable_foldH.comp (hc.comp (measurable_fst.snd.prodMk measurable_snd))))
    have e : (fun p : FieldSample × ℝ => ∫ w, avgReg p.1 k w ∂foldedCircle (p.2 : ℂ) r) =
        fun p => (ENNReal.ofReal (2 * π))⁻¹.toReal *
          ∫ θ, avgReg p.1 k (foldH (circleMap (p.2 : ℂ) r θ))
            ∂(volume.restrict (Ico 0 (2 * π))) := by
      funext p
      have hm := RegClosure.measurable_avgReg_slice p.1 k
      rw [foldedCircle, integral_map measurable_foldH.aemeasurable hm.aestronglyMeasurable,
        circleUnif, integral_smul_measure,
        integral_map (f := fun x => avgReg p.1 k (foldH x)) (measurable_circleMap _ _).aemeasurable
          (hm.comp measurable_foldH).aestronglyMeasurable, smul_eq_mul]
    rw [e]
    exact (hjm.stronglyMeasurable.integral_prod_right').const_mul _
  unfold evalReg
  exact (StronglyMeasurable.limUnder key).measurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## A2. `evalReg` of a fixed circle is the raw coordinate, almost surely -/

open KolmD RegSample CircleFubini in
theorem ae_evalReg_fc_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {w : ℂ}
    (hw : w ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    (fun ω => evalReg (X ω) (foldedCircle w r)) =ᵐ[P] fun ω => X ω (foldedCircle w r) := by
  set V : (Fin 4 → ℝ) → Ω → ℝ := fun q ω => X ω (nuQ q) with hV
  have hVm : ∀ q, AEMeasurable (V q) P := fun q => (hX.measurable_coord _).aemeasurable
  obtain ⟨W, hWc, hWV, hWlim⟩ := exists_continuous_modification_D (d := 4) le_rfl hVm
    fun R => ⟨_, mul_nonneg (pow_nonneg (by positivity) 8) (gaussianAbsMoment_nonneg 16),
      momentBound_nuQ hX R⟩
  have hpt : ∀ ρ : ℝ, 0 < ρ →
      ∀ᵐ ω ∂P, ∫ u, W (pr u ρ 0) ω ∂foldedCircle w r = W (pr w r ρ) ω := by
    intro ρ hρ
    have hYc : ∀ ω, ContinuousOn (fun u => W (pr u ρ 0) ω - W (pr w ρ 0) ω) Hbar := fun ω =>
      (((hWc ω).comp (continuous_pr_fst ρ 0)).sub continuous_const).continuousOn
    have hY : ∀ u ∈ Hbar, (fun ω => W (pr u ρ 0) ω - W (pr w ρ 0) ω) =ᵐ[P]
        fun ω => X ω (foldedCircle u ρ) - X ω (foldedCircle w ρ) := by
      intro u hu
      filter_upwards [hWV (pr u ρ 0), hWV (pr w ρ 0)] with ω h1 h2
      simp only [h1, h2, hV, nuQ_pr_zero hu hρ, nuQ_pr_zero hw hρ]
    have hF := integral_fcAvg_ae_eq_bind_real hX hρ hw hYc hY (foldedCircle w r)
      (isCompact_ballH (‖w‖ + r)) inter_subset_right (foldedCircle_support hr.le le_rfl)
    filter_upwards [hF, hWV (pr w ρ 0), hWV (pr w r ρ)] with ω h1 h2 h3
    have hint : Integrable (fun u => W (pr u ρ 0) ω) (foldedCircle w r) :=
      RegClosure.integrable_fc ((hWc ω).comp (continuous_pr_fst ρ 0)).continuousOn w hr.le
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ,
      one_smul, measure_univ, one_smul] at h1
    simp only [hV] at h2 h3
    rw [nuQ_pr_zero hw hρ] at h2
    rw [h3, nuQ_pr hw hr hρ.le]
    linarith
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ∫ u, W (pr u (radius k) 0) ω ∂foldedCircle w r =
      W (pr w r (radius k)) ω := ae_all_iff.2 fun k => hpt _ (radius_pos k)
  filter_upwards [hWlim, hall, hWV (pr w r 0)] with ω hlim hk h0
  have havg : ∀ k : ℕ, ∀ u ∈ Hbar, avgReg (X ω) k u = W (pr u (radius k) 0) ω := by
    intro k u hu
    have h := hlim (pr u (radius k) 0)
    simp only [rndD_pr, hV] at h
    have e : ∀ n, nuQ (pr (dyadicRoundC n u) (radius k) 0) =
        foldedCircle (dyadicRoundC n u) (radius k) := fun n =>
      nuQ_pr_zero (CircleCont.dyadicRoundC_mem_Hbar hu n) (radius_pos k)
    simp only [e] at h
    exact h.limUnder_eq
  have hint : ∀ k : ℕ, ∫ u, avgReg (X ω) k u ∂foldedCircle w r = W (pr w r (radius k)) ω := by
    intro k
    rw [← hk k]
    exact integral_congr_ae ((RegClosure.fc_ae_mem_Hbar w r).mono fun u hu => havg k u hu)
  have hcont : Continuous fun ρ : ℝ => W (pr w r ρ) ω :=
    (hWc ω).comp (continuousOn_pr.comp_continuous (by fun_prop : Continuous
      fun ρ : ℝ => (((w, r) : ℂ × ℝ), ρ)) fun _ => hr)
  have htend : Tendsto (fun k => W (pr w r (radius k)) ω) atTop (𝓝 (W (pr w r 0) ω)) :=
    (hcont.tendsto 0).comp (tendsto_nhdsWithin_iff.1 RegClosure.tendsto_radius_nhdsGT).1
  unfold evalReg
  simp_rw [hint]
  rw [htend.limUnder_eq, h0]
  show X ω (nuQ (pr w r 0)) = _
  rw [nuQ_pr_zero hw hr]

/-! ## A3. The normalized field at an arbitrary radius -/

/-- `Z_r(t) = evalReg (Z ω) (fc(t,r))` for the normalized field `Z = zField X R`. -/
def zV (X : Ω → FieldSample) (R r t : ℝ) (ω : Ω) : ℝ :=
  evalReg (zField X R ω) (foldedCircle (t : ℂ) r)

theorem measurable_zV (hX : IsFreeGFFModConstH X P) (R r : ℝ) :
    Measurable (fun p : ℝ × Ω => zV X R r p.1 p.2) := by
  have h1 : Measurable (fun p : ℝ × Ω => (zField X R p.2, p.1)) :=
    ((measurable_zField hX R).comp measurable_snd).prodMk measurable_fst
  exact Measurable.comp (g := fun q : FieldSample × ℝ => evalReg q.1 (foldedCircle (q.2 : ℂ) r))
    (f := fun p : ℝ × Ω => (zField X R p.2, p.1)) (measurable_evalReg_fc_real r) h1

/-- On a regular sample, `Z_r(t) = X_r(t) − X(fc(0,R))` at every circle. -/
theorem zV_eq_of_regular {R : ℝ} {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F)
    (t : ℝ) {r : ℝ} (hr : 0 < r) :
    zV X R r t ω = F ((t : ℂ), r) - X ω (foldedCircle 0 R) := by
  have hZ := hF.addConst' (-X ω (foldedCircle 0 R))
  simp only [zV, zField]
  rw [hZ.evalReg_fc_of_mem (ofReal_mem_Hbar t) hr]
  ring

theorem regular_zField {R : ℝ} {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F) :
    IsRegularWith (zField X R ω) (fun q => F q + -X ω (foldedCircle 0 R)) :=
  hF.addConst' _

theorem ae_zV_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (R t : ℝ) {r : ℝ}
    (hr : 0 < r) : zV X R r t =ᵐ[P] fcPairVal X ((t : ℂ), r, 0, R) := by
  filter_upwards [RegSample.ae_isRegularSample hX,
    ae_evalReg_fc_eq hX (ofReal_mem_Hbar t) hr] with ω hreg h
  obtain ⟨F, hF⟩ := hreg
  rw [zV_eq_of_regular hF t hr, ← hF.evalReg_fc_of_mem (ofReal_mem_Hbar t) hr, h]
  rfl

theorem fcPairCov_incr_self_gen {t ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    fcPairCov ((t : ℂ), ρ, (t : ℂ), r) ((t : ℂ), ρ, (t : ℂ), r) = 2 * log r - 2 * log ρ := by
  have hr : 0 < r := hρ.trans_le hρr
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter hρ hρ, kernelCov_fc_real_sameCenter hρ hr,
    kernelCov_fc_real_sameCenter hr hρ, kernelCov_fc_real_sameCenter hr hr,
    max_eq_right hρr, max_eq_left hρr]
  simp only [max_self]
  ring

theorem hasLaw_zV [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {R t r : ℝ}
    (hr : 0 < r) (htR : |t| + r ≤ R) :
    HasLaw (zV X R r t) (gaussianReal 0 (2 * log R - 2 * log r).toNNReal) P := by
  have hR0 : 0 < R := by linarith [abs_nonneg t]
  have := (hasLaw_fcPairVal hX (good_Z (ofReal_mem_Hbar t) hr hR0)).congr (ae_zV_eq hX R t hr)
  rwa [fcPairCov_Zself hr htR] at this

theorem integral_exp_zV [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {R t r : ℝ}
    (hr : 0 < r) (htR : |t| + r ≤ R) (c : ℝ) :
    ∫ ω, exp (c * zV X R r t ω) ∂P =
      exp ((2 * log R - 2 * log r).toNNReal * c ^ 2 / 2) := by
  have h2 := integral_exp_mul_add_gaussianReal (2 * log R - 2 * log r).toNNReal c 0
  simp only [zero_add] at h2
  rw [← h2]
  exact (hasLaw_zV hX hr htR).integral_comp (f := fun x => exp (c * x)) (by fun_prop)

theorem integrable_exp_zV [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {R t r : ℝ}
    (hr : 0 < r) (htR : |t| + r ≤ R) (c : ℝ) :
    Integrable (fun ω => exp (c * zV X R r t ω)) P := by
  have hi : Integrable (fun ω => exp (0 + c * zV X R r t ω)) P :=
    (hasLaw_zV hX hr htR).integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ c 0)
  simpa only [zero_add] using hi

/-! ## A4. Densities, integrals and joint integrability -/

theorem bdryDens_zField (γ R r t : ℝ) (ω : Ω) :
    bdryDens γ (zField X R ω) r t = r ^ (γ ^ 2 / 4) * exp (γ / 2 * zV X R r t ω) := rfl

theorem measurable_bdryDens_zField (hX : IsFreeGFFModConstH X P) (γ R r : ℝ) :
    Measurable (fun p : Ω × ℝ => bdryDens γ (zField X R p.1) r p.2) := by
  have h : Measurable (fun p : Ω × ℝ => zV X R r p.2 p.1) :=
    Measurable.comp (g := fun p : ℝ × Ω => zV X R r p.1 p.2) (f := Prod.swap)
      (measurable_zV hX R r) measurable_swap
  exact measurable_const.mul ((h.const_mul _).exp)

/-- `∫ g dν_r(Z ω)`. -/
def bA (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (g : ℝ → ℝ) (r : ℝ) (ω : Ω) : ℝ :=
  ∫ t, g t ∂bdryR γ (zField X R ω) r

theorem bA_eq (hX : IsFreeGFFModConstH X P) (γ R : ℝ) {r : ℝ} (hr : 0 < r) {S : Set ℝ}
    (hS : MeasurableSet S) {g : ℝ → ℝ} (hgS : ∀ t ∉ S, g t = 0) (ω : Ω) :
    bA γ X R g r ω = ∫ t in S, g t * bdryDens γ (zField X R ω) r t := by
  have hd : Measurable (fun t => bdryDens γ (zField X R ω) r t) := by
    have h : Measurable (fun t : ℝ => ((ω, t) : Ω × ℝ)) := measurable_const.prodMk measurable_id
    exact Measurable.comp (g := fun p : Ω × ℝ => bdryDens γ (zField X R p.1) r p.2)
      (f := fun t : ℝ => ((ω, t) : Ω × ℝ)) (measurable_bdryDens_zField hX γ R r) h
  rw [bA, bdryR, GoodSample.integral_withDensity_ofReal hd
    (fun t => GoodSample.bdryDens_nonneg γ _ hr t),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
      (f := fun t => bdryDens γ (zField X R ω) r t * g t) (fun t ht => by simp [hgS t ht])]
  exact setIntegral_congr_fun hS fun t _ => mul_comm _ _

theorem integrable_gDens [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {R r : ℝ}
    (hr : 0 < r) {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞)
    (hSR : ∀ t ∈ S, |t| + r ≤ R) (γ : ℝ) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) :
    Integrable (fun p : Ω × ℝ => g p.2 * bdryDens γ (zField X R p.1) r p.2)
      (P.prod (volume.restrict S)) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf.ne
  have hmeas : Measurable (fun p : Ω × ℝ => g p.2 * bdryDens γ (zField X R p.1) r p.2) :=
    (hg.comp measurable_snd).mul (measurable_bdryDens_zField hX γ R r)
  have hrp := rpow_pos_of_pos hr (γ ^ 2 / 4)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' hS]
    refine ae_of_all _ fun t ht => ?_
    simp_rw [bdryDens_zField]
    exact ((integrable_exp_zV hX hr (hSR t ht) (γ / 2)).const_mul _).const_mul (g t)
  · refine Integrable.mono' (integrable_const
      (M * (r ^ (γ ^ 2 / 4) * exp ((2 * log R - 2 * log r).toNNReal * (γ / 2) ^ 2 / 2)))) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
    · rw [ae_restrict_iff' hS]
      refine ae_of_all _ fun t ht => ?_
      have e : ∀ ω, ‖g t * bdryDens γ (zField X R ω) r t‖ =
          |g t| * (r ^ (γ ^ 2 / 4) * exp (γ / 2 * zV X R r t ω)) := by
        intro ω
        rw [Real.norm_eq_abs, abs_mul, bdryDens_zField, abs_of_pos (mul_pos hrp (exp_pos _))]
      simp_rw [e]
      rw [integral_const_mul, integral_const_mul, integral_exp_zV hX hr (hSR t ht),
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hM t) (by positivity)

theorem integrable_bA [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {R r : ℝ}
    (hr : 0 < r) {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞)
    (hSR : ∀ t ∈ S, |t| + r ≤ R) (γ : ℝ) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) (hgS : ∀ t ∉ S, g t = 0) :
    Integrable (bA γ X R g r) P := by
  have e : bA γ X R g r = fun ω => ∫ t in S, g t * bdryDens γ (zField X R ω) r t :=
    funext (bA_eq hX γ R hr hS hgS)
  rw [e]
  exact (integrable_gDens hX hr hS hSf hSR γ hg hM).integral_prod_left

theorem ae_integrableOn_gDens [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {R r : ℝ}
    (hr : 0 < r) {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞)
    (hSR : ∀ t ∈ S, |t| + r ≤ R) (γ : ℝ) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) :
    ∀ᵐ ω ∂P, IntegrableOn (fun t => g t * bdryDens γ (zField X R ω) r t) S :=
  (integrable_gDens hX hr hS hSf hSR γ hg hM).prod_right_ae

/-! ## A5. The two-radius lemma at an offset `c ∈ [1,2]` -/

theorem integral_abs_bA_offset_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R M : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 2 ≤ R) {g : ℝ → ℝ} (hg : Measurable g)
    (hM : ∀ t, |g t| ≤ M) (hgS : ∀ t ∉ S, g t = 0) {ε c : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    ∫ ω, |bA γ X R g (c * ε) ω - bA γ X R g ε ω| ∂P
      ≤ M * √((4 * 2 * (1 + 2 ^ (γ ^ 2 / 2)) *
              exp ((γ - max 0 ((3 * γ - 2) / 4)) ^ 2 * (2 * log R) / 2)) * volume.real S *
              ε ^ (1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2))
        + M * (2 * exp ((γ / 2 + (2 - γ) / 4) ^ 2 * (2 * log R) / 2) * 2 ^ ((2 - γ) ^ 2 / 16)) *
            volume.real S * ε ^ ((2 - γ) ^ 2 / 16) := by
  have hcε : 0 < c * ε := by positivity
  have hεcε : ε ≤ c * ε := by nlinarith
  have hcε2 : c * ε ≤ 2 := by nlinarith
  have hR1 : ∀ t ∈ S, |t| + c * ε ≤ R := fun t ht => by linarith [hSR t ht]
  have hR2 : ∀ t ∈ S, |t| + ε ≤ R := fun t ht => by linarith [hSR t ht]
  have hΔe : ∀ t : ℝ, (fun ω => zV X R ε t ω - zV X R (c * ε) t ω) =ᵐ[P]
      fcPairVal X ((t : ℂ), ε, (t : ℂ), c * ε) := by
    intro t
    filter_upwards [ae_zV_eq hX R t hε, ae_zV_eq hX R t hcε] with ω h1 h2
    rw [h1, h2]; simp only [fcPairVal]; ring
  have hlogc : 0 ≤ 2 * log c := mul_nonneg zero_le_two (log_nonneg hc1)
  have key := trl_bound_radii (P := P) (S := S) (f := g) (Λ := 2) (M := M) hγ hγ2 hε one_le_two
    (r₁ := fun _ => c * ε) (r₂ := fun _ => ε) measurable_const
    (fun t _ => ⟨le_rfl, hεcε, by nlinarith⟩) hS hSf hg hM
    (U := zV X R (c * ε)) (Δ := fun t ω => zV X R ε t ω - zV X R (c * ε) t ω)
    (v := fun _ => (2 * log R - 2 * log (c * ε)).toNNReal)
    (w := fun _ => (2 * log c).toNNReal) (K := 2 * log R)
    (measurable_zV hX R _) ((measurable_zV hX R ε).sub (measurable_zV hX R _)) measurable_const
    (fun t ht => hasLaw_zV hX hcε (hR1 t ht))
    (fun t ht => by
      have hR0 : 0 < R := by linarith [hSR t ht, abs_nonneg t]
      have := (hasLaw_fcPairVal hX (good_real (s := t) (t := t) hε hcε)).congr (hΔe t)
      rwa [fcPairCov_incr_self_gen hε hεcε, log_mul (by positivity) hε.ne',
        show 2 * (log c + log ε) - 2 * log ε = 2 * log c by ring] at this)
    (fun t ht => by
      have hlogR : 0 ≤ log R := log_nonneg (by linarith [hSR t ht, abs_nonneg t])
      have hlogr : log (c * ε) ≤ log R := log_le_log hcε (by linarith [hR1 t ht, abs_nonneg t])
      show ((2 * log R - 2 * log (c * ε)).toNNReal : ℝ) ≤ 2 * log (1 / (c * ε)) + 2 * log R
      rw [Real.coe_toNNReal _ (by linarith), one_div, log_inv]
      linarith)
    (fun t _ => by
      show ((2 * log c).toNNReal : ℝ) = 2 * log (c * ε / ε)
      rw [Real.coe_toNNReal _ hlogc, mul_div_cancel_right₀ _ hε.ne'])
    (fun t ht => by
      have hR0 : 0 < R := by linarith [hSR t ht, abs_nonneg t]
      have hI := indepFun_fcPair hX
        (fun _ : Unit => (⟨((t : ℂ), ε, (t : ℂ), c * ε), good_real hε hcε⟩ :
          {p : FcIdx // p.Good}))
        (fun _ : Unit => (⟨((t : ℂ), c * ε, 0, R), good_Z (ofReal_mem_Hbar t) hcε hR0⟩ :
          {p : FcIdx // p.Good}))
        (fun _ _ => fcPairCov_incr_Zsame hε hεcε (hR1 t ht))
      have hI2 := hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
      exact hI2.congr (hΔe t).symm (ae_zV_eq hX R t hcε).symm)
    (fun t ht u hu htu => by
      have hI := indepFun_incr_bullet1 hX (t := t) (u := u) (ε := ε) (ε' := c * ε)
        (r := c * ε) (δ := ε) (δ' := c * ε) (R := R) hε hεcε hcε hε hεcε (hR1 t ht) (hR1 u hu)
        (by rw [max_self]; nlinarith)
      have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
        (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
      have hI2 := hI.comp (measurable_pi_apply ()) hφ
      refine hI2.congr (hΔe t).symm ?_
      filter_upwards [ae_zV_eq hX R t hcε, ae_zV_eq hX R u hcε, hΔe u] with ω h1 h2 h3
      simp [h1, h2]
      rw [← h2]
      exact h3.symm)
  refine le_of_eq_of_le (integral_congr_ae ?_) key
  filter_upwards [ae_integrableOn_gDens hX hcε hS hSf hR1 γ hg hM,
    ae_integrableOn_gDens hX hε hS hSf hR2 γ hg hM] with ω h1 h2
  rw [bA_eq hX γ R hcε hS hgS, bA_eq hX γ R hε hS hgS, ← integral_sub h1 h2]
  refine congrArg abs (setIntegral_congr_fun hS fun t _ => ?_)
  simp only [bdryDens_zField, add_sub_cancel]
  ring

theorem radius_rpow (k : ℕ) (e : ℝ) : radius k ^ e = exp (-e * (k * log 2)) := by
  rw [rpow_def_of_pos (radius_pos k)]
  have h : log (radius k) = -(k * log 2) := by
    have h := log_one_div_radius k
    rw [one_div, log_inv] at h
    linarith
  rw [h]
  congr 1
  ring

/-- Rate form of the offset two-radius lemma, uniform in `c ∈ [1,2]`. -/
theorem exists_offset_rate [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R M : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 2 ≤ R) {g : ℝ → ℝ} (hg : Measurable g)
    (hM : ∀ t, |g t| ≤ M) (hgS : ∀ t ∉ S, g t = 0) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, ∀ c ∈ Icc (1 : ℝ) 2,
      ∫ ω, |bA γ X R g (c * radius k) ω - bA γ X R g (radius k) ω| ∂P
        ≤ C * exp (-bdryRate γ * (k * log 2)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set θ := max 0 ((3 * γ - 2) / 4) with hθ
  set e₁ := 1 - γ ^ 2 / 2 + θ ^ 2 with he₁
  set β := bdryRate γ with hβ
  have hβ1 : β ≤ e₁ / 2 := min_le_left _ _
  have hβ2 : β ≤ (2 - γ) ^ 2 / 16 := min_le_right _ _
  set A := 4 * 2 * (1 + 2 ^ (γ ^ 2 / 2)) * exp ((γ - θ) ^ 2 * (2 * log R) / 2) * volume.real S
    with hA
  set B := M * (2 * exp ((γ / 2 + (2 - γ) / 4) ^ 2 * (2 * log R) / 2) *
    2 ^ ((2 - γ) ^ 2 / 16)) * volume.real S with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine ⟨M * √A + B, by positivity, fun k c hc => ?_⟩
  refine (integral_abs_bA_offset_le hX hγ hγ2 hS hSf hSR hg hM hgS (radius_pos k)
    (radius_le_one k) hc.1 hc.2).trans ?_
  rw [radius_rpow, radius_rpow]
  set L := (k : ℝ) * log 2 with hL
  have hL0 : 0 ≤ L := mul_nonneg (Nat.cast_nonneg k) (log_nonneg one_le_two)
  have h1 : exp (-e₁ * L) ≤ exp (-β * L) ^ 2 := by
    rw [← exp_nat_mul]; apply exp_le_exp.2; push_cast; nlinarith
  have h2 : exp (-((2 - γ) ^ 2 / 16) * L) ≤ exp (-β * L) := exp_le_exp.2 (by nlinarith)
  have ht1 : √(A * exp (-e₁ * L)) ≤ √A * exp (-β * L) := by
    rw [← Real.sqrt_sq (exp_pos (-β * L)).le, ← Real.sqrt_mul hA0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h1 hA0)
  calc M * √(A * exp (-e₁ * L)) + B * exp (-((2 - γ) ^ 2 / 16) * L)
      ≤ M * (√A * exp (-β * L)) + B * exp (-β * L) :=
        add_le_add (mul_le_mul_of_nonneg_left ht1 hM0) (mul_le_mul_of_nonneg_left h2 hB0)
    _ = (M * √A + B) * exp (-β * L) := by ring

/-- **Grid part of M4-B4**: for every offset `c ∈ [1,2]`,
`E|∫ g dν_{c 2^{-k}}(Z) − ∫ g dν(Z)| ≤ C e^{-β k log 2}` (as a lower integral). -/
theorem exists_grid_rate [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 2 ≤ R) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgS : ∀ t ∉ S, g t = 0) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, ∀ c ∈ Icc (1 : ℝ) 2,
      ∫⁻ ω, ENNReal.ofReal |bA γ X R g (c * radius k) ω -
          ∫ t, g t ∂qBoundaryMeasure γ (zField X R ω)| ∂P
        ≤ ENNReal.ofReal (C * exp (-bdryRate γ * (k * log 2))) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hM' : ∀ t, |g t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
  have hSR1 : ∀ t ∈ S, |t| + 1 ≤ R := fun t ht => by linarith [hSR t ht]
  obtain ⟨C₁, hC₁, h₁⟩ := exists_offset_rate hX hγ hγ2 hS hSf hSR hg.measurable hM' hgS
  obtain ⟨C₂, hC₂, h₂⟩ :=
    integral_abs_bdryApprox_sub_qBoundaryMeasure_le hX hγ hγ2 hS hSf hSR1 hg hgc hgS
  refine ⟨C₁ + C₂, by positivity, fun k c hc => ?_⟩
  have hε := radius_pos k
  have hcε : 0 < c * radius k := mul_pos (by linarith [hc.1]) hε
  have hr1 := radius_le_one k
  have hcε2 : c * radius k ≤ 2 := by nlinarith [hc.2]
  have hI1 : Integrable (fun ω => bA γ X R g (c * radius k) ω - bA γ X R g (radius k) ω) P :=
    (integrable_bA hX hcε hS hSf (fun t ht => by linarith [hSR t ht]) γ hg.measurable hM'
      hgS).sub (integrable_bA hX hε hS hSf (fun t ht => by linarith [hSR t ht]) γ
      hg.measurable hM' hgS)
  obtain ⟨hI2, hB2⟩ := h₂ k
  have hae : ∀ᵐ ω ∂P, bA γ X R g (radius k) ω = ∫ t, g t ∂bdryApprox γ (zField X R ω) k := by
    filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg
    obtain ⟨F, hF⟩ := hreg
    rw [bA, ← GoodSample.bdryR_radius γ (regular_zField (R := R) hF) k, one_mul]
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |bA γ X R g (c * radius k) ω -
      ∫ t, g t ∂qBoundaryMeasure γ (zField X R ω)| ≤
      ENNReal.ofReal |bA γ X R g (c * radius k) ω - bA γ X R g (radius k) ω| +
      ENNReal.ofReal |∫ t, g t ∂bdryApprox γ (zField X R ω) k -
        ∫ t, g t ∂qBoundaryMeasure γ (zField X R ω)| := by
    filter_upwards [hae] with ω h
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← h]
    exact abs_sub_le _ _ _
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_add_left' hI1.abs.aemeasurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hI1.abs (ae_of_all _ fun _ => abs_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hI2.abs (ae_of_all _ fun _ => abs_nonneg _),
    ← ENNReal.ofReal_add (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := h₁ k c hc
  nlinarith

end AllOffsets
end QuantumZipper
