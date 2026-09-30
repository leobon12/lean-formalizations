import QuantumZipper.Proofs.LQG.AllOffsets
import QuantumZipper.Proofs.LQG.AreaExistenceAS

/-!
# Area analogue of M4-B4, part 1: interior circles at arbitrary radii, offset TRL

Blueprint `M4_BLUEPRINT.md`, node M4-A1 (item 5: all offsets simultaneously), inputs.

* `zVc X R r z ω = evalReg (Z ω) (fc(z,r))` for the normalized field, jointly measurable in
  `(z, ω)`, almost surely equal to the raw coordinate at each fixed circle.
* `aB γ X R f r ω = ∫ f dμ_r(Z ω)` and the joint integrability of `f · areaDens`.
* `integral_abs_aB_offset_le`, `exists_offset_rateA`: the planar two-radius lemma for the
  constant profiles `c ε`, `ε` (`c ∈ [1,2]`), in rate form uniform in `c`.
* `exists_grid_rateA`: `E|∫ f dμ_{c 2^{-k}}(Z) − ∫ f dμ(Z)| ≤ C e^{-β k log 2}` for `k ≥ k₀`,
  uniformly in `c ∈ [1,2]` (`β = areaRate γ`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaOffsets

open BdryExist GaussTK TwoRadius TwoRadiusC AreaExist AllOffsets

/-! ## Joint measurability with a complex centre -/

theorem measurable_evalReg_fc (r : ℝ) :
    Measurable (fun p : FieldSample × ℂ => evalReg p.1 (foldedCircle p.2 r)) := by
  have key : ∀ k : ℕ, StronglyMeasurable (fun p : FieldSample × ℂ =>
      ∫ w, avgReg p.1 k w ∂foldedCircle p.2 r) := by
    intro k
    have hc : Measurable (fun s : ℂ × ℝ => circleMap s.1 r s.2) := by
      have : Continuous (fun s : ℂ × ℝ => circleMap s.1 r s.2) := by
        simp only [circleMap]; fun_prop
      exact this.measurable
    have hp : Measurable (fun q : (FieldSample × ℂ) × ℝ => (q.1.2, q.2)) :=
      measurable_fst.snd.prodMk measurable_snd
    have h2 : Measurable (fun q : (FieldSample × ℂ) × ℝ => foldH (circleMap q.1.2 r q.2)) :=
      measurable_foldH.comp (Measurable.comp (g := fun s : ℂ × ℝ => circleMap s.1 r s.2)
        (f := fun q : (FieldSample × ℂ) × ℝ => (q.1.2, q.2)) hc hp)
    have hjm : Measurable (fun q : (FieldSample × ℂ) × ℝ =>
        avgReg q.1.1 k (foldH (circleMap q.1.2 r q.2))) :=
      Measurable.comp (g := fun p : FieldSample × ℂ => avgReg p.1 k p.2)
        (f := fun q : (FieldSample × ℂ) × ℝ => (q.1.1, foldH (circleMap q.1.2 r q.2)))
        (measurable_avgReg k) (measurable_fst.fst.prodMk h2)
    have e : (fun p : FieldSample × ℂ => ∫ w, avgReg p.1 k w ∂foldedCircle p.2 r) =
        fun p => (ENNReal.ofReal (2 * π))⁻¹.toReal *
          ∫ θ, avgReg p.1 k (foldH (circleMap p.2 r θ))
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

/-- `Z_r(z) = evalReg (Z ω) (fc(z,r))`. -/
def zVc (X : Ω → FieldSample) (R r : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  evalReg (zField X R ω) (foldedCircle z r)

theorem measurable_zVc (hX : IsFreeGFFModConstH X P) (R r : ℝ) :
    Measurable (fun p : ℂ × Ω => zVc X R r p.1 p.2) := by
  have h1 : Measurable (fun p : ℂ × Ω => (zField X R p.2, p.1)) :=
    ((measurable_zField hX R).comp measurable_snd).prodMk measurable_fst
  exact Measurable.comp (g := fun q : FieldSample × ℂ => evalReg q.1 (foldedCircle q.2 r))
    (f := fun p : ℂ × Ω => (zField X R p.2, p.1)) (measurable_evalReg_fc r) h1

theorem measurable_zVc_swap (hX : IsFreeGFFModConstH X P) (R r : ℝ) :
    Measurable (fun p : Ω × ℂ => zVc X R r p.2 p.1) :=
  Measurable.comp (g := fun p : ℂ × Ω => zVc X R r p.1 p.2) (f := Prod.swap)
    (measurable_zVc hX R r) measurable_swap

theorem zVc_eq_of_regular {R : ℝ} {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F)
    {z : ℂ} (hz : z ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    zVc X R r z ω = F (z, r) - X ω (foldedCircle 0 R) := by
  have hZ := hF.addConst' (-X ω (foldedCircle 0 R))
  simp only [zVc, zField]
  rw [hZ.evalReg_fc_of_mem hz hr]
  ring

theorem ae_zVc_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (R : ℝ) {z : ℂ}
    (hz : z ∈ Hbar) {r : ℝ} (hr : 0 < r) : zVc X R r z =ᵐ[P] fcPairVal X (z, r, 0, R) := by
  filter_upwards [RegSample.ae_isRegularSample hX, ae_evalReg_fc_eq hX hz hr] with ω hreg h
  obtain ⟨F, hF⟩ := hreg
  rw [zVc_eq_of_regular hF hz hr, ← hF.evalReg_fc_of_mem hz hr, h]
  rfl

theorem fcPairCov_incr_self_int_gen {z : ℂ} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hrz : r ≤ z.im) : fcPairCov (z, ρ, z, r) (z, ρ, z, r) = log r - log ρ := by
  have hr : 0 < r := hρ.trans_le hρr
  have hρz : ρ ≤ z.im := hρr.trans hrz
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_sameCenter hρ hρ hρz hρz,
    kernelCov_fc_interior_sameCenter hρ hr hρz hrz,
    kernelCov_fc_interior_sameCenter hr hρ hrz hρz,
    kernelCov_fc_interior_sameCenter hr hr hrz hrz]
  simp only [max_eq_right hρr, max_eq_left hρr, max_self]
  ring

theorem hasLaw_zVc [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {R r : ℝ} {z : ℂ}
    (hr : 0 < r) (hrz : r ≤ z.im) (hR : ‖z‖ + r ≤ R) :
    HasLaw (zVc X R r z) (gaussianReal 0 (fcPairCov (z, r, 0, R) (z, r, 0, R)).toNNReal) P := by
  have hR0 : 0 < R := by linarith [norm_nonneg z]
  have hzH := mem_Hbar_of_le_im hr hrz
  exact (hasLaw_fcPairVal' hX (good_Z hzH hr hR0)).congr (ae_zVc_eq hX R hzH hr)

theorem var_zVc_le {R r d : ℝ} {z : ℂ} (hr : 0 < r) (hr1 : r ≤ 1) (hrz : r ≤ z.im)
    (hR : ‖z‖ + r ≤ R) (hd : 0 < d) (hd1 : 2 * d ≤ 1) (hdz : d ≤ z.im) (hR1 : 1 ≤ R) :
    ((fcPairCov (z, r, 0, R) (z, r, 0, R)).toNNReal : ℝ) ≤
      2 * (1 / 2 * log (1 / r)) + (2 * log R - log (2 * d)) := by
  have hlogR : 0 ≤ log R := log_nonneg hR1
  have hlogr : log r ≤ 0 := log_nonpos hr.le hr1
  have hlogd : log (2 * d) ≤ 0 := log_nonpos (by positivity) hd1
  have hc : log (2 * d) ≤ log ‖z - conj z‖ :=
    log_le_log (by positivity) (by linarith [two_im_le_norm_sub_conj z])
  rw [Real.coe_toNNReal', fcPairCov_Zself_int hr hrz hR,
    show log (1 / r) = -log r by rw [one_div, log_inv]]
  exact max_le (by linarith) (by linarith)

/-! ## Densities and integrals -/

theorem areaDens_zField (γ R r : ℝ) (z : ℂ) (ω : Ω) :
    areaDens γ (zField X R ω) r z = r ^ (γ ^ 2 / 2) * exp (γ * zVc X R r z ω) := rfl

theorem measurable_areaDens_zField (hX : IsFreeGFFModConstH X P) (γ R r : ℝ) :
    Measurable (fun p : Ω × ℂ => areaDens γ (zField X R p.1) r p.2) := by
  have h := measurable_zVc_swap hX R r
  exact measurable_const.mul ((h.const_mul _).exp)

/-- `∫ f dμ_r(Z ω)`. -/
def aB (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (f : ℂ → ℝ) (r : ℝ) (ω : Ω) : ℝ :=
  ∫ z, f z ∂areaR γ (zField X R ω) r

theorem aB_eq_integral (hX : IsFreeGFFModConstH X P) (γ R : ℝ) {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℝ) (ω : Ω) : aB γ X R f r ω = ∫ z in H, areaDens γ (zField X R ω) r z * f z := by
  have hd : Measurable (fun z => areaDens γ (zField X R ω) r z) := by
    have h : Measurable (fun z : ℂ => ((ω, z) : Ω × ℂ)) := measurable_const.prodMk measurable_id
    exact Measurable.comp (g := fun p : Ω × ℂ => areaDens γ (zField X R p.1) r p.2)
      (f := fun z : ℂ => ((ω, z) : Ω × ℂ)) (measurable_areaDens_zField hX γ R r) h
  rw [aB, areaR, GoodSample.integral_withDensity_ofReal hd
    (fun z => GoodSample.areaDens_nonneg γ _ hr z)]

theorem aB_eq (hX : IsFreeGFFModConstH X P) (γ R : ℝ) {r : ℝ} (hr : 0 < r) {S : Set ℂ}
    (hS : MeasurableSet S) (hSH : S ⊆ H) {f : ℂ → ℝ} (hfS : ∀ z ∉ S, f z = 0) (ω : Ω) :
    aB γ X R f r ω = ∫ z in S, f z * areaDens γ (zField X R ω) r z := by
  rw [aB_eq_integral hX γ R hr f ω,
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := H) fun z hz => by
      rw [hfS z (fun h => hz (hSH h)), mul_zero],
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) fun z hz => by
      rw [hfS z hz, mul_zero]]
  exact setIntegral_congr_fun hS fun z _ => mul_comm _ _

/-- Standing hypotheses on the region: `S ⊆ ℍ` measurable of finite measure, `Im z ≥ d`,
`‖z‖ + 1 ≤ R`, `2d ≤ 1`. -/
structure Region (S : Set ℂ) (R d : ℝ) : Prop where
  meas : MeasurableSet S
  fin : volume S < ∞
  subH : S ⊆ H
  d_pos : 0 < d
  d_le : 2 * d ≤ 1
  normR : ∀ z ∈ S, ‖z‖ + 1 ≤ R
  im_ge : ∀ z ∈ S, d ≤ z.im

theorem Region.R_ge {S : Set ℂ} {R d : ℝ} (h : Region S R d) {z : ℂ} (hz : z ∈ S) : 1 ≤ R := by
  linarith [h.normR z hz, norm_nonneg z]

theorem integrable_gDensA [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {S : Set ℂ} {R d : ℝ} (hreg : Region S R d) {r : ℝ} (hr : 0 < r) (hrd : r ≤ d)
    (γ : ℝ) {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) :
    Integrable (fun p : Ω × ℂ => f p.2 * areaDens γ (zField X R p.1) r p.2)
      (P.prod (volume.restrict S)) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hreg.fin.ne
  have hmeas : Measurable (fun p : Ω × ℂ => f p.2 * areaDens γ (zField X R p.1) r p.2) :=
    (hf.comp measurable_snd).mul (measurable_areaDens_zField hX γ R r)
  have hrp := rpow_pos_of_pos hr (γ ^ 2 / 2)
  have hr1 : r ≤ 1 := by linarith [hreg.d_le, hreg.d_pos]
  set Vb := 2 * (1 / 2 * log (1 / r)) + (2 * log R - log (2 * d)) with hVb
  have hrz : ∀ z ∈ S, r ≤ z.im := fun z hz => hrd.trans (hreg.im_ge z hz)
  have hRz : ∀ z ∈ S, ‖z‖ + r ≤ R := fun z hz => by linarith [hreg.normR z hz]
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' hreg.meas]
    refine ae_of_all _ fun z hz => ?_
    have hi : Integrable (fun ω => exp (0 + γ * zVc X R r z ω)) P :=
      (hasLaw_zVc hX hr (hrz z hz) (hRz z hz)).integrable_fun_comp
        (integrable_exp_mul_add_gaussianReal _ γ 0)
    simp only [zero_add] at hi
    simp_rw [areaDens_zField]
    exact (hi.const_mul _).const_mul (f z)
  · refine Integrable.mono' (integrable_const
      (M * (r ^ (γ ^ 2 / 2) * exp (Vb * γ ^ 2 / 2)))) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
    · rw [ae_restrict_iff' hreg.meas]
      refine ae_of_all _ fun z hz => ?_
      have e : ∀ ω, ‖f z * areaDens γ (zField X R ω) r z‖ =
          |f z| * (r ^ (γ ^ 2 / 2) * exp (γ * zVc X R r z ω)) := by
        intro ω
        rw [Real.norm_eq_abs, abs_mul, areaDens_zField, abs_of_pos (mul_pos hrp (exp_pos _))]
      simp_rw [e]
      have h2 := integral_exp_mul_add_gaussianReal
        (fcPairCov (z, r, 0, R) (z, r, 0, R)).toNNReal γ 0
      simp only [zero_add] at h2
      have hE : ∫ ω, exp (γ * zVc X R r z ω) ∂P =
          exp ((fcPairCov (z, r, 0, R) (z, r, 0, R)).toNNReal * γ ^ 2 / 2) := by
        rw [← h2]
        exact (hasLaw_zVc hX hr (hrz z hz) (hRz z hz)).integral_comp
          (f := fun x => exp (γ * x)) (by fun_prop)
      rw [integral_const_mul, integral_const_mul, hE, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      have hv := var_zVc_le hr hr1 (hrz z hz) (hRz z hz) hreg.d_pos hreg.d_le
        (hreg.im_ge z hz) (hreg.R_ge hz)
      have hv' : ((fcPairCov (z, r, 0, R) (z, r, 0, R)).toNNReal : ℝ) * γ ^ 2 / 2 ≤
          Vb * γ ^ 2 / 2 := by
        have hg2 : 0 ≤ γ ^ 2 := sq_nonneg γ
        nlinarith
      exact mul_le_mul (hM z) (mul_le_mul_of_nonneg_left (exp_le_exp.2 hv') hrp.le)
        (by positivity) ((abs_nonneg _).trans (hM z))

theorem integrable_aB [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {S : Set ℂ} {R d : ℝ} (hreg : Region S R d) {r : ℝ} (hr : 0 < r) (hrd : r ≤ d)
    (γ : ℝ) {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M)
    (hfS : ∀ z ∉ S, f z = 0) : Integrable (aB γ X R f r) P := by
  have e : aB γ X R f r = fun ω => ∫ z in S, f z * areaDens γ (zField X R ω) r z :=
    funext (aB_eq hX γ R hr hreg.meas hreg.subH hfS)
  rw [e]
  exact (integrable_gDensA hX hreg hr hrd γ hf hM).integral_prod_left

/-! ## The planar two-radius lemma at an offset -/

theorem integral_abs_aB_offset_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : Set ℂ} {R d M : ℝ} (hreg : Region S R d)
    {f : ℂ → ℝ} (hf : Measurable f) (hM : ∀ z, |f z| ≤ M) (hfS : ∀ z ∉ S, f z = 0)
    {ε c : ℝ} (hε : 0 < ε) (h2ε : 2 * ε ≤ d) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    ∫ ω, |aB γ X R f (c * ε) ω - aB γ X R f ε ω| ∂P
      ≤ √(M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
            (exp ((2 * γ - max 0 ((3 * γ - 2) / 2)) ^ 2 * (2 * log R - log (2 * d)) / 2) *
            exp ((2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2) *
              (1 / 2 * log (1 / (c * ε)))))) *
            (π * (4 * ε) ^ 2 * volume.real S))
        + M * (2 * (exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * (2 * log R - log (2 * d)) / 2) *
            exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * log (1 / (c * ε)))))) * volume.real S := by
  have hcε : 0 < c * ε := by positivity
  have hεcε : ε ≤ c * ε := by nlinarith
  have hcεd : c * ε ≤ d := by nlinarith
  have hcε1 : c * ε ≤ 1 := by linarith [hreg.d_le]
  have hrz : ∀ z ∈ S, c * ε ≤ z.im := fun z hz => hcεd.trans (hreg.im_ge z hz)
  have hzH : ∀ z ∈ S, z ∈ Hbar := fun z hz => mem_Hbar_of_le_im hcε (hrz z hz)
  have hR : ∀ z ∈ S, ‖z‖ + c * ε ≤ R := fun z hz => by linarith [hreg.normR z hz]
  have hR0 : ∀ z ∈ S, 0 < R := fun z hz => by linarith [hreg.R_ge hz]
  have hΔe : ∀ z ∈ S, (fun ω => zVc X R ε z ω - zVc X R (c * ε) z ω) =ᵐ[P]
      fcPairVal X (z, ε, z, c * ε) := by
    intro z hz
    filter_upwards [ae_zVc_eq hX R (hzH z hz) hε, ae_zVc_eq hX R (hzH z hz) hcε] with ω h1 h2
    rw [h1, h2]; simp only [fcPairVal]; ring
  have hlogc : 0 ≤ log c := log_nonneg hc1
  set Lc := 1 / 2 * log (1 / (c * ε)) with hLc
  have hH : TRLHypC P S (4 * ε) (2 * log R - log (2 * d)) (log 2) (fun _ => Lc)
      (fun z => (fcPairCov (z, c * ε, 0, R) (z, c * ε, 0, R)).toNNReal)
      (fun _ => (log c).toNNReal) (zVc X R (c * ε))
      (fun z ω => zVc X R ε z ω - zVc X R (c * ε) z ω) :=
    { measU := measurable_zVc hX R _
      measΔ := (measurable_zVc hX R ε).sub (measurable_zVc hX R _)
      measL := measurable_const
      measw := measurable_const
      lawU := fun z hz => hasLaw_zVc hX hcε (hrz z hz) (hR z hz)
      lawΔ := fun z hz => by
        have := (hasLaw_fcPairVal' hX (p := (z, ε, z, c * ε))
          ⟨hzH z hz, hε, hzH z hz, hcε⟩).congr (hΔe z hz)
        rwa [fcPairCov_incr_self_int_gen hε hεcε (hrz z hz), log_mul (by positivity) hε.ne',
          show log c + log ε - log ε = log c by ring] at this
      varU := fun z hz => var_zVc_le hcε hcε1 (hrz z hz) (hR z hz) hreg.d_pos hreg.d_le
        (hreg.im_ge z hz) (hreg.R_ge hz)
      varΔ := fun z _ => by
        rw [Real.coe_toNNReal _ hlogc]
        exact log_le_log (by linarith) hc2
      indep := fun z hz => by
        have hI := indepFun_fcPair hX
          (fun _ : Unit => (⟨(z, ε, z, c * ε), ⟨hzH z hz, hε, hzH z hz, hcε⟩⟩ :
            {p : FcIdx // p.Good}))
          (fun _ : Unit => (⟨(z, c * ε, 0, R), good_Z (hzH z hz) hcε (hR0 z hz)⟩ :
            {p : FcIdx // p.Good}))
          (fun _ _ => fcPairCov_incr_Zsame_int hε hεcε (hrz z hz) (hR z hz))
        have hI2 := hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
        exact hI2.congr (hΔe z hz).symm (ae_zVc_eq hX R (hzH z hz) hcε).symm
      decor := fun z hz u hu hzu => by
        have hI := indepFun_incr_bullet1_int hX (z := z) (u := u) (ε := ε) (ε' := c * ε)
          (r := c * ε) (δ := ε) (δ' := c * ε) (R := R) hε hεcε (hrz z hz) hcε (hrz u hu) hε
          hεcε (hrz u hu) (hR z hz) (hR u hu) (by rw [max_self]; nlinarith)
        have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
          (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk
            (measurable_pi_apply 2))
        have hI2 := hI.comp (measurable_pi_apply ()) hφ
        refine hI2.congr (hΔe z hz).symm ?_
        filter_upwards [ae_zVc_eq hX R (hzH z hz) hcε, ae_zVc_eq hX R (hzH u hu) hcε,
          hΔe u hu] with ω h1 h2 h3
        simp [h1, h2]
        rw [← h2]
        exact h3.symm }
  have hb := trlC_bound_area hγ hγ2 (δ := 4 * ε) (by positivity) hreg.meas hreg.fin hf hM hH
  refine le_trans (le_of_eq (integral_congr_ae ?_)) hb
  filter_upwards [(integrable_gDensA hX hreg hcε hcεd γ hf hM).prod_right_ae,
    (integrable_gDensA hX hreg hε (by linarith) γ hf hM).prod_right_ae] with ω h1 h2
  rw [aB_eq hX γ R hcε hreg.meas hreg.subH hfS, aB_eq hX γ R hε hreg.meas hreg.subH hfS,
    ← integral_sub h1 h2]
  refine congrArg abs (setIntegral_congr_fun hreg.meas fun z _ => ?_)
  set A := zVc X R (c * ε) z ω with hA
  set B := zVc X R ε z ω with hB
  have e1 : (c * ε) ^ (γ ^ 2 / 2) * exp (γ * A)
      = exp (-((2 * γ) ^ 2 / 4) * Lc + 2 * γ / 2 * A) := by
    rw [rpow_def_of_pos hcε, ← exp_add, hLc,
      show log (1 / (c * ε)) = -log (c * ε) by rw [one_div, log_inv]]
    congr 1; ring
  have e2 : ε ^ (γ ^ 2 / 2) * exp (γ * B)
      = exp (-((2 * γ) ^ 2 / 4) * Lc + 2 * γ / 2 * A) *
        exp (-((2 * γ) ^ 2 / 8 * log c) + 2 * γ / 2 * (B - A)) := by
    rw [rpow_def_of_pos hε, ← exp_add, ← exp_add, hLc,
      show log (1 / (c * ε)) = -log (c * ε) by rw [one_div, log_inv],
      log_mul (by positivity) hε.ne']
    congr 1; ring
  simp only [areaDens_zField, dC, tiltY, ← hA, ← hB]
  rw [Real.coe_toNNReal _ hlogc, e1, e2]
  ring

/-- Rate form of the planar offset lemma, uniform in `c ∈ [1,2]` and `2 · 2^{-k} ≤ d`. -/
theorem exists_offset_rateA [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : Set ℂ} {R d M : ℝ} (hreg : Region S R d)
    {f : ℂ → ℝ} (hf : Measurable f) (hM : ∀ z, |f z| ≤ M) (hfS : ∀ z ∉ S, f z = 0) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, 2 * radius k ≤ d → ∀ c ∈ Icc (1 : ℝ) 2,
      ∫ ω, |aB γ X R f (c * radius k) ω - aB γ X R f (radius k) ω| ∂P
        ≤ C * exp (-areaRate γ * (k * log 2)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set θ := max 0 ((3 * γ - 2) / 2) with hθ
  set E1 := 2 * γ ^ 2 - θ ^ 2 with hE1
  have hE10 : 0 ≤ E1 := (trlC_area_exponent_identities hγ hγ2).2.1
  set β := areaRate γ with hβ
  have hβ1 : β ≤ (2 - γ ^ 2 + θ ^ 2 / 2) / 2 := min_le_left _ _
  have hβ2 : β ≤ (2 - γ) ^ 2 / 8 := min_le_right _ _
  set K := 2 * log R - log (2 * d) with hK
  set A := M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
      exp ((2 * γ - θ) ^ 2 * K / 2)) * (π * 16 * volume.real S) with hA
  set B := M * (2 * exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2)) * volume.real S *
      exp ((2 - γ) ^ 2 / 8 * log 2) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine ⟨√A + B, by positivity, fun k hk c hc => ?_⟩
  have hε := radius_pos k
  refine (integral_abs_aB_offset_le hX hγ hγ2 hreg hf hM hfS hε hk hc.1 hc.2).trans ?_
  set L := (k : ℝ) * log 2 with hL
  have hL0 : 0 ≤ L := mul_nonneg (Nat.cast_nonneg k) (log_nonneg one_le_two)
  have hrad : radius k = exp (-L) := by
    have h := log_one_div_radius k
    rw [one_div, log_inv] at h
    rw [← exp_log hε]; congr 1; linarith
  have hlc0 : 0 ≤ log c := log_nonneg hc.1
  have hlc2 : log c ≤ log 2 := log_le_log (by linarith [hc.1]) hc.2
  have hLc : 1 / 2 * log (1 / (c * radius k)) = 1 / 2 * (L - log c) := by
    rw [log_div one_ne_zero (mul_pos (by linarith [hc.1]) hε).ne', log_one, log_mul (by linarith [hc.1]) hε.ne',
      hrad, log_exp]; ring
  rw [hLc]
  have h1 : M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
      (exp ((2 * γ - θ) ^ 2 * K / 2) * exp (E1 * (1 / 2 * (L - log c))))) *
      (π * (4 * radius k) ^ 2 * volume.real S) ≤ A * exp (-β * L) ^ 2 := by
    have hx : exp (E1 * (1 / 2 * (L - log c))) * radius k ^ 2 ≤ exp (-β * L) ^ 2 := by
      rw [hrad, ← exp_nat_mul, ← exp_nat_mul, ← exp_add]
      apply exp_le_exp.2; push_cast; nlinarith
    calc _ = A * (exp (E1 * (1 / 2 * (L - log c))) * radius k ^ 2) := by rw [hA]; ring
      _ ≤ A * exp (-β * L) ^ 2 := mul_le_mul_of_nonneg_left hx hA0
  have h2 : M * (2 * (exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2) *
      exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * (L - log c))))) * volume.real S ≤
      B * exp (-β * L) := by
    have hx : exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * (L - log c))) ≤
        exp ((2 - γ) ^ 2 / 8 * log 2) * exp (-β * L) := by
      rw [← exp_add]; apply exp_le_exp.2; nlinarith [sq_nonneg (2 - γ)]
    calc _ = M * (2 * exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2)) * volume.real S *
          exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * (L - log c))) := by ring
      _ ≤ M * (2 * exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * K / 2)) * volume.real S *
          (exp ((2 - γ) ^ 2 / 8 * log 2) * exp (-β * L)) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = B * exp (-β * L) := by rw [hB]; ring
  have ht1 : √(M ^ 2 * ((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
      (exp ((2 * γ - θ) ^ 2 * K / 2) * exp (E1 * (1 / 2 * (L - log c))))) *
      (π * (4 * radius k) ^ 2 * volume.real S)) ≤ √A * exp (-β * L) := by
    rw [← Real.sqrt_sq (exp_pos (-β * L)).le, ← Real.sqrt_mul hA0]
    exact Real.sqrt_le_sqrt h1
  calc _ ≤ √A * exp (-β * L) + B * exp (-β * L) := add_le_add ht1 h2
    _ = (√A + B) * exp (-β * L) := by ring

/-! ## Grid part -/

/-- `L(ω) = ∫ f dμ(Z ω)`. -/
def LfA (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (f : ℂ → ℝ) (ω : Ω) : ℝ :=
  ∫ z, f z ∂qAreaMeasure γ (zField X R ω)

theorem exists_grid_rateA [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : Set ℂ} {R d : ℝ} (hreg : Region S R d)
    {f : ℂ → ℝ} (hf : VagueH.IsTestH f) (hfS' : tsupport f ⊆ S) :
    ∃ C, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → 2 * radius k ≤ d ∧ ∀ c ∈ Icc (1 : ℝ) 2,
      AEMeasurable (fun ω => aB γ X R f (c * radius k) ω - LfA γ X R f ω) P ∧
      ∫⁻ ω, ENNReal.ofReal |aB γ X R f (c * radius k) ω - LfA γ X R f ω| ∂P
        ≤ ENNReal.ofReal (C * exp (-areaRate γ * (k * log 2))) := by
  obtain ⟨M, hM⟩ := hf.1.bounded_above_of_compact_support hf.2.1
  have hM' : ∀ z, |f z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  have hfS : ∀ z ∉ S, f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hfS' h)
  have hfR : ∀ z ∈ tsupport f, ‖z‖ + 1 ≤ R := fun z hz => hreg.normR z (hfS' hz)
  obtain ⟨C₁, hC₁, h₁⟩ := exists_offset_rateA hX hγ hγ2 hreg hf.1.measurable hM' hfS
  obtain ⟨C₂, hC₂, k₁, hint, hC⟩ := areaApprox_L1_rate hX hγ hγ2 hf.1 hf.2.1 hf.2.2 hfR
  obtain ⟨k₂, hk₂⟩ := exists_pow_lt_of_lt_one (show 0 < d / 2 by linarith [hreg.d_pos])
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, f z ∂areaApprox γ (aZ X R ω) k) atTop
      (𝓝 (LfA γ X R f ω)) := by
    filter_upwards [ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω hω
    exact hω.2.2 f hf.1 hf.2.1 hf.2.2
  refine ⟨C₁ + C₂, by positivity, max k₁ k₂, fun k hk => ?_⟩
  have hk1 : k₁ ≤ k := le_of_max_le_left hk
  have hk2 : k₂ ≤ k := le_of_max_le_right hk
  have hrk : 2 * radius k ≤ d := by
    have : radius k ≤ radius k₂ := aradius_anti hk2
    have h' : radius k₂ < d / 2 := by simpa [radius] using hk₂
    linarith
  refine ⟨hrk, fun c hc => ?_⟩
  have hε := radius_pos k
  have hcε : 0 < c * radius k := mul_pos (by linarith [hc.1]) hε
  have hcεd : c * radius k ≤ d := by nlinarith [hc.2]
  have hI1 : Integrable (fun ω => aB γ X R f (c * radius k) ω - aB γ X R f (radius k) ω) P :=
    (integrable_aB hX hreg hcε hcεd γ hf.1.measurable hM' hfS).sub
      (integrable_aB hX hreg hε (by linarith) γ hf.1.measurable hM' hfS)
  obtain ⟨hI2, hB2⟩ := integral_abs_sub_lim_le (G := fun k ω =>
    ∫ z, f z ∂areaApprox γ (aZ X R ω) k) hint hlim (fun k k' hk hkk' => hC k k' hk hkk') hk1
  have hae : ∀ᵐ ω ∂P, aB γ X R f (radius k) ω = ∫ z, f z ∂areaApprox γ (aZ X R ω) k := by
    filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg'
    obtain ⟨F, hF⟩ := hreg'
    have := GoodSample.areaR_radius γ (regular_zField (R := R) hF) k
    rw [one_mul] at this
    rw [aB, this]
    rfl
  have hmeas : AEMeasurable (fun ω => aB γ X R f (c * radius k) ω - LfA γ X R f ω) P := by
    refine (hI1.aemeasurable.add hI2.aemeasurable).congr ?_
    filter_upwards [hae] with ω h
    simp only [Pi.add_apply]
    rw [h]; ring
  refine ⟨hmeas, ?_⟩
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |aB γ X R f (c * radius k) ω - LfA γ X R f ω| ≤
      ENNReal.ofReal |aB γ X R f (c * radius k) ω - aB γ X R f (radius k) ω| +
      ENNReal.ofReal |∫ z, f z ∂areaApprox γ (aZ X R ω) k - LfA γ X R f ω| := by
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
  have := h₁ k hrk c hc
  nlinarith

end AreaOffsets
end QuantumZipper
