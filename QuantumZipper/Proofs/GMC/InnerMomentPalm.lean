import QuantumZipper.Proofs.GMC.InnerMomentShift
import QuantumZipper.Proofs.GMC.InnerMomentSub
import QuantumZipper.Proofs.Probability.CameronMartin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GMC-INNERMOM (4): the Palm (rooted-measure) inequality and `innerMomentStmt_holds`

`palmRootedStmt_holds`: for `q ≥ 1`,
`E W^q ≤ 2^{(q−1)γ²/2} ∫_S E[(∫ (δ/max(|x−u|, 2·2^{-k}))^{γ²/2} W(du))^{q−1}] dx`.

Proof (rooted measure / Girsanov; Berestycki–Powell arXiv:2004.04720 ch. 3; Rhodes–Vargas
arXiv:1305.6221 §2.3): `E W^q = ∫_S E[w(x) W^{q−1}] dx` (Tonelli); `w(x)` is a.s. the
Cameron–Martin density of the single coordinate `Y_k(x)` of the inner process (its variance is
`2 log(δ/2^{-k})`, so the normalization is exact), and `CameronMartin.map_tiltMeasure_path`
turns `E[w(x) F(Y)] ` into `E[F(Y + (γ/2) Cov(·, Y_k(x)))]`; the shifted mass is bounded by
`InnerMomentShift` (`massFun_shift_le`).

Final result `innerMomentStmt_holds`: `InnerMomentStmt γ q` for `0 < γ`, `1 < q ≤ 2`,
`q < 4/γ²`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Real Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace GMCMoments

open FracMom BdryExist GaussTK KernelId

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem measurable_palmKer (γ δ : ℝ) (k : ℕ) (x : ℝ) : Measurable (palmKer γ δ k x) := by
  unfold palmKer
  exact ENNReal.measurable_ofReal.comp ((measurable_const.div
    ((continuous_abs.measurable.comp (measurable_const.sub measurable_id)).max
      measurable_const)).pow_const _)

/-- **Pathwise bound on the shifted mass.** -/
theorem massFun_shift_le {γ t δ x : ℝ} {k : ℕ} (hδ : 0 < δ) (hk : 2 * radius k < δ)
    (hx : |x - t| + radius k ≤ δ) {s : InnerQ → ℝ}
    (hs : ∀ j : InnerQ, s j = γ / 2 * covG t δ x (radius k) (innerMeas t δ j)) {ω : Ω}
    (h1 : ∀ z ∈ Hbar, Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k)))
      atTop (𝓝 (avgReg (X ω) k z))) :
    massFun γ t δ k (innerRebuild t δ (innerProc X t δ ω + s)) ≤
      ENNReal.ofReal (2 ^ (γ ^ 2 / 2)) * ∫⁻ u, palmKer γ δ k x u ∂innerMeasure γ X t δ k ω := by
  have hr := radius_pos k
  have hr1 : radius k ≤ 1 := radius_le_one_im k
  have hfm : Measurable fun u => ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) u) :=
    ENNReal.measurable_ofReal.comp (measurable_wDens_slice γ δ k _)
  rw [innerMeasure, lintegral_withDensity_eq_lintegral_mul _ hfm (measurable_palmKer γ δ k x),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, massFun]
  refine setLIntegral_mono ((hfm.mul (measurable_palmKer γ δ k x)).const_mul _) fun u hu => ?_
  have hu' := mem_bI_bound hu hk
  have hA := avgReg_innerRebuild_shift hδ hu' hs (h1 _ (ofReal_mem_Hbar u))
  have hg := covG_fc_le hr hr1 hu'.le hx
  set A := avgReg (innerSample X t δ ω) k (u : ℂ)
  set g := covG t δ x (radius k) (foldedCircle (u : ℂ) (radius k))
  set M := max |u - x| (2 * radius k) with hM
  have hM0 : 0 < M := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  simp only [Pi.mul_apply, palmKer]
  rw [abs_sub_comm x u, ← hM, ← ENNReal.ofReal_mul (wDens_nonneg γ hδ k _ u),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [wDens]
  rw [hA]
  have hc0 : 0 ≤ (radius k / δ) ^ (γ ^ 2 / 4) := rpow_nonneg (div_pos hr hδ).le _
  have key : exp (γ / 2 * (γ / 2 * g)) ≤ 2 ^ (γ ^ 2 / 2) * (δ / M) ^ (γ ^ 2 / 2) := by
    rw [rpow_def_of_pos two_pos, rpow_def_of_pos (div_pos hδ hM0), ← exp_add,
      log_div hδ.ne' hM0.ne']
    apply exp_le_exp.2
    have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
    nlinarith
  calc (radius k / δ) ^ (γ ^ 2 / 4) * exp (γ / 2 * (A + γ / 2 * g))
      = (radius k / δ) ^ (γ ^ 2 / 4) * exp (γ / 2 * A) * exp (γ / 2 * (γ / 2 * g)) := by
        rw [mul_add, exp_add]; ring
    _ ≤ (radius k / δ) ^ (γ ^ 2 / 4) * exp (γ / 2 * A) *
          (2 ^ (γ ^ 2 / 2) * (δ / M) ^ (γ ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hc0 (exp_pos _).le)
    _ = _ := by ring

/-- The inner index of the circle `fc(x, 2^{-k})`. -/
def qAt (t δ x : ℝ) (k : ℕ) (hδ : 0 < δ) (hx : |x - t| + radius k ≤ δ) : InnerQ :=
  ⟨((x - t) / δ, radius k / δ), div_pos (radius_pos k) hδ, by
    rw [abs_div, abs_of_pos hδ, ← add_div, div_le_one hδ]; exact hx⟩

theorem innerIdx_qAt {t δ x : ℝ} {k : ℕ} (hδ : 0 < δ) (hx : |x - t| + radius k ≤ δ) :
    innerIdx t δ (qAt t δ x k hδ hx).1.1 (qAt t δ x k hδ hx).1.2 =
      ((x : ℂ), radius k, (t : ℂ), δ) := by
  simp only [innerIdx, qAt]
  rw [show t + δ * ((x - t) / δ) = x by field_simp; ring,
    show δ * (radius k / δ) = radius k by field_simp]

/-- **Cameron–Martin at level `k` for the inner process.** For measurable `F ≥ 0` on paths and
`x` with `|x − t| + 2^{-k} < δ`:
`E[w(x) F(Y)] = E[F(Y + (γ/2) Cov(·, Y_k(x)))]`. -/
theorem lintegral_wDens_mul_eq_shift [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (γ : ℝ) {t δ x : ℝ} {k : ℕ} (hδ : 0 < δ) (hx : |x - t| + radius k < δ)
    {F : (InnerQ → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∃ s : InnerQ → ℝ, (∀ j : InnerQ, s j = γ / 2 * covG t δ x (radius k) (innerMeas t δ j)) ∧
      ∫⁻ ω, ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) x) * F (innerProc X t δ ω) ∂P =
        ∫⁻ ω, F (innerProc X t δ ω + s) ∂P := by
  have hr := radius_pos k
  set Y : InnerQ → Ω → ℝ := fun q ω => innerProc X t δ ω q with hY
  have hGP : IsGaussianProcess Y P := isGaussianProcess_innerProc hX hδ
  have hmeas : ∀ q, Measurable (Y q) := fun q => measurable_fcPairVal hX _
  have hcent : ∀ q, P[Y q] = 0 := fun q => integral_fcPairVal hX (good_innerIdx hδ q)
  set qx := qAt t δ x k hδ hx.le with hqx
  set σ : InnerQ →₀ ℝ := Finsupp.single qx (γ / 2) with hσ
  have hcovK : ∀ j, CameronMartin.covK Y P j qx =
      covG t δ x (radius k) (innerMeas t δ j) := by
    intro j
    show cov[fcPairVal X _, fcPairVal X _; P] = _
    rw [covariance_fcPairVal hX (good_innerIdx hδ j) (good_innerIdx hδ qx), hqx,
      innerIdx_qAt hδ hx.le]
    rfl
  have hshift : ∀ j, CameronMartin.covShift Y P σ j =
      γ / 2 * covG t δ x (radius k) (innerMeas t δ j) := by
    intro j
    unfold CameronMartin.covShift
    rw [hσ, Finset.sum_subset Finsupp.support_single_subset
      (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, zero_mul])]
    simp [hcovK]
  have hvar : CameronMartin.covK Y P qx qx = 2 * log δ - 2 * log (radius k) := by
    show cov[fcPairVal X _, fcPairVal X _; P] = _
    rw [covariance_fcPairVal hX (good_innerIdx hδ qx) (good_innerIdx hδ qx), hqx,
      innerIdx_qAt hδ hx.le, fcPairCov_innerU_self hr hx.le]
  have hnorm : CameronMartin.covNorm Y P σ =
      γ / 2 * (γ / 2 * (2 * log δ - 2 * log (radius k))) := by
    unfold CameronMartin.covNorm
    rw [hσ, Finset.sum_subset Finsupp.support_single_subset
      (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, zero_mul])]
    simp only [Finset.sum_singleton, Finsupp.single_eq_same]
    rw [← hσ, hshift, ← hvar, ← hcovK]
  have hcomb : ∀ ω, CameronMartin.comb Y σ ω = γ / 2 * Y qx ω := by
    intro ω
    unfold CameronMartin.comb
    rw [hσ, Finset.sum_subset Finsupp.support_single_subset
      (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, zero_mul])]
    simp
  have hdens : (fun ω => ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) x)) =ᵐ[P]
      fun ω => ((CameronMartin.tiltDensity Y P σ ω).toNNReal : ℝ≥0∞) := by
    filter_upwards [iU_ae_eq hX hδ k hx] with ω hω
    show ENNReal.ofReal _ = ENNReal.ofReal _
    congr 1
    simp only [wDens, CameronMartin.tiltDensity, hcomb, hnorm]
    change (radius k / δ) ^ (γ ^ 2 / 4) * exp (γ / 2 * iU X t δ k x ω) = _
    rw [hω]
    have hYq : Y qx ω = fcPairVal X ((x : ℂ), radius k, (t : ℂ), δ) ω := by
      show fcPairVal X _ ω = _
      rw [hqx, innerIdx_qAt hδ hx.le]
    rw [hYq, rpow_def_of_pos (div_pos hr hδ), ← exp_add, log_div hr.ne' hδ.ne']
    congr 1
    ring
  have hpath : Measurable fun ω => innerProc X t δ ω := measurable_innerProc hX t δ
  have hpath' : Measurable fun ω j => Y j ω + CameronMartin.covShift Y P σ j :=
    measurable_pi_iff.mpr fun j => (hmeas j).add_const _
  refine ⟨fun j => CameronMartin.covShift Y P σ j, hshift, ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) x) * F (innerProc X t δ ω) ∂P
      = ∫⁻ ω, ((CameronMartin.tiltDensity Y P σ ω).toNNReal : ℝ≥0∞) *
          F (innerProc X t δ ω) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hdens] with ω hω
        rw [hω]
    _ = ∫⁻ ω, F (innerProc X t δ ω) ∂(CameronMartin.tiltMeasure Y P σ) := by
        rw [CameronMartin.tiltMeasure]
        exact (lintegral_withDensity_eq_lintegral_mul _
          (CameronMartin.measurable_tiltDensity hGP hmeas σ).real_toNNReal.coe_nnreal_ennreal
          (hF.comp hpath)).symm
    _ = ∫⁻ y, F y ∂((CameronMartin.tiltMeasure Y P σ).map fun ω j => Y j ω) := by
        rw [lintegral_map hF hpath]
    _ = ∫⁻ y, F y ∂(P.map fun ω j => Y j ω + CameronMartin.covShift Y P σ j) := by
        rw [CameronMartin.map_tiltMeasure_path hGP hmeas hcent σ]
    _ = _ := by
        rw [lintegral_map hF hpath']
        rfl

/-- **Palm inequality** (`q ≥ 1`), with constant `2^{(q−1)γ²/2}`. -/
theorem palmRootedBound_holds [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {q : ℝ} (hq : 1 ≤ q) :
    PalmRootedBound γ q X P (ENNReal.ofReal (2 ^ (γ ^ 2 / 2)) ^ (q - 1)) := by
  intro t δ k hδ hk
  have hp0 : 0 ≤ q - 1 := by linarith
  have hCt : ENNReal.ofReal (2 ^ (γ ^ 2 / 2)) ^ (q - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top
  have hWm : Measurable (innerMass γ X t δ k) := measurable_innerMass hX γ t δ k
  have hU : Measurable (fun p : Ω × ℝ => avgReg (innerSample X t δ p.1) k (p.2 : ℂ)) :=
    (measurable_avgReg k).comp (((measurable_innerSample hX t δ).comp measurable_fst).prodMk
      (Complex.continuous_ofReal.measurable.comp measurable_snd))
  have hmeas : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (wDens γ δ k (innerSample X t δ p.1) p.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hU.const_mul _).exp)
  have hT : ∫⁻ ω, innerMass γ X t δ k ω ^ q ∂P = ∫⁻ x in bI t δ, ∫⁻ ω,
      ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) x) *
        innerMass γ X t δ k ω ^ (q - 1) ∂P := by
    have e : ∀ ω, innerMass γ X t δ k ω ^ q = ∫⁻ x in bI t δ,
        ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) x) *
          innerMass γ X t δ k ω ^ (q - 1) := by
      intro ω
      have hm : Measurable fun s => ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) s) :=
        ENNReal.measurable_ofReal.comp (measurable_wDens_slice γ δ k _)
      rw [lintegral_mul_const _ hm]
      conv_lhs => rw [show q = 1 + (q - 1) by ring]
      rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one hp0, ENNReal.rpow_one]
      rfl
    simp_rw [e]
    exact lintegral_lintegral_swap (f := fun ω x =>
      ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) x) * innerMass γ X t δ k ω ^ (q - 1))
      (hmeas.mul ((hWm.pow_const _).comp measurable_fst)).aemeasurable
  have hbd : ∀ x ∈ bI t δ, ∫⁻ ω, ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) x) *
        innerMass γ X t δ k ω ^ (q - 1) ∂P ≤
      ENNReal.ofReal (2 ^ (γ ^ 2 / 2)) ^ (q - 1) *
        ∫⁻ ω, (∫⁻ u, palmKer γ δ k x u ∂innerMeasure γ X t δ k ω) ^ (q - 1) ∂P := by
    intro x hx
    have hx' := mem_bI_bound hx hk
    have hFm : Measurable fun y : InnerQ → ℝ => massFun γ t δ k (innerRebuild t δ y) ^ (q - 1) :=
      ((measurable_massFun γ t δ k).comp (measurable_innerRebuild t δ)).pow_const _
    obtain ⟨s, hs, hEq⟩ := lintegral_wDens_mul_eq_shift hX γ hδ hx' hFm
    have hEq' : ∫⁻ ω, ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) x) *
        innerMass γ X t δ k ω ^ (q - 1) ∂P =
        ∫⁻ ω, massFun γ t δ k (innerRebuild t δ (innerProc X t δ ω + s)) ^ (q - 1) ∂P := hEq
    rw [hEq', ← lintegral_const_mul' _ _ hCt]
    refine lintegral_mono_ae ?_
    filter_upwards [(ae_avgReg_spec hX k).1] with ω h1
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0]
    exact ENNReal.rpow_le_rpow (massFun_shift_le hδ hk hx'.le hs h1) hp0
  rw [hT]
  calc ∫⁻ x in bI t δ, ∫⁻ ω, ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) x) *
        innerMass γ X t δ k ω ^ (q - 1) ∂P
      ≤ ∫⁻ x in bI t δ, ENNReal.ofReal (2 ^ (γ ^ 2 / 2)) ^ (q - 1) *
          ∫⁻ ω, (∫⁻ u, palmKer γ δ k x u ∂innerMeasure γ X t δ k ω) ^ (q - 1) ∂P :=
        lintegral_mono_ae (ae_restrict_of_forall_mem (measurableSet_bI t δ) hbd)
    _ = _ := lintegral_const_mul' _ _ hCt

theorem palmRootedStmt_holds (γ : ℝ) {q : ℝ} (hq : 1 ≤ q) : PalmRootedStmt γ q := by
  refine ⟨ENNReal.ofReal (2 ^ (γ ^ 2 / 2)) ^ (q - 1),
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top, ?_⟩
  intro Ω _ P _ X hX
  exact palmRootedBound_holds hX γ hq

/-- **GMC-INNERMOM.** The uniform `q`-th moment of the inner masses, `InnerMomentStmt γ q`, for
`0 < γ < 2`, `1 < q ≤ 2`, `q < 4/γ²`. -/
theorem innerMomentStmt_holds {γ q : ℝ} (hγ : 0 < γ) (_hγ2 : γ < 2) (hq : 1 < q) (hq2 : q ≤ 2)
    (hqγ : q < 4 / γ ^ 2) : InnerMomentStmt γ q :=
  innerMomentStmt_of_palm hγ hq hq2 hqγ (palmRootedStmt_holds γ hq.le)

end GMCMoments
end QuantumZipper
