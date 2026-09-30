import QuantumZipper.Proofs.Zipper.BaseFin2ULG0
import QuantumZipper.Proofs.LQG.KernelIdentities
import QuantumZipper.Proofs.LQG.BoundaryExistence
import QuantumZipper.Proofs.GFF.CoordRegLog
import QuantumZipper.Proofs.Zipper.E1TransferRep3
import QuantumZipper.Proofs.LQG.TwoRadiusTilt
import QuantumZipper.Proofs.LQG.RegularSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1-UL-G1: the one-point bound `BaseULG0PointStmt`

For a normalized free field `X` (`X(fc(0,1)) = 0`) and `Γ⁰ = (2/γ) log|·| + X`:
* a.s. `h_k(t) = (2/γ) log max(2^{-k}, |t|) + (X(fc(t,2^{-k})) − X(fc(0,1)))`
  (`CoordReg`/`integral_logAdd_foldedCircle`: the circle average of `log|·|` is `log max(r,|c|)`);
* the Gaussian pair value has variance `≤ −2 log r + 4 log(|t|+2)`: the Neumann kernel
  `−log|x−y| − log|x−ȳ| ≥ −2 log(|t|+2)` on the two circles, and
  `kernelCov_fc_real_sameCenter`;
* hence `E[r^{γ²/4} e^{(γ/2) h_k(t)}] ≤ (|t|+2)^{1+γ²/2} ≤ e^{A} e^{A|t|}`.
Own elementary computation (the standard first-moment computation for boundary GMC,
cf. Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 2011, §6).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace BaseFin2

/-- A lower bound for an integral against a probability measure from an a.e. lower bound `c ≤ 0`
(no integrability needed). -/
theorem ul_le_integral_of_ae {μ : Measure ℂ} [IsProbabilityMeasure μ] {f : ℂ → ℝ} {c : ℝ}
    (hc : c ≤ 0) (h : ∀ᵐ x ∂μ, c ≤ f x) : c ≤ ∫ x, f x ∂μ := by
  by_cases hi : Integrable f μ
  · have := integral_mono_ae (integrable_const c) hi h
    simpa using this
  · rw [integral_undef hi]; exact hc

theorem ul_ae_norm_fc (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂(foldedCircle c r), ‖x‖ ≤ ‖c‖ + r := by
  unfold foldedCircle
  rw [ae_map_iff measurable_foldH.aemeasurable (measurableSet_le measurable_norm measurable_const)]
  filter_upwards [KernelId.ae_norm_sub_center c hr] with x hx
  have h1 : ‖foldH x‖ = ‖x‖ := by unfold foldH; split_ifs <;> simp
  rw [h1]
  calc ‖x‖ = ‖c + (x - c)‖ := by ring_nf
    _ ≤ ‖c‖ + ‖x - c‖ := norm_add_le _ _
    _ = ‖c‖ + r := by rw [hx]

theorem ul_neumannH_lb {x y : ℂ} {M : ℝ} (hM : 1 ≤ M) (h : ‖x‖ + ‖y‖ ≤ M) :
    -2 * Real.log M ≤ neumannH x y := by
  unfold neumannH
  have hM0 : 0 ≤ Real.log M := Real.log_nonneg hM
  have hb : ∀ w : ℂ, ‖w‖ ≤ M → Real.log ‖w‖ ≤ Real.log M := fun w hw => by
    rcases (norm_nonneg w).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact hM0
    · exact Real.log_le_log h0 hw
  have h1 : ‖x - y‖ ≤ M := (norm_sub_le _ _).trans h
  have h2 : ‖x - conj y‖ ≤ M := (norm_sub_le _ _).trans (by rw [Complex.norm_conj]; exact h)
  linarith [hb _ h1, hb _ h2]

/-- `K(fc(a,r), fc(b,ρ)) ≥ −2 log M` when `|a| + r + |b| + ρ ≤ M`, `M ≥ 1`. -/
theorem ul_kernelCov_lb {a b : ℂ} {r ρ M : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hM : 1 ≤ M)
    (h : ‖a‖ + r + (‖b‖ + ρ) ≤ M) :
    -2 * Real.log M ≤ kernelCov neumannH (foldedCircle a r) (foldedCircle b ρ) := by
  have hc : -2 * Real.log M ≤ 0 := by nlinarith [Real.log_nonneg hM]
  unfold kernelCov
  refine ul_le_integral_of_ae hc ?_
  filter_upwards [ul_ae_norm_fc a hr] with x hx
  refine ul_le_integral_of_ae hc ?_
  filter_upwards [ul_ae_norm_fc b hρ] with y hy
  exact ul_neumannH_lb hM (by linarith)

/-- The variance of the pair `X(fc(t,r)) − X(fc(0,1))`. -/
theorem ul_fcPairCov_le {t r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    GaussTK.fcPairCov ((t : ℂ), r, 0, 1) ((t : ℂ), r, 0, 1) ≤
      -2 * Real.log r + 4 * Real.log (|t| + 2) := by
  simp only [GaussTK.fcPairCov, kernelCov2]
  have h1 := kernelCov_fc_real_sameCenter (s := t) hr hr
  have h2 := kernelCov_fc_real_sameCenter (s := 0) one_pos one_pos
  rw [max_self] at h1 h2
  have hM : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hn : ‖(t : ℂ)‖ = |t| := by simp
  have h3 := ul_kernelCov_lb (a := (t : ℂ)) (b := 0) hr one_pos hM (by rw [hn]; simp; linarith)
  have h4 := ul_kernelCov_lb (a := 0) (b := (t : ℂ)) one_pos hr hM (by rw [hn]; simp; linarith)
  simp only [Complex.ofReal_zero] at h2
  rw [h1, h2, Real.log_one] at *
  linarith

/-- `∫ (2/γ) log|·| d fc(c,r) = (2/γ) log max(r,|c|)`. -/
theorem ul_ofFun_h0rev_fc (κ : ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ofFun (h0rev κ) (foldedCircle c r) = 2 / Real.sqrt κ * Real.log (max r ‖c‖) := by
  have h := CoordReg.integral_logAdd_foldedCircle (2 / Real.sqrt κ) (g₁ := fun _ => (0 : ℝ))
    continuousOn_const c hr
  simp only [add_zero] at h
  have hs : GoodSample.smoothFun (fun _ => (0 : ℝ)) c r = 0 := by
    simp [GoodSample.smoothFun]
  rw [hs, add_zero] at h
  exact h

theorem ul_nrm_fc01 {x : FieldSample} (h : B1Full.nrm x = x) : x (foldedCircle 0 1) = 0 := by
  have e := congrFun h (foldedCircle 0 1)
  simp only [B1Full.nrm, addConst, measure_univ, ENNReal.toReal_one, mul_one] at e
  linarith

theorem ul_addConst_zero (x : FieldSample) : addConst x 0 = x := by
  funext μ; simp [addConst]

/-- **The one-point bound holds.** -/
theorem baseULG0PointStmt_holds : BaseULG0PointStmt := by
  intro κ hκ hκ4
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  refine ⟨1 + γ ^ 2 / 2, by positivity, ENNReal.ofReal (Real.exp (1 + γ ^ 2 / 2)),
    ENNReal.ofReal_ne_top, ?_⟩
  intro Ω _ P _ X hX hN k t
  set r := radius k with hrdef
  have hr : 0 < r := radius_pos k
  have hr1 : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set Y := GaussTK.fcPairVal X ((t : ℂ), r, 0, 1) with hYdef
  set a := 2 / γ with hadef
  -- the a.s. identity
  have hid : ∀ᵐ ω ∂P, avgReg (ulShift (ofFun (h0rev κ) + X ω)) k (t : ℂ) =
      a * Real.log (max r ‖(t : ℂ)‖) + Y ω := by
    filter_upwards [RegSample.ae_isRegularSample hX,
      BdryExist.avgReg_zField_ae_eq hX 1 k (GaussTK.ofReal_mem_Hbar t)] with ω hreg hz
    have hX0 : X ω (foldedCircle 0 1) = 0 := ul_nrm_fc01 (hN ω)
    have hzf : BdryExist.zField X 1 ω = X ω := by
      simp only [BdryExist.zField, hX0, neg_zero, ul_addConst_zero]
    rw [hzf] at hz
    have hsh : ulShift (ofFun (h0rev κ) + X ω) = ofFun (h0rev κ) + X ω := by
      have h0 : (ofFun (h0rev κ) + X ω) ulNorm = 0 := by
        simp only [ulNorm, Pi.add_apply, hX0, add_zero]
        rw [ul_ofFun_h0rev_fc κ 0 one_pos]; simp
      simp only [ulShift, h0, neg_zero, ul_addConst_zero]
    rw [hsh]
    obtain ⟨l, hl⟩ := hreg.rawConverges k (t : ℂ) (GaussTK.ofReal_mem_Hbar t)
    have hXl : avgReg (X ω) k (t : ℂ) = l := hl.limUnder_eq
    have ha : Tendsto (fun n => a * Real.log (max r ‖dyadicRoundC n (t : ℂ)‖)) atTop
        (𝓝 (a * Real.log (max r ‖(t : ℂ)‖))) :=
      (((CoordReg.continuous_log_max_norm hr).tendsto _).comp
        (RegClosure.tendsto_dyadicRoundC _)).const_mul a
    have hsum : Tendsto (fun n => (ofFun (h0rev κ) + X ω)
        (foldedCircle (dyadicRoundC n (t : ℂ)) r)) atTop
        (𝓝 (a * Real.log (max r ‖(t : ℂ)‖) + l)) := by
      refine (ha.add hl).congr fun n => ?_
      simp only [Pi.add_apply]
      rw [ul_ofFun_h0rev_fc κ _ hr]
    unfold avgReg
    rw [hsum.limUnder_eq, ← hXl, hz]
  -- the Gaussian law
  have hGood : GaussTK.FcIdx.Good ((t : ℂ), r, (0 : ℂ), (1 : ℝ)) :=
    ⟨GaussTK.ofReal_mem_Hbar t, hr, GaussTK.zero_mem_Hbar, one_pos⟩
  have hL := BdryExist.hasLaw_fcPairVal (P := P) hX hGood
  set V := GaussTK.fcPairCov ((t : ℂ), r, 0, 1) ((t : ℂ), r, 0, 1) with hVdef
  have hint : Integrable (fun ω => Real.exp (γ / 2 * Y ω)) P := by
    have hi := hL.integrable_fun_comp (TwoRadius.integrable_exp_mul_add_gaussianReal _ (γ / 2) 0)
    simpa only [zero_add] using hi
  have hE : ∫ ω, Real.exp (γ / 2 * Y ω) ∂P = Real.exp (V.toNNReal * (γ / 2) ^ 2 / 2) := by
    have h2 := TwoRadius.integral_exp_mul_add_gaussianReal V.toNNReal (γ / 2) 0
    simp only [zero_add] at h2
    rw [← h2]
    exact hL.integral_comp (f := fun x => Real.exp (γ / 2 * x)) (by fun_prop)
  set m := max r ‖(t : ℂ)‖ with hmdef
  have hm0 : 0 < m := lt_of_lt_of_le hr (le_max_left _ _)
  have hkey : ∀ᵐ ω ∂P, ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 *
      avgReg (ulShift (ofFun (h0rev κ) + X ω)) k (t : ℂ))) =
      ENNReal.ofReal (r ^ (γ ^ 2 / 4) * m) * ENNReal.ofReal (Real.exp (γ / 2 * Y ω)) := by
    filter_upwards [hid] with ω h
    rw [h, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e : γ / 2 * (a * Real.log m + Y ω) = Real.log m + γ / 2 * Y ω := by
      rw [hadef]; field_simp
    rw [e, Real.exp_add, Real.exp_log hm0, hrdef]; ring
  rw [lintegral_congr_ae hkey, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    hE, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real inequality
  have hVle : (V.toNNReal : ℝ) ≤ -2 * Real.log r + 4 * Real.log (|t| + 2) := by
    rw [Real.coe_toNNReal']
    refine max_le (ul_fcPairCov_le hr hr1) ?_
    have := Real.log_nonpos hr.le hr1
    have := Real.log_nonneg (show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
    linarith
  have hmle : m ≤ |t| + 2 := max_le (by linarith [abs_nonneg t]) (by simp)
  have hlog : Real.log (|t| + 2) ≤ |t| + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < |t| + 2 by positivity); linarith
  have hrp : r ^ (γ ^ 2 / 4) = Real.exp (Real.log r * (γ ^ 2 / 4)) := Real.rpow_def_of_pos hr _
  have hm' : m ≤ Real.exp (Real.log (|t| + 2)) := by
    rw [Real.exp_log (by positivity)]; exact hmle
  calc r ^ (γ ^ 2 / 4) * m * Real.exp (V.toNNReal * (γ / 2) ^ 2 / 2)
      ≤ Real.exp (Real.log r * (γ ^ 2 / 4)) * Real.exp (Real.log (|t| + 2)) *
          Real.exp ((-2 * Real.log r + 4 * Real.log (|t| + 2)) * (γ / 2) ^ 2 / 2) := by
        rw [hrp]
        gcongr
    _ = Real.exp ((1 + γ ^ 2 / 2) * Real.log (|t| + 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((1 + γ ^ 2 / 2) * (|t| + 1)) := by
        gcongr
    _ = Real.exp (1 + γ ^ 2 / 2) * Real.exp ((1 + γ ^ 2 / 2) * |t|) := by
        rw [← Real.exp_add]; congr 1; ring

/-- **`BaseULGamma0MomStmt` holds.** -/
theorem baseULGamma0MomStmt_holds : BaseULGamma0MomStmt :=
  baseULGamma0_of_point baseULG0PointStmt_holds

end BaseFin2
end QuantumZipper
