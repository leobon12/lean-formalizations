import QuantumZipper.Proofs.Thm18.A1RFLoopFree
import QuantumZipper.Proofs.Zipper.WedgeCore2XC
import QuantumZipper.Proofs.Zipper.WedgeXContReg
import QuantumZipper.Proofs.Thm18.G1ProfileConvBasic
import QuantumZipper.Proofs.Section5.Prop17Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RF (5): uniform continuum limit of the unscaled wedge pairings along pulled-back circles

Toward `A1RFLoopUCStmt`. For the unscaled wedge sample `Z` with circle values
`Z = X + α₀(−log|·|) + G` (`X` a free sample, `G` continuous: `WedgeUnzip.WDec.wedgeDecompStmt_holds`),
and a driver `W`, the smoothed pairings
`Φ_Z(σ, (s, c, r)) = ∫ evalReg Z (fc(v, σ)) d((f_s⁻¹)_* fc(c, r))(v)`
converge as `σ → 0⁺` **uniformly** on every parameter box, once the `Γ⁰` pairings do
(`A1RF.ae_flowPhiYc_tendstoUniformlyOn`, A1RFLoopFree.lean):

* on circles, `evalReg Z fc(v, σ) = evalReg Γ⁰ fc(v, σ) + √κ (−log max(σ, |v|)) + smoothFun G v σ`
  (`Γ⁰ = 𝔥₀ + X = X + (−2/√κ)(−log|·|)`, time-`0` unzipped; `LogSingGood.evalReg_add_Lf_fc`,
  `GoodSample.evalReg_add_ofFun_fc`, `WedgeUnzip.evalReg_unzip_zero_eq`);
* the log term converges at the uniform Frostman rate `3 C σ^{1/3}`
  (`RegCont.integral_log_max_sub_le`, `RegCont.isFrostman_fwdMapInv_foldedCircle`, constants
  uniform on the box);
* the `G` term by uniform continuity of `G` on a ball containing all the pushed circles
  (`RegCont.fwdMapInv_mem_H_bound`).

Uniform version of `WedgeUnzip.xCont_pathwise` + `wedgeContinuum_of_x`; own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RF

open F1 B3d.ZipLen

variable {W : ℝ → ℝ}

/-- Uniform support bound of the pulled-back folded circles. -/
theorem ae_supp_unif (hW : Continuous W) (hW0 : W 0 = 0) {T M R : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) {w : ℂ} {r : ℝ}
    (hr : 0 < r) (hwR : ‖w‖ + r ≤ R) :
    ∀ᵐ z ∂((foldedCircle w r).map (fwdMapInv W s)), z ∈ H ∧
      ‖z‖ ≤ RegCont.revBound (2 * M) T R := by
  refine (ae_map_iff (RegCont.aemeasurable_fwdMapInv hW hW0 hs w hr)
    ((isOpen_H.measurableSet).inter (measurableSet_le measurable_norm measurable_const))).2 ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr, TwoPoint.foldedCircle_ae_norm_le w hr.le]
    with u hu hun
  exact RegCont.fwdMapInv_mem_H_bound hW hW0 hM hs hsT hu (hun.trans hwR)

/-- **The log term at the uniform Frostman rate.** -/
theorem abs_integral_log_max_sub_le_unif (hW : Continuous W) (hW0 : W 0 = 0) {s T r₀ R : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) {w : ℂ} {r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hwR : ‖w‖ + r ≤ R) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Integrable (fun z => Real.log ‖z‖) ((foldedCircle w r).map (fwdMapInv W s)) ∧
    |(∫ z, Real.log (max ρ ‖z‖) ∂((foldedCircle w r).map (fwdMapInv W s))) -
        ∫ z, Real.log ‖z‖ ∂((foldedCircle w r).map (fwdMapInv W s))| ≤
      3 * (18 / Real.sqrt r₀ + 12 * Real.sqrt (R ^ 2 + 4 * T) / r₀) * ρ ^ (1 / 3 : ℝ) := by
  have hr0 : 0 < r := hr₀.trans_le hr
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  have hP : IsProbabilityMeasure ((foldedCircle w r).map (fwdMapInv W s)) :=
    (Measure.isProbabilityMeasure_map_iff (RegCont.aemeasurable_fwdMapInv hW hW0 hs w hr0)).2
      inferInstance
  have hae := ae_supp_unif hW hW0 hM hs hsT hr0 (le_refl (‖w‖ + r))
  exact RegCont.integral_log_max_sub_le
    (RegCont.isFrostman_fwdMapInv_foldedCircle hW hW0 hs hsT hr₀ hr hwR)
    (hae.mono fun z hz h => by subst h; simp [H] at hz) (hae.mono fun z hz => hz.2) hρ hρ1

/-- **The continuous profile term, uniformly on bounded sets.** -/
theorem abs_smoothFun_sub_le {G : ℂ → ℝ} (hG : Continuous G) (B : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ v ∈ Hbar, ‖v‖ ≤ B → ∀ σ : ℝ, 0 < σ → σ < δ →
      |GoodSample.smoothFun G v σ - G v| ≤ ε := by
  intro ε hε
  have hK : IsCompact (closedBall (0 : ℂ) (B + 1)) := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hG.continuousOn) ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun v hv hvB σ hσ hσδ => ?_⟩
  have hvK : v ∈ closedBall (0 : ℂ) (B + 1) := by
    rw [mem_closedBall, dist_zero_right]; linarith
  obtain ⟨MG, hMG⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have hdist := Thm18Asm.G1RC.foldedCircle_ae_dist_le' hv hσ.le
  have hmemK : ∀ᵐ u ∂foldedCircle v σ, u ∈ closedBall (0 : ℂ) (B + 1) := by
    filter_upwards [hdist] with u hu
    rw [mem_closedBall, dist_zero_right]
    have h1 := norm_le_norm_add_norm_sub' u v
    have h2 : ‖u - v‖ ≤ σ := by rw [← dist_eq_norm]; exact hu
    linarith [min_le_right δ 1]
  have hint : Integrable G (foldedCircle v σ) :=
    Integrable.mono' (integrable_const MG) hG.aestronglyMeasurable
      (hmemK.mono fun u hu => hMG u hu)
  have hae : ∀ᵐ u ∂foldedCircle v σ, ‖G u - G v‖ ≤ ε := by
    filter_upwards [hdist, hmemK] with u hu huK
    have := hδG u huK v hvK (lt_of_le_of_lt hu (lt_of_lt_of_le hσδ (min_le_left _ _)))
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]; exact this.le
  have e : GoodSample.smoothFun G v σ - G v = ∫ u, (G u - G v) ∂foldedCircle v σ := by
    unfold GoodSample.smoothFun
    rw [integral_sub hint (integrable_const _), integral_const]
    simp
  rw [e, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const hae
  simpa using this

/-- **Uniform continuum limit of the unscaled wedge pairings on a parameter box**, from that of
the `Γ⁰` pairings. -/
theorem tendstoUniformlyOn_Zpair {κ : ℝ} (hκ : 0 < κ) {X Z : FieldSample} {FX : ℂ × ℝ → ℝ}
    (hFX : IsRegularWith X FX) {G : ℂ → ℝ} (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    (hW : Continuous W) (hW0 : W 0 = 0)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    {m : ℕ} {L : ℝ × ℝ × ℂ × ℝ → ℝ}
    (hS1 : TendstoUniformlyOn (fun ρ p => flowPhiYc κ X W ρ p) L (𝓝[>] 0) (flowBox m)) :
    ∃ L' : ℝ × ℂ × ℝ → ℝ, TendstoUniformlyOn (fun σ (q : ℝ × ℂ × ℝ) =>
        ∫ v, evalReg Z (foldedCircle v σ) ∂((foldedCircle q.2.1 q.2.2).map (fwdMapInv W q.1)))
      L' (𝓝[>] 0) {q | ((0 : ℝ), q.1, q.2.1, q.2.2) ∈ flowBox m} := by
  set S : Set (ℝ × ℂ × ℝ) := {q | ((0 : ℝ), q.1, q.2.1, q.2.2) ∈ flowBox m} with hSdef
  set ν : ℝ × ℂ × ℝ → Measure ℂ := fun q => (foldedCircle q.2.1 q.2.2).map (fwdMapInv W q.1)
    with hνdef
  set α₀ : ℝ := Real.sqrt κ - 2 / Real.sqrt κ with hα₀
  set β : ℝ := -(2 / Real.sqrt κ) with hβ
  set lm : ℝ → ℂ → ℝ := fun σ v => -Real.log (max σ ‖v‖) with hlm
  set T : ℝ := (m : ℝ) + 1 with hT
  set r₀ : ℝ := 1 / ((m : ℝ) + 2) with hr₀
  set R : ℝ := 3 * (m : ℝ) + 4 with hR
  have hr0 : 0 < r₀ := by positivity
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  set Bu := RegCont.revBound (2 * M) T R with hBu
  have hbox : ∀ q ∈ S, 0 ≤ q.1 ∧ q.1 ≤ T ∧ q.2.1 ∈ Hbar ∧ r₀ ≤ q.2.2 ∧
      ‖q.2.1‖ + q.2.2 ≤ R := by
    intro q hq
    obtain ⟨-, ⟨hs0, hsT⟩, ⟨hre1, hre2⟩, ⟨him0, him1⟩, ⟨hr1, hr2⟩⟩ := hq
    refine ⟨hs0, hsT, him0, hr1, ?_⟩
    have hn := Complex.norm_le_abs_re_add_abs_im q.2.1
    have h1 : |q.2.1.re| ≤ (m : ℝ) + 1 := abs_le.2 ⟨hre1, hre2⟩
    have h2 : |q.2.1.im| ≤ (m : ℝ) + 1 := abs_le.2 ⟨by linarith, him1⟩
    linarith
  have hrpos : ∀ q ∈ S, 0 < q.2.2 := fun q hq => hr0.trans_le (hbox q hq).2.2.2.1
  have hsupp : ∀ q ∈ S, ∀ᵐ z ∂ν q, z ∈ H ∧ ‖z‖ ≤ Bu := fun q hq =>
    ae_supp_unif hW hW0 hM (hbox q hq).1 (hbox q hq).2.1 (hrpos q hq) (hbox q hq).2.2.2.2
  have hcarr : ∀ q ∈ S, ∀ᵐ z ∂ν q, z ∈ Hbar ∧ ‖z‖ ≤ Bu := fun q hq =>
    (hsupp q hq).mono fun z hz => ⟨le_of_lt (show (0 : ℝ) < z.im from hz.1), hz.2⟩
  have hprob : ∀ q ∈ S, IsProbabilityMeasure (ν q) := fun q hq =>
    (Measure.isProbabilityMeasure_map_iff (RegCont.aemeasurable_fwdMapInv hW hW0
      (hbox q hq).1 q.2.1 (hrpos q hq))).2 inferInstance
  -- circle values
  have hFl := LogSingGood.regular_add_Lf hFX α₀
  have hdec : ∀ v ∈ Hbar, ∀ σ : ℝ, 0 < σ → evalReg Z (foldedCircle v σ) =
      evalReg X (foldedCircle v σ) + α₀ * lm σ v + GoodSample.smoothFun G v σ := by
    intro v hv σ hσ
    have hreg := S5.FieldShift.regEq_of_fc hZfc
    rw [WedgeUnzip.evalReg_congr_avgReg (fun k z => hreg k z),
      show X + F2.logSingField κ = X + ofFun (LogSingGood.Lf α₀) from rfl,
      GoodSample.evalReg_add_ofFun_fc hFl hGc.continuousOn hv hσ,
      LogSingGood.evalReg_add_Lf_fc hFX α₀ hv hσ]
  have hdecΓ : ∀ v ∈ Hbar, ∀ σ : ℝ, 0 < σ →
      evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X, W) 0) (foldedCircle v σ) =
        evalReg X (foldedCircle v σ) + β * lm σ v := by
    intro v hv σ hσ
    rw [WedgeUnzip.evalReg_unzip_zero_eq hW hW0 hfy, F2.sgin_h0rev_add_eq_Lf κ X,
      LogSingGood.evalReg_add_Lf_fc hFX β hv hσ]
  -- integrability
  have hiX : ∀ q ∈ S, ∀ σ : ℝ, 0 < σ →
      Integrable (fun v => evalReg X (foldedCircle v σ)) (ν q) := by
    intro q hq σ hσ
    have := hprob q hq
    have hg : ContinuousOn (fun v : ℂ => FX (v, σ)) Hbar :=
      hFX.1.comp (continuous_id.prodMk continuous_const).continuousOn fun v hv => ⟨hv, hσ⟩
    refine (WedgeUnzip.integrable_of_continuousOn_of_carried hg (hcarr q hq)).congr ?_
    filter_upwards [hcarr q hq] with v hv
    exact (hFX.evalReg_fc_of_mem hv.1 hσ).symm
  have hil : ∀ q ∈ S, ∀ σ : ℝ, 0 < σ → Integrable (lm σ) (ν q) := by
    intro q hq σ hσ
    have := hprob q hq
    refine WedgeUnzip.integrable_of_continuousOn_of_carried ?_ (hcarr q hq)
    exact (Continuous.log (continuous_const.max continuous_norm) fun v =>
      (hσ.trans_le (le_max_left _ _)).ne').neg.continuousOn
  have hig : ∀ q ∈ S, ∀ σ : ℝ, Integrable (fun v => GoodSample.smoothFun G v σ) (ν q) := by
    intro q hq σ
    have := hprob q hq
    exact WedgeUnzip.integrable_of_continuousOn_of_carried
      (GoodSample.continuous_smoothFun hGc.continuousOn σ).continuousOn (hcarr q hq)
  -- the split
  have hsplit : ∀ q ∈ S, ∀ σ : ℝ, 0 < σ →
      ∫ v, evalReg Z (foldedCircle v σ) ∂ν q =
        flowPhiYc κ X W σ (0, q.1, q.2.1, q.2.2) + (α₀ - β) * ∫ v, lm σ v ∂ν q +
          ∫ v, GoodSample.smoothFun G v σ ∂ν q := by
    intro q hq σ hσ
    have hflow : flowPhiYc κ X W σ (0, q.1, q.2.1, q.2.2) =
        ∫ v, evalReg X (foldedCircle v σ) ∂ν q + β * ∫ v, lm σ v ∂ν q := by
      unfold flowPhiYc
      simp only
      rw [WedgeUnzip.flowNu_zero_left hW hW0 (hbox q hq).1 q.2.1 (hrpos q hq)]
      rw [integral_congr_ae ((hcarr q hq).mono fun v hv => hdecΓ v hv.1 σ hσ),
        integral_add (hiX q hq σ hσ) ((hil q hq σ hσ).const_mul β), integral_const_mul]
    have hi1 : Integrable (fun v => evalReg X (foldedCircle v σ) + α₀ * lm σ v) (ν q) :=
      (hiX q hq σ hσ).add ((hil q hq σ hσ).const_mul α₀)
    rw [integral_congr_ae ((hcarr q hq).mono fun v hv => hdec v hv.1 σ hσ),
      integral_add hi1 (hig q hq σ),
      integral_add (hiX q hq σ hσ) ((hil q hq σ hσ).const_mul α₀), integral_const_mul, hflow]
    ring
  -- the limit
  set C : ℝ := 18 / Real.sqrt r₀ + 12 * Real.sqrt (R ^ 2 + 4 * T) / r₀ with hC
  refine ⟨fun q => L (0, q.1, q.2.1, q.2.2) + (α₀ - β) * -∫ v, Real.log ‖v‖ ∂ν q +
    ∫ v, G v ∂ν q, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h1 := (Metric.tendstoUniformlyOn_iff.1 (hS1.comp fun q : ℝ × ℂ × ℝ =>
    ((0 : ℝ), q.1, q.2.1, q.2.2))) (ε / 3) (by positivity)
  obtain ⟨δG, hδG, hG⟩ := abs_smoothFun_sub_le hGc Bu (ε / 4) (by positivity)
  have hrate : Tendsto (fun σ : ℝ => |α₀ - β| * (3 * C * σ ^ (1 / 3 : ℝ))) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 (1 / 3 : ℝ)
      (Or.inr (by norm_num))).tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [Real.zero_rpow (by norm_num)] at h
    simpa using (h.const_mul (3 * C)).const_mul |α₀ - β|
  have h2 := (hrate.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity)))
  filter_upwards [h1, h2, Ioo_mem_nhdsGT (lt_min hδG one_pos)] with σ hσ1 hσ2 ⟨hσ0, hσδ⟩ q hq
  have hσ1' : σ ≤ 1 := (hσδ.trans_le (min_le_right _ _)).le
  obtain ⟨hs0, hsT, -, hrr, hwR⟩ := hbox q hq
  obtain ⟨hlogi, hlog⟩ := abs_integral_log_max_sub_le_unif hW hW0 hs0 hsT hr0 hrr hwR hσ0 hσ1'
  have := hprob q hq
  rw [hsplit q hq σ hσ0, Real.dist_eq]
  have e1 := hσ1 q hq
  rw [Real.dist_eq] at e1
  have e1' : |L (0, q.1, q.2.1, q.2.2) - flowPhiYc κ X W σ (0, q.1, q.2.1, q.2.2)| < ε / 3 := e1
  -- the log term
  have hlmI : ∫ v, lm σ v ∂ν q = -∫ v, Real.log (max σ ‖v‖) ∂ν q := integral_neg _
  have e2 : |(α₀ - β) * -∫ v, Real.log ‖v‖ ∂ν q - (α₀ - β) * ∫ v, lm σ v ∂ν q| < ε / 3 := by
    rw [hlmI, ← mul_sub, abs_mul]
    have : |-∫ v, Real.log ‖v‖ ∂ν q - -∫ v, Real.log (max σ ‖v‖) ∂ν q| ≤ 3 * C * σ ^ (1 / 3 : ℝ) := by
      rw [show ∀ a b : ℝ, -a - -b = b - a by intros; ring]
      exact hlog
    calc _ ≤ |α₀ - β| * (3 * C * σ ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ < ε / 3 := hσ2
  -- the profile term
  have e3 : |∫ v, G v ∂ν q - ∫ v, GoodSample.smoothFun G v σ ∂ν q| ≤ ε / 4 := by
    have hGi : Integrable G (ν q) :=
      WedgeUnzip.integrable_of_continuousOn_of_carried hGc.continuousOn (hcarr q hq)
    rw [← integral_sub hGi (hig q hq σ), ← Real.norm_eq_abs]
    have hb : ∀ᵐ v ∂ν q, ‖G v - GoodSample.smoothFun G v σ‖ ≤ ε / 4 := by
      filter_upwards [hcarr q hq] with v hv
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hG v hv.1 hv.2 σ hσ0 (hσδ.trans_le (min_le_left _ _))
    simpa using norm_integral_le_of_norm_le_const hb
  calc |L (0, q.1, q.2.1, q.2.2) + (α₀ - β) * -∫ v, Real.log ‖v‖ ∂ν q + ∫ v, G v ∂ν q -
        (flowPhiYc κ X W σ (0, q.1, q.2.1, q.2.2) + (α₀ - β) * ∫ v, lm σ v ∂ν q +
          ∫ v, GoodSample.smoothFun G v σ ∂ν q)|
      = |(L (0, q.1, q.2.1, q.2.2) - flowPhiYc κ X W σ (0, q.1, q.2.1, q.2.2)) +
          ((α₀ - β) * -∫ v, Real.log ‖v‖ ∂ν q - (α₀ - β) * ∫ v, lm σ v ∂ν q) +
          (∫ v, G v ∂ν q - ∫ v, GoodSample.smoothFun G v σ ∂ν q)| := by ring_nf
    _ ≤ |L (0, q.1, q.2.1, q.2.2) - flowPhiYc κ X W σ (0, q.1, q.2.1, q.2.2)| +
          |(α₀ - β) * -∫ v, Real.log ‖v‖ ∂ν q - (α₀ - β) * ∫ v, lm σ v ∂ν q| +
          |∫ v, G v ∂ν q - ∫ v, GoodSample.smoothFun G v σ ∂ν q| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ < ε := by linarith

end A1RF
end R18
end QuantumZipper
