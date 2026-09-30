import QuantumZipper.Proofs.Thm18.A1RFLoopProf
import QuantumZipper.Proofs.Thm18.A1RFSmear
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Zipper.RegContRandom
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.Thm18.A1R2YCont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RF (6): per-loop uniform convergence for the canonical wedge field (deterministic part)

Toward `A1RFLoopUCStmt`. Let `Z` be an unscaled wedge sample (`Z = X + α₀(−log|·|) + G` on circles),
`y` a field with the regularized averages of `rescale Z Q b` (the canonical wedge, `b > 0` its
scale), and `W(r) = V(b² r⁺)/b` the correspondingly rescaled driver. Then the dyadic pairings of
`y` along the pulled-back folded circles `(f_t⁻¹)_* fc(z, ρ)` are the pairings of `Z` at radius
`b 2^{-k}` along `(g^V_{b² t})_* fc(b z, b ρ)`, plus `Q log b` (Loewner scaling `RS.fwdMapInv_scale`,
`foldedCircle_map_mul`, and the dilation witness `IsRegularWith.rescale'`). The latter converge
uniformly on parameter boxes (`A1RF.tendstoUniformlyOn_Zpair`), so the former converge uniformly
on bounded sets of centres, to `evalReg y` (`A1RF.loopUC_of_Z`).

**`A1RF.a1rfLoopUCStmt_holds : A1RFLoopUCStmt`**: the realization of the Theorem 1.8 field as the
canonical wedge `canonical(Z)` with `Z` decomposed as above, `X` a free field independent of the
Brownian path (`WedgeUnzip.pStarRealizeStmt_holds`, `WedgeUnzip.WDec.wedgeDecompStmt_holds`, as in
`A1R2.a1r2_ae_evalReg_growth`), and the uniform `Γ⁰` limit (`A1RF.ae_flowPhiYc_tendstoUniformlyOn`).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RF

open F1 B3d.ZipLen Thm18Asm

/-- Integrability of the circle values of a regular field along a pulled-back folded circle. -/
theorem integrable_evalReg_fc_loop {Z : FieldSample}
    (hZc : IsRegularWith Z (fun q => evalReg Z (foldedCircle q.1 q.2))) {V : ℝ → ℝ}
    (hV : Continuous V) (hV0 : V 0 = 0) {s : ℝ} (hs : 0 ≤ s) (c : ℂ) {r σ : ℝ} (hr : 0 < r)
    (hσ : 0 < σ) :
    Integrable (fun v => evalReg Z (foldedCircle v σ)) ((foldedCircle c r).map (fwdMapInv V s)) := by
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hV s
  have hP : IsProbabilityMeasure ((foldedCircle c r).map (fwdMapInv V s)) :=
    (Measure.isProbabilityMeasure_map_iff (RegCont.aemeasurable_fwdMapInv hV hV0 hs c hr)).2
      inferInstance
  have hcar := ae_supp_unif hV hV0 hM hs le_rfl hr (le_refl (‖c‖ + r))
  have hpm : ContinuousOn (fun v : ℂ => ((v, σ) : ℂ × ℝ)) Hbar :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hg : ContinuousOn ((fun q : ℂ × ℝ => evalReg Z (foldedCircle q.1 q.2)) ∘
      fun v : ℂ => ((v, σ) : ℂ × ℝ)) Hbar :=
    hZc.1.comp hpm fun v hv => ⟨hv, hσ⟩
  exact WedgeUnzip.integrable_of_continuousOn_of_carried hg
    (hcar.mono fun v hv => ⟨le_of_lt (show (0 : ℝ) < v.im from hv.1), hv.2⟩)

/-- **Per-loop uniform convergence for the rescaled wedge field** (deterministic). -/
theorem loopUC_of_Z {κ : ℝ} (hκ : 0 < κ) {X Z y : FieldSample} {FX : ℂ × ℝ → ℝ}
    (hFX : IsRegularWith X FX) {G : ℂ → ℝ} (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hS1 : ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ X V ρ p) L (𝓝[>] 0) (flowBox m))
    {Q b : ℝ} (hb : 0 < b) (hy : avgReg y = avgReg (rescale Z Q b))
    {t : ℝ} (ht : 0 < t) {ρ : ℝ} (hρ : 0 < ρ) (R : ℝ) :
    TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => ∫ u, avgReg y k u
        ∂((foldedCircle z ρ).map (fwdMapInv (fun r => V (b ^ 2 * max r 0) / b) t)))
      (fun z => evalReg y
        ((foldedCircle z ρ).map (fwdMapInv (fun r => V (b ^ 2 * max r 0) / b) t)))
      atTop (Hbar ∩ closedBall 0 R) := by
  set W : ℝ → ℝ := fun r => V (b ^ 2 * max r 0) / b with hWdef
  set Wb : ℝ → ℝ := fun r => V (b ^ 2 * r) / b with hWbdef
  have hWc : Continuous W := by rw [hWdef]; fun_prop
  have hW0 : W 0 = 0 := by simp [hWdef, hV0]
  have hWbc : Continuous Wb := by rw [hWbdef]; fun_prop
  have hWb0 : Wb 0 = 0 := by simp [hWbdef, hV0]
  have hEqW : EqOn W Wb (Icc 0 t) := fun r hr => by simp [hWdef, hWbdef, max_eq_left hr.1]
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hbt : 0 ≤ b ^ 2 * t := by positivity
  -- Loewner scaling
  have hscale : ∀ w ∈ H, (b : ℂ) * fwdMapInv W t w = fwdMapInv V (b ^ 2 * t) ((b : ℂ) * w) := by
    intro w hw
    rw [RegCont.fwdMapInv_congr hWc hW0 hWbc hWb0 hEqW ⟨ht.le, le_rfl⟩ hw,
      RS.fwdMapInv_scale hV hV0 hb ht.le hw]
    field_simp
  -- regularity of `Z` and of its dilation
  have hFl := LogSingGood.regular_add_Lf hFX (Real.sqrt κ - 2 / Real.sqrt κ)
  have hZF := GoodSample.gs_add_ofFun hFl hGc.continuousOn
  have hZfc' : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → Z (foldedCircle d r) =
      (X + ofFun (LogSingGood.Lf (Real.sqrt κ - 2 / Real.sqrt κ)) + ofFun G)
        (foldedCircle d r) := fun d hd r hr => hZfc d hd r hr
  obtain ⟨FZ, hZ⟩ : IsRegularSample Z := ⟨_, WedgeUnzip.isRegularWith_of_fc hZfc' hZF⟩
  have hZc : IsRegularWith Z (fun q => evalReg Z (foldedCircle q.1 q.2)) := hZ.congr_evalReg
  have hres := hZc.rescale' Q hb
  have havg : ∀ k : ℕ, ∀ u ∈ Hbar, avgReg y k u =
      evalReg Z (foldedCircle ((b : ℂ) * u) (b * radius k)) + Q * Real.log b := by
    intro k u hu
    rw [hy]
    exact avgReg_eq_of_regular hres k hu
  -- the parameter box
  obtain ⟨m, hm⟩ := exists_nat_gt (b ^ 2 * t + b * |R| + b * ρ + 1 / (b * ρ))
  have hbρ : 0 < b * ρ := mul_pos hb hρ
  have hbR : 0 ≤ b * |R| := by positivity
  have hiρ : 0 < 1 / (b * ρ) := by positivity
  have hqS : ∀ z ∈ Hbar ∩ closedBall (0 : ℂ) R,
      ((0 : ℝ), b ^ 2 * t, (b : ℂ) * z, b * ρ) ∈ flowBox m := by
    intro z hz
    have hzR : ‖z‖ ≤ R := by
      have := hz.2; rwa [mem_closedBall, dist_zero_right] at this
    have hzR' : ‖z‖ ≤ |R| := hzR.trans (le_abs_self R)
    have hre : |z.re| ≤ |R| := (Complex.abs_re_le_norm z).trans hzR'
    have him : z.im ≤ |R| := (Complex.im_le_norm z).trans hzR'
    have him0 : 0 ≤ z.im := hz.1
    have hm2 : 1 < (m : ℝ) * (b * ρ) := by
      have h1 : 1 / (b * ρ) < m := by linarith
      rw [div_lt_iff₀ hbρ] at h1; linarith
    refine ⟨⟨le_rfl, by positivity⟩, ⟨hbt, by linarith⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [Complex.re_ofReal_mul]
      have := abs_le.1 (show |b * z.re| ≤ b * |R| by
        rw [abs_mul, abs_of_pos hb]; exact mul_le_mul_of_nonneg_left hre hb.le)
      linarith
    · simp only [Complex.re_ofReal_mul]
      have := abs_le.1 (show |b * z.re| ≤ b * |R| by
        rw [abs_mul, abs_of_pos hb]; exact mul_le_mul_of_nonneg_left hre hb.le)
      linarith
    · simp only [Complex.im_ofReal_mul]; positivity
    · simp only [Complex.im_ofReal_mul]
      have := mul_le_mul_of_nonneg_left him hb.le
      linarith
    · rw [div_le_iff₀ (by positivity)]
      nlinarith
    · linarith
  obtain ⟨L, hL⟩ := hS1 m
  obtain ⟨L', hL'⟩ := tendstoUniformlyOn_Zpair hκ hFX hGc hZfc hV hV0 hfy hL
  -- support of the scaled loops, for integrability
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hV (b ^ 2 * t)
  -- the pairings of `y` are the scaled pairings of `Z`
  have hpair : ∀ k : ℕ, ∀ z ∈ Hbar ∩ closedBall (0 : ℂ) R,
      ∫ u, avgReg y k u ∂((foldedCircle z ρ).map (fwdMapInv W t)) =
        (∫ v, evalReg Z (foldedCircle v (b * radius k))
          ∂((foldedCircle ((b : ℂ) * z) (b * ρ)).map (fwdMapInv V (b ^ 2 * t)))) +
          Q * Real.log b := by
    intro k z hz
    have hσ : 0 < b * radius k := mul_pos hb (radius_pos k)
    have hmg : AEMeasurable (fwdMapInv W t) (foldedCircle z ρ) :=
      RegCont.aemeasurable_fwdMapInv hWc hW0 ht.le z hρ
    have hmg' : AEMeasurable (fwdMapInv V (b ^ 2 * t)) (foldedCircle ((b : ℂ) * z) (b * ρ)) :=
      RegCont.aemeasurable_fwdMapInv hV hV0 hbt _ hbρ
    have hak : Measurable (avgReg y k) :=
      (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
    have hEm : Measurable fun v : ℂ => evalReg Z (foldedCircle v (b * radius k)) :=
      B3d.ZipLen.measurable_evalReg_fc Z _
    -- integrability of the `Z` part
    have hint := integrable_evalReg_fc_loop hZc hV hV0 hbt ((b : ℂ) * z) hbρ hσ
    have hP0 : IsProbabilityMeasure ((foldedCircle z ρ).map (fwdMapInv W t)) :=
      (Measure.isProbabilityMeasure_map_iff hmg).2 inferInstance
    have hmul : Measurable fun w : ℂ => (b : ℂ) * w := measurable_const_mul _
    have hEg : AEStronglyMeasurable
        (fun x => evalReg Z (foldedCircle (fwdMapInv V (b ^ 2 * t) x) (b * radius k)))
        ((foldedCircle z ρ).map fun w => (b : ℂ) * w) := by
      rw [Thm18Asm.foldedCircle_map_mul hb]
      exact (hEm.comp_aemeasurable hmg').aestronglyMeasurable
    have hint1 := (integrable_map_measure hEm.aestronglyMeasurable hmg').1 hint
    rw [← Thm18Asm.foldedCircle_map_mul hb] at hint1
    have hint2 : Integrable (fun w => evalReg Z (foldedCircle (fwdMapInv V (b ^ 2 * t)
        ((b : ℂ) * w)) (b * radius k))) (foldedCircle z ρ) :=
      (integrable_map_measure hEg hmul.aemeasurable).1 hint1
    rw [integral_map hmg' hEm.aestronglyMeasurable, ← Thm18Asm.foldedCircle_map_mul hb,
      integral_map hmul.aemeasurable hEg]
    rw [integral_map hmg hak.aestronglyMeasurable]
    have hcongr : (fun w => avgReg y k (fwdMapInv W t w)) =ᵐ[foldedCircle z ρ]
        fun w => evalReg Z (foldedCircle (fwdMapInv V (b ^ 2 * t) ((b : ℂ) * w))
          (b * radius k)) + Q * Real.log b := by
      filter_upwards [TwoPoint.foldedCircle_ae_mem_H z hρ] with w hw
      rw [havg k _ (F1.fwdMapInv_mem_Hbar W t w), hscale w hw]
    rw [integral_congr_ae hcongr, integral_add hint2 (integrable_const _), integral_const]
    simp
  -- uniform convergence
  have hσk : Tendsto (fun k : ℕ => b * radius k) atTop (𝓝[>] 0) :=
    (F1.tendsto_mul_nhdsGT_zero hb).comp RegClosure.tendsto_radius_nhdsGT
  have hU : TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => ∫ u, avgReg y k u
        ∂((foldedCircle z ρ).map (fwdMapInv W t)))
      (fun z => L' (b ^ 2 * t, (b : ℂ) * z, b * ρ) + Q * Real.log b) atTop
      (Hbar ∩ closedBall 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h1 := hσk.eventually ((Metric.tendstoUniformlyOn_iff.1 hL') ε hε)
    filter_upwards [h1] with k hk z hz
    rw [hpair k z hz, Real.dist_eq]
    have := hk (b ^ 2 * t, (b : ℂ) * z, b * ρ) (hqS z hz)
    rw [Real.dist_eq] at this
    rw [show ∀ a c d : ℝ, a + d - (c + d) = a - c by intros; ring]
    exact this
  refine hU.congr_right fun z hz => ?_
  exact ((hU.tendsto_at hz).limUnder_eq).symm

/-- **`A1RFLoopUCStmt` holds.** -/
theorem a1rfLoopUCStmt_holds : A1RFLoopUCStmt := by
  intro γ Ω _ P _ B Y hS hIn
  have hP := isPStarSample_of_setting hS
  obtain ⟨hκ, hκ4, -⟩ := id hP
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hInd, hB, hIB, hae⟩ :=
    WedgeUnzip.pStarRealizeStmt_holds (γ ^ 2) P Y B hP
  obtain ⟨Ω₃, _, Q₃, _, X'', G, hX'', hB2, hI2, hdec⟩ :=
    WedgeUnzip.WDec.wedgeDecompStmt_holds (γ ^ 2) hκ hκ4 (P.prod Q) X' A B'' hX hA hInd hB hIB
  have hγ' : 0 < Real.sqrt (γ ^ 2) := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt (γ ^ 2) < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα := F2.alpha_lt_Qc' hγ' hγ2
  have hspec := Wire2.ae_wedge_canonical_spec hγ' hγ2 hα hX hA hInd
  have lift2 : ∀ {p : Ω × Ω₂ → Prop}, (∀ᵐ ω ∂(P.prod Q), p ω) →
      ∀ᵐ ω ∂((P.prod Q).prod Q₃), p ω.1 := fun h =>
    ae_of_ae_map measurable_fst.aemeasurable (by rw [measurePreserving_fst.map_eq]; exact h)
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) (WedgeUnzip.ae_of_ae_prod_fst (Q := Q₃) ?_)
  filter_upwards [lift2 hae, lift2 hspec, hdec, RegSample.ae_isRegularSample hX'',
    ae_flowPhiYc_tendstoUniformlyOn hκ hκ4 hB2 hX'' hI2,
    WedgeUnzip.ae_core2Y_inputs hκ hκ4 hB2 hX'' hI2, hB2.cont, hB2.eval_zero_ae_eq_zero]
    with ω hR hsp hD hXreg hS1 hin hc h0
  intro t ht ρ hρ R
  obtain ⟨havg, hcfg⟩ := hR
  obtain ⟨hGc, -, hZfc⟩ := hD
  obtain ⟨FX, hFX⟩ := hXreg
  set s := Real.sqrt (γ ^ 2) with hs
  set Z := F2.zU s X' A ω.1 with hZ
  set b := scaleParam s Z with hbdef
  have hb : 0 < b := hsp.1
  set V : ℝ → ℝ := drive (γ ^ 2) (fun t (ω' : (Ω × Ω₂) × Ω₃) => B'' t ω'.1) ω with hVdef
  have hV : Continuous V := by
    rw [hVdef]; unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hV0 : V 0 = 0 := by simp [hVdef, drive, h0]
  have hW : drive (γ ^ 2) B ω.1.1 = fun r => V (b ^ 2 * max r 0) / b := by
    have h2 : (canonConfig s (Z, drive (γ ^ 2) B'' ω.1)).2 = drive (γ ^ 2) B ω.1.1 :=
      congrArg Prod.snd hcfg
    rw [← h2]
    rfl
  have hy : avgReg (Y ω.1.1) = avgReg (rescale Z (Qc s) b) := havg
  rw [hW]
  exact loopUC_of_Z hκ hFX hGc hZfc hV hV0 hin.2.2.2.2.2.2 hS1 hb hy ht hρ R

end A1RF
end R18
end QuantumZipper
