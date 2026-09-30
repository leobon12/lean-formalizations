import QuantumZipper.Proofs.Thm18.A1RS2Z

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (9): (R2) for the canonical wedge field (rescaling of the unscaled field `Z`)

With `y` having the regularized averages of `rescale Z Q b` and the driver
`W(r) = V(b² r⁺)/b` (as in `A1RF.loopUC_of_Z`):

* `evalReg_loop_rescale`: `evalReg y ((f_t⁻¹)_* fc(z, ρ)) = evalReg Z ((g^V_{b²t})_* fc(bz, bρ)) +
  Q log b` (the dyadic pairing identity of `loopUC_of_Z` and the uniform `Z` limit);
* `continuousOn_evalReg_loop_y`: hence `(t, z, ρ) ↦ evalReg y ((f_t⁻¹)_* fc(z, ρ))` is continuous
  on `(0,∞) × ℍ̄ × (0,∞)` (`continuousOn_evalReg_loop_Z`).

Own bookkeeping (Loewner scaling as in `loopUC_of_Z`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm F1 B3d.ZipLen

variable {κ : ℝ} {X Z : FieldSample} {FX : ℂ × ℝ → ℝ} {G : ℂ → ℝ} {V : ℝ → ℝ}

/-- **The per-loop regularized pairings of the rescaled field.** -/
theorem evalReg_loop_rescale (hκ : 0 < κ) (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    (hV : Continuous V) (hV0 : V 0 = 0)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hS1 : ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ X V ρ p) L (𝓝[>] 0) (flowBox m)) {Q b : ℝ} (hb : 0 < b)
    {y : FieldSample} (hy : avgReg y = avgReg (rescale Z Q b))
    {t : ℝ} (ht : 0 < t) {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : z ∈ Hbar) :
    evalReg y ((foldedCircle z ρ).map (fwdMapInv (fun r => V (b ^ 2 * max r 0) / b) t)) =
      evalReg Z ((foldedCircle ((b : ℂ) * z) (b * ρ)).map (fwdMapInv V (b ^ 2 * t))) +
        Q * Real.log b := by
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
    exact A1RF.avgReg_eq_of_regular hres k hu
  have hbρ : 0 < b * ρ := mul_pos hb hρ
  -- the pairings of `y` are the scaled pairings of `Z`
  have hpair : ∀ k : ℕ, ∀ z ∈ Hbar,
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
    have hint := A1RF.integrable_evalReg_fc_loop hZc hV hV0 hbt ((b : ℂ) * z) hbρ hσ
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
  -- the uniform `Z` limit at the scaled parameter
  obtain ⟨m, hm⟩ := exists_nat_gt (b ^ 2 * t + b * ‖z‖ + b * ρ + 1 / (b * ρ))
  have hbz : 0 ≤ b * ‖z‖ := by positivity
  have hiρ : 0 < 1 / (b * ρ) := by positivity
  have hq : ((b ^ 2 * t, (b : ℂ) * z, b * ρ) : ℝ × ℂ × ℝ) ∈ sliceBox m := by
    have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have him : z.im ≤ ‖z‖ := Complex.im_le_norm z
    have him0 : 0 ≤ z.im := hz
    have hm2 : 1 < (m : ℝ) * (b * ρ) := by
      have h1 : 1 / (b * ρ) < m := by linarith
      rw [div_lt_iff₀ hbρ] at h1; linarith
    have hre' := abs_le.1 (show |b * z.re| ≤ b * ‖z‖ by
      rw [abs_mul, abs_of_pos hb]; exact mul_le_mul_of_nonneg_left hre hb.le)
    show ((0 : ℝ), b ^ 2 * t, (b : ℂ) * z, b * ρ) ∈ flowBox m
    refine ⟨⟨le_rfl, by positivity⟩, ⟨hbt, by linarith⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [Complex.re_ofReal_mul]; linarith
    · simp only [Complex.re_ofReal_mul]; linarith
    · simp only [Complex.im_ofReal_mul]; positivity
    · simp only [Complex.im_ofReal_mul]
      have := mul_le_mul_of_nonneg_left him hb.le
      linarith
    · rw [div_le_iff₀ (by positivity)]
      nlinarith
    · linarith
  obtain ⟨L, hL⟩ := hS1 m
  obtain ⟨L', hL'⟩ := A1RF.tendstoUniformlyOn_Zpair hκ hFX hGc hZfc hV hV0 hfy hL
  have h1 := hL'.tendsto_at hq
  have hσk : Tendsto (fun k : ℕ => b * radius k) atTop (𝓝[>] 0) :=
    (F1.tendsto_mul_nhdsGT_zero hb).comp RegClosure.tendsto_radius_nhdsGT
  have hyt : Tendsto (fun k : ℕ => ∫ u, avgReg y k u ∂((foldedCircle z ρ).map (fwdMapInv W t)))
      atTop (𝓝 (L' (b ^ 2 * t, (b : ℂ) * z, b * ρ) + Q * Real.log b)) :=
    ((h1.comp hσk).add_const _).congr fun k => (hpair k z hz).symm
  have hmf : Measurable (fwdMapInv V (b ^ 2 * t)) := RTBeur.measurable_fwdMapInv_rt hV hV0 hbt
  have hdyZ : ∀ j : ℕ, ∫ v, avgReg Z j v
      ∂((foldedCircle ((b : ℂ) * z) (b * ρ)).map (fwdMapInv V (b ^ 2 * t))) =
      ∫ v, evalReg Z (foldedCircle v (radius j))
        ∂((foldedCircle ((b : ℂ) * z) (b * ρ)).map (fwdMapInv V (b ^ 2 * t))) := by
    intro j
    have hae : ∀ᵐ v ∂((foldedCircle ((b : ℂ) * z) (b * ρ)).map (fwdMapInv V (b ^ 2 * t))),
        v ∈ Hbar := (ae_map_iff hmf.aemeasurable isClosed_Hbar.measurableSet).2
          (ae_of_all _ fun w => F1.fwdMapInv_mem_Hbar V _ _)
    refine integral_congr_ae ?_
    filter_upwards [hae] with v hv
    exact A1RF.avgReg_eq_of_regular hZc j hv
  have hZt : Tendsto (fun j : ℕ => ∫ v, avgReg Z j v
      ∂((foldedCircle ((b : ℂ) * z) (b * ρ)).map (fwdMapInv V (b ^ 2 * t)))) atTop
      (𝓝 (L' (b ^ 2 * t, (b : ℂ) * z, b * ρ))) :=
    (h1.comp RegClosure.tendsto_radius_nhdsGT).congr fun j => (hdyZ j).symm
  have e1 : evalReg y ((foldedCircle z ρ).map (fwdMapInv W t)) =
      L' (b ^ 2 * t, (b : ℂ) * z, b * ρ) + Q * Real.log b := hyt.limUnder_eq
  have e2 : evalReg Z ((foldedCircle ((b : ℂ) * z) (b * ρ)).map (fwdMapInv V (b ^ 2 * t))) =
      L' (b ^ 2 * t, (b : ℂ) * z, b * ρ) := hZt.limUnder_eq
  rw [e1, e2]

/-- **Continuity of the per-loop regularized pairings of the rescaled field.** -/
theorem continuousOn_evalReg_loop_y (hκ : 0 < κ) (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    (hV : Continuous V) (hV0 : V 0 = 0)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hS1 : ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ X V ρ p) L (𝓝[>] 0) (flowBox m)) {Q b : ℝ} (hb : 0 < b)
    {y : FieldSample} (hy : avgReg y = avgReg (rescale Z Q b)) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => evalReg y ((foldedCircle q.2.1 q.2.2).map
      (fwdMapInv (fun r => V (b ^ 2 * max r 0) / b) q.1))) (Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)) := by
  have hZc := continuousOn_evalReg_loop_Z hκ hFX hGc hZfc hV hV0 hfy hS1
  have hmaps : MapsTo (fun q : ℝ × ℂ × ℝ => ((b ^ 2 * q.1, (b : ℂ) * q.2.1, b * q.2.2) :
      ℝ × ℂ × ℝ)) (Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)) (Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)) := by
    rintro ⟨t, z, ρ⟩ ⟨ht, hz, hρ⟩
    refine ⟨show (0 : ℝ) < b ^ 2 * t from mul_pos (by positivity) ht, ?_,
      show (0 : ℝ) < b * ρ from mul_pos hb hρ⟩
    show 0 ≤ ((b : ℂ) * z).im
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg hb.le hz
  have hfc : Continuous fun q : ℝ × ℂ × ℝ =>
      ((b ^ 2 * q.1, (b : ℂ) * q.2.1, b * q.2.2) : ℝ × ℂ × ℝ) := by fun_prop
  have hcomp := hZc.comp hfc.continuousOn hmaps
  refine (hcomp.add (continuousOn_const (c := Q * Real.log b))).congr fun q hq => ?_
  exact evalReg_loop_rescale hκ hFX hGc hZfc hV hV0 hfy hS1 hb hy hq.1 hq.2.2 hq.2.1

/-- **(R2) for the Theorem 1.8 field.** A.s., for both sides, `(p, ρ) ↦ evalReg Y (ν_{p,ρ})` is
continuous on `smearU × (0, ∞)`. -/
theorem ae_continuousOn_smearFam_pos (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (left : Bool) :
    ∀ᵐ ω ∂P, ContinuousOn (fun z : (Fin 4 → ℝ) × ℝ =>
      evalReg (Y ω) (smearFam (drive (γ ^ 2) B ω) left z.1 z.2)) (smearU ×ˢ Ioi 0) := by
  have hLc : ∀ᵐ ω ∂P, ContinuousOn (fun q : ℝ × ℂ × ℝ => evalReg (Y ω)
      ((foldedCircle q.2.1 q.2.2).map (fwdMapInv (drive (γ ^ 2) B ω) q.1)))
      (Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)) := by
    revert hS hIn
    intro hS hIn
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
      A1RF.ae_flowPhiYc_tendstoUniformlyOn hκ hκ4 hB2 hX'' hI2,
      WedgeUnzip.ae_core2Y_inputs hκ hκ4 hB2 hX'' hI2, hB2.cont, hB2.eval_zero_ae_eq_zero]
      with ω hR hsp hD hXreg hS1 hin hc h0
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
    exact continuousOn_evalReg_loop_y hκ hFX hGc hZfc hV hV0 hin.2.2.2.2.2.2 hS1 hb hy
  filter_upwards [A1RF.a1rfLoopUCStmt_holds γ P B Y hS hIn, ae_g1zDrvGood hS hIn, hIn.1, hLc]
    with ω hl hG hgood hc
  obtain ⟨F, hF⟩ := hgood.1.1
  exact continuousOn_evalReg_smearFam hF hG left hc fun t ht ρ hρ R => hl t ht ρ hρ R

end A1RS
end R18
end QuantumZipper
