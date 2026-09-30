import QuantumZipper.Proofs.Zipper.E1Window
import QuantumZipper.Proofs.GFF.CoordRegSwap
import QuantumZipper.Proofs.GFF.CircleMeanValue
import QuantumZipper.Proofs.LQG.WedgeRestriction
import QuantumZipper.Proofs.Zipper.B2Reg
import QuantumZipper.Field.CoordsFull

/-!
# E1-PW: the Palm formula on a live window (fixed driver)

`handoff/E1-PLAN.md`, sub-node **E1-PW**. For a fixed driver `v`, a live negative window `(a,b)`,
a normalizer `ϖ` and a free field `X'`:

```
∫⁻ ω', ∫⁻ x, G x (coordsFull (addConst (𝔥₀ + X') (−m)))
    ∂qBoundaryMeasureOn √κ (addConst (hFix κ v t X') (−m)) (Ioo a b) ∂P'
  = ∫⁻ x in Ioo a b, ρ_t(x) · ∫⁻ ω', G x (coordsFull (targetField κ v t ϖ x (X' ω'))) ∂P'
```

with `m = mFix κ v t ϖ X'` and `ρ_t = rhoT κ v t ϖ`. Paper: Sheffield, *Conformal weldings of
random surfaces*, arXiv:1012.4797, Lemma 5.6 and its proof (pp. 66–68: the Palm point `x` of the
boundary measure weighted law, and "given `f_t`, `h₀ = h̃∘f_t + ĥ_t`"); route of blueprint
`E_BRANCH_BLUEPRINT.md` §4 E1 (Palm formula plus coordinate change).

Proof. (1) The additive constant: `qBoundaryMeasureOn_addConst` (LocalRule), with
`m = (𝔥₀+X')(ϖ_t) + q_t` a.s. (RC1, `CoordReg.ae_evalReg_h0rev_eq_frostman'`, for the Frostman
measure `ϖ_t = F_*ϖ`: `B2.isFrostman_map_revMap_of_compact`, `B2.map_revMap_support_of_compact`).
(2) E1-CC (`ae_lintegral_hFix_eq`) with `g = G(Φ⁻¹ ·)`, `Φ` an order isomorphism extending `F`.
(3) The Palm formula of the free field with mean `𝔥₀` on the image window `(F a, F b)`
(`palm_formula_Ioo`, from `PalmNorm.palm_formula_norm_local` and E1-EX), with `h'` continuous and
equal to `𝔥₀` off a small disc around `0`. (4) The change of variables `y = F x`
(`lintegral_image_realRevMap`, E1-CV).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open PalmNorm B2 CoordsFull

variable {Ω : Type*} [MeasurableSpace Ω] {P' : Measure Ω}
variable {κ t a b : ℝ} {v : ℝ → ℝ} {X' : Ω → FieldSample} {ϖ : Measure ℂ}

/-! ## 1. Measurability of the right side -/

theorem measurable_kPot (ϖ : Measure ℂ) [SFinite ϖ] : Measurable (kPot ϖ) :=
  (measurable_neumannH.stronglyMeasurable.integral_prod_right' (ν := ϖ)).measurable

theorem measurable_rhoNorm {γ : ℝ} {h : ℂ → ℝ} (hh : Measurable h) (ϖ : Measure ℂ) [SFinite ϖ] :
    Measurable (rhoNorm γ h ϖ) := by
  unfold rhoNorm
  have h1 : Measurable fun x : ℝ => h (x : ℂ) := hh.comp Complex.measurable_ofReal
  have h2 : Measurable fun x : ℝ => kPot ϖ (x : ℂ) :=
    (measurable_kPot ϖ).comp Complex.measurable_ofReal
  exact (((((measurable_const.mul h1).div_const _).sub measurable_const).sub
    (measurable_const.mul h2)).add measurable_const).exp

theorem measurable_ofFun_shiftFun {γ : ℝ} {h : ℂ → ℝ} (hh : Measurable h) (ϖ : Measure ℂ)
    [SFinite ϖ] (ν : Measure ℂ) [SFinite ν] :
    Measurable fun x : ℝ => ofFun (shiftFun γ h ϖ x) ν := by
  have hj : Measurable fun p : ℝ × ℂ => shiftFun γ h ϖ p.1 p.2 := by
    unfold shiftFun
    exact (hh.comp measurable_snd).add (measurable_const.mul
      ((measurable_neumannH.comp ((Complex.measurable_ofReal.comp measurable_fst).prodMk
        measurable_snd)).sub ((measurable_kPot ϖ).comp measurable_snd)))
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

/-! ## 2. E1-PW -/

theorem h0rev_eq_log (κ : ℝ) : h0rev κ = fun z => 2 / Real.sqrt κ * Real.log ‖z‖ := rfl

/-- **E1-PW** (`handoff/E1-PLAN.md`): the Palm formula on a live negative window, fixed driver. -/
theorem lintegral_palm_window [IsProbabilityMeasure P'] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hX : IsFreeGFFModConstH X' P') (hϖ : IsNormalizer ϖ) (hv : Continuous v) (hv0 : v 0 = 0)
    (ht : 0 ≤ t) (hab : a < b) (hw : ∀ x ∈ Icc a b, x < 0 ∧ IsLive v t x)
    {G : ℝ → (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) :
    ∫⁻ ω', ∫⁻ x, G x (coordsFull (addConst (ofFun (h0rev κ) + X' ω')
        (-(mFix κ v t ϖ (X' ω')))))
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ v t (X' ω'))
          (-(mFix κ v t ϖ (X' ω')))) (Ioo a b) ∂P' =
      ∫⁻ x in Ioo a b, ENNReal.ofReal (rhoT κ v t ϖ x) *
        ∫⁻ ω', G x (coordsFull (targetField κ v t ϖ x (X' ω'))) ∂P' := by
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  have hγ2 : γ < 2 := by
    rw [hγdef, show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  set ϖ' := varpiT v t ϖ with hϖ'def
  set q := qt κ v t ϖ with hqdef
  set F := realRevMap v t with hFdef
  obtain ⟨Φ, hΦ⟩ := exists_orderIso_eq_realRevMap hv ht hab fun x hx => (hw x hx).2
  have hFneg : ∀ x ∈ Icc a b, F x < 0 := fun x hx =>
    realRevMap_neg hv hv0 ht (hw x hx).1 (hw x hx).2
  have haI : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hbI : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hΦsymm : ∀ x ∈ Icc a b, Φ.symm (F x) = x := fun x hx => by
    rw [← show Φ x = F x from hΦ x hx, OrderIso.symm_apply_apply]
  -- the normalizer `ϖ_t`
  haveI := hϖ.prob
  have hm := TwoPoint.measurable_revMap hv ht
  have : IsProbabilityMeasure ϖ' := by simp only [hϖ'def, varpiT]; infer_instance
  have hϖ'1 : ϖ' univ = 1 := measure_univ
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hfr⟩ := hϖ.frost
  obtain ⟨R, hR⟩ := B2.map_revMap_support_of_compact hv ht hKc hKH hK0
  obtain ⟨C', hC'⟩ := B2.isFrostman_map_revMap_of_compact hv ht hKc hKH hK0 hα.le hfr
  have hadm : IsAdmissibleH ϖ' := FrostmanReg.isAdmissibleH_of_frostman hR hC' hα
  -- the coordinate measures
  set μ : ℕ → Measure ℂ := fun j => foldedCircle (fullIndex j).1 (fullIndex j).2 with hμdef
  have hμ : ∀ j, IsAdmissibleH (μ j) := fun j => by
    simp only [hμdef]
    rw [← CoordReg.foldedCircle_foldH]
    refine isAdmissibleH_foldedCircle (CircleFubini.foldH_mem_Hbar' _) ?_
    have key : ∀ p : ℤ × ℤ × ℕ × ℕ × ℕ, (0 : ℝ) < ((p.2.2.2.1 : ℝ) + 1) / (2 : ℝ) ^ p.2.2.2.2 :=
      fun p => by positivity
    exact key (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ × ℕ) j)
  have hμ1 : ∀ j, (μ j univ).toReal = 1 := fun j => by simp [hμdef]
  -- the continuous modification `h'` of `𝔥₀` near the image window
  set c0 : ℝ := -(F b) / 2 with hc0
  have hc0pos : 0 < c0 := by have := hFneg b hbI; rw [hc0]; linarith
  set h' : ℂ → ℝ := fun z => 2 / Real.sqrt κ * Real.log (max ‖z‖ c0) with hh'def
  have hh' : Continuous h' := continuous_const.mul
    ((continuous_norm.max continuous_const).log fun z => (lt_max_of_lt_right hc0pos).ne')
  set W0 : Set ℂ := {z | c0 < ‖z‖} with hW0
  have hW0o : IsOpen W0 := isOpen_lt continuous_const continuous_norm
  have hEq : EqOn (h0rev κ) h' W0 := fun z hz => by
    have hz' : c0 < ‖z‖ := hz
    simp only [h0rev_eq_log, hh'def, max_eq_left hz'.le]
  have habW : ∀ y ∈ Icc (F a) (F b), (y : ℂ) ∈ W0 := fun y hy => by
    show c0 < ‖(y : ℂ)‖
    have hb := hFneg b hbI
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (hy.2.trans_lt hb)]
    rw [hc0]; linarith [hy.2]
  obtain ⟨N, hN⟩ := exists_nat_ge (max |F a| |F b|)
  have habN : Icc (F a) (F b) ⊆ Icc (-(N : ℝ)) N := fun y hy =>
    ⟨by linarith [hy.1, neg_abs_le (F a), le_max_left |F a| |F b|],
      by linarith [hy.2, hFneg b hbI, le_abs_self (F b), le_max_right |F a| |F b|]⟩
  have hh0m : Measurable (h0rev κ) := by
    rw [h0rev_eq_log]; exact measurable_const.mul (Real.measurable_log.comp measurable_norm)
  have hhϖ : Integrable (h0rev κ) ϖ' := by
    rw [h0rev_eq_log]; exact (WedgeRes.integrable_log_norm_adm hadm).const_mul _
  have hhμ : ∀ j, Integrable (h0rev κ) (μ j) := fun j => by
    rw [h0rev_eq_log]; exact (WedgeRes.integrable_log_norm_adm (hμ j)).const_mul _
  -- the test function of the Palm formula
  set eq : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * -q / 2)) with heq
  set φ : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun c y => eq * G (Φ.symm y) (fun j => c j + -q) with hφdef
  have hφ : Measurable (Function.uncurry φ) := measurable_const.mul (hG.comp
    ((Φ.symm.continuous.measurable.comp measurable_snd).prodMk
      (measurable_pi_iff.2 fun j => ((measurable_pi_apply j).comp measurable_fst).add
        measurable_const)))
  have hK : Measurable fun y => ∫⁻ ω, φ (fun j => normAt ϖ' (ofFun (shiftFun γ (h0rev κ) ϖ' y)
      + X' ω) (μ j)) y ∂P' := by
    refine Measurable.lintegral_prod_right' (f := fun p : ℝ × Ω => φ (fun j =>
      normAt ϖ' (ofFun (shiftFun γ (h0rev κ) ϖ' p.1) + X' p.2) (μ j)) p.1) ?_
    refine hφ.comp ((measurable_pi_iff.2 fun j => ?_).prodMk measurable_fst)
    simp only [normAt, addConst, Pi.add_apply]
    exact (((measurable_ofFun_shiftFun hh0m ϖ' (μ j)).comp measurable_fst).add
      ((hX.measurable_coord _).comp measurable_snd)).add
      ((((measurable_ofFun_shiftFun hh0m ϖ' ϖ').comp measurable_fst).add
        ((hX.measurable_coord _).comp measurable_snd)).neg.mul measurable_const)
  have hPalm := palm_formula_Ioo (P := P') (μ := μ) hX hγ hγ2 habN hh' hW0o habW hEq hadm hϖ'1
    hμ hhϖ hhμ (ae_exists_isVagueLimitR_normAt_h0rev hX hκ hκ4 hϖ'1) hφ
    (measurable_rhoNorm hh0m ϖ') hK
  -- the left side, pathwise
  have hL : ∀ᵐ ω ∂P', ∫⁻ x, G x (coordsFull (addConst (ofFun (h0rev κ) + X' ω)
        (-(mFix κ v t ϖ (X' ω)))))
        ∂qBoundaryMeasureOn γ (addConst (hFix κ v t (X' ω)) (-(mFix κ v t ϖ (X' ω)))) (Ioo a b) =
      ∫⁻ y in Ioo (F a) (F b), φ (fun j => normAt ϖ' (ofFun (h0rev κ) + X' ω) (μ j)) y
        ∂qBoundaryMeasure γ (normAt ϖ' (ofFun (h0rev κ) + X' ω)) := by
    filter_upwards [CoordReg.ae_evalReg_h0rev_eq_frostman' hX hR hC' hα κ,
      CoordReg.ae_isRegularSample_coordChange_h0rev' hv ht hX κ (Qc γ),
      ae_lintegral_hFix_eq hκ hκ4 hX hv hv0 ht hab hw, RegSample.ae_isRegularSample hX,
      ae_exists_isVagueLimitR_normAt_h0rev hX hκ hκ4 hϖ'1] with ω h1 h2 h3 h4 h5
    set Y := ofFun (h0rev κ) + X' ω with hY
    set r := Y ϖ' with hr
    have h1' : evalReg Y ϖ' = r := h1
    have hmr : mFix κ v t ϖ (X' ω) = r + q := by
      show evalReg Y ϖ' + q = r + q
      rw [h1']
    have hYreg : IsRegularSample Y := by
      have h4' : IsRegularSample (X' ω + ofFun (LogSing.logPot (-(2 / Real.sqrt κ)) 0)) :=
        h4.add_ofFun_log' _ 0
      rwa [logPot_h0rev, add_comm] at h4'
    set cc : ℕ → ℝ := fun j => normAt ϖ' Y (μ j) + -q with hcc
    have hcoord : coordsFull (addConst Y (-(r + q))) = cc := by
      funext j
      simp only [coordsFull, hcc, normAt, addConst]
      rw [hμ1 j]
      simp only [hr]
      ring
    set g : ℝ → ℝ≥0∞ := fun y => G (Φ.symm y) cc with hg
    have hgm : Measurable g :=
      hG.comp (Φ.symm.continuous.measurable.prodMk measurable_const)
    obtain ⟨ν, hν⟩ := h5
    have hloc : qBoundaryMeasureOn γ (normAt ϖ' Y) (Ioo (F a) (F b)) =
        (qBoundaryMeasure γ (normAt ϖ' Y)).restrict (Ioo (F a) (F b)) := by
      rw [qBoundaryMeasure_eq hν]
      exact LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo
        (PalmNorm.isVagueLimitOnR_restrict_of_R hν isOpen_Ioo)
    have hexp : ENNReal.ofReal (Real.exp (γ * -(r + q) / 2)) =
        eq * ENNReal.ofReal (Real.exp (γ * -r / 2)) := by
      rw [heq, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
    have hsupp := qBoundaryMeasureOn_compl γ (hFix κ v t (X' ω)) (Ioo a b)
    calc ∫⁻ x, G x (coordsFull (addConst Y (-mFix κ v t ϖ (X' ω))))
          ∂qBoundaryMeasureOn γ (addConst (hFix κ v t (X' ω)) (-mFix κ v t ϖ (X' ω))) (Ioo a b)
        = ENNReal.ofReal (Real.exp (γ * -(r + q) / 2)) *
            ∫⁻ x, g (F x) ∂qBoundaryMeasureOn γ (hFix κ v t (X' ω)) (Ioo a b) := by
          rw [hmr, LocalRule.qBoundaryMeasureOn_addConst (x := hFix κ v t (X' ω)) h2.rawConverges γ _
              isOpen_Ioo,
            lintegral_smul_measure, smul_eq_mul, hcoord]
          congr 1
          refine lintegral_congr_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp] with x hx
          have hx' : x ∈ Icc a b := Ioo_subset_Icc_self (by simpa using hx)
          simp only [hg, hΦsymm x hx']
      _ = eq * (ENNReal.ofReal (Real.exp (γ * -r / 2)) *
            ∫⁻ y, g y ∂qBoundaryMeasureOn γ Y (Ioo (F a) (F b))) := by
          rw [h3 g hgm, hexp, mul_assoc]
      _ = eq * ∫⁻ y in Ioo (F a) (F b), g y ∂qBoundaryMeasure γ (normAt ϖ' Y) := by
          rw [← hloc, show normAt ϖ' Y = addConst Y (-r) from rfl,
            LocalRule.qBoundaryMeasureOn_addConst hYreg.rawConverges γ _ isOpen_Ioo,
            lintegral_smul_measure, smul_eq_mul]
      _ = _ := (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  rw [lintegral_congr_ae hL, hPalm]
  -- the right side: change of variables `y = F x`
  have hlive : ∀ x ∈ Ioo a b, IsLive v t x := fun x hx => (hw x (Ioo_subset_Icc_self hx)).2
  have himg : F '' Ioo a b = Ioo (F a) (F b) := by
    rw [← (show EqOn Φ F (Ioo a b) from fun x hx => hΦ x (Ioo_subset_Icc_self hx)).image_eq,
      OrderIso.image_Ioo, hΦ a haI, hΦ b hbI]
  rw [← himg, lintegral_image_realRevMap hv ht measurableSet_Ioo hlive]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hx' := Ioo_subset_Icc_self hx
  have hGx : ∀ ω, φ (fun j => normAt ϖ' (ofFun (shiftFun γ (h0rev κ) ϖ' (F x)) + X' ω) (μ j))
      (F x) = eq * G x (coordsFull (targetField κ v t ϖ x (X' ω))) := fun ω => by
    simp only [hφdef, hΦsymm x hx']
    congr 2
    funext j
    simp only [coordsFull, targetField, addConst]
    rw [hμ1 j]
    ring
  show ENNReal.ofReal (Fder v t x) * (ENNReal.ofReal (rhoNorm γ (h0rev κ) ϖ' (F x)) *
    ∫⁻ ω, φ (fun j => normAt ϖ' (ofFun (shiftFun γ (h0rev κ) ϖ' (F x)) + X' ω) (μ j)) (F x) ∂P')
    = _
  simp_rw [hGx]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hρ0 : 0 ≤ rhoNorm γ (h0rev κ) ϖ' (F x) := (Real.exp_pos _).le
  simp only [rhoT, heq]
  rw [ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Fder_pos v t x).le),
    ENNReal.ofReal_mul (Real.exp_pos _).le,
    show Real.exp (γ * -q / 2) = Real.exp (-(γ / 2 * q)) by congr 1; ring]
  ring

end E1
end QuantumZipper
