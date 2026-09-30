import QuantumZipper.Proofs.Zipper.E1Window2

/-!
# E1-FIX (part 2): the window term of E1-PW, pathwise, and its measurability in `ω`

`handoff/E1-PW.md`, items (R1) and (R2) of E1-FIX.

* `ae_window_lhs_eq` (R1): the pathwise (a.s.) identity inside the proof of
  `lintegral_palm_window` (E1-PW): the window integral against the boundary measure of
  `addConst (hFix …) (−m)` equals an integral over the image window `(F a, F b)` against the
  boundary measure of the normalized field `N_{ϖ_t}(𝔥₀ + X')`.
* `aemeasurable_setLIntegral_normAt` (R2): such image-window integrals are a.e. measurable in
  `ω` (measurable modification `Palm.kerI` of the random measure).
* `aemeasurable_window_lhs`: hence the window term of E1-PW is a.e. measurable in `ω`.

Paper: Sheffield, arXiv:1012.4797, Lemma 5.6 and its proof (pp. 66–68). The steps are those of
`E1Window2.lintegral_palm_window` (the identity `hL` there, copied); the measurability is own
bookkeeping (as `hgm` in `E1Window.palm_formula_Ioo`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open PalmNorm B2 CoordsFull

variable {Ω : Type*} [MeasurableSpace Ω] {P' : Measure Ω}
variable {κ t a b : ℝ} {v : ℝ → ℝ} {X' : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **(R2)** The integral of `φ(c_ω, ·)` over a bounded window against the boundary measure of
`N_ϖ(h + X)` is a.e. measurable in `ω`. -/
theorem aemeasurable_setLIntegral_normAt {X : Ω → FieldSample} {h : ℂ → ℝ}
    {μ : ℕ → Measure ℂ} {γ a b : ℝ} (hX : IsFreeGFFModConstH X P')
    (hex : ∀ᵐ ω ∂P', ∃ ν, IsVagueLimitR (bdryApprox γ (normAt ϖ (ofFun h + X ω))) ν)
    {φ : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hφ : Measurable (Function.uncurry φ)) :
    AEMeasurable (fun ω => ∫⁻ x in Ioo a b, φ (fun j => normAt ϖ (ofFun h + X ω) (μ j)) x
      ∂(qBoundaryMeasure γ (normAt ϖ (ofFun h + X ω)))) P' := by
  set Nf : Ω → FieldSample := fun ω => normAt ϖ (ofFun h + X ω) with hNf
  set c : Ω → ℕ → ℝ := fun ω j => Nf ω (μ j) with hc
  set ν : Ω → Measure ℝ := fun ω => qBoundaryMeasure γ (Nf ω) with hν
  have hcm : Measurable c := measurable_pi_iff.2 fun j => by
    simp only [hc, hNf, normAt, addConst, Pi.add_apply]
    exact ((measurable_const.add (hX.measurable_coord _)).add
      ((measurable_const.add (hX.measurable_coord _)).neg.mul measurable_const))
  have hνae : AEMeasurable ν P' := by
    refine LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae (fun μ' => ?_) ?_
    · simp only [hNf, normAt, addConst, Pi.add_apply]
      exact (measurable_const.add (hX.measurable_coord _)).add
        ((measurable_const.add (hX.measurable_coord _)).neg.mul measurable_const)
    · filter_upwards [hex] with ω ⟨ν', hν'⟩
      rw [qBoundaryMeasure_eq hν']; exact hν'
  have hfin : ∀ᵐ ω ∂P', ν ω (Icc a b) < ∞ := by
    filter_upwards [hex] with ω ⟨ν', hν'⟩
    have := hν'.1
    show qBoundaryMeasure γ (Nf ω) (Icc a b) < ∞
    rw [qBoundaryMeasure_eq hν']
    exact isCompact_Icc.measure_lt_top
  have hF : Measurable fun p : Ω × ℝ => (Ioo a b).indicator (φ (c p.1)) p.2 := by
    have := (hφ.comp ((hcm.comp measurable_fst).prodMk measurable_snd)).indicator
      ((measurableSet_Ioo (a := a) (b := b)).preimage measurable_snd)
    exact this
  refine ⟨_, hF.lintegral_kernel_prod_right'
    (κ := Palm.kerI hνae (measurableSet_Icc (a := a) (b := b))), ?_⟩
  filter_upwards [nuMod_ae_eq' hνae hfin] with ω hω
  show ∫⁻ x in Ioo a b, φ (c ω) x ∂ν ω = _
  rw [Palm.kerI_apply, hω, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Icc_self]

/-- **(R1)** The pathwise identity of E1-PW: a.s. the window term equals an integral over the
image window against the boundary measure of `N_{ϖ_t}(𝔥₀ + X')`. -/
theorem ae_window_lhs_eq [IsProbabilityMeasure P'] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hX : IsFreeGFFModConstH X' P') (hϖ : IsNormalizer ϖ) (hv : Continuous v) (hv0 : v 0 = 0)
    (ht : 0 ≤ t) (hab : a < b) (hw : ∀ x ∈ Icc a b, x < 0 ∧ IsLive v t x)
    {Φ : ℝ ≃o ℝ} (hΦ : ∀ x ∈ Icc a b, Φ x = realRevMap v t x)
    {G : ℝ → (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) :
    ∀ᵐ ω ∂P', ∫⁻ x, G x (coordsFull (addConst (ofFun (h0rev κ) + X' ω) (-(mFix κ v t ϖ (X' ω)))))
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ v t (X' ω)) (-(mFix κ v t ϖ (X' ω))))
          (Ioo a b)
      = ∫⁻ y in Ioo (realRevMap v t a) (realRevMap v t b),
          ENNReal.ofReal (Real.exp (Real.sqrt κ * -qt κ v t ϖ / 2)) *
            G (Φ.symm y) (fun j => normAt (varpiT v t ϖ) (ofFun (h0rev κ) + X' ω)
              (foldedCircle (fullIndex j).1 (fullIndex j).2) + -qt κ v t ϖ)
          ∂qBoundaryMeasure (Real.sqrt κ) (normAt (varpiT v t ϖ) (ofFun (h0rev κ) + X' ω)) := by
  set γ := Real.sqrt κ with hγdef
  set ϖ' := varpiT v t ϖ with hϖ'def
  set q := qt κ v t ϖ with hqdef
  set F := realRevMap v t with hFdef
  have hΦsymm : ∀ x ∈ Icc a b, Φ.symm (F x) = x := fun x hx => by
    rw [← show Φ x = F x from hΦ x hx, OrderIso.symm_apply_apply]
  have := hϖ.prob
  have hm := TwoPoint.measurable_revMap hv ht
  have : IsProbabilityMeasure ϖ' := by simp only [hϖ'def, varpiT]; infer_instance
  have hϖ'1 : ϖ' univ = 1 := measure_univ
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hfr⟩ := hϖ.frost
  obtain ⟨R, hR⟩ := B2.map_revMap_support_of_compact hv ht hKc hKH hK0
  obtain ⟨C', hC'⟩ := B2.isFrostman_map_revMap_of_compact hv ht hKc hKH hK0 hα.le hfr
  set μ : ℕ → Measure ℂ := fun j => foldedCircle (fullIndex j).1 (fullIndex j).2 with hμdef
  have hμ1 : ∀ j, (μ j univ).toReal = 1 := fun j => by simp [hμdef]
  set eq : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * -q / 2)) with heq
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

/-- The window term of E1-PW is a.e. measurable in `ω` ((R1) + (R2)). -/
theorem aemeasurable_window_lhs [IsProbabilityMeasure P'] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hX : IsFreeGFFModConstH X' P') (hϖ : IsNormalizer ϖ) (hv : Continuous v) (hv0 : v 0 = 0)
    (ht : 0 ≤ t) (hab : a < b) (hw : ∀ x ∈ Icc a b, x < 0 ∧ IsLive v t x)
    {G : ℝ → (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) :
    AEMeasurable (fun ω => ∫⁻ x, G x (coordsFull (addConst (ofFun (h0rev κ) + X' ω)
        (-(mFix κ v t ϖ (X' ω)))))
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ v t (X' ω))
          (-(mFix κ v t ϖ (X' ω)))) (Ioo a b)) P' := by
  obtain ⟨Φ, hΦ⟩ := exists_orderIso_eq_realRevMap hv ht hab fun x hx => (hw x hx).2
  have := hϖ.prob
  have hm := TwoPoint.measurable_revMap hv ht
  have : IsProbabilityMeasure (varpiT v t ϖ) := by simp only [varpiT]; infer_instance
  have hϖ'1 : varpiT v t ϖ univ = 1 := measure_univ
  set e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (Real.sqrt κ * -qt κ v t ϖ / 2))
  have hφ : Measurable (Function.uncurry fun (c : ℕ → ℝ) (y : ℝ) =>
      e * G (Φ.symm y) (fun j => c j + -qt κ v t ϖ)) :=
    measurable_const.mul (hG.comp
      ((Φ.symm.continuous.measurable.comp measurable_snd).prodMk
        (measurable_pi_iff.2 fun j => ((measurable_pi_apply j).comp measurable_fst).add
          measurable_const)))
  refine (aemeasurable_setLIntegral_normAt
    (μ := fun j => foldedCircle (fullIndex j).1 (fullIndex j).2) (a := realRevMap v t a)
    (b := realRevMap v t b) hX (ae_exists_isVagueLimitR_normAt_h0rev hX hκ hκ4 hϖ'1) hφ).congr ?_
  filter_upwards [ae_window_lhs_eq hκ hκ4 hX hϖ hv hv0 ht hab hw hΦ hG] with ω hω
  exact hω.symm

end E1
end QuantumZipper
