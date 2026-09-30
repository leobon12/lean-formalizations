import QuantumZipper.Proofs.Thm18.ZqT5Plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (6): Palm transfer for `V + logSing` (first step of the Palm route of the `V` clause)

For the log-singular free field `y = V + logSing` (`V` a free field with `V(∂𝔻) = 0`, the
singularity `(γ − 2/γ)(−log|·|)` at `0`) and a window `[a, b]` avoiding `0`: if a measurable
event of the dyadic coordinates and the point is null for the Palm field
`normAt ∂𝔻 (h + (γ/2)(G(x, ·) − k) + V)` (`h = Lf`, `shiftFun`) at Lebesgue-a.e. `x ∈ (a, b)`,
then a.s. it fails for `y` at `ν_y`-a.e. `x ∈ (a, b)` (`ae_typ_of_palm_V`).

This is the rooted-measure (Palm) formula of Duplantier–Sheffield, arXiv:0808.1560, §3.3
(`palm_formula_norm_local`, applied as in `R18.g3WedgePalmIdStmt_holds`), used as in
`G3ZqL.ae_hν_of_palm_null` (Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 65: "once we
condition on `x`"). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open R18 PalmNorm Factorization

/-- **Palm transfer of null events for `V + logSing` on a window avoiding `0`.** -/
theorem ae_typ_of_palm_V {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω'' : Type} [MeasurableSpace Ω'']
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {V : Ω'' → FieldSample}
    (hV : IsFreeGFFModConstH V P'') (hV0 : ∀ᵐ ω ∂P'', V ω (foldedCircle 0 1) = 0)
    {E : Set ((ℕ → ℝ) × ℝ)} (hE : MeasurableSet E) {a b : ℝ} {N : ℕ}
    (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) (h0 : (0 : ℝ) ∉ Icc a b)
    (hP : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ᵐ ω ∂P'',
      (coords (normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) g3zS x) + V ω)), x)
        ∉ E) :
    ∀ᵐ ω ∂P'', ∀ᵐ x ∂((qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))).restrict (Ioo a b)),
      (coords (V ω + F2.logSingField (γ ^ 2)), x) ∉ E := by
  set α : ℝ := γ - 2 / γ with hα
  obtain ⟨m, hm, hmab⟩ := g3z_exists_margin h0
  set h' : ℂ → ℝ := fun v => α * -Real.log (max ‖v‖ m) with hh'
  have hh'c : Continuous h' := by
    refine continuous_const.mul (Continuous.neg ?_)
    exact Real.continuousOn_log.comp_continuous (continuous_norm.max continuous_const)
      fun v => by
        simp only [mem_compl_iff, mem_singleton_iff]
        exact ne_of_gt (lt_of_lt_of_le hm (le_max_right _ _))
  set W : Set ℂ := {v | m < ‖v‖} with hWdef
  have hW : IsOpen W := isOpen_lt continuous_const continuous_norm
  have habW : ∀ t ∈ Icc a b, (t : ℂ) ∈ W := fun t ht => by
    show m < ‖(t : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hmab t ht
  have hEq : EqOn (LogSingGood.Lf α) h' W := fun v hv => by
    simp only [hh', LogSingGood.Lf, max_eq_left (le_of_lt (show m < ‖v‖ from hv))]
  have hϖ : IsAdmissibleH g3zS := isAdmissibleH_foldedCircle (by simp [Hbar]) one_pos
  have hϖ1 : g3zS univ = 1 := measure_univ
  set μc : ℕ → Measure ℂ := fun j => foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2)
    with hμc
  have hμ : ∀ j, IsAdmissibleH (μc j) := fun j =>
    D3Plus.isAdmissibleH_foldedCircle' _ (radius_pos _)
  have hint : ∀ (d : ℂ) (ρ : ℝ), Integrable (LogSingGood.Lf α) (foldedCircle d ρ) := fun d ρ =>
    (CoordReg.integrable_log_norm_foldedCircle d ρ).neg.const_mul α
  have hgV := g3pl4_ae_isAreaGood_logSing hγ hγ2 hV
  have hex : ∀ᵐ ω ∂P'', ∃ ν, IsVagueLimitR
      (bdryApprox γ (normAt g3zS (ofFun (LogSingGood.Lf α) + V ω))) ν := by
    filter_upwards [hV0, hgV] with ω h0' hg
    rw [g3z_normAt_eq hγ h0']
    exact ⟨_, isVagueLimitR_qBoundaryMeasure_of_isLQGGood hg.1⟩
  -- the weight
  set w : ℝ → ℝ := fun x => max 0 (min (x - a) (b - x)) with hwdef
  have hw : Continuous w := continuous_const.max
    ((continuous_id.sub continuous_const).min (continuous_const.sub continuous_id))
  have hw0 : ∀ x, 0 ≤ w x := fun x => le_max_left _ _
  have hwout : ∀ x ∉ Ioo a b, w x = 0 := by
    intro x hx
    simp only [mem_Ioo, not_and_or, not_lt] at hx
    refine max_eq_left ?_
    rcases hx with hx | hx
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have hwab : ∀ x ∉ Icc a b, w x = 0 := fun x hx => hwout x fun h => hx (Ioo_subset_Icc_self h)
  have hwpos : ∀ x ∈ Ioo a b, 0 < w x := fun x hx =>
    lt_max_of_lt_right (lt_min (by linarith [hx.1]) (by linarith [hx.2]))
  have hwc : HasCompactSupport w := HasCompactSupport.intro isCompact_Icc hwab
  set φ : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun c x => E.indicator 1 (c, x) with hφdef
  have hφ : Measurable (Function.uncurry φ) := measurable_one.indicator hE
  have H := palm_formula_norm_local (P := P'') (μ := μc) hV hγ hγ2 hab hh'c hW habW hEq hϖ hϖ1
    hμ (hint 0 1) (fun j => hint _ _) hex hw hwc hw0 hwab hφ
  -- the Palm side vanishes
  have hR : ∫⁻ x, ENNReal.ofReal (w x * rhoNorm γ (LogSingGood.Lf α) g3zS x) *
      ∫⁻ ω, φ (fun j => normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf α) g3zS x) + V ω) (μc j)) x
        ∂P'' = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    rw [ae_restrict_iff' measurableSet_Ioo] at hP
    filter_upwards [hP] with x hx
    by_cases hxI : x ∈ Ioo a b
    · have h0' : ∫⁻ ω, φ (fun j => normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf α) g3zS x) +
          V ω) (μc j)) x ∂P'' = 0 := by
        refine (lintegral_congr_ae ?_).trans lintegral_zero
        filter_upwards [hx hxI] with ω hω
        exact indicator_of_notMem hω _
      rw [h0', mul_zero]
    · rw [hwout x hxI, zero_mul, ENNReal.ofReal_zero, zero_mul]
  rw [hR] at H
  -- measurability of the typical-point side
  have hcm : Measurable fun ω => coords (V ω + F2.logSingField (γ ^ 2)) :=
    measurable_pi_iff.2 fun i => (hV.measurable_coord _).add_const _
  have hF'm : Measurable fun ω => ∫⁻ x, ENNReal.ofReal (w x) *
      φ (coords (V ω + F2.logSingField (γ ^ 2))) x
        ∂(bdryMc γ (coords (V ω + F2.logSingField (γ ^ 2)))) :=
    measurable_lintegral_family (H := fun q : Ω'' × ℝ => ENNReal.ofReal (w q.2) *
        φ (coords (V q.1 + F2.logSingField (γ ^ 2))) q.2)
      ((measurable_bdryMc γ).comp hcm) (fun ω N => bdryM_Icc_ne_top γ _ _ _)
      ((ENNReal.measurable_ofReal.comp (hw.measurable.comp measurable_snd)).mul
        (hφ.comp ((hcm.comp measurable_fst).prodMk measurable_snd)))
  have hFF : (fun ω => ∫⁻ x, ENNReal.ofReal (w x) *
      φ (fun j => normAt g3zS (ofFun (LogSingGood.Lf α) + V ω) (μc j)) x
        ∂(qBoundaryMeasure γ (normAt g3zS (ofFun (LogSingGood.Lf α) + V ω)))) =ᵐ[P'']
      fun ω => ∫⁻ x, ENNReal.ofReal (w x) * φ (coords (V ω + F2.logSingField (γ ^ 2))) x
        ∂(bdryMc γ (coords (V ω + F2.logSingField (γ ^ 2)))) := by
    filter_upwards [hV0, hgV] with ω h0' hg
    rw [g3z_normAt_eq hγ h0', bdryMc_coords_of_good hg.1]
    rfl
  rw [lintegral_congr_ae hFF] at H
  filter_upwards [(lintegral_eq_zero_iff hF'm).1 H, hgV] with ω hω hg
  have hZ : ∀ᵐ x ∂(bdryMc γ (coords (V ω + F2.logSingField (γ ^ 2)))),
      ENNReal.ofReal (w x) * φ (coords (V ω + F2.logSingField (γ ^ 2))) x = 0 :=
    (lintegral_eq_zero_iff ((ENNReal.measurable_ofReal.comp hw.measurable).mul
      (hφ.comp (measurable_const.prodMk measurable_id)))).1 hω
  rw [bdryMc_coords_of_good hg.1] at hZ
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hZ] with x hx hxI hmem
  have hw' : ENNReal.ofReal (w x) ≠ 0 := (ENNReal.ofReal_pos.2 (hwpos x hxI)).ne'
  have h1 : φ (coords (V ω + F2.logSingField (γ ^ 2))) x = 1 := indicator_of_mem hmem _
  rw [h1, mul_one] at hx
  exact hw' hx

end ZqT
end Thm18Asm
end QuantumZipper
