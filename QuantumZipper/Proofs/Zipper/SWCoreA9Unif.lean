import QuantumZipper.Proofs.Zipper.SWCoreA9Trans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A9 (2): offset transport uniformly in `α ∈ [1,2]`, and along `goodFilter`

For one map `ψ` of a rational area class and one field sample `x` with window limits: if the
offset distortion error `pushErrR γ x ψ (α 2^{-k}) z` is eventually small uniformly in
`α ∈ [1,2]` and `z` in the rectangle, then `∫ f dμ^{x∘ψ+Q log|ψ'|}_{α 2^{-k}} → ∫ f∘ψ⁻¹ dμ^x`
uniformly in `α` (`a9_transport_signed`), i.e. along `goodFilter` (`a9_tendsto_goodFilter`).
Same proof as `area_transport_nonneg_fam` / `transport_signed_fam` (SWCoreA6Fam), with the
window limit `unifWin` applied to the family indexed by `α` (scale `α ‖ψ'(ψ⁻¹ ·)‖`).
Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7); own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

variable {γ : ℝ} {x : FieldSample}

/-- **Offset transport for a nonnegative test function**, uniformly in `α ∈ [1,2]`. -/
theorem a9_transport_nonneg (hγ : 0 < γ) {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1))
    (hcw' : Tendsto cw' atTop (𝓝 1)) (hWin : WindowLimits γ x cw cw')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ x K < ⊤)
    (hsupm : ∀ N j, Measurable (supWin γ x N j)) (hinfm : ∀ N j, Measurable (infWin γ x N j))
    {a b c d ρ M m : ℚ} (hc : (0 : ℝ) < c) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) {ψ : ℂ → ℂ} (hψ : ψ ∈ AreaClass a b c d ρ M m)
    (hErr : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
      |pushErrR γ x ψ (α * radius k) z| ≤ η) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hfK : tsupport f ⊆ interior (rectC a b c d))
    (hf0 : ∀ z, 0 ≤ f z) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2,
      Integrable (fun z => areaDens γ (coordChange x ψ (Qc γ)) (α * radius k) z * f z)
          (volume.restrict H) ∧
        |∫ z, f z ∂areaR γ (coordChange x ψ (Qc γ)) (α * radius k) -
          ∫ w, pullTest ψ (rectC a b c d) f w ∂qAreaMeasure γ x| ≤ η := by
  set K := rectC (a : ℝ) b c d with hKdef
  set μ := qAreaMeasure γ x with hμ
  set C₀ : Set ℂ := {w | ‖w‖ ≤ (M : ℝ) ∧ (ρ : ℝ) ≤ w.im} with hC₀
  have hC₀c : IsCompact C₀ := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im)
    · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := M)).subset fun w hw => by
        rw [mem_closedBall, dist_zero_right]; exact hw.1
  have hC₀H : C₀ ⊆ H := fun w hw => lt_of_lt_of_le hρ hw.2
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfs
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hfB : ∀ z, f z ≤ B := fun z =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z))
  obtain ⟨Cs, hCs⟩ := pullTest_ne_zero (a := a) (b := b) (c := c) (d := d) (M := M) (m := m)
    hρ (f := f)
  have hpt0 : ∀ w, 0 ≤ pullTest ψ K f w := fun w => by
    unfold pullTest; split_ifs
    · exact hf0 _
    · exact le_rfl
  have hptB : ∀ w, pullTest ψ K f w ≤ B := fun w => by
    unfold pullTest; split_ifs
    · exact hfB _
    · exact hB0
  have hgC : ∀ (_ : Icc (1 : ℝ) 2) w, pullTest ψ K f w ≠ 0 → w ∈ C₀ := fun _ w h => by
    obtain ⟨-, -, h1, h2, -, -⟩ := hCs ψ hψ w h
    exact ⟨h1, h2⟩
  have hgeq : ∀ ε > 0, ∃ δ > 0, ∀ (_ : Icc (1 : ℝ) 2) w w',
      dist w w' < δ → |pullTest ψ K f w - pullTest ψ K f w'| ≤ ε := fun ε hε => by
    obtain ⟨δ, hδ, h⟩ := pullTest_equicont hρ hm hf hfs hfK ε hε
    exact ⟨δ, hδ, fun _ w w' hw => h ψ hψ w w' hw⟩
  have hspos : ∀ (i : Icc (1 : ℝ) 2) w, pullTest ψ K f w ≠ 0 →
      0 < (i : ℝ) * pullScale ψ K w ∧ (i : ℝ) * pullScale ψ K w ≤ 2 * Cs := fun i w h => by
    obtain ⟨-, -, -, -, h1, h2⟩ := hCs ψ hψ w h
    have hi1 : (1 : ℝ) ≤ i := i.2.1
    have hi2 : (i : ℝ) ≤ 2 := i.2.2
    have hs0 : 0 < pullScale ψ K w := lt_of_lt_of_le hm h1
    exact ⟨by positivity, by nlinarith⟩
  have hseq : ∀ ε > 0, ∃ δ > 0, ∀ (i : Icc (1 : ℝ) 2) w w',
      pullTest ψ K f w ≠ 0 → pullTest ψ K f w' ≠ 0 → dist w w' < δ →
      |Real.logb 2 ((i : ℝ) * pullScale ψ K w) - Real.logb 2 ((i : ℝ) * pullScale ψ K w')| ≤ ε :=
    fun ε hε => by
      obtain ⟨δ, hδ, h⟩ := pullScale_logb_equicont (f := f) hρ hm ε hε
      refine ⟨δ, hδ, fun i w w' h1 h2 hw => ?_⟩
      have hi0 : (i : ℝ) ≠ 0 := by have := i.2.1; positivity
      have hs1 : pullScale ψ K w ≠ 0 := by
        obtain ⟨-, -, -, -, h3, -⟩ := hCs ψ hψ w h1; exact (lt_of_lt_of_le hm h3).ne'
      have hs2 : pullScale ψ K w' ≠ 0 := by
        obtain ⟨-, -, -, -, h3, -⟩ := hCs ψ hψ w' h2; exact (lt_of_lt_of_le hm h3).ne'
      rw [Real.logb_mul hi0 hs1, Real.logb_mul hi0 hs2]
      have := h ψ hψ w w' h1 h2 hw
      calc _ = |Real.logb 2 (pullScale ψ K w) - Real.logb 2 (pullScale ψ K w')| := by ring_nf
        _ ≤ ε := this
  have hη8 : (0 : ℝ) < η / 8 := by positivity
  have hU := unifWin (g := fun (_ : Icc (1 : ℝ) 2) => pullTest ψ K f)
    (s := fun i w => (i : ℝ) * pullScale ψ K w) hcw hcw' hWin hμK hsupm hinfm hC₀c hC₀H
    hB0 (fun _ w => hpt0 w) (fun _ w => hptB w) hgC hgeq hspos hseq hη8
  set Im := B * μ.real C₀ with hImdef
  have hIm0 : 0 ≤ Im := mul_nonneg hB0 measureReal_nonneg
  set τ := min (η / (4 * (Im + 1))) 1 with hτdef
  have hτ0 : 0 < τ := lt_min (by positivity) one_pos
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hτIm : τ * Im ≤ η / 4 := by
    have h1 : τ ≤ η / (4 * (Im + 1)) := min_le_left _ _
    have h2 : η / (4 * (Im + 1)) * Im ≤ η / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    exact (mul_le_mul_of_nonneg_right h1 hIm0).trans h2
  set η₃ := Real.log (1 + τ) / γ with hη₃def
  have hη₃ : 0 < η₃ := div_pos (Real.log_pos (by linarith)) hγ
  have hexp₃ : Real.exp (γ * η₃) = 1 + τ := by
    rw [hη₃def, mul_div_cancel₀ _ hγ.ne', Real.exp_log (by linarith)]
  filter_upwards [hU, hErr η₃ hη₃] with k hk herr α hα
  have hr : 0 < α * radius k := mul_pos (by linarith [hα.1]) (radius_pos k)
  set V := vsInt γ x (pullTest ψ K f) (fun w => α * pullScale ψ K w) k with hVdef
  have hV1 : V ≤ ENNReal.ofReal (∫ w, pullTest ψ K f w ∂μ + η / 8) := (hk ⟨α, hα⟩).1
  have hV2 : ENNReal.ofReal (∫ w, pullTest ψ K f w ∂μ) ≤ V + ENNReal.ofReal (η / 8) :=
    (hk ⟨α, hα⟩).2
  set J := ∫ w, pullTest ψ K f w ∂μ with hJdef
  have hJ : 0 ≤ J ∧ J ≤ Im := by
    refine ⟨integral_nonneg hpt0, ?_⟩
    rw [hJdef, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C₀) fun w hw => by
      by_contra h
      obtain ⟨-, -, h1, h2, -, -⟩ := hCs ψ hψ w h
      exact hw ⟨h1, h2⟩]
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := pullTest ψ K f)
      (hμK C₀ hC₀c hC₀H) (C := B) fun w _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpt0 w)]; exact hptB w
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans this)
  have hCV := a9_lintegral_pushDens_eq (γ := γ) (x := x) hc hρ hψ hfK α k
  set D : ℂ → ℝ := fun z => areaDens γ (coordChange x ψ (Qc γ)) (α * radius k) z * f z
    with hDdef
  have hD0 : ∀ z, 0 ≤ D z := fun z =>
    mul_nonneg (GoodSample.areaDens_nonneg _ _ hr _) (hf0 z)
  have hDm : Measurable D := (a9_measurable_areaDens _ _ _).mul hf.measurable
  set E : ℂ → ℝ := fun z => ‖deriv ψ z‖ ^ 2 * areaDens γ x (α * radius k * ‖deriv ψ z‖) (ψ z)
    with hEdef
  have hcmp : ∀ z, ENNReal.ofReal (D z) ≤
      ENNReal.ofReal (1 + τ) * (ENNReal.ofReal (f z) * ENNReal.ofReal (E z)) ∧
      ENNReal.ofReal (1 - τ) * (ENNReal.ofReal (f z) * ENNReal.ofReal (E z)) ≤
        ENNReal.ofReal (D z) := by
    intro z
    by_cases hfz : f z = 0
    · simp [hDdef, hfz]
    have hzK : z ∈ K := interior_subset (hfK (subset_tsupport f hfz))
    have hd0 : deriv ψ z ≠ 0 := fun h => by
      have := hψ.2.2.2 z hzK; rw [h, norm_zero] at this; linarith
    have hfac := areaDens_coordChange_eqR hγ x ψ hr hd0
    have he := herr α hα z hzK
    have hE0 : 0 ≤ E z := mul_nonneg (sq_nonneg _)
      (GoodSample.areaDens_nonneg γ x (mul_pos hr (norm_pos_iff.2 hd0)) _)
    have hup : Real.exp (γ * pushErrR γ x ψ (α * radius k) z) ≤ 1 + τ := by
      rw [← hexp₃]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le.1 he).2 hγ.le)
    have hlo : 1 - τ ≤ Real.exp (γ * pushErrR γ x ψ (α * radius k) z) := by
      have h1 : Real.exp (-(γ * η₃)) ≤ Real.exp (γ * pushErrR γ x ψ (α * radius k) z) :=
        Real.exp_le_exp.2 (by nlinarith [(abs_le.1 he).1])
      have h2 : 1 - τ ≤ Real.exp (-(γ * η₃)) := by
        rw [Real.exp_neg, hexp₃, ← one_div, le_div_iff₀ (by linarith)]; nlinarith
      linarith
    have hDz : D z = E z * Real.exp (γ * pushErrR γ x ψ (α * radius k) z) * f z := by
      simp only [hDdef, hEdef, hfac]
    have hf0z := hf0 z
    rw [← ENNReal.ofReal_mul hf0z, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_mul (by linarith), hDz]
    constructor <;> refine ENNReal.ofReal_le_ofReal ?_
    · have := mul_le_mul_of_nonneg_left hup (mul_nonneg hE0 hf0z)
      nlinarith
    · have := mul_le_mul_of_nonneg_left hlo (mul_nonneg hE0 hf0z)
      nlinarith
  have hLup : ∫⁻ z in H, ENNReal.ofReal (D z) ≤ ENNReal.ofReal (1 + τ) * V := by
    rw [hVdef, ← hCV, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun z => (hcmp z).1
  have hLlo : ENNReal.ofReal (1 - τ) * V ≤ ∫⁻ z in H, ENNReal.ofReal (D z) := by
    rw [hVdef, ← hCV, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun z => (hcmp z).2
  have hfin : ∫⁻ z in H, ENNReal.ofReal (D z) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hV1)) hLup
  have hT : ∫ z, f z ∂areaR γ (coordChange x ψ (Qc γ)) (α * radius k) =
      (∫⁻ z in H, ENNReal.ofReal (D z)).toReal := by
    rw [a9_integral_areaR_eq γ _ hr, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hD0)
      hDm.aestronglyMeasurable]
  set T := (∫⁻ z in H, ENNReal.ofReal (D z)).toReal with hTdef
  have hTL : ENNReal.ofReal T = ∫⁻ z in H, ENNReal.ofReal (D z) := ENNReal.ofReal_toReal hfin
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hTup : T ≤ (1 + τ) * (J + η / 8) := by
    have h : ENNReal.ofReal T ≤ ENNReal.ofReal ((1 + τ) * (J + η / 8)) := by
      rw [hTL, ENNReal.ofReal_mul (by linarith)]
      exact hLup.trans (by gcongr)
    exact (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).1 h
  have hTlo : (1 - τ) * J ≤ T + η / 8 := by
    have h : ENNReal.ofReal ((1 - τ) * J) ≤ ENNReal.ofReal (T + η / 8) := by
      rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_add hT0 (by positivity), hTL]
      calc ENNReal.ofReal (1 - τ) * ENNReal.ofReal J
          ≤ ENNReal.ofReal (1 - τ) * (V + ENNReal.ofReal (η / 8)) := by gcongr
        _ = ENNReal.ofReal (1 - τ) * V + ENNReal.ofReal (1 - τ) * ENNReal.ofReal (η / 8) := by
            rw [mul_add]
        _ ≤ (∫⁻ z in H, ENNReal.ofReal (D z)) + ENNReal.ofReal (η / 8) :=
            add_le_add hLlo (by
              have h1 : ENNReal.ofReal (1 - τ) ≤ 1 := ENNReal.ofReal_le_one.2 (by linarith)
              calc ENNReal.ofReal (1 - τ) * ENNReal.ofReal (η / 8)
                  ≤ 1 * ENNReal.ofReal (η / 8) := by gcongr
                _ = ENNReal.ofReal (η / 8) := one_mul _)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hDm.aestronglyMeasurable
    (ae_of_all _ hD0)).1 hfin, ?_⟩
  rw [hT, abs_le]
  obtain ⟨hJ0, hJI⟩ := hJ
  have hτJ : τ * J ≤ η / 4 := (mul_le_mul_of_nonneg_left hJI hτ0.le).trans hτIm
  constructor <;> nlinarith

/-- **Offset transport, signed test functions**, uniformly in `α ∈ [1,2]`. -/
theorem a9_transport_signed (hγ : 0 < γ) {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1))
    (hcw' : Tendsto cw' atTop (𝓝 1)) (hWin : WindowLimits γ x cw cw')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ x K < ⊤)
    (hsupm : ∀ N j, Measurable (supWin γ x N j)) (hinfm : ∀ N j, Measurable (infWin γ x N j))
    {a b c d ρ M m : ℚ} (hc : (0 : ℝ) < c) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) {ψ : ℂ → ℂ} (hψ : ψ ∈ AreaClass a b c d ρ M m)
    (hErr : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
      |pushErrR γ x ψ (α * radius k) z| ≤ η) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hfK : tsupport f ⊆ interior (rectC a b c d))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2,
      |∫ z, f z ∂areaR γ (coordChange x ψ (Qc γ)) (α * radius k) -
        ∫ w, pullTest ψ (rectC a b c d) f w ∂qAreaMeasure γ x| ≤ η := by
  set fp : ℂ → ℝ := fun z => max (f z) 0 with hfp
  set fm : ℂ → ℝ := fun z => max (-f z) 0 with hfm
  have hfpc : Continuous fp := hf.max continuous_const
  have hfmc : Continuous fm := hf.neg.max continuous_const
  have hsp : support fp ⊆ support f := fun z hz h => hz (by simp [hfp, h])
  have hsm : support fm ⊆ support f := fun z hz h => hz (by simp [hfm, h])
  have hfps : HasCompactSupport fp := hfs.mono hsp
  have hfms : HasCompactSupport fm := hfs.mono hsm
  have hfpK : tsupport fp ⊆ interior (rectC a b c d) := (closure_mono hsp).trans hfK
  have hfmK : tsupport fm ⊆ interior (rectC a b c d) := (closure_mono hsm).trans hfK
  have hsplit : ∀ z, f z = fp z - fm z := fun z => by
    rcases le_total (f z) 0 with h | h
    · simp [hfp, hfm, max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    · simp [hfp, hfm, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
  filter_upwards [a9_transport_nonneg hγ hcw hcw' hWin hμK hsupm hinfm hc hρ hm hψ hErr hfpc
      hfps hfpK (fun z => le_max_right _ _) (half_pos hη),
    a9_transport_nonneg hγ hcw hcw' hWin hμK hsupm hinfm hc hρ hm hψ hErr hfmc hfms hfmK
      (fun z => le_max_right _ _) (half_pos hη)] with k h1 h2 α hα
  have hr : 0 < α * radius k := mul_pos (by linarith [hα.1]) (radius_pos k)
  obtain ⟨hi1, hb1⟩ := h1 α hα
  obtain ⟨hi2, hb2⟩ := h2 α hα
  have eA : ∫ z, f z ∂areaR γ (coordChange x ψ (Qc γ)) (α * radius k) =
      ∫ z, fp z ∂areaR γ (coordChange x ψ (Qc γ)) (α * radius k) -
        ∫ z, fm z ∂areaR γ (coordChange x ψ (Qc γ)) (α * radius k) := by
    rw [a9_integral_areaR_eq γ _ hr, a9_integral_areaR_eq γ _ hr, a9_integral_areaR_eq γ _ hr,
      ← integral_sub hi1 hi2]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [hsplit z, mul_sub]
  have eB : ∫ w, pullTest ψ (rectC a b c d) f w ∂qAreaMeasure γ x =
      ∫ w, pullTest ψ (rectC a b c d) fp w ∂qAreaMeasure γ x -
        ∫ w, pullTest ψ (rectC a b c d) fm w ∂qAreaMeasure γ x := by
    rw [← integral_sub (integrable_pullTest hρ hm hfpc hfps hfpK hμK hψ)
      (integrable_pullTest hρ hm hfmc hfms hfmK hμK hψ)]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [pullTest]
    split_ifs
    · exact hsplit _
    · ring
  rw [eA, eB]
  calc _ = |(∫ z, fp z ∂areaR γ (coordChange x ψ (Qc γ)) (α * radius k) -
          ∫ w, pullTest ψ (rectC a b c d) fp w ∂qAreaMeasure γ x) -
        (∫ z, fm z ∂areaR γ (coordChange x ψ (Qc γ)) (α * radius k) -
          ∫ w, pullTest ψ (rectC a b c d) fm w ∂qAreaMeasure γ x)| := by ring_nf
    _ ≤ η / 2 + η / 2 := (abs_sub _ _).trans (add_le_add hb1 hb2)
    _ = η := by ring

/-- **Offset transport along `goodFilter`.** -/
theorem a9_tendsto_goodFilter (hγ : 0 < γ) {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1))
    (hcw' : Tendsto cw' atTop (𝓝 1)) (hWin : WindowLimits γ x cw cw')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ x K < ⊤)
    (hsupm : ∀ N j, Measurable (supWin γ x N j)) (hinfm : ∀ N j, Measurable (infWin γ x N j))
    {a b c d ρ M m : ℚ} (hc : (0 : ℝ) < c) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) {ψ : ℂ → ℂ} (hψ : ψ ∈ AreaClass a b c d ρ M m)
    (hErr : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
      |pushErrR γ x ψ (α * radius k) z| ≤ η) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hfK : tsupport f ⊆ interior (rectC a b c d)) :
    Tendsto (fun i => ∫ z, f z ∂areaR γ (coordChange x ψ (Qc γ)) (goodRad i)) goodFilter
      (𝓝 (∫ w, pullTest ψ (rectC a b c d) f w ∂qAreaMeasure γ x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := a9_transport_signed hγ hcw hcw' hWin hμK hsupm hinfm hc hρ hm hψ hErr hf hfs hfK
    (half_pos hε)
  filter_upwards [prod_mem_prod h (mem_principal_self (Icc (1 : ℝ) 2))] with i hi
  rw [Real.dist_eq]
  exact (hi.1 i.2 hi.2).trans_lt (half_lt_self hε)

end SWCore
end QuantumZipper
