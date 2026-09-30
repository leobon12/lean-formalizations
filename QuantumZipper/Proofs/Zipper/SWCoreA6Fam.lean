import QuantumZipper.Proofs.Zipper.SWCoreA6Merge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A6 (4): uniform transport and merging for a sub-family of a class (decision D64)

Same as `transport_nonneg` / `transport_signed` / `merge_class_unif` / `mergeUnif_of_sample`, but
the distortion bound is only assumed for the maps `ψ ∈ S` actually transported (hypothesis
`hErr`, e.g. from the finite-parameter primed core `swcNA2I_primed`), not for the whole class.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

variable {γ : ℝ} {x : FieldSample}

/-- **Uniform transport for a nonnegative test function** (one field sample). -/
theorem area_transport_nonneg_fam (hγ : 0 < γ) {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1))
    (hcw' : Tendsto cw' atTop (𝓝 1)) (hWin : WindowLimits γ x cw cw')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ x K < ⊤)
    (hsupm : ∀ N j, Measurable (supWin γ x N j)) (hinfm : ∀ N j, Measurable (infWin γ x N j))
    {a b c d ρ M m : ℚ} (hc : (0 : ℝ) < c) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) {S : Set (ℂ → ℂ)} (hS : S ⊆ AreaClass a b c d ρ M m)
    (hErr : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ ψ ∈ S, ∀ z ∈ rectC a b c d,
      |pushErr γ x ψ k z| ≤ η) {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hfK : tsupport f ⊆ interior (rectC a b c d)) (hf0 : ∀ z, 0 ≤ f z) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ ψ ∈ S,
      Integrable (fun z => areaDensK γ (coordChange x ψ (Qc γ)) k z * f z)
          (volume.restrict H) ∧
        |∫ z, f z ∂areaApprox γ (coordChange x ψ (Qc γ)) k -
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
  have hpt0 : ∀ ψ w, 0 ≤ pullTest ψ K f w := fun ψ w => by
    unfold pullTest; split_ifs
    · exact hf0 _
    · exact le_rfl
  have hptB : ∀ ψ w, pullTest ψ K f w ≤ B := fun ψ w => by
    unfold pullTest; split_ifs
    · exact hfB _
    · exact hB0
  have hgC : ∀ (i : {ψ : ℂ → ℂ // ψ ∈ AreaClass a b c d ρ M m}) w,
      pullTest i.1 K f w ≠ 0 → w ∈ C₀ := fun i w h => by
    obtain ⟨-, -, h1, h2, -, -⟩ := hCs i.1 i.2 w h
    exact ⟨h1, h2⟩
  have hgeq : ∀ ε > 0, ∃ δ > 0, ∀ (i : {ψ : ℂ → ℂ // ψ ∈ AreaClass a b c d ρ M m}) w w',
      dist w w' < δ → |pullTest i.1 K f w - pullTest i.1 K f w'| ≤ ε := fun ε hε => by
    obtain ⟨δ, hδ, h⟩ := pullTest_equicont hρ hm hf hfs hfK ε hε
    exact ⟨δ, hδ, fun i w w' hw => h i.1 i.2 w w' hw⟩
  have hspos : ∀ (i : {ψ : ℂ → ℂ // ψ ∈ AreaClass a b c d ρ M m}) w,
      pullTest i.1 K f w ≠ 0 → 0 < pullScale i.1 K w ∧ pullScale i.1 K w ≤ Cs :=
    fun i w h => by
      obtain ⟨-, -, -, -, h1, h2⟩ := hCs i.1 i.2 w h
      exact ⟨lt_of_lt_of_le hm h1, h2⟩
  have hseq : ∀ ε > 0, ∃ δ > 0, ∀ (i : {ψ : ℂ → ℂ // ψ ∈ AreaClass a b c d ρ M m}) w w',
      pullTest i.1 K f w ≠ 0 → pullTest i.1 K f w' ≠ 0 → dist w w' < δ →
      |Real.logb 2 (pullScale i.1 K w) - Real.logb 2 (pullScale i.1 K w')| ≤ ε :=
    fun ε hε => by
      obtain ⟨δ, hδ, h⟩ := pullScale_logb_equicont (f := f) hρ hm ε hε
      exact ⟨δ, hδ, fun i w w' h1 h2 hw => h i.1 i.2 w w' h1 h2 hw⟩
  have hη8 : (0 : ℝ) < η / 8 := by positivity
  have hU := unifWin (g := fun (i : {ψ : ℂ → ℂ // ψ ∈ AreaClass a b c d ρ M m}) =>
      pullTest i.1 K f) (s := fun i => pullScale i.1 K) hcw hcw' hWin hμK hsupm hinfm hC₀c hC₀H
    hB0 (fun i w => hpt0 _ w) (fun i w => hptB _ w) hgC hgeq hspos hseq hη8
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
  filter_upwards [hU, hErr η₃ hη₃] with k hk herr ψ hψS
  have hψ := hS hψS
  obtain ⟨hV1, hV2⟩ := hk ⟨ψ, hψ⟩
  set J := ∫ w, pullTest ψ K f w ∂μ with hJdef
  have hJ : 0 ≤ J ∧ J ≤ Im := by
    refine ⟨integral_nonneg (hpt0 ψ), ?_⟩
    rw [hJdef, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C₀) fun w hw => by
      by_contra h
      obtain ⟨-, -, h1, h2, -, -⟩ := hCs ψ hψ w h
      exact hw ⟨h1, h2⟩]
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := pullTest ψ K f)
      (hμK C₀ hC₀c hC₀H) (C := B) fun w _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpt0 ψ w)]; exact hptB ψ w
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans this)
  set V := vsInt γ x (pullTest ψ K f) (pullScale ψ K) k with hVdef
  have hCV := lintegral_pushDens_eq (γ := γ) (x := x) hc hρ hψ hfK k
  set D : ℂ → ℝ := fun z => areaDensK γ (coordChange x ψ (Qc γ)) k z * f z with hDdef
  have hD0 : ∀ z, 0 ≤ D z := fun z => mul_nonneg (areaDensK_nonneg _ _ _ _) (hf0 z)
  have hDm : Measurable D := (measurable_areaDensK _ _ _).mul hf.measurable
  set E : ℂ → ℝ := fun z => ‖deriv ψ z‖ ^ 2 * areaDens γ x (radius k * ‖deriv ψ z‖) (ψ z)
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
    have hfac := areaDensK_coordChange_eq hγ x ψ k hd0
    have he := herr ψ hψS z hzK
    have hE0 : 0 ≤ E z := mul_nonneg (sq_nonneg _)
      (GoodSample.areaDens_nonneg γ x (mul_pos (radius_pos k) (norm_pos_iff.2 hd0)) _)
    have hup : Real.exp (γ * pushErr γ x ψ k z) ≤ 1 + τ := by
      rw [← hexp₃]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le.1 he).2 hγ.le)
    have hlo : 1 - τ ≤ Real.exp (γ * pushErr γ x ψ k z) := by
      have h1 : Real.exp (-(γ * η₃)) ≤ Real.exp (γ * pushErr γ x ψ k z) :=
        Real.exp_le_exp.2 (by nlinarith [(abs_le.1 he).1])
      have h2 : 1 - τ ≤ Real.exp (-(γ * η₃)) := by
        rw [Real.exp_neg, hexp₃, ← one_div, le_div_iff₀ (by linarith)]; nlinarith
      linarith
    have hDz : D z = E z * Real.exp (γ * pushErr γ x ψ k z) * f z := by
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
  have hT : ∫ z, f z ∂areaApprox γ (coordChange x ψ (Qc γ)) k =
      (∫⁻ z in H, ENNReal.ofReal (D z)).toReal := by
    rw [integral_areaApprox_eq, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hD0)
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
  rw [abs_le]
  obtain ⟨hJ0, hJI⟩ := hJ
  have hτJ : τ * J ≤ η / 4 := (mul_le_mul_of_nonneg_left hJI hτ0.le).trans hτIm
  constructor <;> nlinarith

/-- **Uniform transport, signed test functions** (one field sample). -/
theorem transport_signed_fam (hγ : 0 < γ) {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1))
    (hcw' : Tendsto cw' atTop (𝓝 1)) (hWin : WindowLimits γ x cw cw')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ x K < ⊤)
    (hsupm : ∀ N j, Measurable (supWin γ x N j)) (hinfm : ∀ N j, Measurable (infWin γ x N j))
    {a b c d ρ M m : ℚ} (hc : (0 : ℝ) < c) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) {S : Set (ℂ → ℂ)} (hS : S ⊆ AreaClass a b c d ρ M m)
    (hErr : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ ψ ∈ S, ∀ z ∈ rectC a b c d,
      |pushErr γ x ψ k z| ≤ η) {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hfK : tsupport f ⊆ interior (rectC a b c d)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ ψ ∈ S,
      |∫ z, f z ∂areaApprox γ (coordChange x ψ (Qc γ)) k -
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
  filter_upwards [area_transport_nonneg_fam hγ hcw hcw' hWin hμK hsupm hinfm hc hρ hm hS hErr hfpc hfps hfpK
      (fun z => le_max_right _ _) (half_pos hη),
    area_transport_nonneg_fam hγ hcw hcw' hWin hμK hsupm hinfm hc hρ hm hS hErr hfmc hfms hfmK
      (fun z => le_max_right _ _) (half_pos hη)] with k h1 h2 ψ hψS
  have hψ := hS hψS
  obtain ⟨hi1, hb1⟩ := h1 ψ hψS
  obtain ⟨hi2, hb2⟩ := h2 ψ hψS
  have eA : ∫ z, f z ∂areaApprox γ (coordChange x ψ (Qc γ)) k =
      ∫ z, fp z ∂areaApprox γ (coordChange x ψ (Qc γ)) k -
        ∫ z, fm z ∂areaApprox γ (coordChange x ψ (Qc γ)) k := by
    rw [integral_areaApprox_eq, integral_areaApprox_eq, integral_areaApprox_eq,
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
  calc _ = |(∫ z, fp z ∂areaApprox γ (coordChange x ψ (Qc γ)) k -
          ∫ w, pullTest ψ (rectC a b c d) fp w ∂qAreaMeasure γ x) -
        (∫ z, fm z ∂areaApprox γ (coordChange x ψ (Qc γ)) k -
          ∫ w, pullTest ψ (rectC a b c d) fm w ∂qAreaMeasure γ x)| := by ring_nf
    _ ≤ η / 2 + η / 2 := (abs_sub _ _).trans (add_le_add hb1 hb2)
    _ = η := by ring

/-- **Uniform merging along the flow** for one field sample, assuming the distortion bound only
for the flow maps `f_t⁻¹`, `t ∈ [0,T]` (decision D64). -/
theorem mergeUnif_of_flowErr (hγ : 0 < γ) {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1))
    (hcw' : Tendsto cw' atTop (𝓝 1)) (hWin : WindowLimits γ x cw cw')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ x K < ⊤) {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ)
    (hErr : ∀ a b c d : ℚ, (0 : ℝ) < c → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      ∀ z ∈ rectC a b c d, |pushErr γ x (fwdMapInv W t) k z| ≤ η)
    {f : ℂ → ℝ} (hf : IsAreaTest f) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ t, 0 ≤ t → t ≤ T → |mergeDiff γ x W f t k| ≤ ε := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ⟨0, fun k _ t ht htT => absurd (ht.trans htT) (not_le.2 hT)⟩
  obtain ⟨hfc, hfs, hfH⟩ := hf
  obtain ⟨a, b, c, d, hc, hsub⟩ := exists_rect_of_compact hfs hfH
  obtain ⟨ρ, M, m, hρ, hm, hcl⟩ := flow_mem_areaClass (a := a) (b := b) (d := d) hW hW0 hT hc
  have hKH : rectC (a : ℝ) b c d ⊆ H := rectC_subset_H hc
  set S : Set (ℂ → ℂ) := (fun t => fwdMapInv W t) '' Icc 0 T with hSdef
  have hS : S ⊆ AreaClass a b c d ρ M m := by
    rintro _ ⟨t, ht, rfl⟩; exact hcl t ht
  have hErrS : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ ψ ∈ S, ∀ z ∈ rectC a b c d,
      |pushErr γ x ψ k z| ≤ η := fun η hη => by
    filter_upwards [hErr a b c d hc η hη] with k hk
    rintro _ ⟨t, ht, rfl⟩ z hz
    exact hk t ht z hz
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((transport_signed_fam hγ hcw hcw' hWin hμK
      (measurable_supWin ⟨F, hF⟩ γ) (measurable_infWin ⟨F, hF⟩ γ) hc hρ hm hS hErrS hfc hfs
      hsub (half_pos hε)).and
    (approx_pull_signed hcw hcw' hWin hμK hF hρ hm hfc hfs hsub (half_pos hε)))
  refine ⟨K, fun k hk t ht htT => ?_⟩
  obtain ⟨h1, h2⟩ := hK k hk
  have hψS : fwdMapInv W t ∈ S := ⟨t, ⟨ht, htT⟩, rfl⟩
  have e1 := h1 _ hψS
  have e2 := h2 _ (hS hψS)
  rw [pullTest_eq_transTest hW hW0 ht hKH (hsub.trans interior_subset)] at e1 e2
  have := abs_sub_le (∫ z, f z ∂areaApprox γ (coordChange x (fwdMapInv W t) (Qc γ)) k)
    (∫ w, transTest W t f w ∂qAreaMeasure γ x) (∫ w, transTest W t f w ∂areaApprox γ x k)
  rw [abs_sub_comm (∫ w, transTest W t f w ∂qAreaMeasure γ x)] at this
  show |∫ z, f z ∂areaApprox γ (coordChange x (fwdMapInv W t) (Qc γ)) k -
    ∫ w, transTest W t f w ∂areaApprox γ x k| ≤ ε
  linarith

end SWCore
end QuantumZipper
