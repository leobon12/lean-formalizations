import QuantumZipper.Proofs.Section5.Prop16LocalAgree

/-!
# Proposition 1.6, M4-P7-LOC (part 2): local rule for translated / rescaled fields

* `fcAgree_translate_add_ofFun`, `fcAgree_rescale_add_ofFun`: for a regular `y` and `ψ`
  continuous on `W ∩ Hbar` only, `translate (y + ψ) t` agrees on `W − t` with
  `translate y t + ψ(· + t)`, and `rescale (y + ψ) Q s` agrees on `s⁻¹ W` with
  `rescale y Q s + ψ(s ·)` (via a cutoff of `ψ` near the circle, `LocalRule.exists_cutoff`);
* `isVagueLimitOn_of_circAgree`, `isVagueLimitOnR_of_circAgree`: local vague limits of
  `areaApprox` / `bdryApprox` transfer between fields agreeing (on dyadic circles) on `W`;
* `isVagueLimitOn_H_of_good`, `isVagueLimitR_of_good`: good samples have dyadic limits.

Own elementary arguments (AGENT_GUIDE cost rule); locality of the approximations as in
Duplantier–Sheffield 2011, Prop. 2.1 and §6.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace QuantumZipper

namespace Prop16Area

namespace G

open GoodSample RegClosure LocalRule CircleFubini

variable {W : Set ℂ} {x x' : FieldSample}

theorem add_mem_ball_inter {d u : ℂ} {r : ℝ} (t : ℝ) (hu : u ∈ closedBall d r ∩ Hbar) :
    u + t ∈ closedBall (d + t) r ∩ Hbar :=
  ⟨by rw [mem_closedBall, dist_add_right]; exact hu.1, mapsTo_add_real t hu.2⟩

theorem mul_mem_ball_inter {d u : ℂ} {r s : ℝ} (hs : 0 < s) (hu : u ∈ closedBall d r ∩ Hbar) :
    (s : ℂ) * u ∈ closedBall ((s : ℂ) * d) (s * r) ∩ Hbar := by
  refine ⟨?_, mapsTo_mul_pos hs hu.2⟩
  have := hu.1
  rw [mem_closedBall, dist_eq_norm] at this ⊢
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  exact mul_le_mul_of_nonneg_left this hs.le

theorem translate_K_subset {d : ℂ} {r t : ℝ}
    (hdW : closedBall d r ∩ Hbar ⊆ (fun z => z + (t : ℂ)) ⁻¹' W) :
    closedBall (d + t) r ∩ Hbar ⊆ W := by
  rintro u ⟨hu1, hu2⟩
  have hm : u - t ∈ closedBall d r ∩ Hbar := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm] at hu1 ⊢
      convert hu1 using 2; ring
    · have : (0 : ℝ) ≤ u.im := hu2
      show (0 : ℝ) ≤ (u - (t : ℂ)).im
      simpa using this
  simpa using hdW hm

theorem rescale_K_subset {d : ℂ} {r s : ℝ} (hs : 0 < s)
    (hdW : closedBall d r ∩ Hbar ⊆ (fun z => (s : ℂ) * z) ⁻¹' W) :
    closedBall ((s : ℂ) * d) (s * r) ∩ Hbar ⊆ W := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rintro u ⟨hu1, hu2⟩
  have hm : u / (s : ℂ) ∈ closedBall d r ∩ Hbar := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm] at hu1 ⊢
      exact norm_div_sub_le hs hu1
    · have : (0 : ℝ) ≤ u.im := hu2
      show (0 : ℝ) ≤ (u / (s : ℂ)).im
      rw [Complex.div_ofReal_im]
      exact div_nonneg this hs.le
  have := hdW hm
  simpa [mul_div_cancel₀ _ hs'] using this

/-- **Local rule under translation.** -/
theorem fcAgree_translate_add_ofFun {y : FieldSample} (hy : IsRegularSample y) (hWo : IsOpen W)
    {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ (W ∩ Hbar)) (t : ℝ) :
    FcAgree ((fun z => z + (t : ℂ)) ⁻¹' W) (translate (y + ofFun ψ) (t : ℂ))
      (translate y (t : ℂ) + ofFun (fun u => ψ (u + t))) := by
  obtain ⟨F, hF⟩ := hy
  intro d hd r hr hdW
  obtain ⟨δ, hδ, φ, hφ, hφψ⟩ := exists_cutoff hWo hψ (isCompact_closedBall_inter_Hbar (d + t) r)
    (translate_K_subset hdW)
  have h1 : translate (y + ofFun ψ) (t : ℂ) (foldedCircle d r) =
      translate (y + ofFun φ) (t : ℂ) (foldedCircle d r) :=
    fcAgree_translate isOpen_thickening (circAgree_add_ofFun_cutoff hφψ) t d hd r hr
      fun u hu => self_subset_thickening hδ _ (add_mem_ball_inter t hu)
  rw [h1, translate_fc_eq (gs_add_ofFun hF hφ) t hd hr, Pi.add_apply, translate_fc_eq hF t hd hr]
  dsimp only
  congr 1
  simp only [ofFun]
  rw [← integral_fc_comp_add_real hφ d r t]
  refine integral_congr_ae ((ae_fc_mem_ball_inter hd hr).mono fun u hu => hφψ ?_)
  exact self_subset_cthickening _ (add_mem_ball_inter t hu)

/-- **Local rule under dilation.** -/
theorem fcAgree_rescale_add_ofFun {y : FieldSample} (hy : IsRegularSample y) (hWo : IsOpen W)
    {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ (W ∩ Hbar)) (Q : ℝ) {s : ℝ} (hs : 0 < s) :
    FcAgree ((fun z => (s : ℂ) * z) ⁻¹' W) (rescale (y + ofFun ψ) Q s)
      (rescale y Q s + ofFun (fun u => ψ ((s : ℂ) * u))) := by
  obtain ⟨F, hF⟩ := hy
  intro d hd r hr hdW
  obtain ⟨δ, hδ, φ, hφ, hφψ⟩ := exists_cutoff hWo hψ
    (isCompact_closedBall_inter_Hbar ((s : ℂ) * d) (s * r)) (rescale_K_subset hs hdW)
  have h1 : rescale (y + ofFun ψ) Q s (foldedCircle d r) =
      rescale (y + ofFun φ) Q s (foldedCircle d r) :=
    fcAgree_rescale isOpen_thickening (circAgree_add_ofFun_cutoff hφψ) Q hs d hd r hr
      fun u hu => self_subset_thickening hδ _ (mul_mem_ball_inter hs hu)
  have e : ofFun (fun u => ψ ((s : ℂ) * u)) (foldedCircle d r) =
      ∫ v, φ v ∂foldedCircle ((s : ℂ) * d) (s * r) := by
    simp only [ofFun]
    rw [← integral_fc_comp_mul hφ d r hs]
    refine integral_congr_ae ((ae_fc_mem_ball_inter hd hr).mono fun u hu => (hφψ ?_).symm)
    exact self_subset_cthickening _ (mul_mem_ball_inter hs hu)
  rw [h1, rescale_fc_eq (gs_add_ofFun hF hφ) Q hs d hr, Pi.add_apply, rescale_fc_eq hF Q hs d hr,
    e]
  dsimp only
  rw [foldH_of_mem' (mapsTo_mul_pos hs hd)]
  ring

/-- **Transfer of local area limits.** -/
theorem isVagueLimitOn_of_circAgree {γ : ℝ} (hWo : IsOpen W) (h : CircAgree W x x')
    {U : Set ℂ} (hUH : U ⊆ H) (hUW : U ⊆ W) {μ : Measure ℂ}
    (hμ : IsVagueLimitOn U (areaApprox γ x') μ) : IsVagueLimitOn U (areaApprox γ x) μ := by
  refine ⟨hμ.1, hμ.2.1, fun f hf hfc hfU => (hμ.2.2 f hf hfc hfU).congr' ?_⟩
  obtain ⟨δ, hδ, hδW⟩ := hfc.isCompact.exists_cthickening_subset_open hWo (hfU.trans hUW)
  filter_upwards [eventually_two_radius_lt hδ] with k hk
  have hd : ∀ y : FieldSample,
      Measurable fun z => radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z) := fun y =>
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_avgReg_slice y k)))
  have hn : ∀ (y : FieldSample) z, 0 ≤ radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z) :=
    fun y z => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  rw [areaApprox, areaApprox, integral_withDensity_ofReal (hd x') (hn x'),
    integral_withDensity_ofReal (hd x) (hn x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport f
  · show _ * f z = _ * f z
    rw [avgReg_eq_of_circAgree h (H_subset_Hbar (hUH (hfU hz))) ?_]
    intro v hv
    refine hδW (mem_cthickening_of_dist_le v z δ _ hz ?_)
    have := hv.1
    rw [mem_closedBall] at this
    linarith
  · show _ * f z = _ * f z
    simp [image_eq_zero_of_notMem_tsupport hz]

/-- **Transfer of local boundary limits.** -/
theorem isVagueLimitOnR_of_circAgree {γ : ℝ} (hWo : IsOpen W) (h : CircAgree W x x')
    {U : Set ℝ} (hUW : ∀ t ∈ U, (t : ℂ) ∈ W) {ν : Measure ℝ}
    (hν : IsVagueLimitOnR U (bdryApprox γ x') ν) : IsVagueLimitOnR U (bdryApprox γ x) ν := by
  refine ⟨hν.1, hν.2.1, fun f hf hfc hfU => (hν.2.2 f hf hfc hfU).congr' ?_⟩
  have hKc : IsCompact ((fun t : ℝ => (t : ℂ)) '' tsupport f) :=
    hfc.isCompact.image Complex.continuous_ofReal
  obtain ⟨δ, hδ, hδW⟩ := hKc.exists_cthickening_subset_open hWo
    (by rintro _ ⟨t, ht, rfl⟩; exact hUW t (hfU ht))
  filter_upwards [eventually_two_radius_lt hδ] with k hk
  have hd : ∀ y : FieldSample, Measurable fun t : ℝ =>
      radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg y k (t : ℂ)) := fun y =>
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_avgReg_slice y k).comp Complex.measurable_ofReal)))
  have hn : ∀ (y : FieldSample) (t : ℝ),
      0 ≤ radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg y k (t : ℂ)) :=
    fun y t => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  rw [bdryApprox, bdryApprox, integral_withDensity_ofReal (hd x') (hn x'),
    integral_withDensity_ofReal (hd x) (hn x)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ tsupport f
  · show _ * f t = _ * f t
    rw [avgReg_eq_of_circAgree h (show (0 : ℝ) ≤ (t : ℂ).im by simp) ?_]
    intro v hv
    refine hδW (mem_cthickening_of_dist_le v (t : ℂ) δ _ ⟨t, ht, rfl⟩ ?_)
    have := hv.1
    rw [mem_closedBall] at this
    linarith
  · show _ * f t = _ * f t
    simp [image_eq_zero_of_notMem_tsupport ht]

theorem isVagueLimitOn_H_of_good {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    IsVagueLimitOn H (areaApprox γ x) (qAreaMeasure γ x) := by
  obtain ⟨F, hF⟩ := hx.1
  obtain ⟨h0, hK, ht⟩ := hx.qAreaMeasure_spec
  refine ⟨h0, hK, fun f hf hfc hfU =>
    ((ht f hf hfc hfU).comp tendsto_one_goodFilter).congr fun k => ?_⟩
  simp only [Function.comp, goodRad, areaR_radius γ hF]

theorem isVagueLimitR_of_good {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    IsVagueLimitR (bdryApprox γ x) (qBoundaryMeasure γ x) := by
  obtain ⟨F, hF⟩ := hx.1
  obtain ⟨h0, ht⟩ := hx.qBoundaryMeasure_spec
  exact ⟨h0, fun f hf hfc => ((ht f hf hfc).comp tendsto_one_goodFilter).congr fun k => by
    simp only [Function.comp, goodRad, bdryR_radius γ hF]⟩

theorem isVagueLimitOn_restrict_sub {U U' : Set ℂ} (hU' : IsOpen U') (hUU : U' ⊆ U)
    {νs : ℕ → Measure ℂ} {μ : Measure ℂ} (h : IsVagueLimitOn U νs μ) :
    IsVagueLimitOn U' νs (μ.restrict U') := by
  obtain ⟨-, hK, ht⟩ := h
  refine ⟨by rw [Measure.restrict_apply' hU'.measurableSet]; simp, fun K hKc hKU =>
    (Measure.restrict_apply_le _ _).trans_lt (hK K hKc (hKU.trans hUU)), fun f hf hfc hfU => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (hfU h)]
  exact ht f hf hfc (hfU.trans hUU)

theorem isVagueLimitOnR_restrict_of {νs : ℕ → Measure ℝ} {ν : Measure ℝ}
    (h : IsVagueLimitR νs ν) {U : Set ℝ} (hU : IsOpen U) : IsVagueLimitOnR U νs (ν.restrict U) := by
  have := h.1
  refine ⟨?_, fun K hK _ => (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top,
    fun f hf hfc hfU => ?_⟩
  · rw [Measure.restrict_apply hU.measurableSet.compl, compl_inter_self, measure_empty]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h => ht (hfU h)]
    exact h.2 f hf hfc

end G

end Prop16Area

end QuantumZipper
