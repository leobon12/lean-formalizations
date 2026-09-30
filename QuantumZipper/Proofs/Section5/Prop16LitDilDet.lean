import QuantumZipper.Proofs.Section5.Prop16LitIdQ
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.LQG.AreaOffsetsBasic
import QuantumZipper.Proofs.Thm18.G1Rescale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the dilation rule, local deterministic form (COORD-CHANGE, D98)

`Prop16Lit.isVagueLimitOn_rescale_local`: the local analogue of `GoodTransforms.hasAreaLimit_rescale`
(M4-T3; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 2.1 for dilations). If a field `Z`
has, on an open `U ⊆ ℍ`, circle averages `w ↦ ⟨Z, fc(w, ρ)⟩` continuous on compacts for small `ρ`
and area approximations at **all** small radii (`areaR`) converging to `μ` against test functions
in `U`, then for every `s > 0` the rescaled field `Z(s ·) + Q log s` has local area limit
`(· / s)_* μ` on `s⁻¹ U`. This is the deterministic core of the dilation clause (2) of
`Prop16LitCovStmt` (the canonical description (1.8) rescales by the random scale `s`). Own
bookkeeping (copy of the global proof with the local circles).
-/

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open GoodSample GoodTransforms

/-- The circle average of the rescaled field at a small circle inside the domain. -/
theorem avgReg_rescale_local {Z : FieldSample} {s : ℝ} (hs : 0 < s) {K₂ : Set ℂ}
    (hK₂H : K₂ ⊆ Hbar) {ρ : ℝ} (hc : ContinuousOn (fun w => evalReg Z (foldedCircle w ρ)) K₂)
    (Q : ℝ) {k : ℕ} (hρk : ρ = s * radius k) {z : ℂ} (hzH : z ∈ Hbar)
    (hK : ∀ᶠ n in atTop, (s : ℂ) * dyadicRoundC n z ∈ K₂) (hzK : (s : ℂ) * z ∈ K₂) :
    avgReg (rescale Z Q s) k z = evalReg Z (foldedCircle ((s : ℂ) * z) ρ) + Q * Real.log s := by
  have hd : Tendsto (fun n => (s : ℂ) * dyadicRoundC n z) atTop (𝓝[K₂] ((s : ℂ) * z)) :=
    tendsto_nhdsWithin_iff.2 ⟨(RegClosure.tendsto_dyadicRoundC z).const_mul _, hK⟩
  have ht := ((hc _ hzK).tendsto.comp hd).add_const (Q * Real.log s)
  unfold avgReg
  refine Tendsto.limUnder_eq (ht.congr fun n => ?_)
  simp only [Function.comp_apply]
  rw [Thm18Asm.G1.rescale_fc_apply Z Q hs, RegClosure.foldH_mul_pos _ hs,
    CircleFubini.foldH_of_mem' (CircleCont.dyadicRoundC_mem_Hbar hzH n), hρk]

theorem areaDensK_rescale_eq {γ : ℝ} (hγ : 0 < γ) {Z : FieldSample} {s : ℝ} (hs : 0 < s) {k : ℕ}
    {z : ℂ} (h : avgReg (rescale Z (Qc γ) s) k z =
      evalReg Z (foldedCircle ((s : ℂ) * z) (s * radius k)) + Qc γ * Real.log s) :
    E6.areaDensK γ (rescale Z (Qc γ) s) k z = s ^ 2 * areaDens γ Z (s * radius k) ((s : ℂ) * z) := by
  unfold E6.areaDensK areaDens
  rw [h]
  have hQ : exp (γ * (Qc γ * Real.log s)) = s ^ 2 * s ^ (γ ^ 2 / 2) := by
    have h1 := gammaQ_area hγ
    rw [rpow_def_of_pos hs, show γ * (Qc γ * Real.log s) =
      Real.log (s ^ 2) + Real.log s * (γ ^ 2 / 2) by
        rw [Real.log_pow]; push_cast; linear_combination (Real.log s) * h1,
      exp_add, exp_log (by positivity)]
  rw [mul_rpow hs.le (radius_pos k).le, mul_add, exp_add, hQ]; ring

theorem measurable_areaDens_z (γ : ℝ) (Z : FieldSample) (r : ℝ) : Measurable (areaDens γ Z r) := by
  unfold areaDens
  exact measurable_const.mul (Real.measurable_exp.comp
    (((AreaOffsets.measurable_evalReg_fc r).comp (measurable_const.prodMk measurable_id)).const_mul γ))

/-- **The dilation rule, local form.** -/
theorem isVagueLimitOn_rescale_local {γ : ℝ} (hγ : 0 < γ) {Z : FieldSample} {U : Set ℂ}
    (hUo : IsOpen U) (hUH : U ⊆ H)
    (hcont : ∀ K, IsCompact K → K ⊆ U → ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ < ρ₀ →
      ContinuousOn (fun w => evalReg Z (foldedCircle w ρ)) K)
    {μ : Measure ℂ} (hμ0 : μ Uᶜ = 0) (hμK : ∀ K, IsCompact K → K ⊆ U → μ K < ∞)
    (hL : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun r => ∫ z, f z ∂areaR γ Z r) (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ)))
    {s : ℝ} (hs : 0 < s) :
    IsVagueLimitOn ((fun z => (s : ℂ) * z) ⁻¹' U) (areaApprox γ (rescale Z (Qc γ) s))
      (μ.map fun z => z / (s : ℂ)) := by
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set h : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (s : ℂ) hsc with hh
  have hsymm : ∀ z, h.symm z = z / s := fun z => by simp [hh, div_eq_inv_mul]
  have hmap : (fun z : ℂ => z / (s : ℂ)) = h.symm := funext fun z => (hsymm z).symm
  have hmeas : Measurable h.symm := h.symm.continuous.measurable
  have hpre : ∀ S : Set ℂ, h.symm ⁻¹' ((fun z => (s : ℂ) * z) ⁻¹' S) = S := fun S => by
    ext z; simp only [mem_preimage, hsymm, mul_div_cancel₀ _ hsc]
  rw [hmap]
  refine ⟨?_, fun K hK hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.map_apply hmeas (hUo.measurableSet.preimage (measurable_const_mul _)).compl,
      preimage_compl, hpre]
    exact hμ0
  · rw [Measure.map_apply hmeas hK.measurableSet]
    refine hμK _ (h.symm.isCompact_preimage.2 hK) fun z hz => ?_
    have := hKU hz
    simpa [hsymm, mul_div_cancel₀ _ hsc] using this
  -- the test function in the original coordinates
  set g : ℂ → ℝ := fun w => f (w / s) with hgdef
  have hgc : Continuous g := hf.comp (continuous_id.div_const _)
  have hge : g = f ∘ h.symm := funext fun w => by simp [hgdef, hsymm]
  have hgs : HasCompactSupport g := hge ▸ hfc.comp_homeomorph h.symm
  have hgU : tsupport g ⊆ U := by
    intro w hw
    rw [hge] at hw
    have := hfU (tsupport_comp_subset h.symm.continuous hw)
    simpa [hsymm, mul_div_cancel₀ _ hsc] using this
  rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
  have hsr : Tendsto (fun k : ℕ => s * radius k) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hs (radius_pos k)⟩
    simpa using (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul s
  have hlim := (hL g hgc hgs hgU).comp hsr
  have e : ∫ x, f (h.symm x) ∂μ = ∫ z, g z ∂μ := by simp only [hgdef, hsymm]
  rw [e]
  refine hlim.congr' ?_
  -- identification of the approximations
  set K := tsupport g with hKdef
  have hK : IsCompact K := hgs
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hK.exists_cthickening_subset_open hUo hgU
  have hK₂ : IsCompact (cthickening ε₀ K) := hK.cthickening
  obtain ⟨ρ₀, hρ₀, hρc⟩ := hcont _ hK₂ hε₀U
  have hrad : ∀ᶠ k in atTop, s * radius k < ρ₀ ∧ 2 * (s * radius k) ≤ ε₀ := by
    have ht : Tendsto (fun k => s * radius k) atTop (𝓝 0) := by
      simpa using (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul s
    exact (ht.eventually (gt_mem_nhds hρ₀)).and (ht.eventually (ge_mem_nhds
      (by linarith : (0 : ℝ) < ε₀ / 2)) |>.mono fun k hk => by linarith)
  filter_upwards [hrad] with k hk
  have hρk : 0 < s * radius k := mul_pos hs (radius_pos k)
  have hcK := hρc _ hρk hk.1
  have hK₂H : cthickening ε₀ K ⊆ Hbar := fun w hw => H_subset_Hbar (hUH (hε₀U hw))
  -- densities on the support of `f`
  have hdens : ∀ z ∈ tsupport f, E6.areaDensK γ (rescale Z (Qc γ) s) k z =
      s ^ 2 * areaDens γ Z (s * radius k) ((s : ℂ) * z) := by
    intro z hz
    have hszK : (s : ℂ) * z ∈ K := by
      rw [hKdef, hge]
      refine (tsupport_comp_eq_preimage f h.symm).symm ▸ ?_
      show h.symm ((s : ℂ) * z) ∈ tsupport f
      rwa [hsymm, mul_div_cancel_left₀ _ hsc]
    have hzH : z ∈ Hbar := by
      have h1 : (0 : ℝ) < ((s : ℂ) * z).im := hUH (hgU hszK)
      rw [Complex.im_ofReal_mul] at h1
      exact (pos_of_mul_pos_right h1 hs.le).le
    refine areaDensK_rescale_eq hγ hs (avgReg_rescale_local hs hK₂H hcK (Qc γ) rfl hzH ?_
      (self_subset_cthickening K hszK))
    have hn := (RegClosure.tendsto_dyadicRoundC z).eventually
      (Metric.ball_mem_nhds z (by positivity : (0 : ℝ) < ε₀ / s))
    filter_upwards [hn] with n hn
    refine mem_cthickening_of_dist_le _ _ ε₀ K hszK ?_
    rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have := mem_ball.1 hn
    rw [dist_eq_norm] at this
    have h2 : s * ‖dyadicRoundC n z - z‖ < s * (ε₀ / s) := mul_lt_mul_of_pos_left this hs
    rw [mul_div_cancel₀ _ hs.ne'] at h2
    exact h2.le
  simp only [Function.comp_apply]
  rw [E6.integral_areaApprox_eq]
  have e1 : ∫ z in H, E6.areaDensK γ (rescale Z (Qc γ) s) k z * f z =
      ∫ z in H, s ^ 2 * (areaDens γ Z (s * radius k) ((s : ℂ) * z) * f z) := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport f
    · simp only; rw [hdens z hz]; ring
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have h2 := integral_H_comp_mul (fun w => areaDens γ Z (s * radius k) w * g w) hs
  simp only [hgdef, mul_div_cancel_left₀ _ hsc] at h2
  rw [e1, integral_const_mul, h2, areaR, integral_withDensity_ofReal
    (measurable_areaDens_z γ Z _) (fun w => by unfold areaDens; positivity)]
  have hs2 : s ^ 2 ≠ 0 := by positivity
  field_simp
  rfl

/-- **Local regularity of a field on `U`**: continuous small circle averages on compacts, dyadic
averages equal to the regularized circle values eventually on compacts, and area approximations
at all small radii converging to `μ` against test functions in `U`. -/
def LocalAreaRegular (γ : ℝ) (Z : FieldSample) (U : Set ℂ) (μ : Measure ℂ) : Prop :=
  μ Uᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ U → μ K < ∞) ∧
  (∀ K, IsCompact K → K ⊆ U → ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ < ρ₀ →
    ContinuousOn (fun w => evalReg Z (foldedCircle w ρ)) K) ∧
  (∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, ∀ z ∈ K,
    avgReg Z k z = evalReg Z (foldedCircle z (radius k))) ∧
  ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
    Tendsto (fun r => ∫ z, f z ∂areaR γ Z r) (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ))

/-- The dyadic area approximations converge to the same limit. -/
theorem LocalAreaRegular.isVagueLimitOn {γ : ℝ} {Z : FieldSample} {U : Set ℂ} {μ : Measure ℂ}
    (h : LocalAreaRegular γ Z U μ) : IsVagueLimitOn U (areaApprox γ Z) μ := by
  obtain ⟨h0, hK, -, havg, hL⟩ := h
  refine ⟨h0, hK, fun f hf hfc hfU => ?_⟩
  refine ((hL f hf hfc hfU).comp RegClosure.tendsto_radius_nhdsGT).congr' ?_
  filter_upwards [havg _ hfc hfU] with k hk
  simp only [Function.comp_apply]
  rw [E6.integral_areaApprox_eq, areaR, integral_withDensity_ofReal
    (measurable_areaDens_z γ Z _) (fun w => mul_nonneg (rpow_nonneg (radius_pos k).le _)
      (exp_pos _).le)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport f
  · simp only [E6.areaDensK, areaDens, hk z hz]
  · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]

end Prop16Lit
end QuantumZipper
