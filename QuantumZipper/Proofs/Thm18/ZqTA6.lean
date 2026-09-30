import QuantumZipper.Proofs.Thm18.ZqTA5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (A6): Palm profiles `c log|·| + ψ_x` (the `V + logSing` Palm field)

The Palm field of `V + logSing` at a fixed point `x ≠ 0` (`logSing = (2/γ − γ) log|·|`) has the
profile `lf c γ x = c log|·| + ψ_x`, `c = 2/γ − γ`, `ψ_x = γ/2 (neumannH x − kPot S)`; the free
field's is the case `c = 2/γ` (`G3ZqF.g2f`). Near `x` the profile is `γ(−log|· − x|)` plus a
continuous function harmonic near `x` (`|x| ≠ 1`), so the ZOOM-A agreement
`G3Za.ae_agreeNear_zoom_palm` applies verbatim: `tf_props_near`, `tf_props_far`,
`ae_agreeNear_zoom_logC` (copies of `G3ZqF.g2f_props` / `G3ZqF.ae_agreeNear_zoom_g2Palm` with the
coefficient `c` in place of `2/γ`).

Sheffield, arXiv:1012.4797, pp. 70–71 and proof of Prop. 5.5, p. 65; Duplantier–Sheffield,
arXiv:0808.1560, §3.3. Own bookkeeping (copies of proved lemmas).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT
namespace LogC

open S5.FieldLaw.Raw D3Plus G3ZqF

/-- The Palm profile `c log|·| + ψ_x`. -/
def lf (c γ x : ℝ) : ℂ → ℝ := fun u => c * Real.log ‖u‖ + g2PalmPsi γ x u

/-- The Palm profile in the frame translated by `x`. -/
def tf (c γ x : ℝ) : ℂ → ℝ := fun u => lf c γ x (u + x)

/-- The continuous part (untranslated frame). -/
def th0 (c γ x : ℝ) (u : ℂ) : ℝ :=
  c * Real.log (max ‖u‖ (|x| / 2)) - γ / 2 * PalmNorm.kPot refS u

/-- The continuous part (translated frame). -/
def th (c γ x : ℝ) (u : ℂ) : ℝ := th0 c γ x (u + x)

/-- The mean of the profile on the normalizing semicircle. -/
def tK (c γ x : ℝ) : ℝ := ∫ u, lf c γ x u ∂refS

theorem continuous_th0 (c γ : ℝ) {x : ℝ} (hx : x ≠ 0) : Continuous (th0 c γ x) := by
  have hx2 : 0 < |x| / 2 := by positivity
  exact (continuous_const.mul ((continuous_norm.max continuous_const).log
    fun u => (lt_max_of_lt_right hx2).ne')).sub (continuous_const.mul continuous_kPot_refS)

theorem tf_props_near {γ c : ℝ} (hγ : 0 < γ) {x : ℝ} (hx : x ≠ 0) (hx1 : |x| < 1) {ρf : ℝ}
    (hρf : 0 < ρf) (hρx : ρf ≤ |x| / 2) (hρ1 : ρf < 1 - |x|) :
    (∀ u ∈ Metric.closedBall (0 : ℂ) ρf ∩ Hbar, tf c γ x u = γ * -Real.log ‖u‖ + th c γ x u) ∧
    Continuous (th c γ x) ∧ Measurable (tf c γ x) ∧
    InnerProductSpace.HarmonicOnNhd (th c γ x) (Metric.ball (0 : ℂ) ρf) ∧
    (∀ u ∈ Metric.ball (0 : ℂ) ρf, th c γ x ((starRingEnd ℂ) u) = th c γ x u) ∧
    IsAdmissibleH (palmCRho refS x) ∧ palmCRho refS x Set.univ = 1 ∧
    (∀ᵐ y ∂palmCRho refS x, ρf < ‖y‖) ∧
    IsAdmissibleH ((palmCRho refS x).map (· + (x : ℂ))) := by
  have hx' : ‖((x : ℝ) : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hadm : IsAdmissibleH (palmCRho refS x) :=
    isAdmissibleH_map_add_real (G3Cv.isAdmissibleH_foldedCircle_g3cv2 0 one_pos) (-x)
  refine ⟨fun u hu => ?_, (continuous_th0 c γ hx).comp (continuous_id.add continuous_const),
    (((Real.measurable_log.comp measurable_norm).const_mul c).comp (measurable_id.add_const _)).add
      ((measurable_g2PalmPsi γ x).comp (measurable_id.add_const _)), fun z hz => ?_,
    fun u _ => ?_, hadm, by rw [palmCRho, map_add_real_univ, measure_univ], ?_,
    isAdmissibleH_map_add_real hadm x⟩
  · have hu1 : ‖u‖ ≤ ρf := by simpa using hu.1
    have hge : |x| / 2 ≤ ‖u + x‖ := by
      have := norm_sub_norm_le (x : ℂ) (-u)
      rw [hx', norm_neg, sub_neg_eq_add, add_comm] at this
      linarith
    simp only [tf, lf, th, th0, g2PalmPsi, neumannH_real, max_eq_left hge,
      add_sub_cancel_right]
    ring
  · have hz' : ‖z‖ < ρf := by simpa using hz
    have hev : th c γ x =ᶠ[𝓝 z] fun w => c • Real.log ‖w + (x : ℂ)‖ := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      have hw' : ‖w‖ < ρf := by simpa using hw
      have h1 : |x| / 2 < ‖w + x‖ := by
        have := norm_sub_norm_le (x : ℂ) (-w)
        rw [hx', norm_neg, sub_neg_eq_add, add_comm] at this
        linarith
      have h2 : ‖w + x‖ ≤ 1 := by
        have := norm_add_le w (x : ℂ)
        rw [hx'] at this
        linarith
      simp only [th, th0, kPot_refS_eq', max_eq_left h1.le, smul_eq_mul]
      rw [(Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (norm_nonneg _)]; exact h2)]
      ring
    have hne : z + (x : ℂ) ≠ 0 := by
      intro h0
      have h3 : ‖z + (x : ℂ)‖ = 0 := by rw [h0, norm_zero]
      have := norm_sub_norm_le (x : ℂ) (-z)
      rw [hx', norm_neg, sub_neg_eq_add, add_comm] at this
      have := abs_pos.2 hx
      linarith
    have hA : AnalyticAt ℂ (fun u : ℂ => u + x) z := analyticAt_id.add analyticAt_const
    have hH := (hA.harmonicAt_log_norm hne).const_smul (c := c)
    refine (InnerProductSpace.harmonicAt_congr_nhds hev).2 ?_
    convert hH using 1
    rfl
  · have e : ‖conj u + (x : ℂ)‖ = ‖u + x‖ := by
      rw [show conj u + (x : ℂ) = conj (u + x) by simp, Complex.norm_conj]
    simp only [th, th0, kPot_refS_eq', e]
  · rw [palmCRho, ae_map_iff (measurable_add_const _).aemeasurable
      (measurableSet_lt measurable_const measurable_norm)]
    filter_upwards [ae_norm_refS] with v hv
    have h1 := norm_sub_le (v + ((-x : ℝ) : ℂ)) ((-x : ℝ) : ℂ)
    rw [add_sub_cancel_right, hv, Complex.norm_real, Real.norm_eq_abs, abs_neg] at h1
    linarith

theorem tf_props_far {γ c : ℝ} (hγ : 0 < γ) {x : ℝ} (hx : x ≠ 0) (hx1 : 1 < |x|) {ρf : ℝ}
    (hρf : 0 < ρf) (hρx : ρf ≤ |x| / 2) (hρ1 : ρf < |x| - 1) :
    (∀ u ∈ Metric.closedBall (0 : ℂ) ρf ∩ Hbar, tf c γ x u = γ * -Real.log ‖u‖ + th c γ x u) ∧
    Continuous (th c γ x) ∧ Measurable (tf c γ x) ∧
    InnerProductSpace.HarmonicOnNhd (th c γ x) (Metric.ball (0 : ℂ) ρf) ∧
    (∀ u ∈ Metric.ball (0 : ℂ) ρf, th c γ x ((starRingEnd ℂ) u) = th c γ x u) ∧
    IsAdmissibleH (palmCRho refS x) ∧ palmCRho refS x Set.univ = 1 ∧
    (∀ᵐ y ∂palmCRho refS x, ρf < ‖y‖) ∧
    IsAdmissibleH ((palmCRho refS x).map (· + (x : ℂ))) := by
  have hx' : ‖((x : ℝ) : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hadm : IsAdmissibleH (palmCRho refS x) :=
    isAdmissibleH_map_add_real (G3Cv.isAdmissibleH_foldedCircle_g3cv2 0 one_pos) (-x)
  refine ⟨fun u hu => ?_, (continuous_th0 c γ hx).comp (continuous_id.add continuous_const),
    (((Real.measurable_log.comp measurable_norm).const_mul c).comp (measurable_id.add_const _)).add
      ((measurable_g2PalmPsi γ x).comp (measurable_id.add_const _)), fun z hz => ?_,
    fun u _ => ?_, hadm, by rw [palmCRho, map_add_real_univ, measure_univ], ?_,
    isAdmissibleH_map_add_real hadm x⟩
  · have hu1 : ‖u‖ ≤ ρf := by simpa using hu.1
    have hge : |x| / 2 ≤ ‖u + x‖ := by
      have := norm_sub_norm_le (x : ℂ) (-u)
      rw [hx', norm_neg, sub_neg_eq_add, add_comm] at this
      linarith
    simp only [tf, lf, th, th0, g2PalmPsi, neumannH_real, max_eq_left hge,
      add_sub_cancel_right]
    ring
  · have hz' : ‖z‖ < ρf := by simpa using hz
    have hev : th c γ x =ᶠ[𝓝 z] fun w => (c + γ) • Real.log ‖w + (x : ℂ)‖ := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      have hw' : ‖w‖ < ρf := by simpa using hw
      have h1 : |x| / 2 < ‖w + x‖ := by
        have := norm_sub_norm_le (x : ℂ) (-w)
        rw [hx', norm_neg, sub_neg_eq_add, add_comm] at this
        linarith
      have h2 : 1 ≤ ‖w + x‖ := by
        have := norm_sub_norm_le (x : ℂ) (-w)
        rw [hx', norm_neg, sub_neg_eq_add, add_comm] at this
        linarith
      simp only [th, th0, kPot_refS_eq', max_eq_left h1.le, smul_eq_mul]
      rw [Real.posLog_eq_log (by rw [abs_of_nonneg (norm_nonneg _)]; exact h2)]
      ring
    have hne : z + (x : ℂ) ≠ 0 := by
      intro h0
      have h3 : ‖z + (x : ℂ)‖ = 0 := by rw [h0, norm_zero]
      have := norm_sub_norm_le (x : ℂ) (-z)
      rw [hx', norm_neg, sub_neg_eq_add, add_comm] at this
      have := abs_pos.2 hx
      linarith
    have hA : AnalyticAt ℂ (fun u : ℂ => u + x) z := analyticAt_id.add analyticAt_const
    have hH := (hA.harmonicAt_log_norm hne).const_smul (c := c + γ)
    refine (InnerProductSpace.harmonicAt_congr_nhds hev).2 ?_
    convert hH using 1
    rfl
  · have e : ‖conj u + (x : ℂ)‖ = ‖u + x‖ := by
      rw [show conj u + (x : ℂ) = conj (u + x) by simp, Complex.norm_conj]
    simp only [th, th0, kPot_refS_eq', e]
  · rw [palmCRho, ae_map_iff (measurable_add_const _).aemeasurable
      (measurableSet_lt measurable_const measurable_norm)]
    filter_upwards [ae_norm_refS] with v hv
    have h1 := norm_sub_le (v + ((-x : ℝ) : ℂ)) v
    rw [add_sub_cancel_left, hv, Complex.norm_real, Real.norm_eq_abs, abs_neg] at h1
    linarith

/-- **The zoom of the Palm field with profile `c log|·| + ψ_x` through a G0 map agrees near `0`
with `zoomS`** of the translated free field (copy of `G3ZqF.ae_agreeNear_zoom_g2Palm`). -/
theorem ae_agreeNear_zoom_logC {γ c : ℝ} (hγ : 0 < γ) {x : ℝ} (hx : x ≠ 0)
    {r₀ : ℝ} {ψ : ℂ → ℂ} (hr₀ : 0 < r₀) (hψ : IsG0Map r₀ ψ) :
    ∃ r : ℝ, 0 < r ∧ ∀ᵐ ω ∂gffBase.P, ∀ L : ℝ,
      D3Plus.AgreeNear (zoomFieldVia γ L (PalmNorm.normAt refS (ofFun (lf c γ x) + gffBase.X ω)) x ψ)
        (G3Cv.zoomS γ (L - γ * tK c γ x) (Qc γ) (tf c γ x) ψ (palmCRho refS x)
          (G3Cv.rawTranslate (gffBase.X ω) x)) r := by
  have hx2 : 0 < |x| / 2 := by positivity
  set f₀ : ℂ → ℝ := lf c γ x with hf₀
  have hf : ∀ u ∈ closedBall (x : ℂ) (|x| / 2) ∩ Hbar,
      f₀ u = γ * -Real.log ‖u - x‖ + th0 c γ x u := by
    intro u hu
    have h1 : ‖u - x‖ ≤ |x| / 2 := by
      have := hu.1; rwa [mem_closedBall, dist_eq_norm] at this
    have hge : |x| / 2 ≤ ‖u‖ := by
      have := norm_sub_norm_le (x : ℂ) (x - u)
      rw [Complex.norm_real, Real.norm_eq_abs, sub_sub_cancel, norm_sub_rev] at this
      linarith
    simp only [hf₀, lf, th0, g2PalmPsi, neumannH_real, max_eq_left hge]
    ring
  have hfm : Measurable f₀ :=
    ((Real.measurable_log.comp measurable_norm).const_mul c).add (measurable_g2PalmPsi γ x)
  obtain ⟨r₁, hr₁, hae⟩ := G3Za.ae_agreeNear_zoom_palm gffBase.gff hr₀ hψ γ hx2 hf
    (continuous_th0 c γ hx) hfm refS
  refine ⟨min r₁ r₀, lt_min hr₁ hr₀, ?_⟩
  filter_upwards [hae] with ω hω L n k z hz
  have hz1 : ‖dyadicRoundC n z‖ + radius k < r₁ := lt_of_lt_of_le hz (min_le_left _ _)
  have e1 := hω L n k z hz1
  have hr : G3Cv.rawTranslate (gffBase.X ω) x (palmCRho refS x) = gffBase.X ω refS := by
    simp only [G3Cv.rawTranslate, palmCRho]
    rw [Measure.map_map (measurable_add_const _) (measurable_add_const _)]
    have hid : ((· + (x : ℂ)) ∘ (· + ((-x : ℝ) : ℂ))) = id := by
      funext u; simp
    rw [hid, Measure.map_id]
  have hsec : addConst (coordChange (ofFun (fun u => f₀ (u + x)) + G3Cv.rawTranslate (gffBase.X ω) x)
        ψ (Qc γ)) (L / γ - (ofFun f₀ + gffBase.X ω) refS) =
      G3Cv.zoomS γ (L - γ * tK c γ x) (Qc γ) (tf c γ x) ψ (palmCRho refS x)
        (G3Cv.rawTranslate (gffBase.X ω) x) := by
    unfold G3Cv.zoomS
    congr 1
    rw [hr]
    have hK : ofFun f₀ refS = tK c γ x := rfl
    simp only [Pi.add_apply, hK]
    field_simp
    ring
  rw [e1, hsec]

end LogC
end ZqT
end Thm18Asm
end QuantumZipper
