import QuantumZipper.Proofs.Thm18.G3Za10
import QuantumZipper.Proofs.Thm18.G3Za8
import QuantumZipper.Proofs.Thm18.G3Z2bPalm
import QuantumZipper.Proofs.Thm18.G3PalmRTightBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, items (a) + (b): the one-point Palm core for the Palm field of `G3WedgePalmIdStmt`

The Palm field at a Palm point `x` (`0 < |x| ≤ 1/2`) is `normAt g3zS (ofFun (palmProf γ x) + V)`
with `palmProf γ x = shiftFun γ (Lf (γ − 2/γ)) g3zS x` (`G3WedgePalmIdStmt`). Near `x`,

  `palmProf γ x u = γ(−log ‖u − x‖) + palmH γ x u`,
  `palmH γ x u = (γ − 2/γ)(−log max(‖u‖, |x|/2)) + γ log⁺ ‖u‖`

(`palmProf_eq`: `kPot g3zS = −2 log⁺ ‖·‖`, `neumannH x = −2 log |· − x|` for real `x`), and
`palmH γ x (· + x)` is harmonic and conjugation-invariant on `ball 0 (|x|/2)`.

* `ae_agreeNear_zoom_palmField` (any probability space, any free `V`): almost surely, for
  every level `L`, the zoom `zoomFieldVia γ L (Palm field) x ψ` agrees near `0` with
  `addConst (coordChange (ofFun (palmProf γ x (· + x)) + V_x) ψ Q) (L/γ − ∫ palmProf dS − V_x(S_x))`,
  where `V_x = rawTranslate V x` (a free field) and `S_x = fc(−x, 1)`;
* `exists_g0Setup_palmField` (the coupling on `stdP`): for a free `W` and D3⁺ `Setup` data with
  `α = γ`, almost surely, for every `L`,
  `addConst (coordChange (ofFun (palmProf γ x (· + x)) + W) ψ Q) (L/γ − W(S_x))` agrees near `0`
  with `zoomModel γ γ L fc(0,s) X' g`.

The two right/left sides have the same form (the Palm level is shifted by the deterministic
`γ ∫ palmProf dS`), so after the law transfer `V_x ↔ W` (free fields, through the dyadic data)
D3⁺(i) with `α = γ` applies to the zoom of the Palm field. Sources: Sheffield arXiv:1012.4797
pp. 70–71 (the field near a quantum-typical point); DS11 §3.3 (Palm formula). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Za

open G3Cv K3 GFFExist LQGDimension.ExistAsm InnerProductSpace D3Plus

/-- The Palm profile of `G3WedgePalmIdStmt`. -/
abbrev palmProf (γ x : ℝ) : ℂ → ℝ :=
  PalmNorm.shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x

/-- Its continuous part near `x`. -/
def palmH (γ x : ℝ) (u : ℂ) : ℝ :=
  (γ - 2 / γ) * -Real.log (max ‖u‖ (|x| / 2)) + γ * Real.posLog ‖u‖

theorem palmProf_eq (γ x : ℝ) {u : ℂ} (hu : |x| / 2 ≤ ‖u‖) :
    palmProf γ x u = γ * -Real.log ‖u - x‖ + palmH γ x u := by
  simp only [palmProf, PalmNorm.shiftFun, LogSingGood.Lf, neumannH, R18.g3zS,
    Thm18Asm.kPot_refS_eq, palmH, max_eq_left hu]
  have e1 : ‖(x : ℂ) - u‖ = ‖u - x‖ := norm_sub_rev _ _
  have e2 : ‖(x : ℂ) - conj u‖ = ‖u - x‖ := by
    rw [show (x : ℂ) - conj u = conj ((x : ℂ) - u) by simp [map_sub], Complex.norm_conj,
      norm_sub_rev]
  rw [e1, e2]
  ring

theorem continuous_palmH (γ : ℝ) {x : ℝ} (hx : x ≠ 0) : Continuous (palmH γ x) := by
  have hx2 : 0 < |x| / 2 := by positivity
  refine (continuous_const.mul ((continuous_norm.max continuous_const).log
    fun u => (lt_max_of_lt_right hx2).ne').neg).add
    (continuous_const.mul (Real.continuous_posLog.comp continuous_norm))

theorem measurable_palmProf (γ x : ℝ) : Measurable (palmProf γ x) := by
  have e : palmProf γ x = fun u => (γ - 2 / γ) * -Real.log ‖u‖ +
      γ / 2 * (neumannH (x : ℂ) u - -2 * Real.posLog ‖u‖) := by
    funext u
    simp only [palmProf, PalmNorm.shiftFun, LogSingGood.Lf, R18.g3zS, Thm18Asm.kPot_refS_eq]
  rw [e]
  have h1 : Measurable fun u : ℂ => neumannH (x : ℂ) u :=
    measurable_neumannH.comp (measurable_const.prodMk measurable_id)
  have h2 : Measurable fun u : ℂ => Real.log ‖u‖ := Real.measurable_log.comp measurable_norm
  have h3 : Measurable fun u : ℂ => Real.posLog ‖u‖ :=
    Real.continuous_posLog.measurable.comp measurable_norm
  exact (h2.neg.const_mul _).add ((h1.sub (h3.const_mul _)).const_mul _)

/-- The profile in the translated frame, near `0`. -/
theorem palmProf_shift_eq (γ : ℝ) {x : ℝ} {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (|x| / 2)) :
    palmProf γ x (u + x) = γ * -Real.log ‖u‖ + palmH γ x (u + x) := by
  have hu' : ‖u‖ ≤ |x| / 2 := by simpa using hu
  have h : |x| / 2 ≤ ‖u + x‖ := by
    have := norm_sub_norm_le (x : ℂ) (-u)
    rw [Complex.norm_real, Real.norm_eq_abs, norm_neg, sub_neg_eq_add, add_comm] at this
    linarith
  rw [palmProf_eq γ x h, add_sub_cancel_right]

theorem harmonicOnNhd_palmH_shift (γ : ℝ) {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≤ 1 / 2) :
    HarmonicOnNhd (fun u => palmH γ x (u + x)) (ball (0 : ℂ) (|x| / 2)) := by
  intro z hz
  have hev : (fun u => palmH γ x (u + x)) =ᶠ[𝓝 z]
      fun u => (γ - 2 / γ) • -Real.log ‖u + x‖ := by
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    have hu' : ‖u‖ < |x| / 2 := by simpa using hu
    have h1 : |x| / 2 < ‖u + x‖ := by
      have := norm_sub_norm_le (x : ℂ) (-u)
      rw [Complex.norm_real, Real.norm_eq_abs, norm_neg, sub_neg_eq_add, add_comm] at this
      linarith
    have h2 : ‖u + x‖ ≤ 1 := by
      have := norm_add_le u (x : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    simp only [palmH, max_eq_left h1.le, smul_eq_mul]
    rw [(Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (norm_nonneg _)]; exact h2)]
    ring
  have hne : z + x ≠ 0 := by
    intro h0
    have hz' : ‖z‖ < |x| / 2 := by simpa using hz
    have : z = -(x : ℂ) := eq_neg_of_add_eq_zero_left h0
    rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hz'
    have := abs_pos.2 hx
    linarith
  have hA : AnalyticAt ℂ (fun u : ℂ => u + x) z := analyticAt_id.add analyticAt_const
  have hH := (hA.harmonicAt_log_norm hne).neg.const_smul (c := γ - 2 / γ)
  refine (harmonicAt_congr_nhds hev).2 ?_
  convert hH using 1
  funext v
  simp

theorem palmH_shift_conj (γ x : ℝ) (u : ℂ) :
    palmH γ x (conj u + x) = palmH γ x (u + x) := by
  have e : conj u + (x : ℂ) = conj (u + x) := by simp
  simp only [palmH, e, Complex.norm_conj]

/-- The translated normalizing circle. -/
theorem fc_neg_far {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≤ 1 / 2) :
    ∀ᵐ y ∂foldedCircle (-(x : ℂ)) 1, |x| / 2 < ‖y‖ := by
  rw [foldedCircle, ae_map_iff measurable_foldH.aemeasurable
    (measurableSet_lt measurable_const measurable_norm)]
  filter_upwards [K3.ae_mem_sphere_circleUnif_k3 (-(x : ℂ)) one_pos] with v hv
  have h1 : ‖v - (-(x : ℂ))‖ = 1 := by simpa using mem_sphere_iff_norm.1 hv
  have h2 : ‖foldH v - ((-x : ℝ) : ℂ)‖ = ‖v - ((-x : ℝ) : ℂ)‖ :=
    K3.norm_foldH_sub_ofReal (-x) v
  push_cast at h2
  rw [h1] at h2
  have h3 := norm_sub_le (foldH v) (-(x : ℂ))
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at h3
  have h4 := abs_pos.2 hx
  linarith

/-- **The zoom of the Palm field of `G3WedgePalmIdStmt` through a G0 map** (any space). -/
theorem ae_agreeNear_zoom_palmField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {V : Ω → FieldSample} (hV : IsFreeGFFModConstH V P)
    {r₀ : ℝ} {ψ : ℂ → ℂ} (hr₀ : 0 < r₀) (hψ : Thm18Asm.IsG0Map r₀ ψ) (γ : ℝ)
    {x : ℝ} (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ᵐ ω ∂P, ∀ L : ℝ,
      AgreeNear (Thm18Asm.zoomFieldVia γ L
          (PalmNorm.normAt R18.g3zS (ofFun (palmProf γ x) + V ω)) x ψ)
        (addConst (coordChange (ofFun (fun u => palmProf γ x (u + x)) +
            rawTranslate (V ω) x) ψ (Qc γ))
          (L / γ - ((∫ u, palmProf γ x u ∂R18.g3zS) +
            rawTranslate (V ω) x (foldedCircle (-(x : ℂ)) 1)))) r := by
  have hρ : 0 < |x| / 2 := by positivity
  have hf : ∀ u ∈ closedBall (x : ℂ) (|x| / 2) ∩ Hbar,
      palmProf γ x u = γ * -Real.log ‖u - x‖ + palmH γ x u := by
    intro u hu
    refine palmProf_eq γ x ?_
    have h1 : ‖u - x‖ ≤ |x| / 2 := by
      have := hu.1; rwa [mem_closedBall, dist_eq_norm] at this
    have := norm_sub_norm_le (x : ℂ) (x - u)
    rw [Complex.norm_real, Real.norm_eq_abs, sub_sub_cancel, norm_sub_rev] at this
    linarith
  obtain ⟨r, hr, hae⟩ := ae_agreeNear_zoom_palm hV hr₀ hψ γ hρ hf (continuous_palmH γ hx)
    (measurable_palmProf γ x) R18.g3zS
  refine ⟨r, hr, hae.mono fun ω hω L => ?_⟩
  have e : rawTranslate (V ω) x (foldedCircle (-(x : ℂ)) 1) = V ω R18.g3zS := by
    simp only [rawTranslate, R18.g3zS]
    rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, IndepParams.fc_map_add_real]
    congr 2; push_cast; ring
  rw [e]
  exact hω L

end G3Za
end QuantumZipper
