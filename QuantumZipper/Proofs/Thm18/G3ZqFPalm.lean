import QuantumZipper.Proofs.Thm18.G3Za11
import QuantumZipper.Proofs.Thm18.G3Zc2Univ
import QuantumZipper.Proofs.Thm18.G2RootSetup
import QuantumZipper.Proofs.Zipper.E5Model2
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-FIX (D): the zoom of the G2 Palm field through a G0 map

The Palm field of the G2 scheme at a fixed point `x ≠ 0` is
`normField γ (xPalm γ x) = 𝔥₀ + X + ψ_x − (X + ψ_x)(S)` with the Palm shift
`ψ_x = γ/2 (neumannH x − kPot S)` (`S = refS`). Near `x` its profile
`f₀ = 𝔥₀ + ψ_x = γ(−log|· − x|) + h₀` (`h₀` continuous, harmonic near `x`), so ZOOM-A's
agreement `G3Za.ae_agreeNear_zoom_palm` applies to `normAt S (ofFun f₀ + X)`, which has the same
raw values as the Palm field at every folded circle near `x` (`normField_xPalm_fc`: both profile
parts are integrable there, and `𝔥₀ = 0` on the unit circle). Hence (`ae_agreeNear_zoom_g2Palm`)
a.s., for every level, the zoom of the Palm field at `x` through a G0 map agrees near `0` with the
ZOOM-C form `zoomS` of the translated free field, at a deterministically shifted level.

Sheffield, arXiv:1012.4797, pp. 70–71 (the field near a quantum-typical point); Duplantier–Sheffield
arXiv:0808.1560 §3.3 (Palm formula `h + γ(−log|x − ·|)`). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqF

open S5.FieldLaw.Raw D3Plus

/-- The Palm profile of the G2 Palm field, in the frame translated by `x`. -/
def g2f (γ x : ℝ) : ℂ → ℝ := fun u => h0rev (γ ^ 2) (u + x) + g2PalmPsi γ x (u + x)

/-- The mean of the Palm profile on the normalizing semicircle. -/
def g2K (γ x : ℝ) : ℝ := ∫ u, (h0rev (γ ^ 2) u + g2PalmPsi γ x u) ∂refS

/-- The continuous part of the Palm profile (untranslated frame). -/
def g2h0 (γ x : ℝ) (u : ℂ) : ℝ :=
  2 / Real.sqrt (γ ^ 2) * Real.log (max ‖u‖ (|x| / 2)) - γ / 2 * PalmNorm.kPot refS u

/-- The continuous part of the Palm profile (translated frame). -/
def g2h (γ x : ℝ) (u : ℂ) : ℝ := g2h0 γ x (u + x)

theorem kPot_refS_eq' (u : ℂ) : PalmNorm.kPot refS u = -2 * Real.posLog ‖u‖ := by
  rw [show refS = foldedCircle 0 1 from rfl, kPot_refS_eq]

theorem continuous_kPot_refS : Continuous (PalmNorm.kPot refS) := by
  have e : PalmNorm.kPot refS = fun u => -2 * Real.posLog ‖u‖ := funext kPot_refS_eq'
  rw [e]
  exact continuous_const.mul (Real.continuous_posLog.comp continuous_norm)

theorem continuous_g2h0 (γ : ℝ) {x : ℝ} (hx : x ≠ 0) : Continuous (g2h0 γ x) := by
  have hx2 : 0 < |x| / 2 := by positivity
  exact (continuous_const.mul ((continuous_norm.max continuous_const).log
    fun u => (lt_max_of_lt_right hx2).ne')).sub (continuous_const.mul continuous_kPot_refS)

theorem measurable_g2PalmPsi (γ x : ℝ) : Measurable (g2PalmPsi γ x) := by
  have h1 : Measurable fun u : ℂ => neumannH (x : ℂ) u :=
    measurable_neumannH.comp (measurable_const.prodMk measurable_id)
  show Measurable fun u => γ / 2 * (neumannH (x : ℂ) u - PalmNorm.kPot refS u)
  exact (h1.sub continuous_kPot_refS.measurable).const_mul _

theorem measurable_h0rev (γ : ℝ) : Measurable (h0rev (γ ^ 2)) := by
  show Measurable fun z : ℂ => 2 / Real.sqrt (γ ^ 2) * Real.log ‖z‖
  exact (Real.measurable_log.comp measurable_norm).const_mul _

theorem neumannH_real (x : ℝ) (u : ℂ) : neumannH (x : ℂ) u = -2 * Real.log ‖u - x‖ := by
  simp only [neumannH]
  have e2 : ‖(x : ℂ) - conj u‖ = ‖u - x‖ := by
    rw [show (x : ℂ) - conj u = conj ((x : ℂ) - u) by simp [map_sub], Complex.norm_conj,
      norm_sub_rev]
  rw [e2, norm_sub_rev]
  ring

theorem ae_norm_refS : ∀ᵐ v ∂refS, ‖v‖ = 1 := by
  rw [show refS = foldedCircle 0 1 from rfl, foldedCircle,
    ae_map_iff measurable_foldH.aemeasurable (measurableSet_eq_fun measurable_norm measurable_const)]
  filter_upwards [K3.ae_mem_sphere_circleUnif_k3 (0 : ℂ) one_pos] with v hv
  have h1 : ‖v‖ = 1 := by simpa using mem_sphere_iff_norm.1 hv
  have h2 := K3.norm_foldH_sub_ofReal (0 : ℝ) v
  simp only [Complex.ofReal_zero, sub_zero] at h2
  rw [h2, h1]

/-- **Properties of the translated Palm profile** (the hypotheses of ZOOM-C's cores). -/
theorem g2f_props {γ : ℝ} (hγ : 0 < γ) {x : ℝ} (hx : x ≠ 0) (hx1 : |x| < 1) {ρf : ℝ}
    (hρf : 0 < ρf) (hρx : ρf ≤ |x| / 2) (hρ1 : ρf < 1 - |x|) :
    (∀ u ∈ Metric.closedBall (0 : ℂ) ρf ∩ Hbar, g2f γ x u = γ * -Real.log ‖u‖ + g2h γ x u) ∧
    Continuous (g2h γ x) ∧ Measurable (g2f γ x) ∧
    InnerProductSpace.HarmonicOnNhd (g2h γ x) (Metric.ball (0 : ℂ) ρf) ∧
    (∀ u ∈ Metric.ball (0 : ℂ) ρf, g2h γ x ((starRingEnd ℂ) u) = g2h γ x u) ∧
    IsAdmissibleH (palmCRho refS x) ∧ palmCRho refS x Set.univ = 1 ∧
    (∀ᵐ y ∂palmCRho refS x, ρf < ‖y‖) ∧
    IsAdmissibleH ((palmCRho refS x).map (· + (x : ℂ))) := by
  have hx' : ‖((x : ℝ) : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hadm : IsAdmissibleH (palmCRho refS x) :=
    isAdmissibleH_map_add_real (G3Cv.isAdmissibleH_foldedCircle_g3cv2 0 one_pos) (-x)
  refine ⟨fun u hu => ?_, (continuous_g2h0 γ hx).comp (continuous_id.add continuous_const),
    ((measurable_h0rev γ).comp (measurable_id.add_const _)).add
      ((measurable_g2PalmPsi γ x).comp (measurable_id.add_const _)), fun z hz => ?_,
    fun u _ => ?_, hadm, by rw [palmCRho, map_add_real_univ, measure_univ], ?_,
    isAdmissibleH_map_add_real hadm x⟩
  · have hu1 : ‖u‖ ≤ ρf := by simpa using hu.1
    have hge : |x| / 2 ≤ ‖u + x‖ := by
      have := norm_sub_norm_le (x : ℂ) (-u)
      rw [hx', norm_neg, sub_neg_eq_add, add_comm] at this
      linarith
    simp only [g2f, g2h, g2h0, g2PalmPsi, h0rev, neumannH_real, max_eq_left hge,
      add_sub_cancel_right]
    ring
  · have hz' : ‖z‖ < ρf := by simpa using hz
    have hev : g2h γ x =ᶠ[𝓝 z] fun w => (2 / Real.sqrt (γ ^ 2)) • Real.log ‖w + (x : ℂ)‖ := by
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
      simp only [g2h, g2h0, kPot_refS_eq', max_eq_left h1.le, smul_eq_mul]
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
    have hH := (hA.harmonicAt_log_norm hne).const_smul (c := 2 / Real.sqrt (γ ^ 2))
    refine (InnerProductSpace.harmonicAt_congr_nhds hev).2 ?_
    convert hH using 1
    rfl
  · have e : ‖conj u + (x : ℂ)‖ = ‖u + x‖ := by
      rw [show conj u + (x : ℂ) = conj (u + x) by simp, Complex.norm_conj]
    simp only [g2h, g2h0, kPot_refS_eq', e]
  · rw [palmCRho, ae_map_iff (measurable_add_const _).aemeasurable
      (measurableSet_lt measurable_const measurable_norm)]
    filter_upwards [ae_norm_refS] with v hv
    have h1 := norm_sub_le (v + ((-x : ℝ) : ℂ)) ((-x : ℝ) : ℂ)
    rw [add_sub_cancel_right, hv, Complex.norm_real, Real.norm_eq_abs, abs_neg] at h1
    linarith

/-- `evalReg` only reads the raw values at folded circles near the support. -/
theorem evalReg_congr_at {h h' : FieldSample} {x b : ℝ}
    (hag : ∀ (c : ℂ) (s : ℝ), 0 < s → ‖c - x‖ + s < b →
      h (foldedCircle c s) = h' (foldedCircle c s))
    {ν : Measure ℂ} {ρ : ℝ} (hν : ∀ᵐ w ∂ν, ‖w - (x : ℂ)‖ ≤ ρ) (hρ : ρ < b) :
    evalReg h ν = evalReg h' ν := by
  unfold evalReg
  apply limUnder_congr_eventually
  obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt (sub_pos.2 hρ)
  filter_upwards [eventually_ge_atTop K] with k hk
  refine integral_congr_ae ?_
  filter_upwards [hν] with w hw
  unfold avgReg
  apply limUnder_congr_eventually
  have hc : Tendsto (fun n => ‖dyadicRoundC n w - x‖ + radius k) atTop
      (𝓝 (‖w - x‖ + radius k)) :=
    ((continuous_norm.tendsto (w - x)).comp
      ((RegClosure.tendsto_dyadicRoundC w).sub_const (x : ℂ))).add_const _
  have hlt : ‖w - x‖ + radius k < b := by linarith [hK k hk]
  filter_upwards [hc.eventually (gt_mem_nhds hlt)] with n hn
  exact hag _ _ (radius_pos k) hn

local notation "Ω₀" => gffBase.Ω

/-- The G2 Palm field and the ZOOM-A form of it have the same raw values at folded circles
near `x`. -/
theorem normField_xPalm_fc (γ : ℝ) {x : ℝ} (hx : x ≠ 0) (ω : Ω₀) {c : ℂ} {s : ℝ} (hs : 0 < s)
    (hcs : ‖c - x‖ + s < |x| / 2) :
    normField γ (xPalm γ x) ω (foldedCircle c s) =
      PalmNorm.normAt refS (ofFun (fun u => h0rev (γ ^ 2) u + g2PalmPsi γ x u) + gffBase.X ω)
        (foldedCircle c s) := by
  have hx2 : 0 < |x| / 2 := by positivity
  have hsupp : ∀ᵐ u ∂foldedCircle c s, u ∈ closedBall (x : ℂ) (‖c - x‖ + s) ∩ Hbar :=
    G3Cv.ae_mem_of_compl_null_g3cv
      (G3Cv.foldedCircle_compl_null (b := x) (ρ := ‖c - x‖ + s) hs le_rfl)
  have hI1 : Integrable (h0rev (γ ^ 2)) (foldedCircle c s) := by
    have hcont : Continuous fun u : ℂ => 2 / Real.sqrt (γ ^ 2) * Real.log (max ‖u‖ (|x| / 2)) :=
      continuous_const.mul ((continuous_norm.max continuous_const).log
        fun u => (lt_max_of_lt_right hx2).ne')
    have hc := E5.integrable_foldedCircle_of_continuousOn (r := ‖c‖ + s + 1)
      hcont.continuousOn c s hs (by linarith)
    refine hc.congr ?_
    filter_upwards [hsupp] with u hu
    have h1 : ‖u - x‖ ≤ ‖c - x‖ + s := by
      have := hu.1; rwa [mem_closedBall, dist_eq_norm] at this
    have hge : |x| / 2 ≤ ‖u‖ := by
      have := norm_sub_norm_le (x : ℂ) (x - u)
      rw [Complex.norm_real, Real.norm_eq_abs, sub_sub_cancel, norm_sub_rev] at this
      linarith
    show _ = 2 / Real.sqrt (γ ^ 2) * Real.log ‖u‖
    rw [max_eq_left hge]
  have hI2 : Integrable (g2PalmPsi γ x) (foldedCircle c s) := by
    have hN := D3Plus.integrable_neumannH_right_adm
      (G3Cv.isAdmissibleH_foldedCircle_g3cv2 c hs) (x : ℂ)
    have hK := E5.integrable_foldedCircle_of_continuousOn (r := ‖c‖ + s + 1)
      continuous_kPot_refS.continuousOn c s hs (by linarith)
    show Integrable (fun u => γ / 2 * (neumannH (x : ℂ) u - PalmNorm.kPot refS u)) _
    exact (hN.sub hK).const_mul _
  have hsplit : ∫ u, (h0rev (γ ^ 2) u + g2PalmPsi γ x u) ∂foldedCircle c s =
      ∫ u, h0rev (γ ^ 2) u ∂foldedCircle c s + ∫ u, g2PalmPsi γ x u ∂foldedCircle c s :=
    integral_add hI1 hI2
  have hrefS : ∫ u, (h0rev (γ ^ 2) u + g2PalmPsi γ x u) ∂refS = ∫ u, g2PalmPsi γ x u ∂refS :=
    integral_congr_ae (ae_norm_refS.mono fun u hu => by simp [h0rev, hu])
  simp only [normField, xPalm, PalmNorm.normAt, addConst, ofFun, Pi.add_apply, measure_univ,
    ENNReal.toReal_one, mul_one]
  rw [hsplit, hrefS]
  ring

/-- **The zoom of the G2 Palm field through a G0 map agrees near `0` with `zoomS`** of the
translated free field, at the level shifted by `γ ∫ f₀ dS` (a.s., all levels). -/
theorem ae_agreeNear_zoom_g2Palm {γ : ℝ} (hγ : 0 < γ) {x : ℝ} (hx : x ≠ 0) (hx1 : |x| < 1)
    {r₀ : ℝ} {ψ : ℂ → ℂ} (hr₀ : 0 < r₀) (hψ : IsG0Map r₀ ψ) :
    ∃ r : ℝ, 0 < r ∧ ∀ᵐ ω ∂gffBase.P, ∀ L : ℝ,
      D3Plus.AgreeNear (zoomFieldVia γ L (normField γ (xPalm γ x) ω) x ψ)
        (G3Cv.zoomS γ (L - γ * g2K γ x) (Qc γ) (g2f γ x) ψ (palmCRho refS x)
          (G3Cv.rawTranslate (gffBase.X ω) x)) r := by
  have hx2 : 0 < |x| / 2 := by positivity
  set f₀ : ℂ → ℝ := fun u => h0rev (γ ^ 2) u + g2PalmPsi γ x u with hf₀
  have hf : ∀ u ∈ closedBall (x : ℂ) (|x| / 2) ∩ Hbar,
      f₀ u = γ * -Real.log ‖u - x‖ + g2h0 γ x u := by
    intro u hu
    have h1 : ‖u - x‖ ≤ |x| / 2 := by
      have := hu.1; rwa [mem_closedBall, dist_eq_norm] at this
    have hge : |x| / 2 ≤ ‖u‖ := by
      have := norm_sub_norm_le (x : ℂ) (x - u)
      rw [Complex.norm_real, Real.norm_eq_abs, sub_sub_cancel, norm_sub_rev] at this
      linarith
    simp only [hf₀, g2h0, g2PalmPsi, h0rev, neumannH_real, max_eq_left hge]
    ring
  have hfm : Measurable f₀ := (measurable_h0rev γ).add (measurable_g2PalmPsi γ x)
  obtain ⟨r₁, hr₁, hae⟩ := G3Za.ae_agreeNear_zoom_palm gffBase.gff hr₀ hψ γ hx2 hf
    (continuous_g2h0 γ hx) hfm refS
  have hψc : ContinuousAt ψ 0 := (hψ.1.differentiableAt (ball_mem_nhds 0 hr₀)).continuousAt
  obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousAt_iff.1 hψc (|x| / 4) (by positivity)
  refine ⟨min (min r₁ δ) r₀, lt_min (lt_min hr₁ hδ) hr₀, ?_⟩
  filter_upwards [hae] with ω hω L n k z hz
  have hz1 : ‖dyadicRoundC n z‖ + radius k < r₁ :=
    lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
  have hz2 : ‖dyadicRoundC n z‖ + radius k < δ :=
    lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))
  have hz3 : ‖dyadicRoundC n z‖ + radius k < r₀ := lt_of_lt_of_le hz (min_le_right _ _)
  have e1 := hω L n k z hz1
  -- the translated fields agree near `0`
  have hT : AgreeNear (translate (normField γ (xPalm γ x) ω) (x : ℂ))
      (translate (PalmNorm.normAt refS (ofFun f₀ + gffBase.X ω)) (x : ℂ)) (|x| / 2) := by
    intro n' k' z' hz'
    show evalReg _ _ = evalReg _ _
    refine evalReg_congr_at (x := x) (b := |x| / 2)
      (fun c s hs hcs => normField_xPalm_fc γ hx ω hs hcs)
      (ρ := ‖dyadicRoundC n' z'‖ + radius k') ?_ hz'
    refine (ae_map_iff (measurable_add_const _).aemeasurable
      (measurableSet_le ((measurable_id.sub_const _).norm) measurable_const)).2 ?_
    filter_upwards [G3Cv.ae_mem_of_compl_null_g3cv (G3Cv.foldedCircle_compl_null (b := 0)
      (ρ := ‖dyadicRoundC n' z'‖ + radius k') (radius_pos k') (by simp))] with u hu
    have : ‖u‖ ≤ ‖dyadicRoundC n' z'‖ + radius k' := by simpa using hu.1
    simpa using this
  have hkey : zoomFieldVia γ L (normField γ (xPalm γ x) ω) x ψ
        (foldedCircle (dyadicRoundC n z) (radius k)) =
      zoomFieldVia γ L (PalmNorm.normAt refS (ofFun f₀ + gffBase.X ω)) x ψ
        (foldedCircle (dyadicRoundC n z) (radius k)) := by
    have hE : evalReg (translate (normField γ (xPalm γ x) ω) (x : ℂ))
        ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ) =
        evalReg (translate (PalmNorm.normAt refS (ofFun f₀ + gffBase.X ω)) (x : ℂ))
        ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ) := by
      have hsp : ∀ᵐ u ∂foldedCircle (dyadicRoundC n z) (radius k),
          u ∈ closedBall ((0 : ℝ) : ℂ) (‖dyadicRoundC n z‖ + radius k) ∩ Hbar :=
        G3Cv.ae_mem_of_compl_null_g3cv (G3Cv.foldedCircle_compl_null (b := 0)
          (ρ := ‖dyadicRoundC n z‖ + radius k) (radius_pos k) (by simp))
      have hm : AEMeasurable ψ (foldedCircle (dyadicRoundC n z) (radius k)) := by
        have h1 := hψ.1.continuousOn.aemeasurable (μ := foldedCircle (dyadicRoundC n z) (radius k))
          (measurableSet_ball (x := (0 : ℂ)) (ε := r₀))
        rwa [Measure.restrict_eq_self_of_ae_mem (hsp.mono fun u hu => by
          have : ‖u‖ ≤ ‖dyadicRoundC n z‖ + radius k := by simpa using hu.1
          rw [mem_ball, dist_zero_right]; linarith)] at h1
      refine D3Plus.evalReg_congr hT (ρ := |x| / 4) ?_ (by linarith)
      have h : ∀ᵐ w ∂(foldedCircle (dyadicRoundC n z) (radius k)).map ψ,
              w ∈ closedBall (0 : ℂ) (|x| / 4) := by
        refine (ae_map_iff hm measurableSet_closedBall).2 ?_
        filter_upwards [hsp] with u hu
        have hu' : ‖u‖ < δ := by
          have : ‖u‖ ≤ ‖dyadicRoundC n z‖ + radius k := by simpa using hu.1
          linarith
        have := hδψ (by rwa [dist_zero_right])
        rw [hψ.2.2.2.1, dist_zero_right] at this
        show dist (ψ u) 0 ≤ |x| / 4
        rw [dist_zero_right]
        exact this.le
      exact mem_ae_iff.1 h
    simp only [zoomFieldVia, addConst, coordChange]
    rw [hE]
  have hr : G3Cv.rawTranslate (gffBase.X ω) x (palmCRho refS x) = gffBase.X ω refS := by
    simp only [G3Cv.rawTranslate, palmCRho]
    rw [Measure.map_map (measurable_add_const _) (measurable_add_const _)]
    have hid : ((· + (x : ℂ)) ∘ (· + ((-x : ℝ) : ℂ))) = id := by
      funext u; simp
    rw [hid, Measure.map_id]
  have hsec : addConst (coordChange (ofFun (fun u => f₀ (u + x)) + G3Cv.rawTranslate (gffBase.X ω) x)
        ψ (Qc γ)) (L / γ - (ofFun f₀ + gffBase.X ω) refS) =
      G3Cv.zoomS γ (L - γ * g2K γ x) (Qc γ) (g2f γ x) ψ (palmCRho refS x)
        (G3Cv.rawTranslate (gffBase.X ω) x) := by
    unfold G3Cv.zoomS
    congr 1
    rw [hr]
    have hK : ofFun f₀ refS = g2K γ x := rfl
    simp only [Pi.add_apply, hK]
    field_simp
    ring
  rw [hkey, e1, hsec]

end G3ZqF
end Thm18Asm
end QuantumZipper
