import QuantumZipper.Proofs.Thm18.ZqTA4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (A5): the free Palm certificate beyond the unit disc

Copies, for fixed Palm points `|x| > 1`, of the proved `|x| < 1` chain (`G3ZqF.g2f_props`,
`G3ZqF.ae_agreeNear_zoom_g2Palm`, `ZqR.ae_locCertC_palm`). The only change is the normalizing
semicircle: for `|x| > 1` the Palm profile near `x` is `(2/γ + γ) log|· + x|`
(`kPot S = −2 log⁺|·|`, and `log⁺ = log` off the unit disc), still harmonic, and the translated
semicircle stays at distance `≥ |x| − 1` from `0`. Hence `g3ZqTFreeFarPalmStmt_holds`,
`g3ZqTFreeFarStmt_holds`, and `G3ZqTSchemeSideStmt` from `G3ZqTVPalmStmt` alone.

Sheffield, arXiv:1012.4797, pp. 70–71 and proof of Prop. 5.5, p. 65; Duplantier–Sheffield,
arXiv:0808.1560, §3.3. Own bookkeeping (copies of proved lemmas).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT
namespace FarA

open S5.FieldLaw.Raw D3Plus G3ZqF

local notation "Ω₀" => gffBase.Ω

/-- **Properties of the translated Palm profile** (the hypotheses of ZOOM-C's cores). -/
theorem g2f_props_far {γ : ℝ} (hγ : 0 < γ) {x : ℝ} (hx : x ≠ 0) (hx1 : 1 < |x|) {ρf : ℝ}
    (hρf : 0 < ρf) (hρx : ρf ≤ |x| / 2) (hρ1 : ρf < |x| - 1) :
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
    have hev : g2h γ x =ᶠ[𝓝 z] fun w => (2 / Real.sqrt (γ ^ 2) + γ) • Real.log ‖w + (x : ℂ)‖ := by
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
      simp only [g2h, g2h0, kPot_refS_eq', max_eq_left h1.le, smul_eq_mul]
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
    have hH := (hA.harmonicAt_log_norm hne).const_smul (c := 2 / Real.sqrt (γ ^ 2) + γ)
    refine (InnerProductSpace.harmonicAt_congr_nhds hev).2 ?_
    convert hH using 1
    rfl
  · have e : ‖conj u + (x : ℂ)‖ = ‖u + x‖ := by
      rw [show conj u + (x : ℂ) = conj (u + x) by simp, Complex.norm_conj]
    simp only [g2h, g2h0, kPot_refS_eq', e]
  · rw [palmCRho, ae_map_iff (measurable_add_const _).aemeasurable
      (measurableSet_lt measurable_const measurable_norm)]
    filter_upwards [ae_norm_refS] with v hv
    have h1 := norm_sub_le (v + ((-x : ℝ) : ℂ)) v
    rw [add_sub_cancel_left, hv, Complex.norm_real, Real.norm_eq_abs, abs_neg] at h1
    linarith

/-- **The zoom of the G2 Palm field through a G0 map agrees near `0` with `zoomS`** of the
translated free field, at the level shifted by `γ ∫ f₀ dS` (a.s., all levels). -/
theorem ae_agreeNear_zoom_g2Palm_any {γ : ℝ} (hγ : 0 < γ) {x : ℝ} (hx : x ≠ 0)
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
    refine G3ZqF.evalReg_congr_at (x := x) (b := |x| / 2)
      (fun c s hs hcs => G3ZqF.normField_xPalm_fc γ hx ω hs hcs)
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

open Factorization G3ZqL D3Plus LQGMeas G3Cv S5.FieldLaw.Raw K3 GFFExist LQGDimension.ExistAsm ZqR

/-- **The local certificate of the pulled-back Palm field at a fixed Palm point.** -/
theorem ae_locCertC_palm_far {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a) {side : Bool} {x : ℝ}
    (hxs : x ∈ g1SideHalf side) (hx1 : 1 < |x|) :
    ∀ᵐ ω ∂gffBase.P, LocCertC γ (G3Z2b2.g3coordsM γ 0 Ψ side (normField γ (xPalm γ x) ω, a, 1, x)) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hxs
    cases side <;> simp [g1SideHalf] at hxs
  -- the local map and its G0 extension
  set y₀ : FieldSample := fun _ => 0 with hy₀
  obtain ⟨r₀, hr₀, Φ, hΦ, heqΦ⟩ := G3ZqF.g3mapP_g0Ext hsel ha hxs y₀
  obtain ⟨rA, hrA, hAg⟩ := ae_agreeNear_zoom_g2Palm_any hγ hx0 hr₀ hΦ
  -- the profile
  set ρf : ℝ := min (|x| / 2) ((|x| - 1) / 2) with hρf
  have hax : 0 < |x| := abs_pos.2 hx0
  have hρf0 : 0 < ρf := lt_min (by positivity) (by linarith)
  have hρfx : ρf ≤ |x| / 2 := min_le_left _ _
  have hρf1 : ρf < |x| - 1 := by
    have := min_le_right (|x| / 2) ((|x| - 1) / 2); linarith
  obtain ⟨hf, hh, hfm, hhh, hhc, hSa, hS1, hSf, -⟩ :=
    g2f_props_far hγ hx0 hx1 hρf0 hρfx hρf1
  -- the coupling with a D3⁺ model
  obtain ⟨r, s, hr, -, E', _, U, X', Ξ, g, hU, hSet, hag, -⟩ :=
    G3Za.G3ZqF.exists_g0Setup_palm_far_le hr₀ hΦ hγ hγ2 hρf0 hf hh hfm hhh hhc hSa hS1 hSf
  obtain ⟨Ψ', r₀', ρ, r₁, m, M, -, hD, heq⟩ := pullData_of_isG0Map hr₀ hΦ
  have hΨ0 : Ψ' 0 = 0 := by rw [heq (mem_ball_self hD.conf.pos)]; exact hΦ.2.2.2.1
  have hM := hD.bl.2.1
  set ρ' : ℝ := min ρ (ρf / (2 * M)) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hD.hρ (by positivity)
  have hDs := hD.shrink hρ'0 (min_le_left _ _)
  have hMρ : M * ρ' < ρf := by
    have h1 : ρ' ≤ ρf / (2 * M) := min_le_right _ _
    have h2 : M * ρ' ≤ M * (ρf / (2 * M)) := mul_le_mul_of_nonneg_left h1 hM.le
    have h3 : M * (ρf / (2 * M)) = ρf / 2 := by
      rw [mul_div_assoc', mul_comm 2 M, mul_div_mul_left _ _ hM.ne']
    linarith
  set r'' : ℝ := min (min r ρ') (min rA r₀) with hr''
  have hr''0 : 0 < r'' := lt_min (lt_min hr hρ'0) (lt_min hrA hr₀)
  have hr''r : r'' ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hr''ρ : r'' ≤ ρ' := (min_le_left _ _).trans (min_le_right _ _)
  have hr''A : r'' ≤ rA := (min_le_right _ _).trans (min_le_left _ _)
  have hr''0' : r'' ≤ r₀ := (min_le_right _ _).trans (min_le_right _ _)
  -- the level and the zoom
  set L' : ℝ := 0 - γ * G3ZqF.g2K γ x with hL'
  set Zf : FieldSample → FieldSample := fun y =>
    zoomS γ L' (Qc γ) (G3ZqF.g2f γ x) Φ (palmCRho refS x) y with hZf
  set V := fun ω =>  rawTranslate (gffBase.X ω) x with hVdef
  have hV : IsFreeGFFModConstH V gffBase.P := isFree_rawTranslate gffBase.gff x
  obtain ⟨hmU, hmV, hlaw⟩ := dyadLaw_eq_free hDs hΨ0 heq hf hh hfm hMρ γ L' (Qc γ) hSa hS1
    hr''ρ hU hV
  -- the certificate event
  set T : Set (DyIdxIn r'' → ℝ) := {ξ | LocCertC γ (coords (dyadField r'' ξ))} with hT
  have hTm : MeasurableSet T :=
    (measurableSet_locCertC γ).preimage (measurable_coords.comp (measurable_dyadField r''))
  have hcS : ∀ᵐ ω ∂stdP, dyadData r'' (Zf (U ω)) ∈ T := by
    filter_upwards [hag, AreaOffsets.ae_isLQGGood hSet.hX hγ hγ2,
      AreaExist.ae_isVagueLimitOn_qAreaMeasure hSet.hX hγ hγ2,
      PositivityArea.ae_forall_pos_qAreaMeasure hSet.hX hγ hγ2] with ω hω hgood hvag hpos
    have hg : ContinuousOn (g ω) (ball (0 : ℂ) r'' ∩ Hbar) :=
      (continuousOn_g_of_harm (hSet.harm ω)).mono fun z hz =>
        ⟨ball_subset_ball hr''r hz.1, hz.2⟩
    have hch : AgreeNear (reconstruct (coords (dyadField r'' (dyadData r'' (Zf (U ω))))))
        (zoomModel γ γ L' (foldedCircle 0 s) (X' ω) (g ω)) r'' :=
      agreeNear_trans (agreeNear_reconstruct_coords _ r'')
        (agreeNear_trans (agreeNear_dyadField r'' (Zf (U ω))).symm'
          (AgreeNear.mono_radius (hω L') hr''r))
    exact locCertC_of_agree_model hγ.ne' hr''0 hgood.1 hvag hpos hg hch
  have h0 : gffBase.P ((fun ω => dyadData r'' (Zf (V ω))) ⁻¹' Tᶜ) = 0 := by
    rw [← Measure.map_apply₀ hmV hTm.compl.nullMeasurableSet, ← hlaw,
      Measure.map_apply₀ hmU hTm.compl.nullMeasurableSet]
    exact ae_iff.1 hcS
  filter_upwards [hAg, measure_eq_zero_iff_ae_notMem.1 h0] with ω hA hω
  have hωT : dyadData r'' (Zf (V ω)) ∈ T := by
    by_contra hc
    exact hω hc
  set y : FieldSample := normField γ (xPalm γ x) ω with hy
  have hmap : G3Z2b2.g3mapP Ψ side (y, a, 1, x) = G3Z2b2.g3mapP Ψ side (y₀, a, 1, x) := rfl
  have hco : G3Z2b2.g3coordsM γ 0 Ψ side (y, a, 1, x) =
      coords (zoomFieldVia γ 0 y x (G3Z2b2.g3mapP Ψ side (y₀, a, 1, x))) := by
    rw [G3Z2b2.g3coordsM_eq (p := (y, a, 1, x)) hsel 0 side ha.1 ha.2 one_pos, hmap]
  rw [hco]
  have hZ : AgreeNear (zoomFieldVia γ 0 y x (G3Z2b2.g3mapP Ψ side (y₀, a, 1, x))) (Zf (V ω)) r'' :=
    agreeNear_trans
      (AgreeNear.mono_radius (G3ZqF.agreeNear_zoomFieldVia_of_eqOn heqΦ γ 0 y x) hr''0')
      (AgreeNear.mono_radius (hA 0) hr''A)
  refine locCertC_congr hr''0 hωT ?_
  exact agreeNear_trans (agreeNear_reconstruct_coords _ r'')
    (agreeNear_trans (agreeNear_dyadField r'' (Zf (V ω))).symm'
      (agreeNear_trans hZ.symm' (agreeNear_reconstruct_coords _ r'').symm'))

end FarA

open FarA G3ZqL

/-- **`G3ZqTFreeFarPalmStmt` holds.** -/
theorem g3ZqTFreeFarPalmStmt_holds : G3ZqTFreeFarPalmStmt := by
  intro γ hγ hγ2 Ψ hsel a ha
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : 1 < |x| := by rw [abs_of_pos (by linarith [show (1 : ℝ) < x from hx])]; exact hx
  have hxs : x ∈ g1SideHalf false := by
    simp only [g1SideHalf, Bool.false_eq_true, if_false, mem_Ioi]
    linarith [show (1 : ℝ) < x from hx]
  exact ae_locCertC_palm_far hγ hγ2 hsel ha hxs hx1

theorem g3ZqTFreeFarStmt_holds : G3ZqTFreeFarStmt := g3ZqTFreeFarStmt_of g3ZqTFreeFarPalmStmt_holds

end ZqT
end Thm18Asm
end QuantumZipper
