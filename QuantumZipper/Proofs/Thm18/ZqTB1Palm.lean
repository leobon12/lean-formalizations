import QuantumZipper.Proofs.Thm18.ZqT8Partner
import QuantumZipper.Proofs.Thm18.G3ZqL20TypQ
import QuantumZipper.Proofs.Thm18.G3ZqL10Cert
import QuantumZipper.Proofs.GFF.CircleContinuity
import QuantumZipper.Proofs.Thm18.G3ZqL11Reg
import QuantumZipper.Proofs.Thm18.G3ZqTop
import QuantumZipper.Proofs.Thm18.G3ZqPath
import QuantumZipper.Proofs.Thm18.G3ZqFLeaf
import QuantumZipper.Proofs.Thm18.G3ZqG3LRegG
import QuantumZipper.Proofs.Thm18.G3ZqG3Unif
import QuantumZipper.Proofs.Thm18.G3ZqSTop
import QuantumZipper.Proofs.Thm18.G3ZqS2Top
import QuantumZipper.Proofs.Thm18.G3ZqO7CoreD
import QuantumZipper.Proofs.Thm18.G3ZqL14RegU
import QuantumZipper.Proofs.Thm18.ZqR2Palm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (B1): the local certificate at fixed Palm points of the log-singular field

`g3ZqTVPalmStmt_holds : G3ZqTVPalmStmt`. For a good path `a`, a free field `V` on any
probability space and a fixed point `x` of the side half-line with `|x| ≠ 1` (so Lebesgue-a.e.
point), almost surely the pulled-back zoomed Palm field of `V + logSing` at `x`,
`g3coordsM γ 0 Ψ side (normAt g3zS (ofFun (palmProf γ x) + V ω), a, 1, x)`, carries `LocCertC`.

Route: the same as ZQ-REG's `ZqR.ae_locCertC_palm` (for the G2 Palm field at `|x| < 1`), with
ZOOM-A's Palm core for the wedge Palm field (`G3Za.ae_agreeNear_zoom_palmField`, any space and any
free field), and ZOOM-A's coupled core `G3Za.exists_g0Setup_palm` used at the profile radius
`ρₓ = min(|x|/2, |1 − |x||/2)` instead of `|x|/2` (the latter restricts ZOOM-A's
`exists_g0Setup_palmField` to `|x| ≤ 1/2`): on `B(0, ρₓ)` the continuous part
`palmH γ x (· + x)` is a multiple of `log ‖· + x‖` (harmonic, conjugation-invariant), and the
translated normalizing circle `fc(−x, 1)` stays at distance `> ρₓ` from `0`.

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 65 ("once we condition on `x`"), pp. 70–71
(near a quantum-typical point the field is a free boundary GFF plus `γ(−log|·|)` plus a smooth
function); Duplantier–Sheffield, arXiv:0808.1560, §3.3 (rooted measure: `h + γ(−log|x − ·|)`).
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric ComplexConjugate
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT
namespace ZqTB

open Factorization G3ZqL D3Plus LQGMeas G3Cv S5.FieldLaw.Raw K3 GFFExist
  LQGDimension.ExistAsm InnerProductSpace

/-- The profile radius at `x`. -/
def rhoX (x : ℝ) : ℝ := min (|x| / 2) ((abs (1 - |x|)) / 2)

theorem rhoX_le_left (x : ℝ) : rhoX x ≤ |x| / 2 := min_le_left _ _

theorem rhoX_le_right (x : ℝ) : rhoX x ≤ (abs (1 - |x|)) / 2 := min_le_right _ _

theorem rhoX_pos {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) : 0 < rhoX x := by
  have h1 : 0 < |x| := abs_pos.2 hx
  have h2 : 0 < (abs (1 - |x|)) := abs_pos.2 (sub_ne_zero.2 (Ne.symm hx1))
  exact lt_min (by positivity) (by positivity)

/-- On `B(0, ρₓ)` the continuous part of the Palm profile is a multiple of `log ‖· + x‖`. -/
theorem palmH_shift_eq_log (γ : ℝ) {x : ℝ} (hx1 : |x| ≠ 1) :
    ∃ c : ℝ, ∀ u ∈ ball (0 : ℂ) (rhoX x), G3Za.palmH γ x (u + x) = c * Real.log ‖u + x‖ := by
  have hxn : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hlow : ∀ u ∈ ball (0 : ℂ) (rhoX x), |x| / 2 < ‖u + x‖ := by
    intro u hu
    have hu' : ‖u‖ < rhoX x := by simpa using hu
    have := norm_sub_norm_le (x : ℂ) (-u)
    rw [hxn, norm_neg, sub_neg_eq_add, add_comm] at this
    linarith [rhoX_le_left x]
  have hbd : ∀ u ∈ ball (0 : ℂ) (rhoX x), ‖u‖ < (abs (1 - |x|)) / 2 := by
    intro u hu
    have hu' : ‖u‖ < rhoX x := by simpa using hu
    linarith [rhoX_le_right x]
  rcases lt_or_gt_of_ne hx1 with h | h
  · refine ⟨-(γ - 2 / γ), fun u hu => ?_⟩
    have hu2 := hbd u hu
    rw [abs_of_pos (by linarith)] at hu2
    have h2 : ‖u + x‖ ≤ 1 := by
      have := norm_add_le u (x : ℂ)
      rw [hxn] at this
      linarith
    simp only [G3Za.palmH, max_eq_left (hlow u hu).le]
    rw [(Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (norm_nonneg _)]; exact h2)]
    ring
  · refine ⟨-(γ - 2 / γ) + γ, fun u hu => ?_⟩
    have hu2 := hbd u hu
    rw [abs_of_neg (by linarith)] at hu2
    have h2 : 1 ≤ ‖u + x‖ := by
      have := norm_sub_norm_le (x : ℂ) (-u)
      rw [hxn, norm_neg, sub_neg_eq_add, add_comm] at this
      linarith
    simp only [G3Za.palmH, max_eq_left (hlow u hu).le]
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg (norm_nonneg _)]; exact h2)]
    ring

theorem harmonicOnNhd_palmH_shift_X (γ : ℝ) {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) :
    HarmonicOnNhd (fun u => G3Za.palmH γ x (u + x)) (ball (0 : ℂ) (rhoX x)) := by
  obtain ⟨c, hc⟩ := palmH_shift_eq_log γ hx1
  intro z hz
  have hev : (fun u => G3Za.palmH γ x (u + x)) =ᶠ[𝓝 z] fun u => c • Real.log ‖u + x‖ := by
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    rw [hc u hu, smul_eq_mul]
  have hne : z + x ≠ 0 := by
    intro h0
    have hz' : ‖z‖ < rhoX x := by simpa using hz
    have : z = -(x : ℂ) := eq_neg_of_add_eq_zero_left h0
    rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hz'
    have := abs_pos.2 hx
    linarith [rhoX_le_left x]
  have hA : AnalyticAt ℂ (fun u : ℂ => u + x) z := analyticAt_id.add analyticAt_const
  have hH := (hA.harmonicAt_log_norm hne).const_smul (c := c)
  refine (harmonicAt_congr_nhds hev).2 ?_
  convert hH using 1
  ext v
  simp

/-- The translated normalizing circle stays at distance `> ρₓ` from `0`. -/
theorem fc_neg_far_X {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) :
    ∀ᵐ y ∂foldedCircle (-(x : ℂ)) 1, rhoX x < ‖y‖ := by
  rw [foldedCircle, ae_map_iff measurable_foldH.aemeasurable
    (measurableSet_lt measurable_const measurable_norm)]
  filter_upwards [K3.ae_mem_sphere_circleUnif_k3 (-(x : ℂ)) one_pos] with v hv
  have h1 : ‖v - (-(x : ℂ))‖ = 1 := by simpa using mem_sphere_iff_norm.1 hv
  have h2 : ‖foldH v - ((-x : ℝ) : ℂ)‖ = ‖v - ((-x : ℝ) : ℂ)‖ :=
    K3.norm_foldH_sub_ofReal (-x) v
  push_cast at h2
  rw [h1] at h2
  have h3 := abs_norm_sub_norm_le (foldH v - -(x : ℂ)) (x : ℂ)
  rw [show foldH v - -(x : ℂ) - x = foldH v by ring, h2, Complex.norm_real,
    Real.norm_eq_abs] at h3
  have hpos := rhoX_pos hx hx1
  have h4 : rhoX x ≤ (abs (1 - |x|)) / 2 := min_le_right _ _
  linarith

/-- **The local certificate of the pulled-back Palm field of `V + logSing` at a fixed point**
(any free field `V` on any probability space; `x` on the side half-line, `|x| ≠ 1`). -/
theorem ae_locCertC_palmField {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (ha : G3Zq.G3ZqGoodPath γ a) {side : Bool} {x : ℝ} (hxs : x ∈ g1SideHalf side)
    (hx1 : |x| ≠ 1) {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''}
    [IsProbabilityMeasure P''] {V : Ω'' → FieldSample} (hV : IsFreeGFFModConstH V P'') :
    ∀ᵐ ω ∂P'', LocCertC γ (G3Z2b2.g3coordsM γ 0 Ψ side
      (PalmNorm.normAt R18.g3zS (ofFun (G3Za.palmProf γ x) + V ω), a, 1, x)) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hxs
    cases side <;> simp [g1SideHalf] at hxs
  have hγ0 : γ ≠ 0 := hγ.ne'
  -- the local map and its G0 extension
  set y₀ : FieldSample := fun _ => 0 with hy₀
  obtain ⟨r₀, hr₀, Φ, hΦ, heqΦ⟩ := G3ZqF.g3mapP_g0Ext hsel ha hxs y₀
  obtain ⟨rA, hrA, hAg⟩ := G3Za.ae_agreeNear_zoom_palmField hV hr₀ hΦ γ hx0
  -- the profile
  set ρf : ℝ := rhoX x with hρf
  have hρf0 : 0 < ρf := rhoX_pos hx0 hx1
  have hρfx : ρf ≤ |x| / 2 := min_le_left _ _
  set f : ℂ → ℝ := fun u => G3Za.palmProf γ x (u + x) with hfdef
  set h : ℂ → ℝ := fun u => G3Za.palmH γ x (u + x) with hhdef
  have hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = γ * -Real.log ‖u‖ + h u :=
    fun u hu => G3Za.palmProf_shift_eq γ (closedBall_subset_closedBall hρfx hu.1)
  have hh : Continuous h :=
    (G3Za.continuous_palmH γ hx0).comp (continuous_id.add continuous_const)
  have hfm : Measurable f :=
    (G3Za.measurable_palmProf γ x).comp (measurable_id.add measurable_const)
  set S : Measure ℂ := foldedCircle (-(x : ℂ)) 1 with hSdef
  have hSa : IsAdmissibleH S := isAdmissibleH_foldedCircle_g3cv2 _ one_pos
  have hS1 : S Set.univ = 1 := measure_univ
  -- the coupling with a D3⁺ model
  obtain ⟨r, s, hr, -, E', _, U, X', Ξ, g, hU, hSet, hag⟩ :=
    G3Za.exists_g0Setup_palm hr₀ hΦ hγ hγ2 hρf0 hf hh hfm
      (harmonicOnNhd_palmH_shift_X γ hx0 hx1) (fun u _ => G3Za.palmH_shift_conj γ x u) hSa hS1
      (fc_neg_far_X hx0 hx1)
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
  set K : ℝ := ∫ u, G3Za.palmProf γ x u ∂R18.g3zS with hK
  set L' : ℝ := 0 - γ * K with hL'
  set Zf : FieldSample → FieldSample := fun y => zoomS γ L' (Qc γ) f Φ S y with hZf
  set Vx : Ω'' → FieldSample := fun ω => rawTranslate (V ω) x with hVdef
  have hVx : IsFreeGFFModConstH Vx P'' := isFree_rawTranslate hV x
  obtain ⟨hmU, hmV, hlaw⟩ := dyadLaw_eq_free hDs hΨ0 heq hf hh hfm hMρ γ L' (Qc γ) hSa hS1
    hr''ρ hU hVx
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
      ZqR.agreeNear_trans (ZqR.agreeNear_reconstruct_coords _ r'')
        (ZqR.agreeNear_trans (agreeNear_dyadField r'' (Zf (U ω))).symm'
          (AgreeNear.mono_radius (hω L') hr''r))
    exact ZqR.locCertC_of_agree_model hγ.ne' hr''0 hgood.1 hvag hpos hg hch
  have h0 : P'' ((fun ω => dyadData r'' (Zf (Vx ω))) ⁻¹' Tᶜ) = 0 := by
    rw [← Measure.map_apply₀ hmV hTm.compl.nullMeasurableSet, ← hlaw,
      Measure.map_apply₀ hmU hTm.compl.nullMeasurableSet]
    exact ae_iff.1 hcS
  filter_upwards [hAg, measure_eq_zero_iff_ae_notMem.1 h0] with ω hA hω
  have hωT : dyadData r'' (Zf (Vx ω)) ∈ T := by
    by_contra hc
    exact hω hc
  set y : FieldSample := PalmNorm.normAt R18.g3zS (ofFun (G3Za.palmProf γ x) + V ω) with hy
  have hmap : G3Z2b2.g3mapP Ψ side (y, a, 1, x) = G3Z2b2.g3mapP Ψ side (y₀, a, 1, x) := rfl
  have hco : G3Z2b2.g3coordsM γ 0 Ψ side (y, a, 1, x) =
      coords (zoomFieldVia γ 0 y x (G3Z2b2.g3mapP Ψ side (y₀, a, 1, x))) := by
    rw [G3Z2b2.g3coordsM_eq (p := (y, a, 1, x)) hsel 0 side ha.1 ha.2 one_pos, hmap]
  rw [hco]
  have e : Zf (Vx ω) = addConst (coordChange (ofFun f + Vx ω) Φ (Qc γ))
      (0 / γ - (K + Vx ω S)) := by
    simp only [hZf, zoomS]
    congr 1
    rw [hL', sub_div, mul_div_cancel_left₀ _ hγ0]
    ring
  have hZ : AgreeNear (zoomFieldVia γ 0 y x (G3Z2b2.g3mapP Ψ side (y₀, a, 1, x))) (Zf (Vx ω))
      r'' := by
    rw [e]
    exact ZqR.agreeNear_trans
      (AgreeNear.mono_radius (G3ZqF.agreeNear_zoomFieldVia_of_eqOn heqΦ γ 0 y x) hr''0')
      (AgreeNear.mono_radius (hA 0) hr''A)
  refine ZqR.locCertC_congr hr''0 hωT ?_
  exact ZqR.agreeNear_trans (ZqR.agreeNear_reconstruct_coords _ r'')
    (ZqR.agreeNear_trans (agreeNear_dyadField r'' (Zf (Vx ω))).symm'
      (ZqR.agreeNear_trans hZ.symm' (ZqR.agreeNear_reconstruct_coords _ r'').symm'))

/-- **`G3ZqTVPalmStmt` holds** (every point of the side half-line with `|x| ≠ 1`, hence
Lebesgue-a.e.; the good path is only used through `G3ZqGoodPath`). -/
theorem g3ZqTVPalmStmt_holds : G3ZqTVPalmStmt := by
  intro γ hγ hγ2 Ψ hsel Ω _ P _ B hB
  refine Eventually.of_forall fun a hg side Ω'' _ P'' _ V hV _ => ?_
  have hnull : ∀ᵐ x ∂(volume.restrict (g1SideHalf side)), x ∉ ({1, -1} : Set ℝ) := by
    refine ae_restrict_of_ae ?_
    have hc : volume ({1, -1} : Set ℝ) = 0 := (Set.toFinite _).measure_zero _
    exact measure_eq_zero_iff_ae_notMem.1 hc
  filter_upwards [ae_restrict_mem (msSide side), hnull] with x hxs hx
  have hx1 : |x| ≠ 1 := by
    intro h
    rcases abs_eq (zero_le_one' ℝ) |>.1 h with h' | h'
    · exact hx (by simp [h'])
    · exact hx (by simp [h'])
  exact ae_locCertC_palmField hγ hγ2 hsel hg.good hxs hx1 hV

end ZqTB
end ZqT
end Thm18Asm
end QuantumZipper
