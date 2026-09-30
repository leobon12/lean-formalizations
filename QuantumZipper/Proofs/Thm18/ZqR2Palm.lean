import QuantumZipper.Proofs.Thm18.ZqR1Model
import QuantumZipper.Proofs.Thm18.G3ZqFFix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-REG (2): the local certificate at fixed Palm points (`G3ZqLPalmCertStmt`)

`g3ZqLPalmCertStmt_holds`: for a good path `a` and every point `x` of the side half-line with
`|x| < 1`, almost surely the pulled-back zoomed Palm field
`g3coordsM γ 0 Ψ side (normField γ (xPalm γ x) ω, a, 1, x)` carries the measurable local
certificate `LocCertC` (uniform dyadic Cauchy bounds and positive local area near `0`).

Route (Sheffield, arXiv:1012.4797, pp. 70–71: near a quantum-typical boundary point the field is
a free boundary GFF plus `γ(−log|·|)` plus a smooth function; proof of Prop. 1.6, p. 25):

* the local map agrees near `0` on `ℍ` with an admissible G0 map `Φ` (`G3ZqF.g3mapP_g0Ext`), and the
  zoom of the Palm field through `Φ` agrees near `0` with the ZOOM-A form `zoomS` of the
  translated free field at a shifted level (`G3ZqF.ae_agreeNear_zoom_g2Palm`);
* on the coupling space of ZOOM-A's Palm core (`G3Za.G3ZqF.exists_g0Setup_palm_far_le`) the same
  `zoomS` agrees near `0` with a D3⁺ model with `α = γ`, whose dyadic data carry `LocCertC`
  (`ZqR.locCertC_of_agree_model`);
* `LocCertC` of the reconstructed dyadic data is a measurable event of the dyadic data near `0`,
  whose law is universal (`G3Cv.dyadLaw_eq_free`), so it transfers to the free field `gffBase`.

Own bookkeeping (AGENT_GUIDE cost rule), following `G3Cv.G3ZqF.cond_zoom_palm_free_full`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace ZqR

open Factorization G3ZqL D3Plus LQGMeas G3Cv S5.FieldLaw.Raw K3 GFFExist LQGDimension.ExistAsm

/-- The reconstruction of the coordinates agrees with the field at every dyadic folded circle. -/
theorem agreeNear_reconstruct_coords (v : FieldSample) (r : ℝ) :
    AgreeNear (reconstruct (coords v)) v r := by
  intro n k z _
  obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
  have := reconstruct_coords_apply v i
  rw [hi] at this
  exact this

theorem agreeNear_trans {y y' y'' : FieldSample} {r : ℝ} (h : AgreeNear y y' r)
    (h' : AgreeNear y' y'' r) : AgreeNear y y'' r :=
  fun n k z hz => (h n k z hz).trans (h' n k z hz)

/-- **The local certificate of the pulled-back Palm field at a fixed Palm point.** -/
theorem ae_locCertC_palm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a) {side : Bool} {x : ℝ}
    (hxs : x ∈ g1SideHalf side) (hx1 : |x| < 1) :
    ∀ᵐ ω ∂gffBase.P, LocCertC γ (G3Z2b2.g3coordsM γ 0 Ψ side (normField γ (xPalm γ x) ω, a, 1, x)) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hxs
    cases side <;> simp [g1SideHalf] at hxs
  -- the local map and its G0 extension
  set y₀ : FieldSample := fun _ => 0 with hy₀
  obtain ⟨r₀, hr₀, Φ, hΦ, heqΦ⟩ := G3ZqF.g3mapP_g0Ext hsel ha hxs y₀
  obtain ⟨rA, hrA, hAg⟩ := G3ZqF.ae_agreeNear_zoom_g2Palm hγ hx0 hx1 hr₀ hΦ
  -- the profile
  set ρf : ℝ := min (|x| / 2) ((1 - |x|) / 2) with hρf
  have hax : 0 < |x| := abs_pos.2 hx0
  have hρf0 : 0 < ρf := lt_min (by positivity) (by linarith)
  have hρfx : ρf ≤ |x| / 2 := min_le_left _ _
  have hρf1 : ρf < 1 - |x| := by
    have := min_le_right (|x| / 2) ((1 - |x|) / 2); linarith
  obtain ⟨hf, hh, hfm, hhh, hhc, hSa, hS1, hSf, -⟩ :=
    G3ZqF.g2f_props hγ hx0 hx1 hρf0 hρfx hρf1
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

/-- **`G3ZqLPalmCertStmt` holds.** -/
theorem g3ZqLPalmCertStmt_holds : G3ZqLPalmCertStmt := by
  intro γ hγ hγ2 Ψ hsel a ha side
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx hxs
  have hx1 : |x| < 1 := abs_lt.2 ⟨hx.1, hx.2⟩
  exact ae_locCertC_palm hγ hγ2 hsel ha hxs hx1

/-- **Zoom locality at quantum-typical points through the local maps** (proved). -/
theorem g3ZqLZoomLocAEMapStmt_holds : G3ZqLZoomLocAEMapStmt :=
  g3ZqLZoomLocAEMapStmt_of_palm g3ZqLPalmCertStmt_holds

end ZqR
end Thm18Asm
end QuantumZipper
