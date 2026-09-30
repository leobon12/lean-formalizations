import QuantumZipper.Proofs.Thm18.ZqTA6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (A7): the fixed Palm points of `V + logSing`, and the scheme clause

* `ae_locCertC_of_profile`: the proof of `ZqR.ae_locCertC_palm` (D3⁺ model near `0` via ZOOM-A's
  coupling and dyadic law transfer), with the profile properties and the zoom agreement as inputs.
* `ae_locCertC_logC`: hence the certificate for the Palm field with profile `c log|·| + ψ_x` at
  every fixed `x ≠ 0` with `|x| ≠ 1` (`tf_props_near` / `tf_props_far`, `ae_agreeNear_zoom_logC`).
* `ae_VPalm_normX`: with `c = 2/γ − γ` this is the Palm field of `normX X + logSing`, i.e. the
  fixed-Palm-point statement `G3ZqTVPalmStmt` for the free field `normX X₀` of the base space
  (the only instance the scheme clause uses).
* `g3ZqTSchemeSideStmt_holds`: **`G3ZqTSchemeSideStmt` is proved.**

Sheffield, arXiv:1012.4797, pp. 70–71 and proof of Prop. 5.5, p. 65 ("once we condition on `x`");
Duplantier–Sheffield, arXiv:0808.1560, §3.3 (rooted measure). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT
namespace LogC

open Factorization G3ZqL D3Plus LQGMeas G3Cv S5.FieldLaw.Raw K3 GFFExist LQGDimension.ExistAsm ZqR
open R18 (g3zS)

/-- **The local certificate of a pulled-back Palm field at a fixed Palm point, from its profile**
(the proof of `ZqR.ae_locCertC_palm` with the profile and the ZOOM-A agreement as inputs). -/
theorem ae_locCertC_of_profile {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a) {side : Bool} {x : ℝ}
    (hxs : x ∈ g1SideHalf side) {Y : gffBase.Ω → FieldSample} {f h : ℂ → ℝ} {K ρf : ℝ}
    (hρf0 : 0 < ρf)
    (hprops : (∀ u ∈ Metric.closedBall (0 : ℂ) ρf ∩ Hbar, f u = γ * -Real.log ‖u‖ + h u) ∧
      Continuous h ∧ Measurable f ∧
      InnerProductSpace.HarmonicOnNhd h (Metric.ball (0 : ℂ) ρf) ∧
      (∀ u ∈ Metric.ball (0 : ℂ) ρf, h ((starRingEnd ℂ) u) = h u) ∧
      IsAdmissibleH (palmCRho refS x) ∧ palmCRho refS x Set.univ = 1 ∧
      (∀ᵐ y ∂palmCRho refS x, ρf < ‖y‖) ∧
      IsAdmissibleH ((palmCRho refS x).map (· + (x : ℂ))))
    (hAgr : ∀ (r₀ : ℝ) (ψ : ℂ → ℂ), 0 < r₀ → IsG0Map r₀ ψ → ∃ r : ℝ, 0 < r ∧
      ∀ᵐ ω ∂gffBase.P, ∀ L : ℝ, AgreeNear (zoomFieldVia γ L (Y ω) x ψ)
        (zoomS γ (L - γ * K) (Qc γ) f ψ (palmCRho refS x) (rawTranslate (gffBase.X ω) x)) r) :
    ∀ᵐ ω ∂gffBase.P, LocCertC γ (G3Z2b2.g3coordsM γ 0 Ψ side (Y ω, a, 1, x)) := by
  -- the local map and its G0 extension
  set y₀ : FieldSample := fun _ => 0 with hy₀
  obtain ⟨r₀, hr₀, Φ, hΦ, heqΦ⟩ := G3ZqF.g3mapP_g0Ext hsel ha hxs y₀
  obtain ⟨rA, hrA, hAg⟩ := hAgr r₀ Φ hr₀ hΦ
  -- the profile
  obtain ⟨hf, hh, hfm, hhh, hhc, hSa, hS1, hSf, -⟩ := hprops
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
  set L' : ℝ := 0 - γ * K with hL'
  set Zf : FieldSample → FieldSample := fun y =>
    zoomS γ L' (Qc γ) f Φ (palmCRho refS x) y with hZf
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
  set y : FieldSample := Y ω with hy
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

/-- **The certificate for the Palm field with profile `c log|·| + ψ_x`** at every fixed side
point `x` with `|x| ≠ 1`. -/
theorem ae_locCertC_logC {γ c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a) {side : Bool} {x : ℝ}
    (hxs : x ∈ g1SideHalf side) (hx1 : |x| ≠ 1) :
    ∀ᵐ ω ∂gffBase.P, LocCertC γ (G3Z2b2.g3coordsM γ 0 Ψ side
      (PalmNorm.normAt refS (ofFun (lf c γ x) + gffBase.X ω), a, 1, x)) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hxs
    cases side <;> simp [g1SideHalf] at hxs
  have hax : 0 < |x| := abs_pos.2 hx0
  have hAgr : ∀ (r₀ : ℝ) (ψ : ℂ → ℂ), 0 < r₀ → IsG0Map r₀ ψ → ∃ r : ℝ, 0 < r ∧
      ∀ᵐ ω ∂gffBase.P, ∀ L : ℝ, AgreeNear
        (zoomFieldVia γ L (PalmNorm.normAt refS (ofFun (lf c γ x) + gffBase.X ω)) x ψ)
        (zoomS γ (L - γ * tK c γ x) (Qc γ) (tf c γ x) ψ (palmCRho refS x)
          (rawTranslate (gffBase.X ω) x)) r :=
    fun r₀ ψ hr₀ hψ => ae_agreeNear_zoom_logC hγ hx0 hr₀ hψ
  rcases lt_or_gt_of_ne hx1 with h1 | h1
  · set ρf : ℝ := min (|x| / 2) ((1 - |x|) / 2) with hρf
    have hρf0 : 0 < ρf := lt_min (by positivity) (by linarith)
    have hρf1 : ρf < 1 - |x| := by
      have := min_le_right (|x| / 2) ((1 - |x|) / 2); linarith
    exact ae_locCertC_of_profile hγ hγ2 hsel ha hxs hρf0
      (tf_props_near hγ hx0 h1 hρf0 (min_le_left _ _) hρf1) hAgr
  · set ρf : ℝ := min (|x| / 2) ((|x| - 1) / 2) with hρf
    have hρf0 : 0 < ρf := lt_min (by positivity) (by linarith)
    have hρf1 : ρf < |x| - 1 := by
      have := min_le_right (|x| / 2) ((|x| - 1) / 2); linarith
    exact ae_locCertC_of_profile hγ hγ2 hsel ha hxs hρf0
      (tf_props_far hγ hx0 h1 hρf0 (min_le_left _ _) hρf1) hAgr

/-- The `V + logSing` Palm field of `V = normX X₀` in profile form. -/
theorem coords_VPalm_eq {γ : ℝ} (x : ℝ) (ω : gffBase.Ω) :
    coords (PalmNorm.normAt g3zS (ofFun (PalmNorm.shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) g3zS x) +
      normX gffBase.X ω)) =
      coords (PalmNorm.normAt refS (ofFun (lf (2 / γ - γ) γ x) + gffBase.X ω)) := by
  have hfun : PalmNorm.shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) g3zS x = lf (2 / γ - γ) γ x :=
    funext fun u => by
      simp only [PalmNorm.shiftFun, LogSingGood.Lf, lf, g2PalmPsi]
      ring
  funext j
  simp only [coords, PalmNorm.normAt, addConst, Pi.add_apply, hfun, normX_apply, measure_univ,
    ENNReal.toReal_one, one_mul, mul_one]
  ring

/-- **`G3ZqTVPalmStmt` for the free field `normX X₀` of the base space.** -/
theorem ae_VPalm_normX {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a) (side : Bool) :
    ∀ᵐ x ∂(volume.restrict (g1SideHalf side)), ∀ᵐ ω ∂gffBase.P,
      LocCertC γ (G3Z2b2.g3coordsM γ 0 Ψ side (PalmNorm.normAt g3zS (ofFun (PalmNorm.shiftFun γ
        (LogSingGood.Lf (γ - 2 / γ)) g3zS x) + normX gffBase.X ω), a, 1, x)) := by
  have hfin : volume ({1, -1} : Set ℝ) = 0 := (Set.toFinite _).measure_zero _
  filter_upwards [ae_restrict_mem (msSide side),
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hfin)] with x hxs hx1
  have hx1' : |x| ≠ 1 := fun h => hx1 (by
    rcases (abs_eq zero_le_one).1 h with h' | h' <;> simp [h'])
  filter_upwards [ae_locCertC_logC (c := 2 / γ - γ) hγ hγ2 hsel ha hxs hx1'] with ω hω
  rw [← g3coordsM_reconstruct_coords, coords_VPalm_eq, g3coordsM_reconstruct_coords]
  exact hω

end LogC

open LogC R18 G3Zq G3Z2b2 G3ZqL

/-- **`G3ZqTSchemeSideStmt` holds.** -/
theorem g3ZqTSchemeSideStmt_holds : G3ZqTSchemeSideStmt := by
  intro γ hγ hγ2 Ψ hsel Ω _ P _ B hB
  refine Eventually.of_forall fun a hg => ?_
  have hga := hg.good
  have hCT := ae_prof_null hγ hγ2 hsel true (ae_VPalm_normX hγ hγ2 hsel hga true)
  have hCF := ae_prof_null hγ hγ2 hsel false (ae_VPalm_normX hγ hγ2 hsel hga false)
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · refine ae_palm_side_of_null (F := g3pX γ (g3wCut γ i.η) i)
      (palmB_null hγ hγ2 i (measurableSet_badSet hsel true a) ?_)
    filter_upwards [ae_free_null hγ hγ2 hsel hga true] with ω hω
    exact hω i
  · refine ae_palm_side_of_null (F := g3pX γ (g3wProf γ) i)
      (palm_null_of_ae (g3pZ_pos_lt_top hγ hγ2 i) (measurableSet_badSet hsel true a) ?_)
    filter_upwards [hCT, ae_g3pFid_sets hγ hγ2] with ω hω hFid
    exact left_restrict_null (hFid i).1 hω
  · refine ae_palm_side_of_null (F := g3pR γ (g3wCut γ i.η) i)
      (palmB_nullR hγ hγ2 i (measurableSet_badSet hsel false a) badSet_pos ?_)
    filter_upwards [ae_free_nullR g3ZqTFreeFarStmt_holds hγ hγ2 hsel hga] with ω hω
    exact hω i
  · refine ae_palm_side_of_null (F := g3pR γ (g3wProf γ) i)
      (palm_nullR_of_ae (g3pZ_pos_lt_top hγ hγ2 i) (measurableSet_badSet hsel false a)
        badSet_pos ?_)
    filter_upwards [hCF, ae_g3pField_good hγ hγ2] with ω hω hgd
    exact partner_meas_null hγ hgd.1 hgd.2.1 hgd.2.2.1 i hω

end ZqT
end Thm18Asm
end QuantumZipper
