import QuantumZipper.Proofs.Thm18.G3ZqFCond
import QuantumZipper.Proofs.Thm18.G3ZqFLoc
import QuantumZipper.Proofs.Thm18.G3ZqFMap
import QuantumZipper.Proofs.Thm18.G3ZqFCore
import QuantumZipper.Proofs.Thm18.G3ZqFPalm
import QuantumZipper.Proofs.Thm18.G1ZmPt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-FIX (core): the conditional zoom through the local map at a fixed Palm point

`fixCore`: let `a` be a good path, `x` a point of the side half-line with `κ/2 < |x|`,
`|x| + κ/2 < 1`, `s` a law cylinder. Eventually in the level `C`, uniformly over every conditioning
variable `W` that is a.s. equal to a map measurable for the D3⁺ conditioning σ-algebra of the free
field outside `B(x, κ/2)` (`condSigma () (palmCField X x) (κ/2)`), and over every measurable event
`G'`,

  `|P(zoom_C through the local map ∈ s, W ∈ G') − μ(s) P(W ∈ G')| ≤ ε`,

`μ = g2WedgeLaw P' Y'` the `γ`-wedge law. This is Sheffield, arXiv:1012.4797, proof of Prop. 5.5
(p. 65) and of Thm. 1.8 (p. 71: "even with this conditioning ... one still obtains the laws of
quantum wedges"), through the local map (Prop. 1.6, pp. 24–25). Steps:

* the local map has an admissible G0 extension `Φ` (`g3mapP_g0Ext`), and the zoom of the Palm field
  through it agrees near `0` with `zoomS` of the translated free field (`ae_agreeNear_zoom_g2Palm`,
  ZOOM-A form);
* ZOOM-C's conditional decorrelation (`cond_zoom_palm_free_full`, from `G3Cv.cond_zoom_palm_free'`)
  for the far Gaussian pairs `g3fPairs x (κ/2)`, which generate the conditioning σ-algebra
  (`exists_gauss_preimage`);
* off the bad dyadic event (vanishing mass) the zoom event equals the local canonical event
  (`locFieldFull_canonProxy_eq`).

Own assembly (AGENT_GUIDE cost rule), following `g2RootXFixStmt_of_model` and
`G1Zm.tendsto_palmZoom_canonical`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqF

open D3Plus G3Cv S5.FieldLaw.Raw

local notation "Ω₀" => gffBase.Ω

/-- Off the bad dyadic set the zoom event is the local canonical event. -/
theorem mem_iff_of_not_bad {γ r : ℝ} {R : ℕ} {s : Set LawD}
    (hR : ∀ Z : FieldSample, locFieldFull R Z ∈ s ↔ lawOf Z ∈ s) {y y' : FieldSample}
    (hag : AgreeNear y y' r) (hg' : ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y') m)
    (hb : dyadData r y' ∉ dyadBad γ r (R + 1)) :
    lawOf (canonProxy γ y) ∈ s ↔ locFieldFull R (canonicalOn γ y' (halfDisc r)) ∈ s := by
  obtain ⟨m, hm⟩ := hg'
  have hag' := agreeNear_dyadField r y'
  have hgood : dyadData r y' ∈
      Prop16Area.Meas.goodSet γ (dyadField r) (fun _ => halfDisc r) :=
    (exists_isVagueLimitOn_halfDisc_iff hag').1 ⟨m, hm⟩
  have hs' := scaleParamOn_halfDisc_congr (γ := γ) hag'
  have hc : 0 < scaleParamOn γ y' (halfDisc r) ∧
      scaleParamOn γ y' (halfDisc r) * ((R : ℝ) + 1) < r := by
    simp only [dyadBad, mem_ofPred_eq, not_not] at hb
    rw [dyadScale_eq hgood, ← hs'] at hb
    push_cast at hb
    exact hb
  rw [← hR, (locFieldFull_canonProxy_eq hag hm hc.1 hc.2).2]

theorem measurable_normField_xPalm (γ x : ℝ) : Measurable (normField γ (xPalm γ x)) :=
  D3Plus.measurable_fieldSample_of fun μ => by
    simp only [normField, xPalm, Pi.add_apply]
    exact measurable_const.add (((gffBase.gff.measurable_coord μ).add measurable_const).sub
      ((gffBase.gff.measurable_coord _).add measurable_const))

/-- The zoom datum through the local map is the canonical proxy of the zoom (good path). -/
theorem g1zM_eq_canonProxy {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a) (C : ℝ) (left : Bool) (y y₀ : FieldSample)
    (x : ℝ) :
    G3Z2b2.g1zM γ C Ψ left ((y, a), x) =
      lawOf (canonProxy γ (zoomFieldVia γ C y x (G3Z2b2.g3mapP Ψ left (y₀, a, 1, x)))) := by
  show G3Z2b2.g3zoomLawM γ C Ψ left (y, a, 1, x) = _
  have e : G3Z2b2.g3mapP Ψ left (y, a, 1, x) = G3Z2b2.g3mapP Ψ left (y₀, a, 1, x) := rfl
  rw [G3Z2b2.g3zoomLawM, G3Z2b2.g3coordsM_eq (p := (y, a, 1, x)) hsel C left ha.1 ha.2 (zero_lt_one : (0 : ℝ) < 1), e,
    canonProxy_recon]
  rfl

/-- **The conditional zoom through the local map at a fixed Palm point.** -/
theorem fixCore {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y' : Ω' → FieldSample) (hW : IsQuantumWedge γ γ Y' P') {s : Set LawD} (hs : s ∈ lawCyl)
    {left : Bool} {x κ : ℝ} (hκ : 0 < κ) (hxs : x ∈ g1SideHalf left) (hxr : κ / 2 < |x|)
    (hx1 : |x| + κ / 2 < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ C in atTop, ∀ {E'' : Type} [MeasurableSpace E''] (Wc : Ω₀ → E''),
      (∃ V : Ω₀ → E'', Measurable[D3Plus.condSigma (fun _ : Ω₀ => ())
        (palmCField gffBase.X x) (κ / 2)] V ∧ ∀ᵐ ω ∂gffBase.P, V ω = Wc ω) →
      ∀ G' : Set E'', MeasurableSet G' →
        |(gffBase.P ({ω | G3Z2b2.g1zM γ C Ψ left ((normField γ (xPalm γ x) ω, a), x) ∈ s} ∩
            Wc ⁻¹' G')).toReal -
          (g2WedgeLaw P' Y').real s * (gffBase.P (Wc ⁻¹' G')).toReal| ≤ ε := by
  classical
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hxr; linarith
  have hxl : |x| < 1 := by linarith
  obtain ⟨R, hR⟩ := exists_nat_locFieldFull_lawCyl hs
  have hsm := measurableSet_lawCyl hs
  set c : ℝ := (g2WedgeLaw P' Y').real s with hc
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hmass := g2Agree_wedge_mass hγ hγ2 hW hsm hR
  -- the local map and its G0 extension
  set y₀ : FieldSample := fun _ => 0 with hy₀
  set ψ₀ := G3Z2b2.g3mapP Ψ left (y₀, a, 1, x) with hψ₀
  obtain ⟨r₀, hr₀, Φ, hΦ, heqΦ⟩ := g3mapP_g0Ext hsel ha hxs y₀
  obtain ⟨rA, hrA, hAg⟩ := ae_agreeNear_zoom_g2Palm hγ hx0 hxl hr₀ hΦ
  -- the profile
  set ρf : ℝ := min (κ / 4) (|x| / 2) with hρf
  have hρf0 : 0 < ρf := lt_min (by positivity) (by positivity)
  have hρfx : ρf ≤ |x| / 2 := min_le_right _ _
  have hρfκ : ρf ≤ κ / 4 := min_le_left _ _
  have hρf1 : ρf < 1 - |x| := by linarith
  obtain ⟨hf, hh, hfm, hhh, hhc, hSa, hS1, hSf, hSx⟩ :=
    g2f_props hγ hx0 hxl hρf0 hρfx hρf1
  obtain ⟨r'', R₀, hr'', hr''le, hR₀, hR₀le, hmain⟩ :=
    G3Cv.G3ZqF.cond_zoom_palm_free_full hr₀ hΦ hγ hγ2 hρf0 hf hh hfm hhh hhc hSa hS1 hSf
      (lt_min hrA hr₀ : 0 < min rA r₀)
  have hR₀κ : R₀ < κ / 2 := by linarith
  obtain ⟨hZm, hgood, hbad, hcond⟩ := hmain x hSx (g3fPairs x (κ / 2))
    (fun k => g3fPairs_far x hR₀κ k) gffBase.P gffBase.X gffBase.gff
  set K : ℝ := g2K γ x with hK
  set Z' : ℝ → Ω₀ → FieldSample := fun L ω => zoomS γ L (Qc γ) (g2f γ x) Φ (palmCRho refS x)
    (rawTranslate (gffBase.X ω) x) with hZ'
  set Bad : ℝ → Set Ω₀ := fun L =>
    (fun ω => dyadData r'' (Z' L ω)) ⁻¹' dyadBad γ r'' (R + 1) with hBad
  set Zev : ℝ → Set Ω₀ := fun C =>
    {ω | G3Z2b2.g1zM γ C Ψ left ((normField γ (xPalm γ x) ω, a), x) ∈ s} with hZev
  have hZevm : ∀ C, MeasurableSet (Zev C) := fun C =>
    ((G3Z2b2.measurable_g1zM hsel C left).comp
      (((measurable_normField_xPalm γ x).prodMk measurable_const).prodMk measurable_const)) hsm
  set Γ : LawD → ℝ≥0∞ := s.indicator 1 with hΓ
  set Loc : ℝ → Ω₀ → ℝ≥0∞ := fun L ω =>
    Γ (locFieldFull R (canonicalOn γ (Z' L ω) (halfDisc r''))) with hLoc
  -- pointwise comparison off the bad event
  have hpt : ∀ C : ℝ, ∀ᵐ ω ∂gffBase.P, ω ∉ Bad (C - γ * K) →
      (ω ∈ Zev C ↔ locFieldFull R (canonicalOn γ (Z' (C - γ * K) ω) (halfDisc r'')) ∈ s) := by
    intro C
    filter_upwards [hAg, hgood (C - γ * K)] with ω hA hg hnb
    have hag : AgreeNear (zoomFieldVia γ C (normField γ (xPalm γ x) ω) x ψ₀)
        (Z' (C - γ * K) ω) r'' := by
      have e1 := agreeNear_zoomFieldVia_of_eqOn heqΦ γ C (normField γ (xPalm γ x) ω) x
      have e2 := hA C
      intro n k z hz
      have hz1 : ‖dyadicRoundC n z‖ + radius k < r₀ :=
        hz.trans_le (hr''le.trans (min_le_right _ _))
      have hz2 : ‖dyadicRoundC n z‖ + radius k < rA :=
        hz.trans_le (hr''le.trans (min_le_left _ _))
      exact (e1 n k z hz1).trans (e2 n k z hz2)
    show G3Z2b2.g1zM γ C Ψ left ((normField γ (xPalm γ x) ω, a), x) ∈ s ↔ _
    rw [g1zM_eq_canonProxy hsel ha C left _ y₀ x]
    exact mem_iff_of_not_bad hR hag hg hnb
  -- the pointwise two-sided bounds
  have hind : ∀ C : ℝ, ∀ (T : Set Ω₀), ∀ᵐ ω ∂gffBase.P,
      (T ∩ Zev C).indicator 1 ω ≤ T.indicator 1 ω * Loc (C - γ * K) ω +
          (Bad (C - γ * K)).indicator 1 ω ∧
        T.indicator 1 ω * Loc (C - γ * K) ω ≤ (T ∩ Zev C).indicator (1 : Ω₀ → ℝ≥0∞) ω +
          (Bad (C - γ * K)).indicator 1 ω := by
    intro C T
    filter_upwards [hpt C] with ω hω
    have hL1 : Loc (C - γ * K) ω ≤ 1 := indicator_le (fun _ _ => le_rfl) _
    have hT1 : T.indicator (1 : Ω₀ → ℝ≥0∞) ω ≤ 1 := indicator_le (fun _ _ => le_rfl) _
    by_cases hb : ω ∈ Bad (C - γ * K)
    · rw [indicator_of_mem hb]
      refine ⟨(indicator_le (fun _ _ => le_rfl) _).trans (le_add_left le_rfl), ?_⟩
      exact (mul_le_one' hT1 hL1).trans (le_add_left le_rfl)
    · rw [indicator_of_notMem hb, add_zero]
      have e := hω hb
      by_cases hT : ω ∈ T
      · by_cases hz : ω ∈ Zev C
        · have hl : Loc (C - γ * K) ω = 1 := by
            simp only [hLoc, hΓ]; exact indicator_of_mem (e.1 hz) _
          rw [indicator_of_mem (show ω ∈ T ∩ Zev C from ⟨hT, hz⟩), indicator_of_mem hT, hl]; simp
        · have hl : Loc (C - γ * K) ω = 0 := by
            simp only [hLoc, hΓ]; exact indicator_of_notMem (fun h => hz (e.2 h)) _
          rw [indicator_of_notMem (fun h => hz h.2), hl]; simp
      · rw [indicator_of_notMem (fun h => hT h.1), indicator_of_notMem hT]; simp
  -- the main estimate
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by positivity)
  have hcondY := hcond P' Y' hW R Γ (measurable_one.indicator hsm)
    (fun _ => indicator_le (fun _ _ => le_rfl) _) _ hη
  have hshift : Tendsto (fun C : ℝ => C - γ * K) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  filter_upwards [hshift.eventually hcondY,
    hshift.eventually ((hbad (R + 1)).eventually (gt_mem_nhds hη))] with C hC hCb E'' _ Wc hWc
    G' hG'
  obtain ⟨V, hVm, hVae⟩ := hWc
  obtain ⟨B, hB, hVB⟩ := exists_gauss_preimage hVm hG'
  set GB : Set Ω₀ := (fun ω k => WedgeTK.gaussFam gffBase.X (g3fPairs x (κ / 2)) k ω) ⁻¹' B
    with hGB
  have hGBm : MeasurableSet GB := (WedgeTK.measurable_gaussFam_pi gffBase.gff _) hB
  have hWGB : (Wc ⁻¹' G' : Set Ω₀) =ᵐ[gffBase.P] GB := by
    rw [← hVB]
    refine Filter.eventuallyEqSet_iff.2 (hVae.mono fun ω h => ?_)
    show Wc ω ∈ G' ↔ V ω ∈ G'
    rw [h]
  have hA : gffBase.P (Zev C ∩ Wc ⁻¹' G') = gffBase.P (GB ∩ Zev C) := by
    rw [inter_comm]
    exact measure_congr (hWGB.inter (EventuallyEq.refl _ _))
  have hU : gffBase.P (Wc ⁻¹' G') = gffBase.P GB := measure_congr hWGB
  set L := C - γ * K with hL
  set I : ℝ≥0∞ := ∫⁻ ω, B.indicator 1
      (fun k => WedgeTK.gaussFam gffBase.X (g3fPairs x (κ / 2)) k ω) * Loc L ω ∂gffBase.P
    with hI
  obtain ⟨hC1, hC2⟩ := hC B hB
  have hIe : I = ∫⁻ ω, GB.indicator 1 ω * Loc L ω ∂gffBase.P := rfl
  have hBadm : AEMeasurable ((Bad L).indicator (1 : Ω₀ → ℝ≥0∞)) gffBase.P :=
    ((measurable_one.indicator (measurableSet_dyadBad γ r'' (R + 1))).comp_aemeasurable
      (hZm L))
  have hBadle : ∫⁻ ω, (Bad L).indicator 1 ω ∂gffBase.P ≤ gffBase.P (Bad L) :=
    lintegral_indicator_one_le _
  have hpA : gffBase.P (GB ∩ Zev C) = ∫⁻ ω, (GB ∩ Zev C).indicator 1 ω ∂gffBase.P :=
    (lintegral_indicator_one (hGBm.inter (hZevm C))).symm
  have hup : gffBase.P (GB ∩ Zev C) ≤ I + gffBase.P (Bad L) := by
    rw [hpA, hIe]
    calc ∫⁻ ω, (GB ∩ Zev C).indicator 1 ω ∂gffBase.P
        ≤ ∫⁻ ω, (GB.indicator 1 ω * Loc L ω + (Bad L).indicator 1 ω) ∂gffBase.P :=
          lintegral_mono_ae ((hind C GB).mono fun ω h => h.1)
      _ = (∫⁻ ω, GB.indicator 1 ω * Loc L ω ∂gffBase.P) +
            ∫⁻ ω, (Bad L).indicator 1 ω ∂gffBase.P := lintegral_add_right' _ hBadm
      _ ≤ _ := add_le_add le_rfl hBadle
  have hdown : I ≤ gffBase.P (GB ∩ Zev C) + gffBase.P (Bad L) := by
    rw [hpA, hIe]
    calc ∫⁻ ω, GB.indicator 1 ω * Loc L ω ∂gffBase.P
        ≤ ∫⁻ ω, ((GB ∩ Zev C).indicator 1 ω + (Bad L).indicator 1 ω) ∂gffBase.P :=
          lintegral_mono_ae ((hind C GB).mono fun ω h => h.2)
      _ = (∫⁻ ω, (GB ∩ Zev C).indicator 1 ω ∂gffBase.P) +
            ∫⁻ ω, (Bad L).indicator 1 ω ∂gffBase.P :=
          lintegral_add_left ((measurable_one.indicator (hGBm.inter (hZevm C)))) _
      _ ≤ _ := add_le_add le_rfl hBadle
  rw [hmass] at hC1 hC2
  set E : ℝ≥0∞ := ENNReal.ofReal (ε / 4) + gffBase.P (Bad L) with hE
  have hBadfin : gffBase.P (Bad L) ≠ ⊤ := measure_ne_top _ _
  have hEfin : E ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hBadfin⟩
  have h1 : gffBase.P (Zev C ∩ Wc ⁻¹' G') ≤
      ENNReal.ofReal c * gffBase.P (Wc ⁻¹' G') + E := by
    rw [hA, hU, mul_comm]
    calc gffBase.P (GB ∩ Zev C) ≤ I + gffBase.P (Bad L) := hup
      _ ≤ (gffBase.P GB * ENNReal.ofReal c + ENNReal.ofReal (ε / 4)) + gffBase.P (Bad L) :=
          add_le_add hC1 le_rfl
      _ = _ := by rw [hE, add_assoc]
  have h2 : ENNReal.ofReal c * gffBase.P (Wc ⁻¹' G') ≤
      gffBase.P (Zev C ∩ Wc ⁻¹' G') + E := by
    rw [hA, hU, mul_comm]
    calc gffBase.P GB * ENNReal.ofReal c ≤ I + ENNReal.ofReal (ε / 4) := hC2
      _ ≤ (gffBase.P (GB ∩ Zev C) + gffBase.P (Bad L)) + ENNReal.ofReal (ε / 4) :=
          add_le_add hdown le_rfl
      _ = _ := by rw [hE]; ring
  have hEle : E.toReal ≤ ε := by
    rw [hE, ENNReal.toReal_add ENNReal.ofReal_ne_top hBadfin,
      ENNReal.toReal_ofReal (by positivity)]
    have : (gffBase.P (Bad L)).toReal ≤ ε / 4 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hCb.le
    linarith
  exact (abs_toReal_sub_le_of_two_sided hc0 (measure_ne_top _ _) (measure_ne_top _ _) hEfin
    h1 h2).trans hEle

end G3ZqF
end Thm18Asm
end QuantumZipper
