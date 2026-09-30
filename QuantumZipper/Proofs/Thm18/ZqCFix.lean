import QuantumZipper.Proofs.Thm18.G3ZqFFix
import QuantumZipper.Proofs.Thm18.G1ZmPt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (1): the conditional zoom of the wedge Palm field through the local map (`Γ` form)

`palmFix_gamma`: let `a` be a good path, `x` a point of the side half-line with `|x| ≤ 1/2`,
`ρ > 0`, `V` a free field, and `h^x = N_S(ofFun (palmProf γ x) + V)` the Palm field of the wedge
Palm identity (`R18.G3WedgePalmIdStmt`, `G1Zm.palmFieldAt`). For every measurable `Γ ∈ [0, 1]`
and `e > 0`, eventually in the level `L`, uniformly over the measurable events `B` of the free
field's balanced increments carried outside `B(x, ρ)` (`G3ZqF.g3fPairs x ρ`),

  `E[1_B · Γ(loc_R(zoom_L of h^x at x through the local map))] = P(B) · E Γ(loc_R(wedge)) ± e`.

This is the `Γ`-version of `G3ZqF.fixCore` (the G2 Palm field replaced by the wedge Palm field):
ZOOM-A's agreement for the wedge Palm field (`G3Za.ae_agreeNear_zoom_palmField`), ZOOM-C's
conditional decorrelation with goodness and bad mass (`G3Cv.G3ZqF.cond_zoom_palm_free_full`), and
the local canonical proxy off the bad event (`locFieldFull_canonProxy_eq`).

Sheffield, arXiv:1012.4797, proof of Prop. 5.5 (p. 65) and of Thm. 1.8 (pp. 70–71: "even with
this conditioning ... one still obtains the laws of quantum wedges"). Own assembly (AGENT_GUIDE
cost rule), copied from `G3ZqF.fixCore` and `G1Zm.tendsto_palmZoom_canonical`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open D3Plus G3Cv S5.FieldLaw.Raw

/-- Off the bad dyadic set, `Γ` of the zoom datum is `Γ` of the local canonical description. -/
theorem gamma_eq_of_not_bad {γ r : ℝ} {R : ℕ} (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    {y y' : FieldSample}
    (hag : AgreeNear y y' r) (hg' : ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y') m)
    (hb : dyadData r y' ∉ dyadBad γ r (R + 1)) :
    Γ (g1zLocData R (lawOf (canonProxy γ y))) =
      Γ (locFieldFull R (canonicalOn γ y' (halfDisc r))) := by
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
  show Γ (locFieldFull R (canonProxy γ y)) = _
  rw [(G3ZqF.locFieldFull_canonProxy_eq hag hm hc.1 hc.2).2]

/-- **The conditional zoom of the wedge Palm field through the local map, `Γ` form.** -/
theorem palmFix_gamma {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a) {left : Bool} {x ρ : ℝ}
    (hxs : x ∈ g1SideHalf left) (hx1 : |x| ≤ 1 / 2) (hρ : 0 < ρ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (V : Ω' → FieldSample) (hV : IsFreeGFFModConstH V P')
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Y'' : Ω'' → FieldSample) (hW : IsQuantumWedge γ γ Y'' P'') (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∀ᶠ L in atTop, ∀ B : Set (K3.OutIdx 0 ρ → ℝ), MeasurableSet B →
      ∫⁻ ω, B.indicator 1 (fun k => WedgeTK.gaussFam V (G3ZqF.g3fPairs x ρ) k ω) *
          Γ (g1zLocData R (G3Z2b2.g1zM γ L Ψ left ((G1Zm.palmFieldAt γ x (V ω), a), x))) ∂P' ≤
        P' ((fun ω k => WedgeTK.gaussFam V (G3ZqF.g3fPairs x ρ) k ω) ⁻¹' B) *
          (∫⁻ ω, Γ (locFieldFull R (Y'' ω)) ∂P'') + e ∧
      P' ((fun ω k => WedgeTK.gaussFam V (G3ZqF.g3fPairs x ρ) k ω) ⁻¹' B) *
          (∫⁻ ω, Γ (locFieldFull R (Y'' ω)) ∂P'') ≤
        ∫⁻ ω, B.indicator 1 (fun k => WedgeTK.gaussFam V (G3ZqF.g3fPairs x ρ) k ω) *
          Γ (g1zLocData R (G3Z2b2.g1zM γ L Ψ left ((G1Zm.palmFieldAt γ x (V ω), a), x))) ∂P' +
          e := by
  classical
  have hx0 : x ≠ 0 := by
    intro h; subst h
    cases left
    · simp [g1SideHalf] at hxs
    · simp [g1SideHalf] at hxs
  -- the local map and its G0 extension
  set y₀ : FieldSample := fun _ => 0 with hy₀
  set ψ₀ := G3Z2b2.g3mapP Ψ left (y₀, a, 1, x) with hψ₀
  obtain ⟨r₀, hr₀, Φ, hΦ, heqΦ⟩ := G3ZqF.g3mapP_g0Ext hsel ha hxs y₀
  obtain ⟨rA, hrA, hA⟩ := G3Za.ae_agreeNear_zoom_palmField hV hr₀ hΦ γ hx0
  -- the profile
  set K : ℝ := ∫ u, G3Za.palmProf γ x u ∂R18.g3zS with hK
  set f : ℂ → ℝ := fun u => G3Za.palmProf γ x (u + x) with hfdef
  set S : Measure ℂ := foldedCircle (-(x : ℂ)) 1 with hSdef
  set ρf : ℝ := min (ρ / 2) (|x| / 2) with hρf
  have hxpos : 0 < |x| := abs_pos.2 hx0
  have hρf0 : 0 < ρf := lt_min (by positivity) (by positivity)
  have hρfx : ρf ≤ |x| / 2 := min_le_right _ _
  have hρfρ : ρf < ρ := (min_le_left _ _).trans_lt (by linarith)
  have hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar,
      f u = γ * -Real.log ‖u‖ + G3Za.palmH γ x (u + x) := fun u hu =>
    G3Za.palmProf_shift_eq γ (closedBall_subset_closedBall hρfx hu.1)
  have hh : Continuous fun u => G3Za.palmH γ x (u + x) :=
    (G3Za.continuous_palmH γ hx0).comp (continuous_id.add continuous_const)
  have hfm : Measurable f :=
    (G3Za.measurable_palmProf γ x).comp (measurable_id.add measurable_const)
  have hhh := (G3Za.harmonicOnNhd_palmH_shift γ hx0 hx1).mono (ball_subset_ball hρfx)
  have hhc : ∀ u ∈ ball (0 : ℂ) ρf,
      G3Za.palmH γ x ((starRingEnd ℂ) u + x) = G3Za.palmH γ x (u + x) := fun u _ =>
    G3Za.palmH_shift_conj γ x u
  have hSa : IsAdmissibleH S := isAdmissibleH_foldedCircle_g3cv2 _ one_pos
  have hS1 : S Set.univ = 1 := measure_univ
  have hSf : ∀ᵐ y ∂S, ρf < ‖y‖ :=
    (G3Za.fc_neg_far hx0 hx1).mono fun y hy => hρfx.trans_lt hy
  have hSx : IsAdmissibleH (S.map (· + (x : ℂ))) := isAdmissibleH_map_add_real hSa x
  obtain ⟨r'', R₀, hr'', hr''le, hR₀, hR₀le, hmain⟩ :=
    G3Cv.G3ZqF.cond_zoom_palm_free_full hr₀ hΦ hγ hγ2 hρf0 hf hh hfm hhh hhc hSa hS1 hSf
      (lt_min hrA hr₀ : 0 < min rA r₀)
  have hR₀ρ : R₀ < ρ := hR₀le.trans_lt hρfρ
  obtain ⟨hZm, hgood, hbad, hcond⟩ := hmain x hSx (G3ZqF.g3fPairs x ρ)
    (fun k => G3ZqF.g3fPairs_far x hR₀ρ k) P' V hV
  set Z' : ℝ → Ω' → FieldSample := fun L ω => zoomS γ L (Qc γ) f Φ S (rawTranslate (V ω) x)
    with hZ'
  set Bad : ℝ → Set Ω' := fun L =>
    (fun ω => dyadData r'' (Z' L ω)) ⁻¹' dyadBad γ r'' (R + 1) with hBad
  set Loc : ℝ → Ω' → ℝ≥0∞ := fun L ω =>
    Γ (locFieldFull R (canonicalOn γ (Z' L ω) (halfDisc r''))) with hLoc
  set Itg : ℝ → Ω' → ℝ≥0∞ := fun C ω =>
    Γ (g1zLocData R (G3Z2b2.g1zM γ C Ψ left ((G1Zm.palmFieldAt γ x (V ω), a), x))) with hItg
  -- pointwise comparison off the bad event
  have hpt : ∀ C : ℝ, ∀ᵐ ω ∂P', ω ∉ Bad (C - γ * K) → Itg C ω = Loc (C - γ * K) ω := by
    intro C
    filter_upwards [hA, hgood (C - γ * K)] with ω hAω hg hnb
    have e2 : AgreeNear (zoomFieldVia γ C (G1Zm.palmFieldAt γ x (V ω)) x Φ)
        (Z' (C - γ * K) ω) rA := by
      have e : Z' (C - γ * K) ω =
          addConst (coordChange (ofFun (fun u => G3Za.palmProf γ x (u + x)) +
              rawTranslate (V ω) x) Φ (Qc γ))
            (C / γ - ((∫ u, G3Za.palmProf γ x u ∂R18.g3zS) +
              rawTranslate (V ω) x (foldedCircle (-(x : ℂ)) 1))) := by
        simp only [hZ', zoomS, hSdef, hfdef]
        congr 1
        rw [← hK]
        field_simp
        ring
      rw [e]
      exact hAω C
    have hag : AgreeNear (zoomFieldVia γ C (G1Zm.palmFieldAt γ x (V ω)) x ψ₀)
        (Z' (C - γ * K) ω) r'' := by
      have e1 := G3ZqF.agreeNear_zoomFieldVia_of_eqOn heqΦ γ C (G1Zm.palmFieldAt γ x (V ω)) x
      intro n k z hz
      have hz1 : ‖dyadicRoundC n z‖ + radius k < r₀ :=
        hz.trans_le (hr''le.trans (min_le_right _ _))
      have hz2 : ‖dyadicRoundC n z‖ + radius k < rA :=
        hz.trans_le (hr''le.trans (min_le_left _ _))
      exact (e1 n k z hz1).trans (e2 n k z hz2)
    show Γ (g1zLocData R (G3Z2b2.g1zM γ C Ψ left ((G1Zm.palmFieldAt γ x (V ω), a), x))) = _
    rw [G3ZqF.g1zM_eq_canonProxy hsel ha C left _ y₀ x]
    exact gamma_eq_of_not_bad Γ hag hg hnb
  -- the pointwise two-sided bounds
  have hind : ∀ C : ℝ, ∀ (T : Set Ω'), ∀ᵐ ω ∂P',
      T.indicator 1 ω * Itg C ω ≤ T.indicator 1 ω * Loc (C - γ * K) ω +
          (Bad (C - γ * K)).indicator 1 ω ∧
        T.indicator 1 ω * Loc (C - γ * K) ω ≤ T.indicator (1 : Ω' → ℝ≥0∞) ω * Itg C ω +
          (Bad (C - γ * K)).indicator 1 ω := by
    intro C T
    filter_upwards [hpt C] with ω hω
    have hT1 : T.indicator (1 : Ω' → ℝ≥0∞) ω ≤ 1 := indicator_le (fun _ _ => le_rfl) _
    by_cases hb : ω ∈ Bad (C - γ * K)
    · rw [indicator_of_mem hb]
      exact ⟨(mul_le_one' hT1 (hΓ1 _)).trans (le_add_left le_rfl),
        (mul_le_one' hT1 (hΓ1 _)).trans (le_add_left le_rfl)⟩
    · rw [indicator_of_notMem hb, add_zero, add_zero, hω hb]
      exact ⟨le_rfl, le_rfl⟩
  -- the main estimate
  have he2 : (0 : ℝ≥0∞) < e / 2 := ENNReal.div_pos he.ne' ENNReal.ofNat_ne_top
  have hcondY := hcond P'' Y'' hW R Γ hΓ hΓ1 _ he2
  have hshift : Tendsto (fun C : ℝ => C - γ * K) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  filter_upwards [hshift.eventually hcondY,
    hshift.eventually ((hbad (R + 1)).eventually (gt_mem_nhds he2))] with C hC hCb B hB
  set GB : Set Ω' := (fun ω k => WedgeTK.gaussFam V (G3ZqF.g3fPairs x ρ) k ω) ⁻¹' B with hGB
  set L := C - γ * K with hL
  have hIe : ∀ F : Ω' → ℝ≥0∞, ∫⁻ ω, B.indicator 1
      (fun k => WedgeTK.gaussFam V (G3ZqF.g3fPairs x ρ) k ω) * F ω ∂P' =
      ∫⁻ ω, GB.indicator 1 ω * F ω ∂P' := fun F => rfl
  obtain ⟨hC1, hC2⟩ := hC B hB
  rw [hIe] at hC1 hC2 ⊢
  have hBadm : AEMeasurable ((Bad L).indicator (1 : Ω' → ℝ≥0∞)) P' :=
    ((measurable_one.indicator (measurableSet_dyadBad γ r'' (R + 1))).comp_aemeasurable
      (hZm L))
  have hBadle : ∫⁻ ω, (Bad L).indicator 1 ω ∂P' ≤ P' (Bad L) :=
    lintegral_indicator_one_le _
  have hup : ∫⁻ ω, GB.indicator 1 ω * Itg C ω ∂P' ≤
      ∫⁻ ω, GB.indicator 1 ω * Loc L ω ∂P' + P' (Bad L) :=
    calc ∫⁻ ω, GB.indicator 1 ω * Itg C ω ∂P'
        ≤ ∫⁻ ω, (GB.indicator 1 ω * Loc L ω + (Bad L).indicator 1 ω) ∂P' :=
          lintegral_mono_ae ((hind C GB).mono fun ω h => h.1)
      _ = (∫⁻ ω, GB.indicator 1 ω * Loc L ω ∂P') + ∫⁻ ω, (Bad L).indicator 1 ω ∂P' :=
          lintegral_add_right' _ hBadm
      _ ≤ _ := add_le_add le_rfl hBadle
  have hdown : ∫⁻ ω, GB.indicator 1 ω * Loc L ω ∂P' ≤
      ∫⁻ ω, GB.indicator 1 ω * Itg C ω ∂P' + P' (Bad L) :=
    calc ∫⁻ ω, GB.indicator 1 ω * Loc L ω ∂P'
        ≤ ∫⁻ ω, (GB.indicator 1 ω * Itg C ω + (Bad L).indicator 1 ω) ∂P' :=
          lintegral_mono_ae ((hind C GB).mono fun ω h => h.2)
      _ = (∫⁻ ω, GB.indicator 1 ω * Itg C ω ∂P') + ∫⁻ ω, (Bad L).indicator 1 ω ∂P' :=
          lintegral_add_right' _ hBadm
      _ ≤ _ := add_le_add le_rfl hBadle
  have hsum : e / 2 + e / 2 = e := ENNReal.add_halves e
  constructor
  · calc ∫⁻ ω, GB.indicator 1 ω * Itg C ω ∂P'
        ≤ ∫⁻ ω, GB.indicator 1 ω * Loc L ω ∂P' + P' (Bad L) := hup
      _ ≤ (P' GB * ∫⁻ ω, Γ (locFieldFull R (Y'' ω)) ∂P'' + e / 2) + e / 2 :=
          add_le_add hC1 hCb.le
      _ = _ := by rw [add_assoc, hsum]
  · calc P' GB * ∫⁻ ω, Γ (locFieldFull R (Y'' ω)) ∂P''
        ≤ ∫⁻ ω, GB.indicator 1 ω * Loc L ω ∂P' + e / 2 := hC2
      _ ≤ (∫⁻ ω, GB.indicator 1 ω * Itg C ω ∂P' + P' (Bad L)) + e / 2 :=
          add_le_add hdown le_rfl
      _ ≤ (∫⁻ ω, GB.indicator 1 ω * Itg C ω ∂P' + e / 2) + e / 2 :=
          add_le_add (add_le_add le_rfl hCb.le) le_rfl
      _ = _ := by rw [add_assoc, hsum]

end ZqC
end Thm18Asm
end QuantumZipper
