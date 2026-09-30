import QuantumZipper.Proofs.Thm18.ZqCS2
import QuantumZipper.Proofs.Thm18.ZqCC1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (13): the bad functional vanishes under the Palm law; `G3ZqO6CoreDStmt`

`tendsto_betaS_palm`: at every core point `x`, `E β_L(h^x) → 0` for the wedge Palm field
`h^x = N_S(ofFun (palmProf γ x) + V)`. ZOOM-A (`G3Za.ae_agreeNear_zoom_palmField`) and the local
map's G0 extension put the zoom of `h^x` near `0` equal to the ZOOM-C field `zoomS` of the free
field `V_x`; ZOOM-C with certificates (`G3Cv.ZqCC.cond_zoom_palm_free_cert`) gives a radius `r''`
with the local certificate a.s. at every smaller radius and vanishing bad-scale mass at `r''`;
the dyadic radius `ρ = 1/(⌊1/r''⌋ + 1) ∈ [r''/2, r'']` then carries a small local scale off the
bad event (`ZqC.not_dyadBad_mono`), and the local map is controlled there (`mapOK`), so
`(vOf h^x, x) ∈ okSet`, i.e. `β_L = 0`, off an event of vanishing probability.

Hence **`zqCLocSandwichStmt_holds`** and **`g3ZqO6CoreDStmt_holds : G3ZqO6CoreDStmt`**.

Sheffield, arXiv:1012.4797, pp. 70–71 and proof of Prop. 5.5 (p. 65). Own assembly (AGENT_GUIDE
cost rule), following `G1Zm.tendsto_palmZoom_canonical` and `G3ZqF.fixCore`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization G2PalmLoc G3Cv S5.FieldLaw.Raw

variable {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

theorem rhoM_anti {m m' : ℕ} (h : m ≤ m') : rhoM m' ≤ rhoM m := by
  unfold rhoM
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1

theorem abs_le_quarter_of_core {left : Bool} {η x : ℝ} (hη : 0 < η) (hx : x ∈ coreSet left η) :
    |x| ≤ 1 / 4 := by
  cases left
  · simp only [coreSet, Bool.false_eq_true, ite_false, mem_Icc] at hx
    rw [abs_of_pos (by linarith)]; linarith
  · simp only [coreSet, ite_true, mem_Icc] at hx
    rw [abs_of_neg (by linarith)]; linarith

/-- **The local map is controlled at all small dyadic scales.** -/
theorem eventually_mapOK (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3ZqGoodPath γ a)
    {left : Bool} {x : ℝ} (hxs : x ∈ g1SideHalf left) (hx4 : |x| ≤ 1 / 4) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → mapOK Ψ left a m x := by
  obtain ⟨r₀, hr₀, Φ, hΦ, heqΦ⟩ := G3ZqF.g3mapP_g0Ext hsel ha hxs fz
  have hcont : ContinuousAt Φ 0 :=
    hΦ.1.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr₀))
  obtain ⟨ε, hε, hεs⟩ := Metric.continuousAt_iff.1 hcont (1 / 4) (by norm_num)
  obtain ⟨m₀, hm₀⟩ := exists_nat_one_div_lt (lt_min hε hr₀)
  refine ⟨m₀, fun m hm q hq1 hq2 => ?_⟩
  have hq : ‖qpt q‖ < min ε r₀ := hq2.trans_le ((rhoM_anti hm).trans (by
    unfold rhoM; exact hm₀.le))
  have hqH : qpt q ∈ ball (0 : ℂ) r₀ ∩ H :=
    ⟨by rw [mem_ball, dist_zero_right]; exact hq.trans_le (min_le_right _ _),
      show 0 < (qpt q).im by simpa [qpt] using hq1⟩
  have e : mapX Ψ left a x (qpt q) = Φ (qpt q) := (heqΦ hqH).symm
  have h1 : ‖Φ (qpt q)‖ < 1 / 4 := by
    have := hεs (show dist (qpt q) 0 < ε by
      rw [dist_zero_right]; exact hq.trans_le (min_le_left _ _))
    rwa [hΦ.2.2.2.1, dist_zero_right] at this
  rw [e]
  have h2 := norm_add_le (Φ (qpt q)) (x : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at h2
  linarith

theorem rhoM_floor_props {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2) :
    rhoM ⌊1 / r⌋₊ ≤ r ∧ r / 2 ≤ rhoM ⌊1 / r⌋₊ := by
  have h1 := Nat.lt_floor_add_one (1 / r)
  have h2 := Nat.floor_le (show (0 : ℝ) ≤ 1 / r by positivity)
  have hpos : (0 : ℝ) < (⌊1 / r⌋₊ : ℝ) + 1 := by positivity
  unfold rhoM
  constructor
  · rw [div_le_iff₀ hpos]
    have : 1 / r * r = 1 := by field_simp
    nlinarith
  · rw [le_div_iff₀ hpos]
    have h3 : 1 ≤ 1 / r := by rw [le_div_iff₀ hr]; linarith
    have : r * (1 / r) = 1 := by field_simp
    nlinarith

/-- **The bad functional vanishes in expectation under the Palm law.** -/
theorem tendsto_betaS_palm (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (ha : G3ZqGoodPath γ a) {left : Bool} {x : ℝ} (hxs : x ∈ g1SideHalf left)
    (hx4 : |x| ≤ 1 / 4) (R : ℕ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (V : Ω' → FieldSample) (hV : IsFreeGFFModConstH V P') :
    Tendsto (fun L => ∫⁻ ω, betaS γ L Ψ left a R (vOf (G1Zm.palmFieldAt γ x (V ω))) x ∂P')
      atTop (𝓝 0) := by
  classical
  have hx0 : x ≠ 0 := by
    intro h; subst h
    cases left
    · simp [g1SideHalf] at hxs
    · simp [g1SideHalf] at hxs
  have hx1 : |x| ≤ 1 / 2 := by linarith
  obtain ⟨m₀, hm₀⟩ := eventually_mapOK hsel ha hxs hx4
  obtain ⟨r₀, hr₀, Φ, hΦ, heqΦ⟩ := G3ZqF.g3mapP_g0Ext hsel ha hxs fz
  obtain ⟨rA, hrA, hA⟩ := G3Za.ae_agreeNear_zoom_palmField hV hr₀ hΦ γ hx0
  -- the profile
  set K : ℝ := ∫ u, G3Za.palmProf γ x u ∂R18.g3zS with hK
  set f : ℂ → ℝ := fun u => G3Za.palmProf γ x (u + x) with hfdef
  set S : Measure ℂ := foldedCircle (-(x : ℂ)) 1 with hSdef
  have hxpos : 0 < |x| := abs_pos.2 hx0
  have hρf0 : 0 < |x| / 2 := by positivity
  have hf : ∀ u ∈ closedBall (0 : ℂ) (|x| / 2) ∩ Hbar,
      f u = γ * -Real.log ‖u‖ + G3Za.palmH γ x (u + x) := fun u hu =>
    G3Za.palmProf_shift_eq γ hu.1
  have hh : Continuous fun u => G3Za.palmH γ x (u + x) :=
    (G3Za.continuous_palmH γ hx0).comp (continuous_id.add continuous_const)
  have hfm : Measurable f :=
    (G3Za.measurable_palmProf γ x).comp (measurable_id.add measurable_const)
  have hhh := G3Za.harmonicOnNhd_palmH_shift γ hx0 hx1
  have hhc : ∀ u ∈ ball (0 : ℂ) (|x| / 2),
      G3Za.palmH γ x ((starRingEnd ℂ) u + x) = G3Za.palmH γ x (u + x) := fun u _ =>
    G3Za.palmH_shift_conj γ x u
  have hSa : IsAdmissibleH S := isAdmissibleH_foldedCircle_g3cv2 _ one_pos
  have hS1 : S Set.univ = 1 := measure_univ
  have hSf : ∀ᵐ y ∂S, |x| / 2 < ‖y‖ := G3Za.fc_neg_far hx0 hx1
  have hSx : IsAdmissibleH (S.map (· + (x : ℂ))) := isAdmissibleH_map_add_real hSa x
  have hrmax : 0 < min (min rA r₀) (min (rhoM m₀) (1 / 2)) :=
    lt_min (lt_min hrA hr₀) (lt_min (rhoM_pos m₀) (by norm_num))
  obtain ⟨r'', R₀, hr'', hr''le, -, -, hmain⟩ :=
    G3Cv.ZqCC.cond_zoom_palm_free_cert hr₀ hΦ hγ hγ2 hρf0 hf hh hfm hhh hhc hSa hS1 hSf hrmax
  obtain ⟨hcert, -, hgood, hbad, -⟩ := hmain x hSx (K := PEmpty) (fun k => k.elim)
    (fun k => k.elim) P' V hV
  have hr''A : r'' ≤ rA := hr''le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr''0 : r'' ≤ r₀ := hr''le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr''m : r'' ≤ rhoM m₀ := hr''le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr''h : r'' ≤ 1 / 2 := hr''le.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the dyadic radius
  set m₁ : ℕ := ⌊1 / r''⌋₊ with hm₁
  obtain ⟨hρle, hρge⟩ := rhoM_floor_props hr'' hr''h
  have hm₀₁ : m₀ ≤ m₁ := by
    rw [hm₁]
    apply Nat.le_floor
    have h1 : (m₀ : ℝ) + 1 ≤ 1 / r'' := by
      rw [le_div_iff₀ hr'']
      have := hr''m
      unfold rhoM at this
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    linarith
  have hmap : mapOK Ψ left a m₁ x := hm₀ m₁ hm₀₁
  set ρ₁ := rhoM m₁ with hρ₁
  have hρ₁0 : 0 < ρ₁ := rhoM_pos m₁
  have hψm : Measurable (mapX Ψ left a x) :=
    (g3mapB_props hsel ha.1 ha.2 left (zero_lt_one' ℝ) (x / 1)).2.2
  set Z' : ℝ → Ω' → FieldSample := fun L ω => zoomS γ L (Qc γ) f Φ S (rawTranslate (V ω) x)
    with hZ'
  set Bad : ℝ → Set Ω' := fun L =>
    (fun ω => dyadData r'' (Z' L ω)) ⁻¹' dyadBad γ r'' (2 * R + 1 + 1) with hBad
  -- off the bad event the bad functional vanishes
  have hkey : ∀ L : ℝ, ∀ᵐ ω ∂P', ω ∉ Bad (L - γ * K) →
      betaS γ L Ψ left a R (vOf (G1Zm.palmFieldAt γ x (V ω))) x = 0 := by
    intro L
    filter_upwards [hA, hcert ρ₁ hρ₁0 hρle (L - γ * K), hgood (L - γ * K)] with ω hAω hcω hgω hnb
    set hx' := G1Zm.palmFieldAt γ x (V ω) with hhx'
    -- agreement of the zoom through `Φ` with `Z'`
    have e2 : AgreeNear (zoomFieldVia γ L hx' x Φ) (Z' (L - γ * K) ω) rA := by
      have e : Z' (L - γ * K) ω =
          addConst (coordChange (ofFun (fun u => G3Za.palmProf γ x (u + x)) +
              rawTranslate (V ω) x) Φ (Qc γ))
            (L / γ - ((∫ u, G3Za.palmProf γ x u ∂R18.g3zS) +
              rawTranslate (V ω) x (foldedCircle (-(x : ℂ)) 1))) := by
        simp only [hZ', zoomS, hSdef, hfdef]
        congr 1
        rw [← hK]
        field_simp
        ring
      rw [e]
      exact hAω L
    have e1 := G3ZqF.agreeNear_zoomFieldVia_of_eqOn heqΦ γ L hx' x
    have e3 := agreeNear_zoomFieldVia_recF γ L hx' x hψm (hpsi_of_mapOK hsel ha left hmap)
    have e4 := agreeNear_Zr hsel ha L left (vOf hx') x ρ₁
    have hag : AgreeNear (Zr γ L Ψ left a (vOf hx') x) (Z' (L - γ * K) ω) ρ₁ := by
      intro n k z hz
      have hzA : ‖dyadicRoundC n z‖ + radius k < rA := hz.trans_le (hρle.trans hr''A)
      have hz0 : ‖dyadicRoundC n z‖ + radius k < r₀ := hz.trans_le (hρle.trans hr''0)
      exact (e4 n k z hz).trans ((e3 n k z hz).trans ((e1 n k z hz0).trans (e2 n k z hzA)))
    have hdd := dyadData_eq_of_agreeNear hag
    -- the scale at `r''`
    have hag' := agreeNear_dyadField r'' (Z' (L - γ * K) ω)
    have hgood' := (exists_isVagueLimitOn_halfDisc_iff hag').1 hgω
    have hs' := scaleParamOn_halfDisc_congr (γ := γ) hag'
    have hds : dyadScale γ r'' (dyadData r'' (Z' (L - γ * K) ω)) =
        scaleParamOn γ (Z' (L - γ * K) ω) (halfDisc r'') := by
      rw [dyadScale_eq hgood', ← hs']
    have hnb' : 0 < scaleParamOn γ (Z' (L - γ * K) ω) (halfDisc r'') ∧
        scaleParamOn γ (Z' (L - γ * K) ω) (halfDisc r'') * ((2 * R + 1 + 1 : ℕ) : ℝ) < r'' := by
      have := hnb
      simp only [hBad, mem_preimage, dyadBad, mem_setOf_eq, not_not] at this
      rwa [hds] at this
    set s := scaleParamOn γ (Z' (L - γ * K) ω) (halfDisc r'') with hs
    have hsR : s * ((R : ℝ) + 1) < r'' / 2 := by
      have := hnb'.2
      push_cast at this
      nlinarith [hnb'.1]
    have hb1 : dyadData r'' (Z' (L - γ * K) ω) ∉ dyadBad γ r'' (R + 1) := by
      simp only [dyadBad, mem_setOf_eq, not_not]
      rw [hds]
      refine ⟨hnb'.1, ?_⟩
      push_cast
      nlinarith [hnb'.1]
    obtain ⟨-, hbρ⟩ := not_dyadBad_mono hρ₁0 hρle hgω hb1 (hsR.trans_le hρge)
    have hok : (vOf hx', x) ∈ okSet γ L Ψ left a R m₁ := by
      refine ⟨hmap, ?_, ?_⟩
      · show G3ZqF.dyadCert γ ρ₁ (dyadData ρ₁ (Zr γ L Ψ left a (vOf hx') x))
        rw [hdd]; exact hcω
      · show dyadData ρ₁ (Zr γ L Ψ left a (vOf hx') x) ∉ dyadBad γ ρ₁ (R + 1)
        rw [hdd]; exact hbρ
    unfold betaS
    rw [indicator_of_notMem (show (vOf hx', x) ∉ (⋃ m, okSet γ L Ψ left a R m)ᶜ from
      fun h => h (mem_iUnion.2 ⟨m₁, hok⟩))]
  have hbound : ∀ L : ℝ,
      ∫⁻ ω, betaS γ L Ψ left a R (vOf (G1Zm.palmFieldAt γ x (V ω))) x ∂P' ≤
        P' (Bad (L - γ * K)) := by
    intro L
    calc _ ≤ ∫⁻ ω, (Bad (L - γ * K)).indicator 1 ω ∂P' := by
          refine lintegral_mono_ae ((hkey L).mono fun ω hω => ?_)
          by_cases hb : ω ∈ Bad (L - γ * K)
          · rw [indicator_of_mem hb]; exact betaS_le_one L left a R _ x
          · rw [hω hb]; exact bot_le
      _ ≤ _ := lintegral_indicator_one_le _
  have hshift : Tendsto (fun L : ℝ => L - γ * K) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((hbad (2 * R + 1 + 1)).comp hshift) (fun _ => bot_le) hbound

/-- **The local sandwich node holds.** -/
theorem zqCLocSandwichStmt_holds : ZqCLocSandwichStmt := by
  intro γ hγ hγ2 Ψ hsel a ha left R Γ hΓ hΓ1 η hη hη4
  refine ⟨fun L => phiS γ L Ψ left a R Γ, fun L => betaS γ L Ψ left a R,
    fun L => measurable_phiS hsel L left a R hΓ, fun L => measurable_betaS hsel L left a R,
    fun L v x => betaS_le_one L left a R v x,
    fun L y x hx => sandwichS hsel ha (mem_side_of_core hη hη4 hx).1 L R Γ hΓ1 y, ?_⟩
  intro Ω' _ P' _ V hV x hx
  exact tendsto_betaS_palm hγ hγ2 hsel ha (mem_side_of_core hη hη4 hx).1
    (abs_le_quarter_of_core hη hx) R P' V hV

/-- **`G3ZqO6CoreDStmt` holds.** -/
theorem g3ZqO6CoreDStmt_holds : G3ZqO6CoreDStmt :=
  g3ZqO6CoreDStmt_of_sandwich zqCLocSandwichStmt_holds

end ZqC
end Thm18Asm
end QuantumZipper
