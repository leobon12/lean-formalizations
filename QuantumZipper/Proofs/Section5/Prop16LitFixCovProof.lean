import QuantumZipper.Proofs.Section5.Prop16LitFixCov
import QuantumZipper.Proofs.LQG.CoordChangeAreaZoom
import QuantumZipper.Proofs.Section5.Prop16ShiftGoodPalm
import QuantumZipper.Proofs.Section5.Prop17PalmCSetup
import QuantumZipper.Proofs.Complex.BasicsUnivalent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the chart clause at a fixed point (COORD-CHANGE, D98)

`Prop16Lit.prop16LitFixCov1Stmt_proved : Prop16LitFixCov1Stmt`. At a fixed boundary point
`x ∈ (a,b)` the chart `ψ_x` is deterministic, and the Palm-shifted field
`h₀ + X + (γ/2) G_D(x,·)` is, on the dyadic circles inside `D`, a free field plus the continuous
function `φ + h₀ + (γ/2) G_D(x,·)` (the local coupling `prop16MixedFreeLocCoupling_mm` and the
Palm shift `Prop16Asm.palmPsi`, continuous on `D`). Translating by `x` (the free field stays
free, `S5.FieldLaw.Raw.isFreeGFFModConstH_translate`) and applying the local coordinate-change
theorem (Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 2.1;
`CoordChangeArea.ae_map_qAreaMeasureOn_coordChange`) to the zoomed field `h(· + x) + C/γ`
gives the identity of `Prop16LitCovStmt` (1) almost surely, simultaneously for every level `C`
(the constant commutes with the coordinate change: `isVagueLimitOn_addConst_coordChange`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open Prop16Asm CoordChangeArea G1Side

set_option maxHeartbeats 1600000 in
/-- **Clause (1) of `Prop16LitCovStmt` at a fixed point, for the Palm-shifted field.** -/
theorem prop16LitFixCov1Stmt_proved : Prop16LitFixCov1Stmt := by
  intro γ D c d a b h0 Ω _ P X hdat ψ r₀ hfam x hx
  obtain ⟨hγ, hγ2, hgeo, hab, hca, hbd, hh0, hP, hX, -, -⟩ := hdat
  obtain ⟨hψm, -, hch⟩ := hfam
  have hxcd : x ∈ Ioo c d := ⟨lt_of_le_of_lt hca hx.1, lt_of_lt_of_le hx.2 hbd⟩
  have hcd : c < d := hgeo.2.2.2.2.1
  obtain ⟨hψd, hψi, hψim, hr0, -⟩ := hch x hx
  set ψx := ψ x with hψxdef
  have hψxm : Measurable ψx := hψm.comp (measurable_const.prodMk measurable_id)
  have hDo : IsOpen D := hgeo.1
  have hDH : D ⊆ H := hgeo.2.2.2.1
  have hZo : IsOpen (zoomDomain D x) := hDo.preimage (continuous_id.add continuous_const)
  have hZH : zoomDomain D x ⊆ H := fun z hz => by
    have h1 : (0 : ℝ) < (z + (x : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using h1
  have hψZ : MapsTo ψx H (zoomDomain D x) := fun w hw => hψim ▸ mem_image_of_mem ψx hw
  have hψH : MapsTo ψx H H := hψZ.mono_right hZH
  have hψ0 : ∀ z ∈ H, deriv ψx z ≠ 0 := fun z hz => CA.deriv_ne_zero_of_injOn isOpen_H hψd hψi hz
  set U := ball (0 : ℂ) (r₀ x) ∩ H with hUdef
  have hUo : IsOpen U := isOpen_ball.inter isOpen_H
  have hUH : U ⊆ H := inter_subset_right
  have hUZ : MapsTo ψx U (zoomDomain D x) := hψZ.mono_left hUH
  -- the local coupling and the translated free field
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo le_rfl le_rfl (a := c) (b := d)
  obtain ⟨Ω₀, _, _, P₀, Y, Xf, hP₀, hY, hXf, hag⟩ :=
    prop16MixedFreeLocCoupling_mm D c d c d hgeo hcd le_rfl le_rfl
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hXf
  set Xt : Ω₀ → FieldSample := fun ω₀ μ => Xf ω₀ (μ.map (· + (x : ℂ))) with hXtdef
  have hXt : IsFreeGFFModConstH Xt P₀ := S5.FieldLaw.Raw.isFreeGFFModConstH_translate hXf x
  -- raw values of the translate at the dyadic circles
  have hraw : ∀ᵐ ω₀ ∂P₀, ∀ (n k : ℕ) (p : ℤ × ℤ),
      (⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) ∈ Hbar →
      Xt ω₀ (foldedCircle ⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ (radius k)) =
        G ω₀ ((⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) + (x : ℂ), radius k) := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro p
    by_cases hp : (⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) ∈ Hbar
    · have hpx : (⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) + (x : ℂ) ∈ Hbar := by
        have h0 : (0 : ℝ) ≤ (⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ).im := hp
        show (0 : ℝ) ≤ _; simpa using h0
      filter_upwards [hG.raw _ hpx _ (radius_pos k)] with ω₀ h _
      simp only [hXtdef]
      rw [Thm18Asm.ExactCl.foldedCircle_map_add x]
      exact h.symm
    · exact ae_of_all _ fun _ h => absurd h hp
  -- the good set of the coupling space
  have hS : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ {ω₀ |
      (∀ (x' : FieldSample) (W' : Set ℂ) (φ : ℂ → ℝ) (U' V' : Set ℂ), IsOpen W' →
        ContinuousOn φ W' → Prop16Area.G.CircAgree W' x' (Xt ω₀ + ofFun φ) → IsOpen U' →
        U' ⊆ H → IsOpen V' → V' ⊆ H → V' ⊆ W' → MapsTo ψx U' V' →
        (qAreaMeasureOn γ (coordChange x' ψx (Qc γ)) U').map ψx =
          (qAreaMeasureOn γ x' V').restrict (ψx '' U')) ∧
      (∀ (x' : FieldSample) (W' : Set ℂ) (φ : ℂ → ℝ) (U' : Set ℂ), IsOpen W' →
        ContinuousOn φ W' → Prop16Area.G.CircAgree W' x' (Xt ω₀ + ofFun φ) → IsOpen U' →
        U' ⊆ H → MapsTo ψx U' W' →
        IsVagueLimitOn U' (areaApprox γ (coordChange x' ψx (Qc γ)))
          (((pullMu (qAreaMeasure γ (Xt ω₀)) ψx).restrict U').withDensity
            fun z => ENNReal.ofReal (Real.exp (γ * φ (ψx z))))) ∧
      PushRegular (Xt ω₀) ψx ∧ IsRegularSample (Xt ω₀) ∧ IsRegularWith (Xf ω₀) (G ω₀) ∧
      (∀ (n k : ℕ) (p : ℤ × ℤ), (⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) ∈ Hbar →
        Xt ω₀ (foldedCircle ⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ (radius k)) =
          G ω₀ ((⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) + (x : ℂ), radius k)) ∧
      ∃ φ : ℂ → ℝ, ContinuousOn φ (D ∪ realSet (Ioo c d)) ∧
        Prop16Area.G.CircAgree (D ∪ realSet (Ioo c d)) (Y ω₀) (Xf ω₀ + ofFun φ)} := by
    filter_upwards [ae_map_qAreaMeasureOn_coordChange hXt hγ hγ2 hψxm hψd hψi hψH hψ0,
      ae_isVagueLimitOn_coordChange_local hXt hγ hγ2 hψxm hψd hψi hψH hψ0,
      ae_pushRegular hXt hψd hψi hψH hψ0, RegSample.ae_isRegularSample hXt, hG.reg, hraw, hag]
      with ω₀ h1 h2 h3 h4 h5 h6 h7 using ⟨h1, h2, h3, h4, h5, h6, h7⟩
  -- law transfer to `X`
  have hDW : D ⊆ W := fun z hz => by
    have : z ∈ W ∩ Hbar := by rw [hWV]; exact Or.inl hz
    exact this.1
  let I := {m : Measure ℂ // m ∈ locCircSet D}
  have : Countable I := (locCircSet_countable D).to_subtype
  have hadm : ∀ i : I, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) i.1 := by
    rintro ⟨_, n, k, z, hz, hsub, rfl⟩
    exact locGood_isAdmissible_circle hgeo le_rfl le_rfl hWo hWV
      (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k) (hsub.trans hDW)
  have hlaw := locGood_map_eq_of_isMixedGFF hX hY (fun i : I => i.1) hadm
  have hmF : Measurable fun ω (i : I) => X ω i.1 :=
    measurable_pi_iff.2 fun i => hX.measurable_coord _
  have hmG : Measurable fun ω (i : I) => Y ω i.1 :=
    measurable_pi_iff.2 fun i => hY.measurable_coord _
  filter_upwards [locGood_ae_exists_of_map_eq hmF.aemeasurable hmG hlaw hS] with ω hω C
  obtain ⟨ω₀, ⟨hgood, hvague, hpush, hregt, hreg, hrawω, φ, hφ, hag'⟩, hFG⟩ := hω
  have hφD : ContinuousOn φ D := hφ.mono subset_union_left
  -- `X ω` is the free sample plus `φ` on `D`
  have hXD : Prop16Area.G.CircAgree D (X ω) (Xf ω₀ + ofFun φ) := by
    intro n k z hz hsub
    have h1 := congrFun hFG ⟨_, n, k, z, hz, hsub, rfl⟩
    exact h1.trans (hag' n k z hz fun u hu => Or.inl (hsub hu))
  -- the Palm-shifted field on `D`
  set ψP := palmPsi D (realSet (Icc c d)) x with hψPdef
  have hψPc : ContinuousOn ψP D := continuousOn_palmPsi hgeo hxcd
  set Φ : ℂ → ℝ := fun z => (φ z + (γ / 2) * ψP z) + h0 z with hΦdef
  have hΦc : ContinuousOn Φ D :=
    (hφD.add (continuousOn_const.mul hψPc)).add (hh0.mono subset_union_left)
  have hPD : Prop16Area.G.CircAgree D (palmMixedField γ D (realSet (Icc c d)) X x ω)
      (Xf ω₀ + ofFun fun z => φ z + (γ / 2) * ψP z) := by
    intro n k z hz hsub
    have hc := CircleCont.dyadicRoundC_mem_Hbar hz n
    simp only [palmMixedField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hXD n k z hz hsub, Pi.add_apply,
      mixedGreenSample_eq_ofFun_palmPsi hgeo hxcd hc (radius_pos k) hsub]
    simp only [ofFun]
    rw [integral_add (Prop16Area.G.integrable_fc_of_continuousOn hc (radius_pos k) (hφD.mono hsub))
      ((Prop16Area.G.integrable_fc_of_continuousOn hc (radius_pos k) (hψPc.mono hsub)).const_mul
        (γ / 2)), integral_const_mul]
    ring
  have hxD := circAgree_ofFun_add_open (hφD.add (continuousOn_const.mul hψPc))
    (hh0.mono subset_union_left) hPD
  -- a measurable version of the profile
  classical
  set Φ' : ℂ → ℝ := D.piecewise Φ 0 with hΦ'def
  have hΦ'm : Measurable Φ' := hΦc.measurable_piecewise continuousOn_const hDo.measurableSet
  have hΦΦ' : EqOn Φ' Φ D := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  have hΦ'c : ContinuousOn Φ' D := hΦc.congr hΦΦ'
  set x' := ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X x ω with hx'def
  have hx'D : Prop16Area.G.CircAgree D x' (Xf ω₀ + ofFun Φ') := by
    intro n k z hz hsub
    rw [hxD n k z hz hsub]
    simp only [Pi.add_apply, ofFun]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [G1Side.ae_fc_mem_closedBall (CircleCont.dyadicRoundC_mem_Hbar hz n)
      (radius_pos k).le, RegClosure.fc_ae_mem_Hbar _ _] with u h1 h2
    exact (hΦΦ' (hsub ⟨h1, h2⟩)).symm
  -- the translate by `x`
  have hy' : ∀ (n k : ℕ) (z : ℂ), z ∈ Hbar →
      Xt ω₀ (foldedCircle (dyadicRoundC n z) (radius k)) =
        G ω₀ (dyadicRoundC n z + (x : ℂ), radius k) := fun n k z hz =>
    hrawω n k (⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋) (CircleCont.dyadicRoundC_mem_Hbar hz n)
  have hT : Prop16Area.G.CircAgree (zoomDomain D x) (translate x' (x : ℂ))
      (Xt ω₀ + ofFun fun u => Φ' (u + (x : ℂ))) :=
    circAgree_translate hDo hreg hΦ'c hΦ'm hx'D x hy'
  have hgc : ContinuousOn (fun u => Φ' (u + (x : ℂ))) (zoomDomain D x) :=
    hΦ'c.comp (continuous_id.add continuous_const).continuousOn fun u hu => hu
  have hTC := circAgree_addConst hgc hT (C / γ)
  -- the coordinate-change identity for the zoomed field
  have hmain := hgood (zoomField γ C x' x) (zoomDomain D x) _ U (zoomDomain D x) hZo
    (hgc.add continuousOn_const) hTC hUo hUH hZo hZH subset_rfl hUZ
  have hv := hvague (zoomField γ C x' x) (zoomDomain D x) _ U hZo
    (hgc.add continuousOn_const) hTC hUo hUH hUZ
  obtain ⟨Ft, hFt⟩ := hregt
  have hlit := isVagueLimitOn_addConst_coordChange hFt hψxm hψd hpush hZo hgc hT hUo hUH hUZ
    (fun z hz => H_subset_Hbar (hZH (hUZ hz))) (Qc γ) (C / γ) hv
  have heq : qAreaMeasureOn γ (zoomFieldLit γ C x' x ψx) U =
      qAreaMeasureOn γ (coordChange (zoomField γ C x' x) ψx (Qc γ)) U := by
    rw [LocalRule.qAreaMeasureOn_eq hUo hv]
    exact LocalRule.qAreaMeasureOn_eq hUo hlit
  rw [heq]
  exact hmain

end Prop16Lit

end QuantumZipper
