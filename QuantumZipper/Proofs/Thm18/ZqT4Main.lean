import QuantumZipper.Proofs.Thm18.ZqT3Wedge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (4): the typical-point goodness node with the wedge clause discharged

* `ae_wedge_typQ`: for a.e. path (good in the sense of `G3ZqGoodPathF`), a.s. in the field, the
  unscaled wedge satisfies the area-only map goodness at every point, both sides (ZqT3).
* `G3ZqTMapTypFStmt`: `G3ZqLMapTypQAEStmt` with the good-path hypothesis `G3ZqGoodPathF` (the one
  its only consumer, `G3ZqPathSmallUStmt`, provides). The Brownian a.s. trace-existence clauses
  of `G3ZqGoodPathF` are used to relate the unscaled path to the scaled one (`exists_dilUnif`,
  `isSimpleChord_scalePath`); they are not implied by `G3ZqGoodPath` pathwise, and a property of
  the path that is only Brownian-a.s. (for `P`) need not hold for `P.map (pathOf B)`-a.e. path
  (the set of continuous paths is not measurable). `g3ZqTMapTypFStmt_of_typQAE`: the old node
  implies the new one.
* `g3ZqTMapTypFStmt_of`: the new node from the two remaining clauses, `G3ZqTSchemeStmt` (Palm
  points of the scheme `B`/`C` laws) and `G3ZqTVStmt` (`V + logSing`), each strictly smaller.
* Headline `theorem1_8PaperMO_of_typF` (copy of `G3ZqL.theorem1_8PaperMO_of_typQAE`).

Sheffield, arXiv:1012.4797, pp. 65–66, 70–72. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open G1Zm G3Zq G3Zr G3Z2b2 G1SSR2 G3ZqS G1Side SWCore G3ZqL R18.G3ZqL R18

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **The unscaled wedge is area-only good for the map zooms at every point, for a.e. path.** -/
theorem ae_wedge_typQ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ a ∂(P.map (pathOf B)), G3ZqGoodPathF γ a →
      ∀ᵐ ω ∂P', ∀ side : Bool, ∀ x : ℝ, g3zMapGdQ γ Ψ side a (R18.g3plUW γ X A ω) x := by
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hWS : E6.WedgeWindowStmt := wedgeWindowStmt_of_splitR fun κ hκ hκ4 => by
    have h2 : Real.sqrt κ < 2 := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
    exact ⟨E6.swC (Real.sqrt κ), E6.swC' (Real.sqrt κ), E6.tendsto_swC _, E6.tendsto_swC' _,
      swWindowSplitStmtR_holds (Real.sqrt_pos.2 hκ) h2⟩
  have hsq : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  obtain ⟨cw, cw', hcw, hcw', hWin⟩ := hWS (γ ^ 2) (by positivity) (by nlinarith)
  have hA' : IsWedgeProcess (Real.sqrt (γ ^ 2) - 2 / Real.sqrt (γ ^ 2)) (Qc (Real.sqrt (γ ^ 2)))
      A P' := by rw [hsq]; exact hA
  have hWin' := hWin P' X A hX hA' hXA
  simp only [hsq] at hWin'
  filter_upwards [ae_unsc_facts hγ hγ2 hsel hX hA hXA hB] with a hfa hgf
  have hSF : ∀ side, SideMapFacts (Ψ side a) := fun side =>
    sideMapFacts_of_sel hsel hgf.1 hgf.2.1 side
  filter_upwards [hfa, ae_inputs hX hG (hSF true), ae_inputs hX hG (hSF false), hG.ae_good,
    WedgeCan.ae_raw_dyadic hG, WedgeCan4.ae_continuous_wedgeProcess hA, hWin',
    R18.g3pl4_ae_isAreaGood_Z hγ hγ2 hX hA hXA] with ω hf hinT hinF hgood hraw hAc hwin hAG
  obtain ⟨hWg, hb, hcs⟩ := hf hgf
  intro side x
  exact wedge_gdQ_pt hγ hsel hgf hgood hraw hAc hWg hcw hcw' hwin hAG hb hcs
    (fun left => by cases left; exact hinF; exact hinT) side x

/-- **Node: area-only typical-point goodness for a.e. good Brownian path** (the good-path
condition of the consumer, `G3ZqGoodPathF`). -/
def G3ZqTMapTypFStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ᵐ a ∂(P.map (pathOf B)), G3ZqGoodPathF γ a →
    G3ZqLSchemeTypQ γ Ψ a ∧
    (∀ᵐ ω ∂P', G3ZqLTypQ γ Ψ a (R18.g3plUW γ X A ω)) ∧
    (∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
      (V : Ω'' → FieldSample), IsFreeGFFModConstH V P'' →
      (∀ᵐ ω ∂P'', V ω (foldedCircle 0 1) = 0) →
      ∀ᵐ ω ∂P'', G3ZqLTypQ γ Ψ a (V ω + F2.logSingField (γ ^ 2)))

/-- **Node (scheme clause): area-only goodness at the Palm points of the scheme `B`/`C` laws, for
a.e. good path.** -/
def G3ZqTSchemeStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ᵐ a ∂(P.map (pathOf B)), G3ZqGoodPathF γ a → G3ZqLSchemeTypQ γ Ψ a

/-- **Node (`V + logSing` clause): area-only goodness of the log-singular free field at typical
points, for a.e. good path.** -/
def G3ZqTVStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ᵐ a ∂(P.map (pathOf B)), G3ZqGoodPathF γ a →
    ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
      (V : Ω'' → FieldSample), IsFreeGFFModConstH V P'' →
      (∀ᵐ ω ∂P'', V ω (foldedCircle 0 1) = 0) →
      ∀ᵐ ω ∂P'', G3ZqLTypQ γ Ψ a (V ω + F2.logSingField (γ ^ 2))

/-- **The node from its two remaining clauses** (the wedge clause is `ae_wedge_typQ`). -/
theorem g3ZqTMapTypFStmt_of (hS : G3ZqTSchemeStmt) (hV : G3ZqTVStmt) : G3ZqTMapTypFStmt := by
  intro γ hγ hγ2 Ψ hsel Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA
  filter_upwards [hS γ hγ hγ2 Ψ hsel P B hB, hV γ hγ hγ2 Ψ hsel P B hB,
    ae_wedge_typQ hγ hγ2 hsel hB hX hA hXA] with a h1 h2 h3 ha
  refine ⟨h1 ha, ?_, fun P'' _ V hV' hV0 => h2 ha P'' V hV' hV0⟩
  filter_upwards [h3 ha] with ω hω
  exact ae_of_all _ fun x => ⟨hω true x, hω false _⟩

theorem g3ZqPathSmallUStmt_of_typF (hL : G3ZqLZoomLocAEMapStmt) (hGd : G3ZqTMapTypFStmt) :
    G3ZqPathSmallUStmt := by
  intro γ Ω _ P _ B Y hS hIn Ψ hsel Ω' _ P' _ X A hX' hA hXA s hs t ht c hc ε hε
  have hγ := hS.1
  have hγ2 := hS.2.1
  obtain ⟨Ω'', _, P'', Y'', -, hP'', hW, -, -, -⟩ :=
    NonVacuity.exists_wedge_indep_BM_uncond_prob_uncond hγ hγ2 (S5.FieldLaw.Raw.gamma_lt_Qc' hγ hγ2)
  have := hP''
  have hcEq := plain_limit_eq hγ hγ2 P'' Y'' hW hs ht hc
  have hc0 : 0 ≤ c := by
    rw [hcEq]; exact mul_nonneg measureReal_nonneg measureReal_nonneg
  obtain ⟨U₀, hU₀, H⟩ := R18.G3ZqL.g3UnscaledTransferZ_ballAE hγ hγ2 hs ht hε
  refine ⟨U₀, hU₀, fun U hU hUU => ?_⟩
  filter_upwards [hGd γ hγ hγ2 Ψ hsel P B hS.2.2.1 P' X A hX' hA hXA] with a hga ha
  obtain ⟨⟨gS1, gS2, gS3, gS4⟩, gW, gV⟩ := hga ha
  have hbody := g3FixMixBody_mapAE hL hγ hγ2 hsel ha.good P'' Y'' hW
  have HL := H U hU hUU _ _ (measurable_g3zMapZ hsel true a)
    (fun C y y' x h => g3zMapZ_avgReg_congr γ true a C y y' x h)
    (measurable_g3zMapZ hsel false a)
    (fun C y y' x h => g3zMapZ_avgReg_congr γ false a C y y' x h) _ _
    (g3zMapZ_ballLocQ hγ hsel ha.good true) (g3zMapZ_ballLocQ hγ hsel ha.good false)
    gS1 gS2 gS3 gS4 (g2WedgeLaw P'' Y'') (g2WedgeLaw P'' Y'')
    inferInstance inferInstance hbody P' X A hX' hA hXA gW
    (fun V hV hV0 => gV P' V hV hV0)
  have heq : ∀ L : ℝ, ∫⁻ ω', g3PhiM2 γ L Ψ U s t (wedgeU γ X A ω', a) ∂P' =
      ∫⁻ ω', R18.g3plPhiZ (g3zMapZ γ Ψ true a) (g3zMapZ γ Ψ false a) γ L U s t
        (R18.g3plUW γ X A ω') ∂P' := fun L => by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_wedgeU_good_pos hγ hγ2 hX' hA hXA] with ω' h
    exact g3PhiM2_eq_plPhiZ h.1 h.2 a
  filter_upwards [HL] with L hL'
  have hJ : ∫⁻ ω', g3PhiM2 γ L Ψ U s t (wedgeU γ X A ω', a) ∂P' ≤ ENNReal.ofReal U :=
    calc ∫⁻ ω', g3PhiM2 γ L Ψ U s t (wedgeU γ X A ω', a) ∂P'
        ≤ ∫⁻ _ω', ENNReal.ofReal U ∂P' := lintegral_mono fun ω' => G3Zp.g3PhiM2_le _
      _ = ENNReal.ofReal U := by simp
  rw [heq L] at hJ ⊢
  exact abs_toReal_div_sub_le hU hc0 hε hJ (by rw [hcEq]; exact hL'.1) (by rw [hcEq]; exact hL'.2)

end ZqT
end Thm18Asm
end QuantumZipper
