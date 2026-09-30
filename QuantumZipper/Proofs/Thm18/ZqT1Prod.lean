import QuantumZipper.Proofs.Thm18.G3ZqS2Top

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (1): the coupled facts of the unscaled wedge along the unscaled path, path first

For the unscaled wedge `w = wedgeU ω'` (scale `b(ω')`) and an independent Brownian path `a`, the
facts that relate `w` along `Ψ_a` to the canonical wedge along the scaled path `S_b a` (core and
side area of the canonical wedge along `S_b a`, continuum limits of `w` along the pushed circles of
`Ψ_a`) hold a.s. on the PRODUCT space `P' ⊗ W` (`W` the path law): the setting-level results
apply to the randomly scaled Brownian motion `rsBM c` (G3ZqSBm), whose joint law with the field
coordinate is again `P' ⊗ W` (`map_rs_eq`), so every product-a.s. property transfers to the scaled
path (`ae_rs_transfer`, no measurability needed). Product-a.s. statements then hold for a.e.
path, a.s. in the field (`ae_path_first`, `Measure.ae_ae_of_ae_prod` after the swap).

Headline: `ae_unsc_facts`. Sheffield, arXiv:1012.4797, p. 70 (the curve is independent of the
field; SLE scale invariance). Own bookkeeping (AGENT_GUIDE cost rule), following G3ZqS.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open G1Zm G3Zq G3Zr G3Z2b2 G1SSR2 G3ZqS

variable {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}

theorem isProb_W (hB : IsBrownianReal B P) : IsProbabilityMeasure (P.map (pathOf B)) :=
  (Measure.isProbabilityMeasure_map_iff (IsBrownianReal.aemeasurable_pathOf hB)).2 inferInstance

/-- **Product-a.s. gives path first.** -/
theorem ae_path_first {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
    {p : Ω' → (ℝ≥0 → ℝ) → Prop} (h : ∀ᵐ z ∂(P'.prod W), p z.1 z.2) :
    ∀ᵐ a ∂W, ∀ᵐ ω' ∂P', p ω' a := by
  have h2 : ∀ᵐ z ∂((W.prod P').map Prod.swap), p z.1 z.2 := by
    rw [Measure.prod_swap]; exact h
  have h3 : ∀ᵐ z ∂(W.prod P'), p z.2 z.1 := ae_of_ae_map measurable_swap.aemeasurable h2
  exact Measure.ae_ae_of_ae_prod h3

/-- Lift an a.s. statement of the first factor to the product. -/
theorem ae_fst_lift {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W] {p : Ω' → Prop}
    (h : ∀ᵐ ω' ∂P', p ω') : ∀ᵐ z ∂(P'.prod W), p z.1 := by
  have e : (P'.prod W).map Prod.fst = P' := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact ae_of_ae_map measurable_fst.aemeasurable (by rw [e]; exact h)

/-- The path law of a Brownian motion is the projective limit of the Brownian family. -/
theorem isProjLim_pathLaw {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {D : ℝ≥0 → Ω₀ → ℝ} (hD : IsBrownianReal D P₀) :
    IsProjectiveLimit (P₀.map (pathOf D)) BrownianReal.projectiveFamily := by
  intro I
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable
    (IsBrownianReal.aemeasurable_pathOf hD)]
  exact (hD.hasLaw I).map_eq

/-- **The joint law of the field coordinate and the randomly scaled path.** -/
theorem map_rs_eq (hB : IsBrownianReal B P) {c : Ω' → ℝ} (hc : Measurable c)
    (hc0 : ∀ ω', 0 < c ω') :
    (P'.prod (P.map (pathOf B))).map (fun z => (z.1, pathOf (rsBM c) z)) =
      P'.prod (P.map (pathOf B)) := by
  haveI := isProb_W hB
  have hI := indepFun_rsBM (P' := P') hB hc hc0 (fun ω' : Ω' => ω')
  have hpm := measurable_pathOf_rsBM (Ω' := Ω') hc
  have hlaw : (P'.prod (P.map (pathOf B))).map (pathOf (rsBM c)) = P.map (pathOf B) :=
    (isProjLim_pathLaw (isBrownianReal_rsBM hB hc hc0)).unique (isProjLim_pathLaw hB)
  rw [indepFun_iff_map_prod_eq_prod_map_map hpm.aemeasurable measurable_fst.aemeasurable] at hI
  have e : (fun z : Ω' × (ℝ≥0 → ℝ) => (z.1, pathOf (rsBM c) z)) =
      Prod.swap ∘ (fun z => (pathOf (rsBM c) z, z.1)) := rfl
  rw [e, ← Measure.map_map measurable_swap (hpm.prodMk measurable_fst), hI, hlaw,
    Measure.map_fst_prod, measure_univ, one_smul, Measure.prod_swap]

/-- **Transfer of product-a.s. properties to the randomly scaled path.** -/
theorem ae_rs_transfer (hB : IsBrownianReal B P) {c : Ω' → ℝ} (hc : Measurable c)
    (hc0 : ∀ ω', 0 < c ω') {p : Ω' × (ℝ≥0 → ℝ) → Prop}
    (h : ∀ᵐ z ∂(P'.prod (P.map (pathOf B))), p z) :
    ∀ᵐ z ∂(P'.prod (P.map (pathOf B))), p (z.1, pathOf (rsBM c) z) := by
  have hm : Measurable fun z : Ω' × (ℝ≥0 → ℝ) => (z.1, pathOf (rsBM c) z) :=
    measurable_fst.prodMk (measurable_pathOf_rsBM hc)
  have hmp : MeasurePreserving (fun z : Ω' × (ℝ≥0 → ℝ) => (z.1, pathOf (rsBM c) z))
      (P'.prod (P.map (pathOf B))) (P'.prod (P.map (pathOf B))) := ⟨hm, map_rs_eq hB hc hc0⟩
  exact hmp.quasiMeasurePreserving.ae h

/-- The randomly scaled path at a continuous path. -/
theorem pathOf_rsBM_of_cont {c : Ω' → ℝ} (z : Ω' × (ℝ≥0 → ℝ)) (hz : Continuous z.2) :
    pathOf (rsBM c) z = scalePath (c z.1) z.2 := by
  have e : G1Pkg.pathReg z.2 = z.2 := G1Pkg.pathReg_spec.2.2 _ hz
  funext t; simp only [pathOf, rsBM, e]

variable {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **The coupled facts, path first.** For a.e. path, a.s. in the field: if the path is good, the
unscaled wedge is good with positive scale, the canonical wedge along the path scaled by that
scale has the core and the side area at every normalized uniformizer, and the unscaled wedge has
continuum limits along the circles pushed by `Ψ_a`. -/
theorem ae_unsc_facts {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') (hB : IsBrownianReal B P) :
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P', G3ZqGoodPathF γ a →
      IsLQGGood γ (wedgeU γ X A ω') ∧ 0 < scaleParam γ (wedgeU γ X A ω') ∧
      ∀ left : Bool,
        (∀ φ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2)
            (scalePath (scaleParam γ (wedgeU γ X A ω')) a)) left) φ →
          G1.ChoiceRegularCore γ (canonical γ (wedgeU γ X A ω'))
            (invFunOn φ (sideDom (pathTrace (γ ^ 2)
              (scalePath (scaleParam γ (wedgeU γ X A ω')) a)) left)) ∧
          G1Z2MeasGood γ left (coordChange (canonical γ (wedgeU γ X A ω'))
            (invFunOn φ (sideDom (pathTrace (γ ^ 2)
              (scalePath (scaleParam γ (wedgeU γ X A ω')) a)) left)) (Qc γ))) ∧
        ∀ (d : ℂ) (r : ℝ), 0 < r →
          F1.ContData (wedgeU γ X A ω') ((foldedCircle d r).map (Ψ left a)) := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have := isProb_W hB
  set W := P.map (pathOf B) with hWdef
  obtain ⟨c, hc, hc0, hce⟩ := exists_meas_scale hγ hγ2 hX hA hXA
  have hZ2 : G1Z2SideGoodStmt := g1Z2SideGoodStmt_of_area
    (g1Z2SideAreaStmt_of_sel (g1Z2SideAreaSelStmt_of_top G1Top.g1Z2SideTopSelStmt_holds))
  have hS := thm18Setting_rs (P := P) hγ hγ2 hX hA hXA hB hc hc0
  have hIn := thm18Inputs_of_setting hS
  -- (H1) core and side area along the randomly scaled path
  have hprod : ∀ left : Bool, ∀ᵐ z ∂(P'.prod W),
      IsSimpleChord (pathTrace (γ ^ 2) (pathOf (rsBM c) z)) →
      ∀ φ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) (pathOf (rsBM c) z)) left) φ →
        G1.ChoiceRegularCore γ (wedgeRep γ X A z.1)
            (invFunOn φ (sideDom (pathTrace (γ ^ 2) (pathOf (rsBM c) z)) left)) ∧
          G1Z2MeasGood γ left (coordChange (wedgeRep γ X A z.1)
            (invFunOn φ (sideDom (pathTrace (γ ^ 2) (pathOf (rsBM c) z)) left)) (Qc γ)) := by
    intro left
    have hR : G1RegExSide γ (P'.prod W) (rsBM c)
        (fun z : Ω' × (ℝ≥0 → ℝ) => wedgeRep γ X A z.1) left := by
      have := g1RegExStmt_of_rest g1RegRepRestStmt_holds γ _ _ _ hS hIn
      cases left
      · exact this.2
      · exact this.1
    filter_upwards [hR, hZ2 γ _ _ _ hS hIn left] with z hRz hZz hsz φ hφ
    obtain ⟨φ₀, hφ₀, hcore₀⟩ := hRz
    exact ⟨G1.choiceRegularCore_invFunOn_of_normalized hsz left hφ₀ hφ hcore₀, hZz φ hφ⟩
  -- (H2) the continuum condition along the randomly scaled path
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hαQ, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, rfl⟩
  have hm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  set E : Set G1PathData := {p | ∀ l : Bool, UCond (E1.fromC p.2.1) (Ψ l p.1)} with hEdef
  have hE : MeasurableSet E :=
    measurableSet_setOfPred.2 (Measurable.forall fun l => measurable_ucond hsel l)
  have hfromC : ∀ y : FieldSample, avgReg (E1.fromC (WedgeMeas.dataFull H y).1) = avgReg y :=
    fun y => CoordsFull.avgReg_congr_full (E1.coordsFull_fromC y)
  set g := hm.mk _ with hg
  have hae : ∀ᵐ a ∂W, ∀ᵐ ω' ∂P', (a, g ω') ∈ E := by
    filter_upwards [g1SidePushUCRepStmt_holds γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hsel] with a ha
    filter_upwards [ha true, ha false, hm.ae_eq_mk] with ω' ht hf hgω
    intro l
    show UCond (E1.fromC (g ω').1) (Ψ l a)
    rw [hg, ← hgω, ucond_congr (hfromC _)]
    cases l
    · exact hf
    · exact ht
  have hSm : MeasurableSet {q : (ℝ≥0 → ℝ) × Ω' | (q.1, g q.2) ∈ E} :=
    (measurable_fst.prodMk (hm.measurable_mk.comp measurable_snd)) hE
  have hWP : ∀ᵐ q ∂(W.prod P'), (q.1, g q.2) ∈ E := (Measure.ae_prod_iff_ae_ae hSm).2 hae
  have hPW : ∀ᵐ z ∂(P'.prod W), (z.2, g z.1) ∈ E := by
    rw [← Measure.prod_swap]
    exact (ae_map_iff measurable_swap.aemeasurable
      ((measurable_snd.prodMk (hm.measurable_mk.comp measurable_fst)) hE)).2 hWP
  have hU0 : ∀ᵐ z ∂(P'.prod W), ∀ l : Bool, UCond (wedgeRep γ X A z.1) (Ψ l z.2) := by
    filter_upwards [hPW, ae_fst_lift (W := W) hm.ae_eq_mk] with z hz hgz l
    have h1 : UCond (E1.fromC (WedgeMeas.dataFull H (wedgeRep γ X A z.1)).1) (Ψ l z.2) := by
      rw [hgz]; exact hz l
    rwa [ucond_congr (hfromC _)] at h1
  have hU := ae_rs_transfer hB hc hc0 hU0
  -- (H3) the Schwarz-reflection extension along the randomly scaled path
  have hpe0 := G1RC.g1PsiExtStmt_holds γ hγ hγ2 (P'.prod W) (rsBM c)
    (isBrownianReal_rsBM hB hc hc0) P' X A hX hA hXA Ψ hsel
  have hpe : ∀ᵐ z ∂(P'.prod W), ∀ left : Bool, G1RC.PsiExt (Ψ left (pathOf (rsBM c) z)) :=
    ae_of_ae_map (measurable_pathOf_rsBM hc).aemeasurable hpe0
  -- assembly on the product
  have hall : ∀ᵐ z ∂(P'.prod W), G3ZqGoodPathF γ z.2 →
      IsLQGGood γ (wedgeU γ X A z.1) ∧ 0 < scaleParam γ (wedgeU γ X A z.1) ∧
      ∀ left : Bool,
        (∀ φ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2)
            (scalePath (scaleParam γ (wedgeU γ X A z.1)) z.2)) left) φ →
          G1.ChoiceRegularCore γ (canonical γ (wedgeU γ X A z.1))
            (invFunOn φ (sideDom (pathTrace (γ ^ 2)
              (scalePath (scaleParam γ (wedgeU γ X A z.1)) z.2)) left)) ∧
          G1Z2MeasGood γ left (coordChange (canonical γ (wedgeU γ X A z.1))
            (invFunOn φ (sideDom (pathTrace (γ ^ 2)
              (scalePath (scaleParam γ (wedgeU γ X A z.1)) z.2)) left)) (Qc γ))) ∧
        ∀ (d : ℂ) (r : ℝ), 0 < r →
          F1.ContData (wedgeU γ X A z.1) ((foldedCircle d r).map (Ψ left z.2)) := by
    filter_upwards [hprod true, hprod false, hU, hpe, ae_fst_lift (W := W) hce,
      ae_fst_lift (W := W)
        (LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA)]
      with z k1 k2 hu hpz he hgd hgood
    obtain ⟨hac, hs', hWd, hW0, hex⟩ := hgood
    have hb : 0 < scaleParam γ (wedgeU γ X A z.1) := he ▸ hc0 z.1
    have hrs : pathOf (rsBM c) z = scalePath (scaleParam γ (wedgeU γ X A z.1)) z.2 := by
      rw [pathOf_rsBM_of_cont z hac, he]
    have hsb : IsSimpleChord (pathTrace (γ ^ 2)
        (scalePath (scaleParam γ (wedgeU γ X A z.1)) z.2)) :=
      isSimpleChord_scalePath hb _ hWd hW0 hex hs'
    rw [hrs] at k1 k2 hu hpz
    refine ⟨hgd, hb, fun left => ⟨?_, ?_⟩⟩
    · cases left
      · exact k2 hsb
      · exact k1 hsb
    · exact contData_unscaled_pt hsel hgd hb hac hs' hWd hW0 hex left (hpz left) (hu left)
  exact ae_path_first (p := fun ω' a => G3ZqGoodPathF γ a →
      IsLQGGood γ (wedgeU γ X A ω') ∧ 0 < scaleParam γ (wedgeU γ X A ω') ∧
      ∀ left : Bool,
        (∀ φ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2)
            (scalePath (scaleParam γ (wedgeU γ X A ω')) a)) left) φ →
          G1.ChoiceRegularCore γ (canonical γ (wedgeU γ X A ω'))
            (invFunOn φ (sideDom (pathTrace (γ ^ 2)
              (scalePath (scaleParam γ (wedgeU γ X A ω')) a)) left)) ∧
          G1Z2MeasGood γ left (coordChange (canonical γ (wedgeU γ X A ω'))
            (invFunOn φ (sideDom (pathTrace (γ ^ 2)
              (scalePath (scaleParam γ (wedgeU γ X A ω')) a)) left)) (Qc γ))) ∧
        ∀ (d : ℂ) (r : ℝ), 0 < r →
          F1.ContData (wedgeU γ X A ω') ((foldedCircle d r).map (Ψ left a))) hall

end ZqT
end Thm18Asm
end QuantumZipper
