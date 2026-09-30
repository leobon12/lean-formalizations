import QuantumZipper.Proofs.Thm18.G3ZqSReg1
import QuantumZipper.Proofs.Thm18.G3ZrDil2
import QuantumZipper.Proofs.Thm18.G1SSR2UC
import QuantumZipper.Proofs.Thm18.Thm18HeadlineV3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3ZqS (3): the dilation regularity along the scaled path (clause (ii))

* `map_scalePath_pathLaw`: the Brownian path law is invariant under `scalePath c`.
* `ae_swap_scale`: a MEASURABLE property of (path, field data) that holds for a.e. path, a.s. in
  the field (path first, as the representative results of G1/Z-REG are stated), holds a.s. in the
  field, a.s. in the Brownian sample, along the path scaled by any measurable positive `c(ω')`
  (Tonelli on the measurable set, then the scale invariance fibrewise).
* `ae_ucond_scaled`: the countable continuum condition `UCond` (measurable, `measurable_ucond`)
  along the scaled path; `ae_psiExt_scaled`: the Schwarz-reflection extension along the scaled
  path (path-only, Brownian scaling at fixed scale).
* `dilRegCore_pt`: the pointwise form of `G3Zr.ae_dilRegCore_rep`.
* **`ae_dilReg_scaled`**: clause (ii) of `G3ZqResclFieldReg`, `DilReg` at every point for the
  local maps of the scaled path, both sides.

Sheffield, arXiv:1012.4797, p. 70. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqS

open G1Zm G3Zq G3Zr G3Z2b2 G1SSR2

variable {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- **Scale invariance of the Brownian path law.** -/
theorem map_scalePath_pathLaw (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    (P.map (pathOf B)).map (scalePath c) = P.map (pathOf B) := by
  have hgm : AEMeasurable (pathOf B) P := IsBrownianReal.aemeasurable_pathOf hB
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_scalePath c).aemeasurable hgm]
  have e : scalePath c ∘ pathOf B = pathOf (G4TraceNull2.scaledBM c B) := by
    funext ω; exact (pathOf_scaledBM hc ω).symm
  rw [e]
  exact (F1.map_pathOf_eq_of_isBrownianReal hB (G4TraceNull2.isBrownianReal_scaledBM hB hc)).symm

/-- **Path-first measurable properties hold along the randomly scaled path.** -/
theorem ae_swap_scale (hB : IsBrownianReal B P) {D : Type} [MeasurableSpace D] {f : Ω' → D}
    (hf : AEMeasurable f P') {c : Ω' → ℝ} (hc0 : ∀ ω', 0 < c ω')
    {E : Set ((ℝ≥0 → ℝ) × D)} (hE : MeasurableSet E)
    (h : ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P', (a, f ω') ∈ E) :
    ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P, (scalePath (c ω') (pathOf B ω), f ω') ∈ E := by
  set W := P.map (pathOf B) with hW
  have hWp : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff (IsBrownianReal.aemeasurable_pathOf hB)).2
      inferInstance
  set ν := P'.map f with hν
  have h1 : ∀ᵐ a ∂W, ∀ᵐ d ∂ν, (a, d) ∈ E :=
    h.mono fun a ha => (ae_map_iff hf (measurable_prodMk_left hE)).2 ha
  have h2 : ∀ᵐ z ∂(W.prod ν), z ∈ E := (Measure.ae_prod_iff_ae_ae hE).2 h1
  have hEs : MeasurableSet {z : D × (ℝ≥0 → ℝ) | z.swap ∈ E} := measurable_swap hE
  have h3 : ∀ᵐ z ∂(ν.prod W), z.swap ∈ E := by
    rw [← Measure.prod_swap]
    exact (ae_map_iff measurable_swap.aemeasurable hEs).2 (h2.mono fun z hz => by
      simpa using hz)
  have h4 : ∀ᵐ d ∂ν, ∀ᵐ a ∂W, (a, d) ∈ E := (Measure.ae_prod_iff_ae_ae hEs).1 h3
  have h5 : ∀ᵐ ω' ∂P', ∀ᵐ a ∂W, (a, f ω') ∈ E := ae_of_ae_map hf h4
  filter_upwards [h5] with ω' hω'
  have hsec : MeasurableSet {a : ℝ≥0 → ℝ | (a, f ω') ∈ E} := measurable_prodMk_right hE
  have h6 : ∀ᵐ a ∂(W.map (scalePath (c ω'))), (a, f ω') ∈ E := by
    rw [map_scalePath_pathLaw hB (hc0 ω')]; exact hω'
  have h7 : ∀ᵐ a ∂W, (scalePath (c ω') a, f ω') ∈ E :=
    (ae_map_iff (measurable_scalePath _).aemeasurable hsec).1 h6
  exact ae_of_ae_map (IsBrownianReal.aemeasurable_pathOf hB) h7

variable {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **The continuum condition `UCond` along the scaled path.** -/
theorem ae_ucond_scaled {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') (hB : IsBrownianReal B P) {c : Ω' → ℝ}
    (hc0 : ∀ ω', 0 < c ω') :
    ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P, ∀ left : Bool,
      UCond (wedgeRep γ X A ω') (Ψ left (scalePath (c ω') (pathOf B ω))) := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
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
  have hae : ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
      (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ E := by
    filter_upwards [g1SidePushUCRepStmt_holds γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hsel] with a ha
    filter_upwards [ha true, ha false] with ω' ht hf
    intro l
    show UCond (E1.fromC (WedgeMeas.dataFull H (wedgeRep γ X A ω')).1) (Ψ l a)
    rw [ucond_congr (hfromC _)]
    cases l
    · exact hf
    · exact ht
  filter_upwards [ae_swap_scale hB hm hc0 hE hae] with ω' hω'
  filter_upwards [hω'] with ω h l
  have := h l
  rwa [ucond_congr (hfromC _)] at this

/-- **The Schwarz-reflection extension along the path scaled at a fixed scale.** -/
theorem ae_psiExt_scaled {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') (hB : IsBrownianReal B P) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂P, ∀ left : Bool, G1RC.PsiExt (Ψ left (scalePath c (pathOf B ω))) := by
  have hB' := G4TraceNull2.isBrownianReal_scaledBM hB hc
  have h := G1RC.g1PsiExtStmt_holds γ hγ hγ2 P _ hB' P' X A hX hA hXA Ψ hsel
  have h2 := ae_of_ae_map (IsBrownianReal.aemeasurable_pathOf hB') h
  filter_upwards [h2] with ω hω
  rw [← pathOf_scaledBM hc ω]
  exact hω

/-- **Pointwise `DilRegCore`** (the body of `G3Zr.ae_dilRegCore_rep`). -/
theorem dilRegCore_pt {γ : ℝ} (hsel : G1PsiSel γ Ψ) {y : FieldSample} (hg : IsLQGGood γ y)
    (hb : 0 < scaleParam γ y) {a : ℝ≥0 → ℝ} (hac : Continuous a)
    (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool) (hpe : G1RC.PsiExt (Ψ left a))
    (hu : UCond (canonical γ y) (Ψ left a)) (x : ℝ) (d : ℂ) (k : ℕ) :
    DilRegCore γ y (scaleParam γ y) x
      (g1zLocMap left (pathDrive (γ ^ 2) a) (x / scaleParam γ y)) (foldedCircle d (radius k)) := by
  obtain ⟨ψe, -, hψec, hψeH, heq, -⟩ := hpe
  have hΨm : Measurable (Ψ left a) := (hsel.1 left).comp (measurable_const.prodMk measurable_id)
  have hN := G1ZA1a.isNormalizedUniformizer_sideDom hs left
  obtain ⟨hm, hH⟩ := sideMap_facts hs left hN
  obtain ⟨F, hF⟩ := hg.1
  have hFr := hF.rescale' (Qc γ) hb
  have hcΨ : ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData (rescale y (Qc γ) (scaleParam γ y))
      ((foldedCircle d r).map (Ψ left a)) := fun d r hr =>
    G1SSR2.contData_of_ucond hFr hΨm hψec hψeH heq hu d hr
  have hcψ : ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData y
      ((foldedCircle d r).map fun w =>
        ((scaleParam γ y : ℝ) : ℂ) * g1zSideMap left (pathDrive (γ ^ 2) a) w) := by
    intro d r hr
    have h1 := contData_sideMap_of_Psi hsel hac hs left hcΨ d hr
    have h2 := contData_dilate_of_rescale ⟨F, hF⟩ (Qc γ) hb
      (ae_map_mem_Hbar hm ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw =>
        H_subset_Hbar (hH hw))) h1
    rw [Measure.map_map (measurable_const_mul _) hm] at h2
    exact h2
  exact dilRegCore_of_contData γ ⟨F, hF⟩ hb hm hH hcψ x
    (g1zBdryPre left (pathDrive (γ ^ 2) a) (x / scaleParam γ y)) d k

/-- **Clause (ii): `DilReg` at every point for the local maps of the scaled path.** -/
theorem ae_dilReg_scaled {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') (hB : IsBrownianReal B P)
    (hsc : ∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) :
    ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P, ∀ (left : Bool) (x : ℝ),
      DilReg γ (wedgeU γ X A ω') (scaleParam γ (wedgeU γ X A ω')) x
        (g1zLocMap left (pathDrive (γ ^ 2) (scalePath (scaleParam γ (wedgeU γ X A ω'))
          (pathOf B ω))) (x / scaleParam γ (wedgeU γ X A ω'))) := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  obtain ⟨c, hc, hc0, hce⟩ := exists_meas_scale hγ hγ2 hX hA hXA
  filter_upwards [ae_ucond_scaled hγ hγ2 hsel hX hA hXA hB hc0, hce,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA]
    with ω' hu he hg
  have hb : 0 < scaleParam γ (wedgeU γ X A ω') := he ▸ hc0 ω'
  filter_upwards [hu, ae_psiExt_scaled hγ hγ2 hsel hX hA hXA hB hb, ae_goodPathF hγ hγ2 hB hsc]
    with ω hu' hpe hgood left x
  obtain ⟨hac, hs', hWd, hW0, hex⟩ := hgood
  set b := scaleParam γ (wedgeU γ X A ω') with hbdef
  have hsb : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b (pathOf B ω))) :=
    isSimpleChord_scalePath hb _ hWd hW0 hex hs'
  have hcb : Continuous (scalePath b (pathOf B ω)) := continuous_scalePath hac
  have hu2 : UCond (canonical γ (wedgeU γ X A ω')) (Ψ left (scalePath b (pathOf B ω))) := by
    have := hu' left; rw [he] at this; exact this
  exact dilReg_g1zLocMap hsb left (G1ZA1a.isNormalizedUniformizer_sideDom hsb left)
    fun d k => dilRegCore_pt hsel hg hb hcb hsb left (hpe left) hu2 x d k

end G3ZqS
end Thm18Asm
end QuantumZipper
