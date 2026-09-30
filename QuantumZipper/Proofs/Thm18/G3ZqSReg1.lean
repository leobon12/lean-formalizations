import QuantumZipper.Proofs.Thm18.G3ZqSBm
import QuantumZipper.Proofs.Thm18.G3ZqWireU

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3ZqS (2): the setting of Theorem 1.8 with the path scaled by the wedge's own scale

For the wedge representative `wedgeRep ω' = canonical (wedgeU ω')` with scale
`b(ω') = scaleParam γ (wedgeU ω')` and an independent Brownian motion `B`, the pair
`(wedgeRep ω', S_{b(ω')}(path of B))` on `P' ⊗ W` is a Theorem 1.8 setting (`thm18Setting_rs`):
the randomly scaled path is Brownian and independent of the wedge (G3ZqSBm), and the lifted
wedge is a quantum wedge. Hence every setting-level a.s. regularity result holds a.s. in `ω'`,
a.s. in the Brownian sample, along the scaled path; here: Z-REG's area-only window regularity
`G1FacRegA` at every side point (`ae_g1FacRegA_scaled`), clause (i) of `G3ZqResclFieldReg`.

Sheffield, arXiv:1012.4797, p. 70 (the curve is independent of the field; SLE scale invariance).
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqS

open G1Zm G3Zq Factorization

variable {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}

/-- **The wedge scale is a.e. a measurable positive function.** -/
theorem exists_meas_scale {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P') (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∃ c : Ω' → ℝ, Measurable c ∧ (∀ ω', 0 < c ω') ∧
      ∀ᵐ ω' ∂P', c ω' = scaleParam γ (wedgeU γ X A ω') := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hcu : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P' :=
    WedgeMeas.aemeasurable_coords_wedgeField hX.measurable_coord hA
  have hpm : AEMeasurable (fun ω' => scaleProxy γ (reconstruct (coords (wedgeU γ X A ω')))) P' :=
    ((measurable_scaleProxy γ).comp Factorization.measurable_reconstruct).comp_aemeasurable hcu
  set c₀ := hpm.mk _ with hc₀
  set c : Ω' → ℝ := fun ω' => if 0 < c₀ ω' then c₀ ω' else 1 with hc
  have hcm : Measurable c :=
    Measurable.ite (measurableSet_lt measurable_const hpm.measurable_mk) hpm.measurable_mk
      measurable_const
  refine ⟨c, hcm, fun ω' => ?_, ?_⟩
  · simp only [hc]; split_ifs with h
    · exact h
    · exact one_pos
  · filter_upwards [hpm.ae_eq_mk, G1RC.ae_scale_pos hγ hγ2 hX hA hXA,
      LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA]
      with ω' h1 hb hg
    have e : scaleProxy γ (reconstruct (coords (wedgeU γ X A ω'))) =
        scaleParam γ (wedgeU γ X A ω') := by
      rw [scaleProxy_recon]; exact scaleProxy_eq_scaleParam_of_good hg
    have hb' : 0 < c₀ ω' := by
      rw [hc₀, ← h1, e]; exact hb
    simp only [hc, if_pos hb']
    rw [hc₀, ← h1, e]

/-- **The lifted wedge on the product space is a quantum wedge.** -/
theorem isQuantumWedge_lift {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P') (hXA : IndepFun X (fun ω t => A t ω) P')
    {E : Type} [MeasurableSpace E] (W : Measure E) [IsProbabilityMeasure W] :
    IsQuantumWedge γ (γ - 2 / γ) (fun z : Ω' × E => wedgeRep γ X A z.1) (P'.prod W) := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hαQ, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, rfl⟩
  have hm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  refine ⟨hαQ, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, ?_⟩
  have hfst : (P'.prod W).map Prod.fst = P' := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hm' : AEMeasurable (fun ω' => WedgeMeas.dataFull H (wedgeRep γ X A ω'))
      ((P'.prod W).map Prod.fst) := by rw [hfst]; exact hm
  show (P'.prod W).map (fun z => WedgeMeas.dataFull H (wedgeRep γ X A z.1)) =
    P'.map (fun ω' => WedgeMeas.dataFull H (wedgeRep γ X A ω'))
  conv_rhs => rw [← hfst]
  rw [AEMeasurable.map_map_of_aemeasurable hm' measurable_fst.aemeasurable]
  rfl

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The Theorem 1.8 setting with the randomly scaled path.** -/
theorem thm18Setting_rs {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P') (hXA : IndepFun X (fun ω t => A t ω) P')
    (hB : IsBrownianReal B P) {c : Ω' → ℝ} (hc : Measurable c) (hc0 : ∀ ω', 0 < c ω') :
    Thm18Setting γ (P'.prod (P.map (pathOf B))) (rsBM c)
      (fun z : Ω' × (ℝ≥0 → ℝ) => wedgeRep γ X A z.1) := by
  have hW : IsProbabilityMeasure (P.map (pathOf B)) :=
    (Measure.isProbabilityMeasure_map_iff (IsBrownianReal.aemeasurable_pathOf hB)).2
      inferInstance
  exact ⟨hγ, hγ2, isBrownianReal_rsBM hB hc hc0, isQuantumWedge_lift hγ hγ2 hX hA hXA _,
    indepFun_rsBM hB hc hc0 _⟩

/-- **Transfer from the product setting to the coupled scaled path.** A property that holds a.s.
in the product setting with the randomly scaled path holds a.s. in `ω'`, a.s. in the Brownian
sample, along the path scaled by `c(ω')`. -/
theorem ae_ae_scaled_of_prod (hB : IsBrownianReal B P) {c : Ω' → ℝ}
    {p : Ω' → (ℝ≥0 → ℝ) → Prop}
    (h : ∀ᵐ z ∂(P'.prod (P.map (pathOf B))), p z.1 (pathOf (rsBM c) z)) :
    ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P, p ω' (scalePath (c ω') (pathOf B ω)) := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with ω' hω'
  have h2 := ae_of_ae_map (IsBrownianReal.aemeasurable_pathOf hB) hω'
  filter_upwards [h2, hB.cont] with ω hω hcont
  have e : G1Pkg.pathReg (pathOf B ω) = pathOf B ω := G1Pkg.pathReg_spec.2.2 _ hcont
  have e2 : pathOf (rsBM c) (ω', pathOf B ω) = scalePath (c ω') (pathOf B ω) := by
    funext t; simp only [pathOf, rsBM, e]
  rw [← e2]; exact hω

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **Clause (i): the area-only window regularity of the canonical field along the scaled path,
a.s. at every side point.** -/
theorem ae_g1FacRegA_scaled {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') (hB : IsBrownianReal B P) (left : Bool) (L : ℝ) :
    ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P, ∀ x ∈ g1SideHalf left,
      G3Zr.G1FacRegA γ L Ψ left (canonical γ (wedgeU γ X A ω'))
        (scalePath (scaleParam γ (wedgeU γ X A ω')) (pathOf B ω)) x := by
  obtain ⟨c, hc, hc0, hce⟩ := exists_meas_scale hγ hγ2 hX hA hXA
  have hZ2 : G1Z2SideGoodStmt := g1Z2SideGoodStmt_of_area
    (g1Z2SideAreaStmt_of_sel (g1Z2SideAreaSelStmt_of_top G1Top.g1Z2SideTopSelStmt_holds))
  have hS := thm18Setting_rs hγ hγ2 hX hA hXA hB hc hc0
  have hW : IsProbabilityMeasure (P.map (pathOf B)) :=
    (Measure.isProbabilityMeasure_map_iff (IsBrownianReal.aemeasurable_pathOf hB)).2
      inferInstance
  have h := G3Zr.ae_g1FacRegA hZ2 γ _ _ _ hS (thm18Inputs_of_setting hS) hsel left L
  filter_upwards [ae_ae_scaled_of_prod hB (p := fun ω' a => ∀ x ∈ g1SideHalf left,
    G3Zr.G1FacRegA γ L Ψ left (wedgeRep γ X A ω') a x) h, hce] with ω' hω' he
  rw [← he]
  exact hω'

end G3ZqS
end Thm18Asm
end QuantumZipper
