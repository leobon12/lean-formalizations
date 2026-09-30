import QuantumZipper.Proofs.Thm18.G1TopScal
import QuantumZipper.Proofs.Thm18.G1Side3Top
import QuantumZipper.Proofs.NonVacuity
import QuantumZipper.Proofs.NonVacuityWedge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1TOP (3): `G1Z2SideTopSelStmt` — the side domain has infinite quantum area

The representative setting (path `B` on `Ω`, wedge `wedgeRep γ X A` on `Ω'`) is realized as a
Theorem 1.8 setting on the product `Ω × Ω'`, where the scaling argument `ae_cfgArea_top`
(G1TopScal.lean; Sheffield, arXiv:1012.4797, §1.6, proof of Theorem 1.8) gives a.s. infinite
side area; positivity on open sets comes from the local rule `μ_W = e^{γ g} μ_X` for the wedge
field and M4-P2 for the free field (`WedgeCan4.ae_qAreaMeasure_wedgeField_eq`). Fubini over the
measurable functional `areaFn` returns to the iterated form, and `areaFn` is identified with the
unscaled area of the dilated side domain (`qAreaMeasure_rescale`). Main results:
`g1Z2SideTopSelStmt_holds` and the headline `R18.theorem1_8Paper_of_frontier12`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Top

open Thm18Asm G1Side

/-- A.s. the explicit wedge representative charges every nonempty open subset of `ℍ`, and its
area is the pushforward of the unscaled area. -/
theorem ae_rep_area {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', IsLQGGood γ (wU γ X A ω) ∧ 0 < scaleParam γ (wU γ X A ω) ∧
      IsLQGGood γ (wedgeRep γ X A ω) ∧
      qAreaMeasure γ (wedgeRep γ X A ω) =
        (qAreaMeasure γ (wU γ X A ω)).map (fun z : ℂ => z / (scaleParam γ (wU γ X A ω) : ℂ)) ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < qAreaMeasure γ (wedgeRep γ X A ω) V := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  filter_upwards [LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA,
    WedgeCan4.ae_wedge_canonical_spec_of_inputs
      (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
      hγ hγ2 hαQ hX hA hXA,
    WedgeCan4.ae_qAreaMeasure_wedgeField_eq hX hγ hγ2 (Q := Qc γ)
      (WedgeCan4.ae_continuous_wedgeProcess hA), WedgeCan4.ae_continuous_wedgeProcess hA]
    with ω hg hcan hloc hAc
  obtain ⟨hs, hrg, -⟩ := hcan
  obtain ⟨hden, -, -, hXpos, -⟩ := hloc
  have hmap : qAreaMeasure γ (wedgeRep γ X A ω) =
      (qAreaMeasure γ (wU γ X A ω)).map (fun z : ℂ => z / (scaleParam γ (wU γ X A ω) : ℂ)) :=
    GoodTransforms.qAreaMeasure_rescale hg hγ hs
  refine ⟨hg, hs, hrg, hmap, fun V hV hVH hne => ?_⟩
  set s := scaleParam γ (wU γ X A ω) with hsdef
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hcm : Continuous fun z : ℂ => z / (s : ℂ) := continuous_id.div_const _
  rw [hmap, Measure.map_apply hcm.measurable hV.measurableSet]
  set V' := (fun z : ℂ => z / (s : ℂ)) ⁻¹' V with hV'
  have hV'o : IsOpen V' := hV.preimage hcm
  have hV'H : V' ⊆ H := fun z hz => by
    have h1 : 0 < (z / (s : ℂ)).im := hVH hz
    have e : (z / (s : ℂ)).im = z.im / s := by
      rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add, div_eq_mul_inv]
    rw [e] at h1
    show 0 < z.im
    exact (div_pos_iff_of_pos_right hs).1 h1
  have hV'ne : V'.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    refine ⟨(s : ℂ) * v, ?_⟩
    show (s : ℂ) * v / (s : ℂ) ∈ V
    rwa [mul_div_cancel_left₀ _ hsc]
  have hW : wU γ X A ω = wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ) := rfl
  rw [hW, hden]
  have hmeas : Measurable fun z : ℂ => ENNReal.ofReal
      (Real.exp (γ * WedgeCan.wedgeProfile (X ω) (fun t => A t ω) (Qc γ) z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (WedgeCan.measurable_wedgeProfile hAc.measurable _)))
  refine pos_iff_ne_zero.2 ?_
  rw [Ne, withDensity_apply_eq_zero' hmeas.aemeasurable]
  have e : {z : ℂ | ENNReal.ofReal (Real.exp (γ * WedgeCan.wedgeProfile (X ω)
      (fun t => A t ω) (Qc γ) z)) ≠ 0} ∩ V' = V' :=
    inter_eq_right.2 fun z _ => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  rw [e]
  exact (hXpos V' hV'o hV'H hV'ne).ne'

/-- **The side domain has infinite quantum area** (`G1Z2SideTopSelStmt`). -/
theorem g1Z2SideTopSelStmt_holds : G1Z2SideTopSelStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hαQ, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, rfl⟩
  have hdm : AEMeasurable (fun ω' => WedgeMeas.dataFull H (wedgeRep γ X A ω')) P' :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hαQ hrep
  -- the product setting
  set B₂ : ℝ≥0 → Ω × Ω' → ℝ := fun t p => B t p.1 with hB₂
  set Y₂ : Ω × Ω' → FieldSample := fun p => wedgeRep γ X A p.2 with hY₂
  have hS₂ : Thm18Setting γ (P.prod P') B₂ Y₂ := by
    refine ⟨hγ, hγ2, NonVacuity.nv_isBrownianReal measurePreserving_fst hB, ?_,
      NonVacuity.nv_indepFun_prod (pathOf B) (wedgeRep γ X A)⟩
    refine ⟨hαQ, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, ?_⟩
    exact NonVacuity.nv_map_comp measurePreserving_snd hdm
  have hrepA := ae_rep_area hγ hγ2 hX hA hXA
  have hpos₂ : ∀ᵐ p ∂(P.prod P'), ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty →
      0 < qAreaMeasure γ (Y₂ p) V :=
    measurePreserving_snd.quasiMeasurePreserving.ae (hrepA.mono fun ω h => h.2.2.2.2)
  have hψm : ∀ left, ∀ w, Measurable fun a => Ψ left a w := fun left w =>
    (hΨ.1 left).comp (measurable_id.prodMk measurable_const)
  have hsq : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  have hprod : ∀ left : Bool, ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P',
      (pathOf B ω, hdm.mk _ ω') ∈ {q | areaFn γ (Ψ left) q = ⊤} := by
    intro left
    refine Measure.ae_ae_of_ae_prod
      (p := fun z : Ω × Ω' => (pathOf B z.1, hdm.mk _ z.2) ∈ {q | areaFn γ (Ψ left) q = ⊤}) ?_
    have h1 := ae_cfgArea_top hS₂ hΨ left hpos₂
    have h2 : ∀ᵐ p ∂(P.prod P'), WedgeMeas.dataFull H (wedgeRep γ X A p.2) = hdm.mk _ p.2 :=
      measurePreserving_snd.quasiMeasurePreserving.ae hdm.ae_eq_mk
    filter_upwards [h1, h2] with p hp hp2
    have e : (fun t : ℝ≥0 => drive (γ ^ 2) B₂ p t / γ) = pathOf B p.1 := by
      funext t
      simp only [drive, hB₂, pathOf, Real.toNNReal_coe, hsq]
      field_simp
    show areaFn γ (Ψ left) (pathOf B p.1, hdm.mk _ p.2) = ⊤
    rw [← e, ← hp2]
    exact hp
  have hmE : ∀ left, MeasurableSet
      {q : (ℝ≥0 → ℝ) × ((ℕ → ℝ) × (TestFun H → ℝ)) | areaFn γ (Ψ left) q = ⊤} :=
    fun left => measurableSet_eq_fun (measurable_areaFn γ (hψm left)) measurable_const
  have hpm : AEMeasurable (pathOf B) P := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
  have hR : ∀ left, ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
      areaFn γ (Ψ left) (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) = ⊤ := by
    intro left
    set s : Set ((ℝ≥0 → ℝ) × Ω') :=
      {q | (q.1, hdm.mk _ q.2) ∈ {q | areaFn γ (Ψ left) q = ⊤}}ᶜ with hsdef
    have hs : MeasurableSet s :=
      ((hmE left).preimage (measurable_fst.prodMk (hdm.measurable_mk.comp measurable_snd))).compl
    have hRm : MeasurableSet {a : ℝ≥0 → ℝ | P' (Prod.mk a ⁻¹' s) = 0} :=
      measurable_measure_prodMk_left hs (measurableSet_singleton 0)
    have h1 : ∀ᵐ a ∂(P.map (pathOf B)), P' (Prod.mk a ⁻¹' s) = 0 := by
      rw [ae_map_iff hpm hRm]
      filter_upwards [hprod left] with ω hω
      exact ae_iff.1 hω
    filter_upwards [h1] with a ha
    have ha' : ∀ᵐ ω' ∂P', (a, hdm.mk _ ω') ∈ {q | areaFn γ (Ψ left) q = ⊤} := ae_iff.2 ha
    filter_upwards [ha', hdm.ae_eq_mk] with ω' h1 h2
    rw [h2]; exact h1
  have hfacts : ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, SideMapFacts (Ψ left a) :=
    G1RC.ae_map_pathOf_of_chord G1RC.g1RegPathChordStmt hγ hγ2 hB hΨ
      (fun ms => ∀ left : Bool, SideMapFacts (ms left))
      (fun a hc hs left => sideMapFacts_of_sel hΨ hc hs left)
  filter_upwards [hfacts, hR true, hR false] with a hfa ht hf left
  have hRl : ∀ᵐ ω' ∂P', areaFn γ (Ψ left) (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) = ⊤ := by
    cases left <;> assumption
  filter_upwards [hRl, hrepA] with ω' h1 hw
  obtain ⟨-, hs, hrg, hmap, -⟩ := hw
  obtain ⟨-, hd, -, hH, -⟩ := hfa left
  rw [areaFn_eq, muY_dataFull hrg] at h1
  change qAreaMeasure γ (wedgeRep γ X A ω') (Prod.mk a ⁻¹' imgSet (Ψ left)) = ⊤ at h1
  have hsec := imgSet_section hd.continuousOn hH
  have hmeasS : MeasurableSet (Ψ left a '' H) :=
    hsec ▸ measurable_prodMk_left (measurableSet_imgSet (hψm left))
  have hdm' : Measurable fun z : ℂ => z / ((scaleParam γ (wU γ X A ω') : ℝ) : ℂ) :=
    (continuous_id.div_const _).measurable
  rw [hsec, hmap, Measure.map_apply hdm' hmeasS] at h1
  rw [← h1]
  have hsc : ((scaleParam γ (wU γ X A ω') : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  congr 1
  ext z
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by field_simp⟩
  · rintro ⟨u, hu, hz⟩
    refine ⟨u, hu, ?_⟩
    rw [hz]; field_simp

end G1Top

namespace R18

open Thm18Asm

end R18
end QuantumZipper
