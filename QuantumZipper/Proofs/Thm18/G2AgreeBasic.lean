import QuantumZipper.Proofs.Thm18.G2RootSetup
import QuantumZipper.Proofs.Thm18.G3G2LocZoom
import QuantumZipper.Proofs.Wire2b
import QuantumZipper.Proofs.Section5.Prop16MarkovMask2Agree
import QuantumZipper.Proofs.Section5.Prop16MeasCoords
import QuantumZipper.Proofs.Section5.Prop17PalmCLog
import QuantumZipper.Proofs.Section5.Prop17PalmCField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 identification nodes: the deterministic and measurability parts

For the identification nodes `G2RootXAgreeStmt γ μ`, `G2RootRAgreeStmt γ μ` (`G2RootSetup.lean`),
with the D3⁺ data of `g2Root_setup` (`X' = palmCField X₀ x`, `ρ₀ = palmCRho refS x`,
`g = g2Corr γ x`, `r = κ/2`), this file proves:

* `exists_nat_locFieldFull_lawCyl`: a cylinder event `s ∈ lawCyl` of `lawOf Z` is the same event
  of the rich local data `locFieldFull R Z` for some `R` (so the local set is `S = s`);
* `g2Agree_wedge_mass` (clause (a)): with `μ = g2WedgeLaw P' Y'` (the law of `lawOf Y'` for a
  `γ`-wedge `Y'`), `P'(locFieldFull R Y' ∈ s) = μ(s)`;
* `g2_pt_identity`, `g2_zoomField_eq_zoomModel`: **the correction constant is exact**: at every
  folded circle where the Palm field `normField γ (X₀ + ψ_x)` is regular after translation by `x`,
  the zoomed field `zoomField γ C (normField γ (X₀ + ψ_x)) x` equals the D3⁺ model field
  `zoomModel γ γ C ρ₀ X' g2Corr` (no additive constant is lost: pointwise
  `γ(−log‖z‖) + g2Corr γ x z = 𝔥₀(z + x) + ψ_x(z + x) − ∫ψ_x dS`, and `X'(ρ₀) = X₀(S)`);
* `aemeasurable_g3ModelData_g2` (clause (c)): the model data are a.e.-measurable. The model field
  agrees on all dyadic folded circles with the measurable field `g2ModelW`, hence has the same
  rescalings (`rescale_eq_of_fc_agree`, via `D3Plus.avgReg_congr`), and the local scale is
  a.e.-measurable (`Prop16Asm.aemeasurable_scaleParamOn_zoomModel_mm`).

Sources: Sheffield, arXiv:1012.4797, Prop. 5.5 (p. 65) and proof of Thm. 1.8 (p. 71); the Palm
shift `ψ_x` as in Duplantier–Sheffield, arXiv:0808.1560, §3.3. The formal arguments are own
elementary bookkeeping (AGENT_GUIDE cost rule), following `Prop17PalmCField`/`Prop17PalmCAgree`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

open CoordsFull S5.FieldLaw.Raw

local notation "Ω₀" => gffBase.Ω

/-! ## Cylinder events through rich local data -/

/-- A cylinder event of `lawOf Z` is the same event of `locFieldFull R Z`, for some `R`. -/
theorem exists_nat_locFieldFull_lawCyl {s : Set LawD} (hs : s ∈ lawCyl) :
    ∃ R : ℕ, ∀ Z : FieldSample, D3Plus.locFieldFull R Z ∈ s ↔ lawOf Z ∈ s := by
  classical
  obtain ⟨A, hA, B, hB, rfl⟩ := hs
  rw [mem_measurableCylinders] at hA hB
  obtain ⟨I, S, -, rfl⟩ := hA
  obtain ⟨J, T, -, rfl⟩ := hB
  have hbd : ∀ ρ : TestFun H, ∃ r : ℝ, tsupport ρ.1 ⊆ closedBall (0 : ℂ) r := fun ρ =>
    ρ.2.2.1.isCompact.isBounded.subset_closedBall 0
  choose rb hrb using hbd
  set a₁ : ℕ → ℝ := fun j => |‖(fullIndex j).1‖ + (fullIndex j).2|
  set a₂ : TestFun H → ℝ := fun ρ => |rb ρ|
  obtain ⟨R, hR⟩ := exists_nat_ge (∑ j ∈ I, a₁ j + ∑ ρ ∈ J, a₂ ρ)
  have h₁ : 0 ≤ ∑ j ∈ I, a₁ j := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h₂ : 0 ≤ ∑ ρ ∈ J, a₂ ρ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hI : ∀ j ∈ I, D3Plus.inBallFull R j := fun j hj => by
    unfold D3Plus.inBallFull
    exact (le_abs_self _).trans
      ((Finset.single_le_sum (f := a₁) (fun _ _ => abs_nonneg _) hj).trans (by linarith))
  have hJ : ∀ ρ ∈ J, D3Plus.suppIn R ρ := fun ρ hρ => by
    unfold D3Plus.suppIn
    exact (hrb ρ).trans (closedBall_subset_closedBall ((le_abs_self _).trans
      ((Finset.single_le_sum (f := a₂) (fun _ _ => abs_nonneg _) hρ).trans (by linarith))))
  refine ⟨R, fun Z => ?_⟩
  have e₁ : I.restrict (D3Plus.locFieldFull R Z).1 = I.restrict (coordsFull Z) := by
    funext j
    simp only [Finset.restrict, D3Plus.locFieldFull, if_pos (hI j j.2)]
  have e₂ : J.restrict (D3Plus.locFieldFull R Z).2 =
      J.restrict (fun ρ : TestFun H => pairRaw Z ρ.1) := by
    funext ρ
    simp only [Finset.restrict, D3Plus.locFieldFull, if_pos (hJ ρ ρ.2)]
  simp only [lawOf, mem_prod, mem_cylinder, e₁, e₂]

/-! ## Clause (a): the wedge law -/

/-- The law of the data `lawOf Y'` of a random field (for a `γ`-wedge: the limit law `μ`). -/
def g2WedgeLaw {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (Y' : Ω' → FieldSample) :
    Measure LawD :=
  P'.map fun ω' => lawOf (Y' ω')

instance isProbabilityMeasure_g2WedgeLaw {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y' : Ω' → FieldSample} : IsProbabilityMeasure (g2WedgeLaw P' Y') := by
  unfold g2WedgeLaw; infer_instance

/-- **Clause (a).** -/
theorem g2Agree_wedge_mass {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y' : Ω' → FieldSample}
    (hW : IsQuantumWedge γ γ Y' P') {s : Set LawD} (hs : MeasurableSet s) {R : ℕ}
    (hR : ∀ Z : FieldSample, D3Plus.locFieldFull R Z ∈ s ↔ lawOf Z ∈ s) :
    ∫⁻ ω', s.indicator 1 (D3Plus.locFieldFull R (Y' ω')) ∂P' =
      ENNReal.ofReal ((g2WedgeLaw P' Y').real s) := by
  have hae : AEMeasurable (fun ω' => lawOf (Y' ω')) P' :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 (gamma_lt_Qc' hγ hγ2) hW
  have hpt : ∀ ω', s.indicator (1 : LawD → ℝ≥0∞) (D3Plus.locFieldFull R (Y' ω')) =
      s.indicator 1 (lawOf (Y' ω')) := fun ω' => by
    by_cases h : lawOf (Y' ω') ∈ s
    · rw [indicator_of_mem h, indicator_of_mem ((hR _).2 h)]; rfl
    · rw [indicator_of_notMem h, indicator_of_notMem fun h' => h ((hR _).1 h')]
  simp_rw [hpt]
  rw [palmC_lintegral_indicator hae hs, Measure.real, ← g2WedgeLaw,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-! ## The field identity (the correction constant is exact) -/

/-- Pointwise: `γ(−log‖z‖) + g2Corr γ x z = 𝔥₀(z + x) + ψ_x(z + x) − ∫ ψ_x dS`. -/
theorem g2_pt_identity (γ x : ℝ) (z : ℂ) :
    γ * -Real.log ‖z‖ + g2Corr γ x z =
      h0rev (γ ^ 2) (z + x) + g2PalmPsi γ x (z + x) - ∫ u, g2PalmPsi γ x u ∂refS := by
  have h1 : (x : ℂ) - (z + x) = -z := by ring
  have h2 : (x : ℂ) - conj (z + (x : ℂ)) = -conj z := by
    rw [map_add, Complex.conj_ofReal]; ring
  simp only [g2Corr, g2PalmPsi, neumannH, h1, h2, norm_neg, Complex.norm_conj]
  ring

theorem integrable_h0rev_add_fc (γ x : ℝ) (c : ℂ) (ρ : ℝ) :
    Integrable (fun z => h0rev (γ ^ 2) (z + x)) (foldedCircle c ρ) := by
  refine ((palmC_integrable_log_sub_fc c (-x) ρ).const_mul (2 / Real.sqrt (γ ^ 2))).congr
    (ae_of_all _ fun z => ?_)
  simp only [h0rev]
  congr 3
  push_cast
  ring

theorem integrable_g2PalmPsi_add_fc (γ x : ℝ) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun z => g2PalmPsi γ x (z + x)) (foldedCircle c ρ) := by
  have hc : Continuous fun z : ℂ => γ * Real.posLog ‖z + (x : ℂ)‖ := by fun_prop
  refine (((CoordReg.integrable_log_norm_foldedCircle c ρ).neg.const_mul γ).add
    (E5.integrable_foldedCircle_of_continuousOn hc.continuousOn c ρ hρ (lt_add_one _))).congr
    (ae_of_all _ fun z => ?_)
  have h1 : (x : ℂ) - (z + x) = -z := by ring
  have h2 : (x : ℂ) - conj (z + (x : ℂ)) = -conj z := by
    rw [map_add, Complex.conj_ofReal]; ring
  simp only [Pi.add_apply, g2PalmPsi, neumannH, h1, h2, norm_neg, Complex.norm_conj]
  rw [show refS = foldedCircle 0 1 from rfl, kPot_refS_eq]
  simp only [Pi.neg_apply]
  ring

/-- **Field identity at a regular translated folded circle.** -/
theorem g2_zoomField_eq_zoomModel (γ C x : ℝ) (ω : Ω₀) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hreg : evalReg (normField γ (xPalm γ x) ω) ((foldedCircle c ρ).map (· + (x : ℂ))) =
      normField γ (xPalm γ x) ω ((foldedCircle c ρ).map (· + (x : ℂ)))) :
    zoomField γ C (normField γ (xPalm γ x) ω) x (foldedCircle c ρ) =
      D3Plus.zoomModel γ γ C (palmCRho refS x) (palmCField gffBase.X x ω) (g2Corr γ x)
        (foldedCircle c ρ) := by
  have hA := integrable_h0rev_add_fc γ x c ρ
  have hB := integrable_g2PalmPsi_add_fc γ x c hρ
  have hint : ∀ K : ℝ, ∫ z, (γ * -Real.log ‖z‖ + g2Corr γ x z + K) ∂(foldedCircle c ρ) =
      (∫ z, h0rev (γ ^ 2) (z + x) ∂(foldedCircle c ρ)) +
        (∫ z, g2PalmPsi γ x (z + x) ∂(foldedCircle c ρ)) +
        (K - ∫ u, g2PalmPsi γ x u ∂refS) := by
    intro K
    have e : (fun z => γ * -Real.log ‖z‖ + g2Corr γ x z + K) = fun z =>
        (h0rev (γ ^ 2) (z + x) + g2PalmPsi γ x (z + x)) + (K - ∫ u, g2PalmPsi γ x u ∂refS) := by
      funext z; rw [g2_pt_identity]; ring
    rw [e, integral_add ?_ (integrable_const _), integral_add hA hB, integral_const,
      Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    exact hA.add hB
  simp only [zoomField, addConst, translate]
  rw [hreg]
  simp only [D3Plus.zoomModel, Pi.add_apply, ofFun]
  rw [hint, palmCField_rho]
  simp only [normField, xPalm, Pi.add_apply, ofFun, palmCField]
  rw [integral_map_add_real, integral_map_add_real, measure_univ, ENNReal.toReal_one]
  ring

/-! ## Clause (c): measurability of the model data -/

/-- Fields agreeing at all dyadic folded circles have the same rescalings. -/
theorem rescale_eq_of_fc_agree {y y' : FieldSample}
    (h : ∀ (n k : ℕ) (z : ℂ), y (foldedCircle (dyadicRoundC n z) (radius k)) =
      y' (foldedCircle (dyadicRoundC n z) (radius k))) (Q a : ℝ) :
    rescale y Q a = rescale y' Q a := by
  have hav : ∀ k w, avgReg y k w = avgReg y' k w := fun k w =>
    D3Plus.avgReg_congr (r := ‖w‖ + radius k + 1) (fun n k' z _ => h n k' z) (lt_add_one _)
  funext ν
  simp only [rescale, coordChange, evalReg, hav]

/-- A measurable field agreeing with the model field at all folded circles. -/
def g2ModelW (γ C x : ℝ) (ω : Ω₀) : FieldSample :=
  addConst (palmCField gffBase.X x ω + ofFun fun z => γ * -Real.log ‖z‖ + g2Corr γ x z)
    (C / γ - gffBase.X ω refS)

theorem measurable_g2ModelW (γ C x : ℝ) : Measurable (g2ModelW γ C x) := by
  refine measurable_pi_iff.2 fun μ => ?_
  simp only [g2ModelW, addConst, Pi.add_apply, palmCField]
  exact ((gffBase.gff.measurable_coord _).add measurable_const).add
    ((measurable_const.sub (gffBase.gff.measurable_coord _)).mul measurable_const)

theorem g2ModelW_fc (γ C x : ℝ) (ω : Ω₀) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    g2ModelW γ C x ω (foldedCircle c ρ) = D3Plus.zoomModel γ γ C (palmCRho refS x)
      (palmCField gffBase.X x ω) (g2Corr γ x) (foldedCircle c ρ) := by
  have hI : Integrable (fun z => γ * -Real.log ‖z‖ + g2Corr γ x z) (foldedCircle c ρ) := by
    refine (((integrable_h0rev_add_fc γ x c ρ).add (integrable_g2PalmPsi_add_fc γ x c hρ)).sub
      (integrable_const (∫ u, g2PalmPsi γ x u ∂refS))).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [g2_pt_identity]
  simp only [g2ModelW, D3Plus.zoomModel, addConst, Pi.add_apply, ofFun]
  rw [palmCField_rho, integral_add hI (integrable_const _), integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul, mul_one]
  ring

theorem measurable_locFieldFull_rescale (Q : ℝ) (R : ℕ) :
    Measurable fun p : FieldSample × ℝ => D3Plus.locFieldFull R (rescale p.1 Q p.2) := by
  classical
  unfold D3Plus.locFieldFull
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · split_ifs
    · simp only [CoordsFull.coordsFull]
      exact Prop16Area.measurable_rescale_apply_joint Q _
    · exact measurable_const
  · split_ifs
    · simp only [pairRaw]
      exact (Prop16Area.measurable_rescale_apply_joint Q _).sub
        (Prop16Area.measurable_rescale_apply_joint Q _)
    · exact measurable_const

/-- **Clause (c).** -/
theorem aemeasurable_g3ModelData_g2 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {x r : ℝ} (hr : 0 < r)
    (hxr : r < |x|) (hx1 : |x| + r < 1) (C : ℝ) (R : ℕ) :
    AEMeasurable (g3ModelData γ r C (palmCRho refS x) R (palmCField gffBase.X x)
      (fun _ => g2Corr γ x)) gffBase.P := by
  have hS := g2Root_setup hγ hγ2 hr hxr hx1
  have ha := Prop16Asm.aemeasurable_scaleParamOn_zoomModel_mm hS C
  have hp := (measurable_locFieldFull_rescale (Qc γ) R).comp_aemeasurable
    ((measurable_g2ModelW γ C x).aemeasurable.prodMk ha)
  refine hp.congr (ae_of_all _ fun ω => ?_)
  simp only [Function.comp_apply, g3ModelData, canonicalOn]
  rw [rescale_eq_of_fc_agree fun n k z => g2ModelW_fc γ C x ω _ (radius_pos k)]

end Thm18Asm
end QuantumZipper
