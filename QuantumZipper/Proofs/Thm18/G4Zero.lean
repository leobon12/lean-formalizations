import QuantumZipper.Proofs.Thm18.Assembly
import QuantumZipper.Proofs.Zipper.Cor15GroupNeg
import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.Zipper.UnzipFullSplit
import QuantumZipper.Proofs.Zipper.Cor15LawCongr
import QuantumZipper.Proofs.Field.Factorization
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.Zipper.E6UpBasic

/-!
# Theorem 1.8, node G4: the length zipper at `t = 0` (clause (3) at `t = 0`)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (zipper
stationarity (3), `t = 0`: `Z^LEN_0` is the identity). In the formalization `zipLenC γ 0 =
zipLenUpC γ 0` zips along the chosen length-welding driver `lenWeldDriver γ x 0` and then
canonicalizes (mismatch 3 of `handoff/THM18-ASM.md`), so it is not literally the identity.

* `lenWeldDriver_zero_spec` (deterministic): at `ℓ = 0` the length-welding driver has time
  `T = 0` (a positive time would give a simple-curve hull with `0₋ < 0`, `B5.swallowedSet_eq_Icc_
  zeroMinus`, but `0₋ = lenWeldPoint γ x 0 = 0`), is continuous and vanishes at `0`.
* `zipLenC_zero_data` (deterministic): if the field `x` has regularized folded-circle averages
  equal to its raw ones and `scaleParam γ x = 1`, then `Z^LEN_0 (x, W)` has the circle
  coordinates of `x`, test pairings `pairTest x ρ` (regularized), and driver `W` on `[0,∞)`.
* `configLawFull_zipLenC_zero`: clause (3) at `t = 0`, given the explicit regularity hypothesis
  `WedgeZeroRegStmt` on the `(γ − 2/γ)`-wedge (raw = regularized at the full folded circles and
  at test functions, and `scaleParam = 1`: the wedge is in canonical description).

The pattern follows `Cor15Partial.theorem1_5a_zero` (Corollary 1.5 (a) at `t = 0`).
Own elementary argument (unfolding definitions; coordinatewise law comparison).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## 1. The length-welding driver at `ℓ = 0` -/

theorem isLenWeldingDriver_zero_zero (γ : ℝ) (x : FieldSample) :
    IsLenWeldingDriver γ x 0 (0, fun _ => 0) := by
  rw [isLenWeldingDriver_iff]
  refine ⟨le_rfl, Cor15Partial.isWeldingDriver_zero γ x, ?_⟩
  rw [lenWeldPoint_of_nonpos le_rfl]
  exact B5.zeroMinus_zero_time continuous_const rfl

/-- At `ℓ = 0` the chosen length-welding driver has time `0`, is continuous and starts at `0`. -/
theorem lenWeldDriver_zero_spec (γ : ℝ) (x : FieldSample) :
    (lenWeldDriver γ x 0).1 = 0 ∧ Continuous (lenWeldDriver γ x 0).2 ∧
      (lenWeldDriver γ x 0).2 0 = 0 := by
  obtain ⟨hT, hc, h0, hK, hz, -⟩ := lenWeldDriver_spec ⟨_, isLenWeldingDriver_zero_zero γ x⟩
  refine ⟨?_, hc, h0⟩
  rcases hK with hK | hK
  · exact hK
  · by_contra hne
    have hpos : 0 < (lenWeldDriver γ x 0).1 := lt_of_le_of_ne hT (Ne.symm hne)
    have h := (B5.swallowedSet_eq_Icc_zeroMinus hc h0 hpos hK).1
    rw [hz, lenWeldPoint_of_nonpos le_rfl] at h
    exact lt_irrefl _ h

/-! ## 2. `Z^LEN_0` on a regular canonical field -/

/-- **`Z^LEN_0` is the identity on the data**, for a field whose regularized folded-circle
averages are its raw ones and whose scale parameter is `1`. -/
theorem zipLenC_zero_data {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ}
    (hreg : ∀ i : ℕ, evalReg x (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2) = x (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2))
    (hsc : scaleParam γ x = 1) (hW0 : W 0 = 0) :
    CoordsFull.coordsFull (zipLenC γ 0 (x, W)).1 = CoordsFull.coordsFull x ∧
      (∀ ρ : TestFun H, pairRaw (zipLenC γ 0 (x, W)).1 ρ.1 = pairTest x ρ.1) ∧
      ∀ t : ℝ≥0, (zipLenC γ 0 (x, W)).2 t = W t := by
  have hz : zipLenC γ 0 (x, W) =
      canonConfig γ (zipWeldUp γ (lenWeldDriver γ x 0).1 (lenWeldDriver γ x 0).2 (x, W)) := by
    rw [zipLenC_of_nonneg le_rfl]; rfl
  obtain ⟨hT, hc, h0⟩ := lenWeldDriver_zero_spec γ x
  rw [hz]
  generalize lenWeldDriver γ x 0 = p at hT hc h0 ⊢
  obtain ⟨T, V⟩ := p
  simp only at hT hc h0
  subst hT
  set x₀ := coordChange x (revMapInv V 0) (Qc γ) with hx₀def
  have hx₀ : CoordsFull.coordsFull x₀ = CoordsFull.coordsFull x := by
    funext i
    have hr := UnzipFull.fullIndex_radius_pos i
    show coordChange x (revMapInv V 0) (Qc γ) _ = x _
    rw [CoordReg.coordChange_fc_congr x (Cor15Partial.revMapInv_zero_eqOn hc h0) _ _ hr,
      Cor15Partial.coordChange_id_apply, hreg i]
  have havg : avgReg x₀ = avgReg x := CoordsFull.avgReg_congr_full hx₀
  have ha : scaleParam γ x₀ = 1 := (Factorization.scaleParam_congr havg γ).trans hsc
  have hcan : ∀ μ : Measure ℂ, canonical γ x₀ μ = evalReg x μ := by
    intro μ
    rw [canonical_eq_coordChange, ha]
    simp only [coordChange, Complex.ofReal_one, one_mul, Measure.map_id', deriv_id'',
      norm_one, Real.log_one, integral_zero, mul_zero, add_zero]
    exact Cor15Group.evalReg_congr_regEq (fun k z => by rw [havg]) μ
  refine ⟨?_, fun ρ => ?_, fun t => ?_⟩
  · funext i
    show canonical γ x₀ _ = x _
    rw [hcan, hreg i]
  · show canonical γ x₀ _ - canonical γ x₀ _ = pairTest x ρ.1
    rw [hcan, hcan]
    rfl
  · show (zipWeldUp γ 0 V (x, W)).2 (scaleParam γ x₀ ^ 2 * max (t : ℝ) 0) /
        scaleParam γ x₀ = W t
    rw [ha, max_eq_left t.coe_nonneg, one_pow, one_mul, div_one]
    simp only [zipWeldUp]
    split_ifs with ht
    · have ht0 : (t : ℝ) = 0 := le_antisymm ht t.2
      rw [ht0, hW0]
      simp [h0]
    · rw [h0, sub_zero, sub_zero]

/-! ## 3. Coordinatewise comparison of `configLawFull` data laws -/

/-- Two a.e.-measurable random `configLawFull` data whose coordinates agree almost surely
(coordinate by coordinate) have the same law. -/
theorem map_fullData_eq_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {F G : Ω → E6.FullData} (hF : AEMeasurable F P)
    (hG : AEMeasurable G P) (h1 : ∀ n, ∀ᵐ ω ∂P, (F ω).1.1 n = (G ω).1.1 n)
    (h2 : ∀ ρ, ∀ᵐ ω ∂P, (F ω).1.2 ρ = (G ω).1.2 ρ)
    (h3 : ∀ t, ∀ᵐ ω ∂P, (F ω).2 t = (G ω).2 t) : P.map F = P.map G := by
  let E : ((ℕ ⊕ TestFun H) ⊕ ℝ≥0 → ℝ) ≃ᵐ E6.FullData :=
    (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ)
        (MeasurableEquiv.refl _))
  have key : ∀ K : Ω → E6.FullData, AEMeasurable K P →
      P.map K = (P.map (fun ω => E.symm (K ω))).map E := by
    intro K hK
    show _ = (P.map (E.symm ∘ K)).map E
    rw [AEMeasurable.map_map_of_aemeasurable E.measurable.aemeasurable
      (E.symm.measurable.comp_aemeasurable hK)]
    simp [Function.comp_def]
  rw [key F hF, key G hG]
  congr 1
  have hall : ∀ i, ∀ᵐ ω ∂P, E.symm (F ω) i = E.symm (G ω) i := by
    rintro ((n | ρ) | t)
    · exact h1 n
    · exact h2 ρ
    · exact h3 t
  refine (map_eq_iff_forall_finset_map_restrict_eq (X := fun i ω => E.symm (F ω) i)
    (Y := fun i ω => E.symm (G ω) i) (E.symm.measurable.comp_aemeasurable hF)
    (E.symm.measurable.comp_aemeasurable hG)).2 fun I => ?_
  refine Measure.map_congr ?_
  filter_upwards [ae_all_iff.2 fun i : I => hall i.1] with ω hω
  funext i
  exact hω i

/-! ## 4. Clause (3) at `t = 0` -/

/-- **Regularity of the `(γ − 2/γ)`-wedge sample needed at `t = 0`** (explicit hypothesis):
a.s. its regularized folded-circle averages at the full coordinate circles equal the raw ones
and `scaleParam γ (Y ω) = 1` (the canonical description is a fixed point of canonicalization);
for each test function, a.s. the regularized pairing equals the raw one. -/
def WedgeZeroRegStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample), 0 < γ → γ < 2 → IsQuantumWedge γ (γ - 2 / γ) Y P →
    (∀ᵐ ω ∂P, (∀ i : ℕ, evalReg (Y ω) (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2) = Y ω (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2)) ∧ scaleParam γ (Y ω) = 1) ∧
    ∀ ρ : TestFun H, ∀ᵐ ω ∂P, pairTest (Y ω) ρ.1 = pairRaw (Y ω) ρ.1

theorem pairTest_eq_reconstruct (x : FieldSample) (ρ : ℂ → ℝ) :
    pairTest x ρ = pairTest (Factorization.reconstruct
      (E6.coordsOfFull (CoordsFull.coordsFull x))) ρ := by
  have h : RegEq (Factorization.reconstruct (E6.coordsOfFull (CoordsFull.coordsFull x))) x :=
    fun k z => by rw [E6.coordsOfFull_coordsFull, Factorization.avgReg_reconstruct_coords]
  unfold pairTest
  rw [Cor15Group.evalReg_congr_regEq h, Cor15Group.evalReg_congr_regEq h]

/-- **Theorem 1.8 (3) at `t = 0`**, given `WedgeZeroRegStmt`. -/
theorem configLawFull_zipLenC_zero (hZ : WedgeZeroRegStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    configLawFull (fun ω => zipLenC γ 0 (wedgeConfig γ B Y ω)) P =
      configLawFull (wedgeConfig γ B Y) P := by
  obtain ⟨hγ, hγ2, hB, hY, -⟩ := hS
  obtain ⟨hR, hT⟩ := hZ γ P Y hγ hγ2 hY
  have hYm := hIn.2.1
  -- the regularized data of `Y`
  let G : Ω → E6.FullData := fun ω =>
    ((CoordsFull.coordsFull (Y ω), fun ρ : TestFun H => pairTest (Y ω) ρ.1),
      fun t : ℝ≥0 => drive (γ ^ 2) B ω t)
  have hstep1 : configLawFull (fun ω => zipLenC γ 0 (wedgeConfig γ B Y ω)) P = P.map G := by
    refine Measure.map_congr ?_
    filter_upwards [hR, hB.eval_zero_ae_eq_zero] with ω hω h0
    have hW0 : drive (γ ^ 2) B ω 0 = 0 := by simp [drive, h0]
    obtain ⟨e1, e2, e3⟩ := zipLenC_zero_data (γ := γ) hω.1 hω.2 hW0
    exact Prod.ext (Prod.ext e1 (funext e2)) (funext e3)
  -- a.e.-measurability
  obtain ⟨B'', hB''m, -, -, -, hB''eq⟩ := RS.exists_good_version0 hB
  have hd : AEMeasurable (fun ω => fun t : ℝ≥0 => drive (γ ^ 2) B ω t) P := by
    refine (measurable_pi_iff.2 fun t => (hB''m t).const_mul (Real.sqrt (γ ^ 2))).aemeasurable.congr
      ?_
    filter_upwards [hB''eq] with ω hω
    funext t
    simp [drive, hω t]
  have hΦ : Measurable fun y : ℕ → ℝ => fun ρ : TestFun H =>
      pairTest (Factorization.reconstruct (E6.coordsOfFull y)) ρ.1 :=
    measurable_pi_iff.2 fun ρ => (measurable_pairTest ρ.1).comp
      (Factorization.measurable_reconstruct.comp E6.measurable_coordsOfFull)
  have hc : AEMeasurable (fun ω => CoordsFull.coordsFull (Y ω)) P :=
    measurable_fst.comp_aemeasurable hYm
  have hGm : AEMeasurable G P := by
    have h2 : AEMeasurable (fun ω => fun ρ : TestFun H => pairTest (Y ω) ρ.1) P := by
      refine (hΦ.comp_aemeasurable hc).congr (ae_of_all _ fun ω => ?_)
      funext ρ
      exact (pairTest_eq_reconstruct (Y ω) ρ.1).symm
    exact (hc.prodMk h2).prodMk hd
  have hDm : AEMeasurable (E6.dataFull (wedgeConfig γ B Y)) P := hYm.prodMk hd
  rw [hstep1, E6.configLawFull_eq_map]
  exact map_fullData_eq_of_ae hGm hDm (fun _ => ae_of_all _ fun _ => rfl) hT
    (fun _ => ae_of_all _ fun _ => rfl)

end Thm18Asm
end QuantumZipper
