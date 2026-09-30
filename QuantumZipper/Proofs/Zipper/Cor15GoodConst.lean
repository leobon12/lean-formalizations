import QuantumZipper.Proofs.Zipper.Cor15LawCongr
import QuantumZipper.Proofs.Zipper.E1TransferRep
import QuantumZipper.Proofs.Zipper.UnzipFullSplit
import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.Zipper.Cor15LawTransfer

/-!
# Corollary 1.5(a), positive times: `Z_t` modulo additive constants

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
the paper gives no proof). Task COR15-R12, the doubt of `handoff/COR15.md` (R2): `b1Data`
normalizes the field (`nrm`), so the determination `hfac` needs `mod0Data (Z_t x)` to be
unchanged when a constant is added to `x.1`.

This is true only where the regularizing limits exist (`avgReg`, `evalReg` are `limUnder`s,
which commute with adding a constant only where the limits exist):

* `qBoundaryMeasure_addConst_ae`: `ν_{x+c} = e^{γc/2} ν_x` if the boundary circle averages
  converge at Lebesgue-a.e. real point (`BdryConvAE`), a weakening of
  `LocalRule.qBoundaryMeasure_addConst'` (which asks for convergence at every point of `ℍ̄`);
* `weldHomR_eq_of_smul`, `weldDriver_addConst_ae`: the welding function, hence the welding
  driver, is then unchanged;
* `evalReg_addConst_of_regShift'`: `evalReg (x+c) ν = evalReg x ν + c ν(ℂ)` for finite `ν`
  under `E1.RegShift x ν`;
* `pairRaw_coordChange_addConst`: raw pairings of a coordinate change with a mass-zero test
  function are unchanged, under `RegShift` at the two pushed signed parts;
* **`mod0Data_zipCapUp_fst_eq_fromC`**, **`mod0Data_zipCapUp_snd_eq_fromC`**: under these
  hypotheses the `configLawMod0` data of `Z_t x` is computed from the field
  `fromC (coordsFull (nrm x.1))` rebuilt from `b1Data x` (and from the driver of `x` on
  `(0,∞)`).

Own elementary arguments (bookkeeping of junk values; cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull

/-- The boundary circle averages of `x` converge at Lebesgue-a.e. real point, at every scale. -/
def BdryConvAE (x : FieldSample) : Prop :=
  ∀ k : ℕ, ∀ᵐ s : ℝ, ∃ l, Tendsto (fun n => x (foldedCircle (dyadicRoundC n (s : ℂ)) (radius k)))
    atTop (𝓝 l)

theorem bdryApprox_addConst_ae {x : FieldSample} (hx : BdryConvAE x) (γ c : ℝ) (k : ℕ) :
    bdryApprox γ (addConst x c) k =
      ENNReal.ofReal (Real.exp (γ * c / 2)) • bdryApprox γ x k := by
  unfold bdryApprox
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae ?_
  filter_upwards [hx k] with s hs
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [LocalRule.avgReg_addConst_of_tendsto hs, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [mul_add, Real.exp_add]
  ring_nf

theorem qBoundaryMeasure_addConst_ae {x : FieldSample} (hx : BdryConvAE x) (γ c : ℝ) :
    qBoundaryMeasure γ (addConst x c) =
      ENNReal.ofReal (Real.exp (γ * c / 2)) • qBoundaryMeasure γ x := by
  set C := ENNReal.ofReal (Real.exp (γ * c / 2))
  have hC0 : C ≠ 0 := LocalRule.ofReal_exp_ne_zero _
  have hCT : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have he : bdryApprox γ (addConst x c) = fun k => C • bdryApprox γ x k :=
    funext (bdryApprox_addConst_ae hx γ c)
  by_cases hex : ∃ ν, IsVagueLimitR (bdryApprox γ x) ν
  · obtain ⟨ν, hν⟩ := hex
    rw [qBoundaryMeasure_eq hν]
    refine qBoundaryMeasure_eq ?_
    rw [he]; exact BdryVague.IsVagueLimitR.const_smul hν ENNReal.ofReal_ne_top
  · have hex' : ¬∃ ν, IsVagueLimitR (bdryApprox γ (addConst x c)) ν := by
      rintro ⟨ν, hν⟩
      refine hex ⟨C⁻¹ • ν, ?_⟩
      have := BdryVague.IsVagueLimitR.const_smul hν (c := C⁻¹)
        (ENNReal.inv_ne_top.2 (LocalRule.ofReal_exp_ne_zero _))
      rw [he] at this
      simpa only [smul_smul, ENNReal.inv_mul_cancel hC0 hCT, one_smul] using this
    unfold qBoundaryMeasure
    rw [dif_neg hex, dif_neg hex', smul_zero]

/-- The welding function only sees the boundary measure up to a positive finite factor. -/
theorem weldHomR_eq_of_smul {γ : ℝ} {x x' : FieldSample} {C : ℝ≥0∞} (h0 : C ≠ 0) (hT : C ≠ ⊤)
    (h : qBoundaryMeasure γ x' = C • qBoundaryMeasure γ x) (s : ℝ) :
    weldHomR γ x' s = weldHomR γ x s := by
  have key : ∀ a b : ℝ≥0∞, C * a ≤ C * b ↔ a ≤ b := fun a b => ⟨fun h' => by
      have : C⁻¹ * (C * a) ≤ C⁻¹ * (C * b) := by gcongr
      rwa [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul, one_mul] at this,
    fun h' => by gcongr⟩
  unfold weldHomR
  simp only [h, Measure.smul_apply, smul_eq_mul, key]

theorem weldDriver_addConst_ae {x : FieldSample} (hx : BdryConvAE x) (γ c t : ℝ) :
    weldDriver γ (addConst x c) t = weldDriver γ x t := by
  have hw : ∀ s, weldHomR γ (addConst x c) s = weldHomR γ x s :=
    weldHomR_eq_of_smul (LocalRule.ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top
      (qBoundaryMeasure_addConst_ae hx γ c)
  have : IsWeldingDriver γ (addConst x c) t = IsWeldingDriver γ x t := by
    funext W'
    unfold IsWeldingDriver
    simp only [hw]
  unfold weldDriver
  rw [this]

/-- `evalReg` commutes with adding a constant, for a finite measure, under `RegShift`. -/
theorem evalReg_addConst_of_regShift' {y : FieldSample} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (h : E1.RegShift y ν) (c : ℝ) :
    evalReg (addConst y c) ν = evalReg y ν + c * (ν univ).toReal := by
  obtain ⟨hraw, hint, L, hL⟩ := h
  have hk : ∀ k : ℕ, ∫ z, avgReg (addConst y c) k z ∂ν =
      ∫ z, avgReg y k z ∂ν + c * (ν univ).toReal := by
    intro k
    rw [integral_congr_ae (hraw.mono fun z hz => LocalRule.avgReg_addConst_of_tendsto (hz k) c),
      integral_add (hint k) (integrable_const c)]
    simp [integral_const, Measure.real, mul_comm]
  have h2 : Tendsto (fun k => ∫ z, avgReg (addConst y c) k z ∂ν) atTop
      (𝓝 (L + c * (ν univ).toReal)) := by
    simpa only [hk] using hL.add_const (c * (ν univ).toReal)
  unfold evalReg
  rw [h2.limUnder_eq, hL.limUnder_eq]

theorem isFiniteMeasure_tdens (ρ : TestFun H) : IsFiniteMeasure (CharFun.tdens ρ.1) := by
  unfold CharFun.tdens
  exact isFiniteMeasure_withDensity_ofReal (TReg.integrable_tf ρ).2

theorem isFiniteMeasure_tdens_neg (ρ : TestFun H) :
    IsFiniteMeasure (CharFun.tdens fun z => -ρ.1 z) := by
  unfold CharFun.tdens
  exact isFiniteMeasure_withDensity_ofReal (TReg.integrable_tf ρ).neg.2

/-- Raw pairings of a coordinate change with a mass-zero test function do not see additive
constants, when the two pushed signed parts satisfy `RegShift`. -/
theorem pairRaw_coordChange_addConst {x : FieldSample} {f : ℂ → ℂ} {Q : ℝ} (ρ : TestFun0 H)
    (hf₁ : AEMeasurable f (CharFun.tdens ρ.1.1))
    (hf₂ : AEMeasurable f (CharFun.tdens fun z => -ρ.1.1 z))
    (hp : E1.RegShift x ((CharFun.tdens ρ.1.1).map f))
    (hm : E1.RegShift x ((CharFun.tdens fun z => -ρ.1.1 z).map f)) (c : ℝ) :
    pairRaw (coordChange (addConst x c) f Q) ρ.1.1 = pairRaw (coordChange x f Q) ρ.1.1 := by
  have := isFiniteMeasure_tdens ρ.1
  have := isFiniteMeasure_tdens_neg ρ.1
  have hmass := tdens_univ_sub ρ.1
  rw [ρ.2] at hmass
  show coordChange (addConst x c) f Q (CharFun.tdens ρ.1.1) -
      coordChange (addConst x c) f Q (CharFun.tdens fun z => -ρ.1.1 z) =
    coordChange x f Q (CharFun.tdens ρ.1.1) - coordChange x f Q (CharFun.tdens fun z => -ρ.1.1 z)
  unfold coordChange
  rw [evalReg_addConst_of_regShift' hp, evalReg_addConst_of_regShift' hm,
    Measure.map_apply_of_aemeasurable hf₁ MeasurableSet.univ,
    Measure.map_apply_of_aemeasurable hf₂ MeasurableSet.univ]
  simp only [Set.preimage_univ]
  linear_combination c * hmass

/-- The field rebuilt from the `b1Data` coordinates. -/
def fieldOf (x : FieldSample) : FieldSample := E1.fromC (coordsFull (nrm x))

theorem regEq_fieldOf (x : FieldSample) : RegEq (fieldOf x) (nrm x) :=
  UnzipFull.regEq_of_coordsFull (E1.coordsFull_fromC _)

theorem nrm_eq_addConst (x : FieldSample) : nrm x = addConst x (-(x (foldedCircle 0 1))) := rfl

theorem weldDriver_fieldOf {x : FieldSample} (hx : BdryConvAE x) (γ t : ℝ) :
    weldDriver γ (fieldOf x) t = weldDriver γ x t := by
  rw [weldDriver_congr_regEq (regEq_fieldOf x), nrm_eq_addConst, weldDriver_addConst_ae hx]

/-- **Pairing half of the determination of `Z_t x` by `b1Data x`.** -/
theorem mod0Data_zipCapUp_fst_eq_fromC {γ t : ℝ} {x : FieldSample × (ℝ → ℝ)}
    (hx : BdryConvAE x.1) (ρ : TestFun0 H)
    (hf₁ : AEMeasurable (revMapInv (weldDriver γ x.1 t) t) (CharFun.tdens ρ.1.1))
    (hf₂ : AEMeasurable (revMapInv (weldDriver γ x.1 t) t) (CharFun.tdens fun z => -ρ.1.1 z))
    (hp : E1.RegShift x.1 ((CharFun.tdens ρ.1.1).map (revMapInv (weldDriver γ x.1 t) t)))
    (hm : E1.RegShift x.1
      ((CharFun.tdens fun z => -ρ.1.1 z).map (revMapInv (weldDriver γ x.1 t) t))) :
    (mod0Data (zipCapUp γ t x)).1 ρ =
      pairRaw (coordChange (fieldOf x.1) (revMapInv (weldDriver γ (fieldOf x.1) t) t) (Qc γ))
        ρ.1.1 := by
  rw [weldDriver_fieldOf hx, coordChange_congr_regEq (regEq_fieldOf x.1), nrm_eq_addConst,
    pairRaw_coordChange_addConst ρ hf₁ hf₂ hp hm]
  rfl

end Cor15Group
end QuantumZipper
