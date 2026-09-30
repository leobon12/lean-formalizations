import QuantumZipper.Proofs.Zipper.E5Palm2Drv
import QuantumZipper.Proofs.Zipper.E5LocB
import QuantumZipper.Proofs.LQG.LogSingGood

/-!
# E5-PALM2, part 5: `ModelGood` (proved)

Task E5-PALM2. The collision target field is
`targetColl κ V τ ϖ X' = X' + shiftFun(√κ, 𝔥₀, ϖ_τ, 0) + const`, and
`shiftFun(√κ, 𝔥₀, ϖ_τ, 0) = α (−log|·|) − (√κ/2) k_{ϖ_τ}` with `α = √κ − 2/√κ < Q`
(`TRegE4.shiftFun_zero_eq`). So `targetColl` is (on the circle coordinates, which is all that
goodness reads: `WedgeGood.isLQGGood_congr_coords`) the free field plus an `α`-log singularity at
`0` (a.s. good: `LogSingGood.logSingGoodAS_holds`, M4-P4) plus the continuous function
`−(√κ/2) k_{ϖ_τ}` (`E5.continuous_kPot_varpiT`, rule (5.1) `IsLQGGood.add_ofFun`), plus constants
(`IsLQGGood.addConst`).

Main result `modelGood_holds : E5.Setup … → IsFreeGFFModConstH X' P' → ModelGood …`.
Own bookkeeping around the cited repository results.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1 CoordsFull E4Grid

/-- **Goodness of the collision target field** (deterministic): if `k_{ϖ_t}` is continuous and
`Y + α(−log|·|)` is good, `α = √κ − 2/√κ`, then `targetColl κ V t ϖ Y` is good. -/
theorem isLQGGood_targetColl {κ : ℝ} {V : ℝ → ℝ} {t : ℝ} {ϖ : Measure ℂ} {Y : FieldSample}
    (hk : Continuous (PalmNorm.kPot (varpiT V t ϖ)))
    (hY : IsLQGGood (Real.sqrt κ)
      (Y + ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖)) :
    IsLQGGood (Real.sqrt κ) (targetColl κ V t ϖ Y) := by
  set γ := Real.sqrt κ
  set ϖ' := varpiT V t ϖ
  set g : ℂ → ℝ := fun u => -(γ / 2) * PalmNorm.kPot ϖ' u with hg
  have hgc : Continuous g := continuous_const.mul hk
  have h1 := hY.add_ofFun hgc.continuousOn
  have hc : Factorization.coords (ofFun (PalmNorm.shiftFun γ (h0rev κ) ϖ' 0) + Y) =
      Factorization.coords ((Y + ofFun fun z => (γ - 2 / γ) * -Real.log ‖z‖) + ofFun g) := by
    funext i
    simp only [Factorization.coords, Pi.add_apply, ofFun]
    set c := (Factorization.dyadicIndex i).1
    set ρ := radius (Factorization.dyadicIndex i).2
    have hρ : 0 < ρ := radius_pos _
    have hlog := CoordReg.integrable_log_norm_foldedCircle c ρ
    have hgi : Integrable g (foldedCircle c ρ) :=
      integrable_foldedCircle_of_continuousOn (r := ‖c‖ + ρ + 1) hgc.continuousOn c ρ hρ
        (lt_add_one _)
    have hS : ∫ v, PalmNorm.shiftFun γ (h0rev κ) ϖ' 0 v ∂foldedCircle c ρ =
        (2 / Real.sqrt κ - γ) * ∫ v, Real.log ‖v‖ ∂foldedCircle c ρ +
          ∫ v, g v ∂foldedCircle c ρ := by
      rw [TRegE4.shiftFun_zero_eq, ← integral_const_mul]
      exact integral_add (hlog.const_mul _) hgi
    rw [hS]
    have e : ∫ v, (γ - 2 / γ) * -Real.log ‖v‖ ∂foldedCircle c ρ =
        (2 / Real.sqrt κ - γ) * ∫ v, Real.log ‖v‖ ∂foldedCircle c ρ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [γ]; ring
    rw [e]
    ring
  have h2 := (WedgeGood.isLQGGood_congr_coords hc).2 h1
  exact (h2.addConst _).addConst _

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → FieldSample}

/-- **`ModelGood` holds.** -/
theorem modelGood_holds (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P') (δ : ℝ) :
    ModelGood κ T P B X ϖ P' X' δ := by
  obtain ⟨hκ, hκ4, -, hB, -, -, hϖ⟩ := hS
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := (Real.sqrt_lt' two_pos).2 (by linarith)
  have hα : Real.sqrt κ - 2 / Real.sqrt κ < Qc (Real.sqrt κ) := by
    unfold Qc
    have h : 1 < 2 / Real.sqrt κ := (one_lt_div hγ).2 hγ2
    linarith
  have hLS := LogSingGood.logSingGoodAS_holds hγ hγ2 hα Ω' _ P' X' inferInstance hX'
  filter_upwards [hB.cont] with ω hc
  refine Eventually.of_forall fun x _ => ?_
  filter_upwards [hLS] with ω' h'
  exact isLQGGood_targetColl
    (continuous_kPot_varpiT hϖ (continuous_Vr_e5 (κ := κ) (T := T) hc) ENNReal.toReal_nonneg) h'

end E5
end QuantumZipper
